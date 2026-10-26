const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Declarations = @import("Declarations.zig");
const Value = @import("../interpreter/Value.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// types: type expressions lowered to pool types, type definitions with their members,
// traits and conformance
const Types = @This();

// a primitive type node `type_X` stands for the pool type `X_type`
const primitive_types = blk: {
    var table: [256]StaticPool.Index = @splat(.none);
    const info = @typeInfo(StaticPool.Index).@"enum";
    for (info.field_names, info.field_values) |fname, fvalue| {
        if (!std.mem.endsWith(u8, fname, "_type")) continue;
        const kind_name = "type_" ++ fname[0 .. fname.len - 5];
        if (!@hasField(ParseTree.Node.Kind, kind_name)) continue;
        table[@backingInt(@field(ParseTree.Node.Kind, kind_name))] =
            @fromBackingInt(fvalue);
    }
    break :blk table;
};

pub fn owning_resolver(self: *Types) *Resolver {
    return @alignCast(@fieldParentPtr("types", self));
}

pub fn meta_type_of_node(self: *Types, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const kind = resolver.declarations.declared_type_kind(node);
    const is_unified = resolver.tree.kind(node) == .unify_variants or
        resolver.tree.kind(node) == .unify_variants_packed or
        resolver.tree.kind(node) == .variant_difference;
    return kind.meta_type(if (is_unified) .variant_type else .type_type);
}

// ------------------------------------------------------------------------------------------ //
// type expressions
// ------------------------------------------------------------------------------------------ //

pub fn type_from_node(self: *Types, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const kind = resolver.tree.kind(node);
    const primitive = primitive_types[@backingInt(kind)];
    if (primitive != .none) return primitive;

    return switch (kind) {
        .capture => self.type_from_node(context, resolver.tree.arg(node, 0)),
        .typeof => self.type_of_expression(context, node),
        .type_ptr, .type_ptrmut => {
            const pointee = self.type_from_node(context, resolver.tree.arg(node, 0));
            return resolver.static_pool.pointer_to(pointee, kind == .type_ptrmut);
        },
        .type_array_unlengthed => self.unlengthed_array_type(context, node),
        .type_slice => {
            const element = self.type_from_node(context, resolver.tree.arg(node, 0));
            if (element == .poison_type) return element;
            return resolver.static_pool.slice_of(element);
        },
        .type_array => self.lengthed_array_type(context, node),
        .def_fun_declaration => self.function_type_of(context, node, .default, .unit_type, .none),
        else => self.type_from_static_value(context, node),
    };
}

fn type_of_expression(self: *Types, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const operand = resolver.tree.arg(node, 0);
    const operand_type = resolver.expressions.infer(context, operand, .none);
    const operand_kind = resolver.tree.kind(operand);

    const names_template = operand_kind == .identifier and
        resolver.generics.is_template(resolver.node_declarations[operand]);
    if (names_template) return resolver.report(.unrealized_template, operand, 0, 0);

    if (operand_kind == .identifier_self) return resolver.static_pool.pointee(operand_type);
    return operand_type;
}

// an unlengthed array gets a var as its length: inferred from the value, or per call for parameters
// record fields, `main` parameters and lengths nothing fixes become runtime lengths later on
// trees are listed by macros as they come, `[]ast` has no length to infer
fn unlengthed_array_type(self: *Types, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const element = self.type_from_node(context, resolver.tree.arg(node, 0));
    const length = if (resolver.tree.macros and static_pool.is_tree(element))
        StaticPool.dyn_len
    else
        static_pool.fresh_type_variable(node);
    return static_pool.intern(.{ .array_type = .{ .length = length, .element = element } });
}

fn lengthed_array_type(self: *Types, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const length_node = resolver.tree.arg(node, 0);
    const length_value = resolver.static_values.evaluate_or_defer(context, length_node) orelse
        .poison_type;
    const length: StaticPool.Index = blk: {
        if (static_pool.tag(length_value) == .int_value) {
            const bits = static_pool.get(length_value).int_value.bits;
            break :blk static_pool.intern(.{ .int_value = .{
                .value_type = .u64_type,
                .bits = bits,
            } });
        }
        if (length_value == .poison_type) break :blk length_value;
        break :blk resolver.report(.not_static, length_node, length_value, 0);
    };
    const element = self.type_from_node(context, resolver.tree.arg(node, 1));
    const array_type = StaticPool.ArrayType{ .length = length, .element = element };
    return resolver.static_pool.intern(.{ .array_type = array_type });
}

fn type_from_static_value(
    self: *Types,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    // a loop makes an array and never a type, an interpreted body would leave it unchecked
    if (context.is_interpreted and resolver.tree.props(node).loop) {
        const inferred = resolver.expressions.infer(context, node, .none);
        return resolver.report(.not_a_type, node, inferred, .none);
    }

    const value = resolver.static_values.evaluate_or_defer(context, node) orelse .poison_type;
    if (static_pool.tag(value) == .static_function) {
        const declaration = static_pool.get(value).static_function.declaration;
        const function_type = resolver.decl_pool.get(declaration, .value_type);
        const return_type = static_pool.get(function_type).function_type.return_type;
        if (static_pool.tag(return_type) == .meta_type) {
            return static_pool.intern(.{ .template_type = declaration });
        }
    }

    if (value == .poison_type or static_pool.properties(value).is_type) return value;
    return resolver.report(.not_a_type, node, value, .none);
}

pub fn define_static_type(
    self: *Types,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    return switch (resolver.tree.kind(node)) {
        .unify_variants, .unify_variants_packed => self.unified_variant_type(context, node),
        .variant_difference => {
            const sides = [_]NodeId{ resolver.tree.arg(node, 0), resolver.tree.arg(node, 1) };
            const types = [_]StaticPool.Index{
                self.type_from_node(context, sides[0]),
                self.type_from_node(context, sides[1]),
            };
            if (types[0] == .poison_type or types[1] == .poison_type) return .poison_type;
            // the left side needs a variant with tags, the right side parts of it
            return switch (resolver.static_pool.difference_of(types[0], types[1])) {
                .difference => |difference| difference,
                .wrong_side => |i| {
                    const expected = if (i == 0) StaticPool.Index.variant_type else types[0];
                    return resolver.report(.type_mismatch, sides[i], types[i], expected);
                },
            };
        },
        .def_type,
        .def_type_packed,
        .def_type_assertsize,
        .def_type_implof,
        .def_variant,
        .def_variant_packed,
        .def_variant_tagtype,
        .def_variant_notagtype,
        .def_variant_assertsize,
        .def_variant_implof,
        .def_trait,
        .def_trait_implof,
        => {
            const kind = resolver.declarations.declared_type_kind(node);
            const declaration = resolver.decl_pool.push(.empty, node, kind, .none, .{});
            resolver.node_declarations[node] = declaration;
            return self.check_type_definition(context, declaration, node);
        },
        .def_fun => {
            _ = resolver.expressions.infer(context, node, .none);
            return resolver.decl_pool.get(resolver.node_declarations[node], .static_value);
        },
        else => {
            if (resolver.tree.props(node).type_expr) return self.type_from_node(context, node);
            return resolver.report(.not_static, node, 0, 0);
        },
    };
}

// `A || B`, `A ||| B` (see `StaticPool.unified_of`)
fn unified_variant_type(self: *Types, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const sides = [_]NodeId{ resolver.tree.arg(node, 0), resolver.tree.arg(node, 1) };
    const types = [_]StaticPool.Index{
        self.type_from_node(context, sides[0]),
        self.type_from_node(context, sides[1]),
    };
    const is_packed = resolver.tree.kind(node) == .unify_variants_packed;
    // a strategy stores its variant in all of its storage, no unified tag fits beside it
    const static_pool = &resolver.static_pool;
    for (sides, types) |side, side_type| {
        const whole = static_pool.whole_of(side_type);
        const is_custom = static_pool.tag(whole) == .variant_type and
            static_pool.get(whole).variant_type.tag_mode == .custom;
        if (is_custom) return resolver.report(.strategy_member, side, side_type, 0);
    }
    return switch (resolver.static_pool.unified_of(types[0], types[1], is_packed)) {
        .unified => |unified| unified,
        .sizeless_side => |i| resolver.report(.unstorable_outside_parameter, sides[i], types[i], 0),
    };
}

// ------------------------------------------------------------------------------------------ //
// type definitions
// ------------------------------------------------------------------------------------------ //

// the traits a record or variant implements, its anonymous `!{..}` body first
const ImplementedTraits = struct {
    // completed after the type: member signatures may realize types that construct this one
    own: StaticPool.Index,
    traits: []StaticPool.Index,
};

pub fn check_type_definition(
    self: *Types,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;
    const definition = ParseTree.Def.from_node(resolver.tree, node);
    const core = definition.core;
    const core_kind = resolver.tree.kind(core);
    const is_trait = core_kind == .def_trait or core_kind == .def_trait_implof;
    var first_local = decl_pool.entries.len();

    // reserved first (or already by `instantiate`), so fields can point back at the type (`*Tree`)
    if (decl_pool.get(declaration, .static_value) == .none) {
        decl_pool.set(declaration, .static_value, static_pool.reserve_nominal(declaration));
    }
    const nominal = decl_pool.get(declaration, .static_value);
    const meta_type = resolver.declarations.declared_type_kind(core).meta_type(.type_type);
    decl_pool.set(declaration, .value_type, meta_type);
    if (decl_pool.get(declaration, .state) == .resolving_signature) {
        decl_pool.set(declaration, .state, .signature_ready);
    }
    resolver.scopes.open();
    defer resolver.scopes.close();

    const body = definition.body;
    // `!{..}` keeps its members in argument 0, `implof(..) !{..}` in argument 1
    const members = if (!is_trait and body != 0)
        resolver.tree.arg(body, if (resolver.tree.kind(body) == .def_trait_implof) 1 else 0)
    else
        0;
    const implemented: ImplementedTraits = blk: {
        // `implof(A, B) X` names its traits in argument 0, anything else implements none
        const trait_nodes: []const NodeId = if (members != 0 and
            resolver.tree.kind(body) == .def_trait_implof)
            resolver.tree.manychildren(resolver.tree.arg(body, 0))
        else
            &.{};
        const traits = resolver.temporary_slice(StaticPool.Index, trait_nodes.len + 1);
        if (members == 0) break :blk .{ .own = .none, .traits = traits[0..0] };

        var own: StaticPool.Index = .none;
        var count: usize = 0;
        if (resolver.tree.manychildren(members).len > 0) {
            own = static_pool.reserve_nominal(declaration);
            traits[0] = own;
            count = 1;
        }
        count += self.resolve_traits(context, trait_nodes, traits[count..]);
        break :blk .{ .own = own, .traits = traits[0..count] };
    };
    var own = implemented.own;

    switch (core_kind) {
        .def_trait, .def_trait_implof => {
            own = self.define_trait(context, declaration, nominal, core);
        },
        .def_variant, .def_variant_packed => {
            self.define_variant(context, declaration, nominal, definition, implemented.traits);
        },
        // records: `*(..)`, `**(..)` and payload tuples
        else => self.define_record(context, declaration, nominal, core, implemented.traits),
    }

    if (own != .none and !is_trait) {
        _ = self.trait_body(context, members, own, nominal, &.{}, declaration);
    }
    // member bodies once the type is complete, before the fields are names
    if (own != .none) {
        const trait = static_pool.get(own).trait_type;
        const member_count = trait.member_names.len;
        for (0..member_count) |i| resolver.declarations.check_body(trait.declaration.member(i));
        resolver.mutability.propagate_writes(trait.declaration, member_count);
    }
    // defaults and where-clauses see the fields by name, the snapshot's locals start at them
    if (static_pool.tag(nominal) == .record_type) {
        const fields = resolver.tree.fields_of(core);
        first_local = decl_pool.entries.len();
        for (fields, 0..) |field_node, i| {
            const field_type = static_pool.field_type(nominal, i);
            const name = static_pool.get(nominal).record_type.field_names[i];
            const field_declaration =
                resolver.declarations.declare_local(name, field_node, .field, field_type);
            const field = ParseTree.Param.from_node(resolver.tree, field_node);
            decl_pool.pointer(field_declaration, .flags).is_mut = field.is_mut;
            resolver.declarations.link_identifier(field.name, field_declaration, field_type);
        }

        // a default sees the fields before its own, a where-clause all of them
        const first_field = resolver.scopes.local_names.len - fields.len;
        const names = resolver.temporary_slice(NamePool.Index, fields.len);
        @memcpy(names, resolver.scopes.local_names.buffer[first_field..][0..fields.len]);
        @memset(resolver.scopes.local_names.buffer[first_field..][0..fields.len], .empty);

        for (fields, 0..) |field_node, i| {
            const field = ParseTree.Param.from_node(resolver.tree, field_node);
            if (field.default != 0) {
                const field_type = static_pool.field_type(nominal, i);
                _ = resolver.expressions.check(context, field.default, field_type);
            }
            resolver.scopes.local_names.buffer[first_field + i] = names[i];
        }
        for (fields, 0..) |field_node, i| {
            const field = ParseTree.Param.from_node(resolver.tree, field_node);
            const field_type = static_pool.field_type(nominal, i);
            resolver.declarations.check_parameter_guards(context, field, field_type);
        }
    }
    if (!is_trait) {
        for (implemented.traits) |trait| {
            if (trait == own or static_pool.tag(trait) != .trait_type) continue;
            self.conform(nominal, own, trait, node);
        }
        if (static_pool.layout(nominal).state == .infinite) {
            _ = resolver.report(.recursive_by_value_type, node, nominal, .none);
        }
        resolver.bodies.register(resolver.capture_body(declaration, node, first_local));
    }
    if (definition.size != 0) {
        const size_node = definition.size;
        const value = resolver.interpreter.evaluate_static(context, size_node);
        if (value == .poison_type) return nominal;
        // `assertsize(T)` asks for the size of `T`, `assertsize(8)` for 8 bytes
        const wanted_size: u64 = if (static_pool.properties(value).is_type)
            static_pool.layout(value).size
        else if (static_pool.tag(value) == .int_value)
            static_pool.get(value).int_value.bits
        else {
            // a size is asserted as a type or a byte count
            _ = resolver.report(.type_mismatch, size_node, static_pool.type_of(value), .u64_type);
            return nominal;
        };

        const actual_size = static_pool.layout(nominal).size;
        if (actual_size != wanted_size) {
            _ = resolver.report(.assertsize_failed, size_node, actual_size, wanted_size);
        }
    }
    return nominal;
}

// the traits named by `trait_nodes` into `traits`, poisoned ones left out; returns their count
fn resolve_traits(
    self: *Types,
    context: *FunctionContext,
    trait_nodes: []const NodeId,
    traits: []StaticPool.Index,
) usize {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    var count: usize = 0;
    for (trait_nodes) |trait_node| {
        traits[count] = self.type_from_node(context, trait_node);
        const is_trait = static_pool.tag(traits[count]) == .trait_type;
        if (traits[count] != .poison_type and !is_trait) {
            traits[count] = resolver.report_mismatch(trait_node, traits[count], .trait_type);
        }
        count += @intFromBool(traits[count] != .poison_type);
    }
    return count;
}

fn define_trait(
    self: *Types,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    nominal: StaticPool.Index,
    core: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const is_implof = resolver.tree.kind(core) == .def_trait_implof;
    // `implof(A, B) X` names its traits in argument 0, anything else implements none
    const super_nodes: []const NodeId = if (is_implof)
        resolver.tree.manychildren(resolver.tree.arg(core, 0))
    else
        &.{};
    const super_traits = resolver.temporary_slice(StaticPool.Index, super_nodes.len);
    const super_count = self.resolve_traits(context, super_nodes, super_traits);
    // `!{..}` keeps its members in argument 0, `implof(..) !{..}` in argument 1
    const members = resolver.tree.arg(core, if (is_implof) 1 else 0);
    const resolved_supers = super_traits[0..super_count];
    return self.trait_body(context, members, nominal, .none, resolved_supers, declaration);
}

// the parts of one variant case `name: Payload = tag`, absent parts are 0
const VariantCaseParts = struct { name: NodeId, tag: NodeId, payload: NodeId };

// which cases carry a payload: how many and the last one
const PayloadSummary = struct { count: usize = 0, last_case: ?usize = null };

fn define_variant(
    self: *Types,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    nominal: StaticPool.Index,
    definition: ParseTree.Def,
    traits: []const StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const core = definition.core;
    const tagof = definition.tagtype;
    const case_nodes = resolver.tree.manychildren(resolver.tree.arg(core, 0));
    const cases = resolver.temporary_slice(StaticPool.Index, case_nodes.len);
    var payloads = PayloadSummary{};
    var payload_name: NodeId = 0;
    var next_tag: StaticPool.IntValue = .{ .value_type = .u64_type, .bits = 0 };
    for (case_nodes, 0..) |case_node, i| {
        var parts = VariantCaseParts{ .name = 0, .tag = 0, .payload = 0 };
        var inner = case_node;
        if (resolver.tree.kind(inner) == .partial__variant_def_param_tagged) {
            parts.tag = resolver.tree.arg(inner, 1);
            inner = resolver.tree.arg(inner, 0);
        }
        if (resolver.tree.kind(inner) == .partial__variant_def_param_typed) {
            parts.payload = resolver.tree.arg(inner, 1);
            inner = resolver.tree.arg(inner, 0);
        }
        const is_case = resolver.tree.kind(inner) == .partial__variant_def_param and
            resolver.tree.kind(resolver.tree.arg(inner, 0)) == .identifier;
        if (!is_case) {
            const Kind = ParseTree.Node.Kind;
            const found_kind = @as(u16, @backingInt(resolver.tree.kind(inner))) + 1;
            const case_kind = @as(u16, @backingInt(Kind.partial__variant_def_param)) + 1;
            const found = static_pool.ast_type_of(.none, found_kind);
            const wanted = static_pool.ast_type_of(.none, case_kind);
            _ = resolver.report(.type_mismatch, case_node, found, wanted);
        }
        parts.name = if (is_case) resolver.tree.arg(inner, 0) else case_node;
        const payload = if (parts.payload == 0)
            .none
        else
            self.check_type_definition(
                context,
                resolver.decl_pool.push(.empty, parts.payload, .record, .none, .{}),
                parts.payload,
            );

        const tag_value = if (parts.tag == 0)
            static_pool.intern(.{ .int_value = next_tag })
        else
            resolver.interpreter.evaluate_static(context, parts.tag);
        if (static_pool.tag(tag_value) == .int_value) {
            const int = static_pool.get(tag_value).int_value;
            next_tag = .{ .value_type = int.value_type, .bits = int.bits +% 1 };
        } else if (tag_value != .poison_type) {
            _ = resolver.report_mismatch(parts.tag, static_pool.type_of(tag_value), .u64_type);
        }

        const name = if (is_case) resolver.name_pool.name_of_node(parts.name) else .empty;
        for (cases[0..i]) |previous| {
            if (static_pool.get(previous).variant_case_type.name != name) continue;
            // one report per repeated case, like fields and parameters
            resolver.doctor.report(.duplicate_declaration, case_node, name, declaration);
            break;
        }

        const case_type = static_pool.intern(.{ .variant_case_type = .{
            .variant = nominal,
            .case_index = @intCast(i),
            .name = name,
            .tag = tag_value,
            .payload = payload,
        } });
        cases[i] = resolver.set_node_type(parts.name, case_type);
        if (static_pool.get(cases[i]).variant_case_type.payload == .none) continue;
        payloads.last_case = i;
        payload_name = parts.name;
        payloads.count += 1;
    }

    // without tagof by the smallest tag type holding their tags, `notagtype` without any tag.
    // `tagtype self.f.g` keeps the tag in that field of the payload
    const tree = resolver.tree;
    var tag_names: std.ArrayList(NodeId) = .empty;
    defer tag_names.deinit(resolver.allocator);
    var tag_root = tagof;
    while (tag_root != 0 and tree.kind(tag_root) == .member) : (tag_root = tree.arg(tag_root, 0)) {
        tag_names.insert(resolver.allocator, 0, tree.arg(tag_root, 1)) catch @panic("OOM");
    }
    const is_self_tagged = tag_root != 0 and tree.kind(tag_root) == .identifier_self;
    var tag_path: std.ArrayList(u32) = .empty;
    defer tag_path.deinit(resolver.allocator);
    // `tagtype <static expr>` of a record of `storage`, `wrap`, `case_of` and `unwrap`: a strategy,
    // its parts as `[storage, wrap, case_of, unwrap]`
    const strategy: StaticPool.Index = strategy: {
        if (tagof == 0 or is_self_tagged) break :strategy .none;
        const value = resolver.static_values.try_evaluate(context, tagof) orelse
            break :strategy .none;
        if (static_pool.tag(value) != .aggregate_value) break :strategy .none;
        const record_type = static_pool.type_of(value);
        if (static_pool.tag(record_type) != .record_type) break :strategy .none;
        const names = [_][]const u8{ "storage", "wrap", "case_of", "unwrap" };
        var parts: [names.len]StaticPool.Index = undefined;
        for (names, &parts) |text, *part| {
            const name = resolver.name_pool.intern(text);
            const field_names = static_pool.get(record_type).record_type.field_names;
            const index = std.mem.indexOfScalar(NamePool.Index, field_names, name) orelse
                break :strategy .none;
            part.* = static_pool.get(value).aggregate_value.elements[index];
        }
        const strategy_parts = StaticPool.AggregateValue{ .value_type = .none, .elements = &parts };
        break :strategy static_pool.intern(.{ .aggregate_value = strategy_parts });
    };
    const mode: StaticPool.VariantTagMode = if (strategy != .none)
        .custom
    else if (is_self_tagged)
        .self
    else if (definition.untagged)
        .none
    else
        .int;
    // a self tag tells the payload case by its niche: its own tag is one no other case has
    if (mode == .self and payloads.count == 1) {
        const payload_index = payloads.last_case.?;
        var case = static_pool.get(cases[payload_index]).variant_case_type;
        // the smallest tag no other case has, and whether the payload case's own is taken
        var free: u64 = 0;
        var own_is_taken = false;
        const own: ?u64 = if (static_pool.tag(case.tag) == .int_value)
            static_pool.get(case.tag).int_value.bits
        else
            null;
        var searching = true;
        while (searching) {
            searching = false;
            for (cases, 0..) |other, i| {
                const tag = static_pool.get(other).variant_case_type.tag;
                if (i == payload_index or static_pool.tag(tag) != .int_value) continue;
                const bits = static_pool.get(tag).int_value.bits;
                own_is_taken = own_is_taken or bits == own;
                if (bits != free) continue;
                free += 1;
                searching = true;
            }
        }
        if (own_is_taken) {
            const free_tag = StaticPool.IntValue{ .value_type = .u64_type, .bits = free };
            case.tag = static_pool.intern(.{ .int_value = free_tag });
            const retagged = static_pool.intern(.{ .variant_case_type = case });
            cases[payload_index] = resolver.set_node_type(payload_name, retagged);
        }
    }
    const tag_type: StaticPool.Index = blk: {
        if (mode == .none) break :blk .unit_type;
        if (tagof == 0) {
            var tag_count: u64 = cases.len;
            for (cases) |case| {
                const tag = static_pool.get(case).variant_case_type.tag;
                if (static_pool.tag(tag) != .int_value) continue;
                tag_count = @max(tag_count, static_pool.get(tag).int_value.bits +| 1);
            }
            break :blk StaticPool.smallest_tag_type(tag_count);
        }
        // a strategy takes and gives the tags of the cases as `u32`s
        if (mode == .custom) break :blk .u32_type;
        if (mode != .self) break :blk self.type_from_node(context, tagof);

        // the one payload type encodes the other cases in bit patterns it never uses
        if (payloads.count != 1) {
            break :blk resolver.report(.self_tag_without_niche, tagof, payloads.count, 0);
        }
        const payload = static_pool.get(cases[payloads.last_case.?]).variant_case_type.payload;
        // each name a field of the record reached so far, or of the one record it holds
        var field_type = payload;
        for (tag_names.items) |name_node| {
            const name = resolver.name_pool.name_of_node(name_node);
            while (true) {
                if (static_pool.tag(field_type) != .record_type) {
                    break :blk resolver.report(.unknown_member, name_node, name, field_type);
                }
                const record = static_pool.get(field_type).record_type;
                if (std.mem.indexOfScalar(NamePool.Index, record.field_names, name)) |index| {
                    tag_path.append(resolver.allocator, @intCast(index)) catch @panic("OOM");
                    field_type = record.field_types[index];
                    break;
                }
                if (record.field_types.len != 1) {
                    break :blk resolver.report(.unknown_member, name_node, name, field_type);
                }
                tag_path.append(resolver.allocator, 0) catch @panic("OOM");
                field_type = record.field_types[0];
            }
        }
        if (tag_names.items.len == 0) {
            if (static_pool.get(payload).record_type.field_types.len != 1) {
                break :blk resolver.report(.self_tag_without_niche, tagof, 0, 0);
            }
            tag_path.append(resolver.allocator, 0) catch @panic("OOM");
            field_type = static_pool.get(payload).record_type.field_types[0];
        }
        const field = static_pool.properties(field_type);
        if (field.is_integer) break :blk field_type;
        // the bits of any other scalar are an unsigned int of its size: the null address, the
        // byte values a bool never has
        if (!field.is_float and !field.is_pointer and field_type != .bool_type) {
            break :blk resolver.report(.self_tag_without_niche, tagof, 0, 0);
        }
        break :blk switch (static_pool.layout(field_type).size) {
            1 => .u8_type,
            2 => .u16_type,
            4 => .u32_type,
            else => .u64_type,
        };
    };
    // with a self tag the payload case is told apart by its niche, it has no tag value to overflow
    if (tag_type != .none and tag_type != .poison_type) {
        for (case_nodes, 0..) |case_node, i| {
            const case = static_pool.get(cases[i]).variant_case_type;
            if (mode == .self and case.payload != .none) continue;
            // without a tag only a written one overflows
            const is_written = resolver.tree.kind(case_node) == .partial__variant_def_param_tagged;
            if (mode == .none and !is_written) continue;
            if (static_pool.tag(case.tag) != .int_value) continue;
            if (static_pool.fits(case.tag, tag_type)) continue;
            _ = resolver.report(.tag_overflow, case_node, case.tag, tag_type);
        }
    }

    if (mode == .custom and tag_type == .u32_type) {
        self.verify_strategy(context, tagof, strategy, cases);
    }

    static_pool.complete_nominal(nominal, .{ .variant_type = .{
        .declaration = declaration,
        .tag_mode = mode,
        .tag_type = tag_type,
        .tag_path = tag_path.items,
        .strategy = strategy,
        .is_packed = resolver.tree.kind(core) == .def_variant_packed,
        .cases = cases[0..case_nodes.len],
        .traits = traits,
    } });
}

// a strategy gives every case and payload back as they went in, its stored bits fit `storage`.
// probed with payloads 0, 1, all ones, alternating bits and the top bit, every one up to 16 bits
fn verify_strategy(
    self: *Types,
    context: *FunctionContext,
    node: NodeId,
    strategy: StaticPool.Index,
    cases: []const StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const interpreter = &resolver.interpreter;
    var parts: [4]StaticPool.Index = undefined;
    @memcpy(&parts, static_pool.get(strategy).aggregate_value.elements);
    const storage, const wrap, const case_of, const unwrap = parts;
    if (static_pool.tag(storage) != .int_type) {
        _ = resolver.report(.type_mismatch, node, static_pool.type_of(storage), .u64_type);
        return;
    }
    const storage_bits = static_pool.get(storage).int_type.bits;
    for (cases) |case_index| {
        const case = static_pool.get(case_index).variant_case_type;
        const tag: u64 = if (static_pool.tag(case.tag) == .int_value)
            static_pool.get(case.tag).int_value.bits
        else
            0;
        var width: u64 = 0;
        if (case.payload != .none) {
            const fields = static_pool.get(case.payload).record_type.field_types;
            const field: StaticPool.TagProperties = if (fields.len == 1)
                static_pool.properties(fields[0])
            else
                .{};
            const is_scalar = field.is_integer or field.is_float or field.is_pointer or
                fields.len == 1 and fields[0] == .bool_type;
            if (!is_scalar) {
                const count = static_pool.intern(.{
                    .int_value = .{ .value_type = .u64_type, .bits = fields.len },
                });
                _ = resolver.report(.tag_strategy_failed, node, case.name, count);
                return;
            }
            width = static_pool.field_bits(fields[0]);
        }
        const mask: u64 = if (width == 64)
            std.math.maxInt(u64)
        else
            (@as(u64, 1) << @intCast(width)) - 1;
        const exhaustive = width <= 16;
        const probes: u64 = if (exhaustive) mask + 1 else 6;
        for (0..probes) |i| {
            const payload: u64 = if (exhaustive) i else switch (i) {
                0 => 0,
                1 => 1,
                2 => mask,
                3 => 0x5555_5555_5555_5555 & mask,
                4 => 0xAAAA_AAAA_AAAA_AAAA & mask,
                else => @as(u64, 1) << @intCast(width - 1),
            };
            const wrapped = [_]Value{ .int(.u32_type, tag), .int(.u64_type, payload) };
            const stored = interpreter.call_static(context, node, wrap, &wrapped);
            if (!Value.is_int(stored.value_type)) return;
            const fits = storage_bits == 64 or stored.bits >> @intCast(storage_bits) == 0;
            const stored_value = [_]Value{.int(.u64_type, stored.bits)};
            const tag_back = interpreter.call_static(context, node, case_of, &stored_value);
            if (!Value.is_int(tag_back.value_type)) return;
            const payload_back = if (case.payload == .none)
                Value.int(.u64_type, payload)
            else
                interpreter.call_static(context, node, unwrap, &.{ stored_value[0], wrapped[0] });
            if (!Value.is_int(payload_back.value_type)) return;
            if (fits and tag_back.bits == tag and payload_back.bits & mask == payload) continue;
            const shown_value = StaticPool.IntValue{ .value_type = .u64_type, .bits = payload };
            const shown = static_pool.intern(.{ .int_value = shown_value });
            _ = resolver.report(.tag_strategy_failed, node, case.name, shown);
            return;
        }
    }
}

fn define_record(
    self: *Types,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    nominal: StaticPool.Index,
    core: NodeId,
    traits: []const StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const fields = resolver.tree.fields_of(core);
    const names = resolver.temporary_slice(NamePool.Index, fields.len);
    const types = resolver.temporary_slice(StaticPool.Index, fields.len);
    for (fields, 0..) |field_node, i| {
        const field = ParseTree.Param.from_node(resolver.tree, field_node);
        types[i] = self.with_runtime_lengths(self.concrete_type_from_node(context, field.ty));
        names[i] = resolver.declarations.parameter_or_position_name(field, i);
        if (std.mem.indexOfScalar(NamePool.Index, names[0..i], names[i]) != null) {
            resolver.doctor.report(.duplicate_declaration, field_node, names[i], declaration);
        }
    }

    resolver.static_pool.complete_nominal(nominal, .{ .record_type = .{
        .declaration = declaration,
        .is_packed = resolver.tree.kind(core) == .def_type_packed,
        .field_names = names[0..fields.len],
        .field_types = types[0..fields.len],
        .traits = traits,
    } });
    // in a bit-packed record only integers and bools may share their bytes with other fields
    const static_pool = &resolver.static_pool;
    const record = static_pool.get(nominal).record_type;
    for (fields, 0..) |field_node, i| {
        if (!static_pool.is_bit_field(record, i)) continue;
        const field_type = record.field_types[i];
        if (static_pool.tag(field_type) == .int_type or field_type == .bool_type) continue;
        resolver.doctor.report(.unaligned_field, field_node, record.field_names[i], field_type);
    }
}

// a trait body: one row for the body (its value is the self type), then one row per function member
// rows are contiguous so member i is row + 1 + i; static members (`stc u32 MASK = ..`) are locals
fn trait_body(
    self: *Types,
    context: *FunctionContext,
    body: NodeId,
    reserved: StaticPool.Index,
    self_type: StaticPool.Index,
    super_traits: []const StaticPool.Index,
    owner: DeclPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const body_name = if (self_type == .none) resolver.decl_pool.get(owner, .name) else .empty;
    const body_declaration = resolver.decl_pool.push(body_name, body, .trait, .trait_type, .{});

    // the body of a realized type belongs to the same realization as the type
    const generics = &resolver.generics;
    if (generics.realization_arguments.get(owner)) |arguments| {
        generics.realization_arguments.put(
            resolver.allocator,
            body_declaration,
            arguments,
        ) catch @panic("OOM");
    }
    if (generics.template_of.get(owner)) |template| {
        generics.template_of.put(
            resolver.allocator,
            body_declaration,
            template,
        ) catch @panic("OOM");
    }

    const trait = if (reserved != .none)
        reserved
    else
        static_pool.reserve_nominal(body_declaration);
    const body_value = if (self_type != .none) self_type else trait;
    resolver.decl_pool.set(body_declaration, .static_value, body_value);

    // one declaration per function member, pushed right after the body
    const statements = resolver.tree.manychildren(body);
    const names = resolver.temporary_slice(NamePool.Index, statements.len);
    var count: usize = 0;
    for (statements) |statement| {
        const member = Declarations.Stmt.from_node(resolver, statement);
        if (!member.is_member()) continue;

        const name_node = member.assignees[0];
        names[count] = resolver.name_pool.name_of_node(name_node);
        if (std.mem.indexOfScalar(NamePool.Index, names[0..count], names[count]) != null) {
            resolver.doctor.report(.duplicate_declaration, name_node, names[count], owner);
        }
        const declaration = resolver.decl_pool.push(
            names[count],
            member.node,
            .trait_member,
            .none,
            member.flags,
        );
        resolver.node_declarations[name_node] = declaration;
        count += 1;
    }
    for (resolver.tree.manychildren(body)) |statement| {
        if (Declarations.Stmt.from_node(resolver, statement).is_member()) continue;
        _ = resolver.declarations.check_statement(context, statement);
    }

    const types = resolver.temporary_slice(StaticPool.Index, count);
    for (0..count) |i| types[i] = self.declaration_type(body_declaration.member(i));
    static_pool.complete_nominal(trait, .{ .trait_type = .{
        .declaration = body_declaration,
        .member_names = names[0..count],
        .member_types = types,
        .super_traits = super_traits,
    } });
    return trait;
}

pub fn declaration_type(self: *Types, declaration: DeclPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    resolver.declarations.ensure_signature(declaration);
    const value_type = resolver.decl_pool.get(declaration, .value_type);
    return if (value_type == .none) .poison_type else value_type;
}

pub fn field_nodes_of(self: *Types, record: StaticPool.Index) []const NodeId {
    const resolver = self.owning_resolver();
    const declaration = resolver.static_pool.get(record).record_type.declaration;
    const value_node = resolver.declarations.value_node(declaration);
    return resolver.tree.fields_of(ParseTree.Def.from_node(resolver.tree, value_node).core);
}

pub fn signature(self: *Types, declaration: DeclPool.Index) StaticPool.FunctionType {
    const resolver = self.owning_resolver();
    const function_type = resolver.decl_pool.get(declaration, .value_type);
    return resolver.static_pool.get(function_type).function_type;
}

// ------------------------------------------------------------------------------------------ //
// trait conformance
// ------------------------------------------------------------------------------------------ //

// implof: every member of the trait and its supers exists, with `typeof self` read as the type
// members with a default may be left out, an override keeps the signature
fn conform(
    self: *Types,
    implementer: StaticPool.Index,
    own: StaticPool.Index,
    trait: StaticPool.Index,
    node: NodeId,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    for (0..static_pool.get(trait).trait_type.member_names.len) |i| {
        const trait_type = static_pool.get(trait).trait_type;
        const name = trait_type.member_names[i];
        const wanted = trait_type.member_types[i];
        const member = if (own == .none)
            StaticPool.Member.none
        else
            static_pool.lookup_member(own, name);
        if (member != .trait_method) {
            const default_node = resolver.declarations.value_node(trait_type.declaration.member(i));
            if (resolver.tree.kind(default_node) != .def_fun) {
                resolver.doctor.report(.trait_member_missing, node, name, trait);
            }
            continue;
        }

        const own_types = static_pool.get(own).trait_type.member_types;
        const have = static_pool.substitute_type_variables(own_types[member.trait_method.index]);
        const want = static_pool.substitute_type_variables(wanted);
        const same_signature = blk: {
            if (have == want or have == .poison_type or want == .poison_type) break :blk true;
            if (static_pool.tag(have) != .function_type) break :blk false;
            if (static_pool.tag(want) != .function_type) break :blk false;

            const have_function = static_pool.get(have).function_type;
            const want_function = static_pool.get(want).function_type;
            if (have_function.parameters.len != want_function.parameters.len) break :blk false;
            for (
                have_function.parameters,
                want_function.parameters,
            ) |have_parameter, want_parameter| {
                if (!self.same_as(have_parameter, want_parameter, trait, implementer)) {
                    break :blk false;
                }
            }
            break :blk self.same_as(
                have_function.return_type,
                want_function.return_type,
                trait,
                implementer,
            );
        };
        if (!same_signature) {
            resolver.doctor.report(.trait_signature_mismatch, node, name, trait);
        }
    }

    for (0..static_pool.get(trait).trait_type.super_traits.len) |i| {
        self.conform(implementer, own, static_pool.get(trait).trait_type.super_traits[i], node);
    }
}

// left == right with the trait read as the implementing type anywhere inside
fn same_as(
    self: *Types,
    left: StaticPool.Index,
    right: StaticPool.Index,
    trait: StaticPool.Index,
    implementer: StaticPool.Index,
) bool {
    const static_pool = &self.owning_resolver().static_pool;
    if (left == right or left == .poison_type or right == .poison_type) return true;
    if (right == trait and left == implementer) return true;
    if (static_pool.tag(left) != static_pool.tag(right)) return false;

    // equal tags, so both sides have the same composition
    return switch (static_pool.composition(left)) {
        .pointer => {
            const pointer = static_pool.get(left).pointer_type;
            const right_pointer = static_pool.get(right).pointer_type;
            if (pointer.is_mutable != right_pointer.is_mutable) return false;
            return self.same_as(pointer.pointee, right_pointer.pointee, trait, implementer);
        },
        .array => {
            const array = static_pool.get(left).array_type;
            const right_array = static_pool.get(right).array_type;
            if (array.length != right_array.length) return false;
            return self.same_as(array.element, right_array.element, trait, implementer);
        },
        .slice => {
            const element = static_pool.get(left).slice_type.element;
            const right_element = static_pool.get(right).slice_type.element;
            return self.same_as(element, right_element, trait, implementer);
        },
        .function => self.same_function_type(left, right, trait, implementer),
        // distinct leaves, unified variants and trees are distinct types
        .leaf, .unified_variants, .tree => false,
    };
}

fn same_function_type(
    self: *Types,
    left: StaticPool.Index,
    right: StaticPool.Index,
    trait: StaticPool.Index,
    implementer: StaticPool.Index,
) bool {
    const static_pool = &self.owning_resolver().static_pool;
    const parameter_count = static_pool.get(left).function_type.parameters.len;
    if (parameter_count != static_pool.get(right).function_type.parameters.len) return false;
    for (0..parameter_count) |i| {
        const left_parameter = static_pool.get(left).function_type.parameters[i];
        const right_parameter = static_pool.get(right).function_type.parameters[i];
        if (!self.same_as(left_parameter, right_parameter, trait, implementer)) return false;
    }
    const left_return = static_pool.get(left).function_type.return_type;
    const right_return = static_pool.get(right).function_type.return_type;
    return self.same_as(left_return, right_return, trait, implementer);
}

// ------------------------------------------------------------------------------------------ //
// function types, runtime lengths and casts
// ------------------------------------------------------------------------------------------ //

pub fn function_type_of(
    self: *Types,
    context: *FunctionContext,
    value_node: NodeId,
    category: StaticPool.FunctionType.Category,
    default_return_type: StaticPool.Index,
    self_parameter: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const header = resolver.tree.arg(value_node, 0);
    const parameter_nodes = resolver.tree.params_of(value_node);
    const offset = @intFromBool(self_parameter != .none);
    const parameters = resolver.temporary_slice(StaticPool.Index, parameter_nodes.len + offset);
    if (offset == 1) parameters[0] = self_parameter;

    for (parameter_nodes, 0..) |parameter_node, i| {
        const type_node = ParseTree.Param.from_node(resolver.tree, parameter_node).ty;
        const parameter_type = self.type_from_node(context, type_node);
        parameters[i + offset] = parameter_type;
        // a template is only taken as the whole parameter type, `T`, `*T` or `&T`
        const is_nested_template = static_pool.contains_template(parameter_type) and
            static_pool.template_of(parameter_type) == .none;
        if (is_nested_template) {
            const reported = resolver.report(.unrealized_template, type_node, parameter_type, 0);
            parameters[i + offset] = reported;
        }
        const is_nested_parameter_only = static_pool.contains_parameter_only(parameter_type) and
            static_pool.trait_of(parameter_type) == .none and
            static_pool.packed_of(parameter_type) == .none;
        if (is_nested_parameter_only) {
            parameters[i + offset] =
                resolver.report(.unstorable_outside_parameter, type_node, parameter_type, 0);
        }
    }

    const return_type = blk: {
        if (resolver.tree.kind(header) != .partial__fun_def_header_ret) {
            break :blk default_return_type;
        }
        const declared = self.concrete_type_from_node(context, resolver.tree.arg(header, 1));
        // a result behind a pointer to an unlengthed array has a runtime length: any length fits
        if (category == .static or static_pool.tag(declared) != .pointer_type) break :blk declared;
        const pointer = static_pool.get(declared).pointer_type;
        if (static_pool.tag(pointer.pointee) != .array_type) break :blk declared;
        const array = static_pool.get(pointer.pointee).array_type;
        if (static_pool.tag(array.length) != .type_variable) break :blk declared;
        const runtime_array = static_pool.intern(.{ .array_type = .{
            .length = StaticPool.dyn_len,
            .element = array.element,
        } });
        break :blk static_pool.pointer_to(runtime_array, pointer.is_mutable);
    };
    return static_pool.intern(.{ .function_type = .{
        .category = category,
        .parameters = parameters,
        .return_type = return_type,
    } });
}

// unlengthed arrays that are not inferred per value become runtime-length arrays
pub fn with_runtime_lengths(self: *Types, value_type: StaticPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (value_type == .none or !static_pool.has_type_variables(value_type)) return value_type;

    return switch (static_pool.composition(value_type)) {
        .array => {
            const array = static_pool.get(value_type).array_type;
            const resolved_length = static_pool.substitute_type_variables(array.length);
            const is_open = static_pool.tag(resolved_length) == .type_variable;
            const length = if (is_open) StaticPool.dyn_len else array.length;
            const element = self.with_runtime_lengths(array.element);
            return static_pool.intern(.{ .array_type = .{ .length = length, .element = element } });
        },
        .pointer => {
            const pointer = static_pool.get(value_type).pointer_type;
            const pointee = self.with_runtime_lengths(pointer.pointee);
            return static_pool.pointer_to(pointee, pointer.is_mutable);
        },
        .slice => {
            const element = static_pool.get(value_type).slice_type.element;
            return static_pool.slice_of(self.with_runtime_lengths(element));
        },
        // the parameters are read from the pool again each time, interning may move them
        .function => {
            const function = static_pool.get(value_type).function_type;
            const parameters = resolver.temporary_slice(StaticPool.Index, function.parameters.len);
            for (parameters, 0..) |*parameter, i| {
                const original = static_pool.get(value_type).function_type.parameters[i];
                parameter.* = self.with_runtime_lengths(original);
            }
            const original_return = static_pool.get(value_type).function_type.return_type;
            const return_type = self.with_runtime_lengths(original_return);
            return static_pool.intern(.{ .function_type = .{
                .category = function.category,
                .parameters = parameters,
                .return_type = return_type,
            } });
        },
        // lengths are only made runtime ones through arrays, pointers and functions
        .leaf, .unified_variants, .tree => value_type,
    };
}

pub fn concrete_type_from_node(
    self: *Types,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const node_type = self.type_from_node(context, node);
    if (resolver.static_pool.contains_template(node_type)) {
        return resolver.report(.unrealized_template, node, node_type, 0);
    }
    // a function taking a trait or packed variant is realized per argument type, so no value has
    // such a type
    if (resolver.static_pool.contains_parameter_only(node_type)) {
        return resolver.report(.unstorable_outside_parameter, node, node_type, 0);
    }
    return node_type;
}

// `[lo..hi]T` and `*[lo..hi]T` as cast targets: a static part of the source array
pub fn cast_target(
    self: *Types,
    context: *FunctionContext,
    target_node: NodeId,
    source_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const is_pointer = resolver.tree.props(target_node).pointer;
    const array_node = if (is_pointer) resolver.tree.arg(target_node, 0) else target_node;
    const is_ranged_array = resolver.tree.kind(array_node) == .type_array and
        resolver.tree.props(resolver.tree.arg(array_node, 0)).range;
    if (!is_ranged_array) return self.type_from_node(context, target_node);

    const range_node = resolver.tree.arg(array_node, 0);
    const range = ParseTree.Range.from_node(resolver.tree, range_node);
    const static_length = static_pool.static_length(static_pool.pointee(source_type));
    const source_length: ?i128 = if (static_length) |length| length else null;

    var low: i128 = 0;
    if (range.lo != 0) {
        low = resolver.static_values.static_integer(context, range.lo) orelse
            return resolver.report(.not_static, range.lo, 0, 0);
    }
    var high: i128 = undefined;
    if (range.hi == 0) {
        high = source_length orelse return resolver.report(.not_static, range_node, 0, 0);
    } else {
        const end = resolver.static_values.static_integer(context, range.hi) orelse
            return resolver.report(.not_static, range_node, 0, 0);
        high = end + @intFromBool(range.incl);
    }

    const exceeds_source = source_length != null and high > source_length.?;
    if (low < 0 or high < low or exceeds_source) {
        return resolver.report(.invalid_cast, range_node, source_type, .none);
    }

    const element = self.type_from_node(context, resolver.tree.arg(array_node, 1));
    const array = static_pool.array_of(@intCast(high - low), element);
    if (!is_pointer) return array;
    return static_pool.pointer_to(array, resolver.tree.kind(target_node) == .type_ptrmut);
}

// ------------------------------------------------------------------------------------------ //
// end of inference
// ------------------------------------------------------------------------------------------ //

// type vars nothing bound: an open element type is an error, an open length a runtime length
pub fn finish_inference(self: *Types) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (static_pool.type_variables.count() == 0) return;

    for (resolver.decl_pool.entries.column(.value_type), 0..) |value_type, i| {
        if (value_type == .none or !static_pool.has_type_variables(value_type)) continue;
        const resolved = static_pool.substitute_type_variables(value_type);
        if (!static_pool.has_open_type_variable(resolved)) continue;
        if (static_pool.is_length_generic(resolved)) continue;
        const node = resolver.decl_pool.get(@fromBackingInt(@intCast(i)), .node);
        _ = resolver.report(.uninferable_type, node, resolved, .none);
    }

    // lengths nothing fixed are only known at runtime, a loop value then needs its count at entry
    const type_variables = &static_pool.type_variables;
    const columns = type_variables.variables.columns();

    // per unbound group: none_node unseen, 0 when every origin counts, else an uncounted origin
    const group_count = columns.parent.len;
    const group = resolver.allocator.alloc(ParseTree.NodeId, group_count) catch @panic("OOM");
    defer resolver.allocator.free(group);
    @memset(group, ParseTree.none_node);

    for (0..columns.parent.len) |i| {
        const root = @backingInt(type_variables.root_of(@fromBackingInt(@intCast(i))));
        if (columns.binding[root] != .none) continue;
        const origin = columns.origin[i];
        // whether the element count is known where the length's origin needs it
        const counted = switch (resolver.tree.kind(origin)) {
            .for_seq, .for_var_in_seq => blk: {
                const sequence = ParseTree.Loop.from_node(resolver.tree, origin).seq;
                const sequence_type = resolver.node_types[sequence];
                const through = static_pool.through_pointer(
                    static_pool.substitute_type_variables(sequence_type),
                );
                if (resolver.tree.props(sequence).range) {
                    break :blk ParseTree.Range.from_node(resolver.tree, sequence).hi != 0;
                }
                if (through == .none) break :blk false;
                break :blk static_pool.tag(static_pool.pointee(through)) == .array_type;
            },
            .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => false,
            .type_array_unlengthed,
            .array_index,
            .gen_incl,
            .gen_excl,
            .gen_lowerbound,
            .gen_upperbound_incl,
            .gen_upperbound_excl,
            => true,
            else => continue,
        };
        if (group[root] == ParseTree.none_node or !counted) {
            group[root] = if (counted) 0 else origin;
        }
    }

    for (group, 0..) |origin, i| {
        if (origin == ParseTree.none_node) continue;
        if (origin != 0) {
            const origin_type = static_pool.substitute_type_variables(resolver.node_types[origin]);
            _ = resolver.report(.uninferable_type, origin, origin_type, .none);
        }
        type_variables.bind(@fromBackingInt(@intCast(i)), StaticPool.dyn_len);
    }

    const tables = [_][]StaticPool.Index{
        resolver.node_types,
        resolver.decl_pool.entries.column(.value_type),
    };
    for (tables) |table| for (table) |*entry| {
        if (entry.* == .none or !static_pool.has_type_variables(entry.*)) continue;
        entry.* = static_pool.substitute_type_variables(entry.*);
    };
}
