const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Declarations = @import("Declarations.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;
const max_nesting = 256;

// templates and realizations: stcfuns realized per static arguments,
// functions per length, type or template
const Generics = @This();

// a realization's key: its template (a stcfun, a length-generic function) and its static arguments
// the arguments are one pool index, so the whole key is 8 bytes and compares as one
pub const AbstractKey = packed struct(u64) {
    generic_tuple: DeclPool.Index,
    args_tuple: StaticPool.Index,
};

// realizations: the template a declaration was realized from and its static arguments
template_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
realization_arguments: std.AutoHashMapUnmanaged(DeclPool.Index, StaticPool.Index) = .empty,
// functions produced by a stcfun: the realization whose static parameters they see
static_scope: std.AutoHashMapUnmanaged(DeclPool.Index, AbstractKey) = .empty,
// every realization by its template and static arguments
realizations: std.AutoHashMapUnmanaged(AbstractKey, StaticPool.Index) = .empty,

pub fn owning_resolver(self: *Generics) *Resolver {
    return @alignCast(@fieldParentPtr("generics", self));
}

pub fn deinit(self: *Generics, alloc: std.mem.Allocator) void {
    self.template_of.deinit(alloc);
    self.realization_arguments.deinit(alloc);
    self.static_scope.deinit(alloc);
    self.realizations.deinit(alloc);
}

pub fn realize(
    self: *Generics,
    generic: DeclPool.Index,
    arguments: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const key = AbstractKey{ .generic_tuple = generic, .args_tuple = arguments };
    if (self.realizations.get(key)) |realization| return realization;

    const node = resolver.decl_pool.get(generic, .node);
    // a realization that realizes itself forever eats the static budget and stops there
    if (resolver.scopes.scope_starts.len > max_nesting) {
        const origin = resolver.interpreter.failure_origin(node);
        return resolver.report(.static_eval_failed, origin, generic, 0);
    }
    if (!resolver.interpreter.charge_steps(node, 64)) return .poison_type;

    // a `fun` taking only types and making a function (`fun f = (type T): (&[]T x) ..`) is
    // realized like a `stcfun`: what it makes sees the types, also in its per-length realizations
    const tree = resolver.tree;
    const value_node = resolver.declarations.value_node(generic);
    const makes_function_of_types = tree.kind(tree.arg(value_node, 1)) == .def_fun and
        for (tree.params_of(value_node)) |parameter_node| {
            const type_node = ParseTree.Param.from_node(tree, parameter_node).ty;
            if (type_node == 0 or tree.kind(type_node) != .type_type) break false;
        } else true;

    // a length-generic function: a declaration per tuple of lengths, bound in order of appearance
    const is_static = resolver.decl_pool.get(generic, .kind) == .static_function;
    if (!is_static and !makes_function_of_types) {
        const static_pool = &resolver.static_pool;
        // copied out of the pool, which may move while realizing interns new entries
        const length = static_pool.get(arguments).aggregate_value.elements.len;
        const argument_values = resolver.temporary_slice(StaticPool.Index, length);
        @memcpy(argument_values, static_pool.get(arguments).aggregate_value.elements);

        const decl_pool = &resolver.decl_pool;
        resolver.declarations.check_body(generic);
        if (decl_pool.get(generic, .state) == .failed) return .poison_type;

        const realization = decl_pool.push(
            decl_pool.get(generic, .name),
            node,
            decl_pool.get(generic, .kind),
            .none,
            decl_pool.get(generic, .flags),
        );
        self.template_of.put(resolver.allocator, realization, generic) catch @panic("OOM");
        const function_value = resolver.static_pool.intern(.{ .function_value = realization });
        self.memo(key, function_value);

        const outer_key = self.static_scope.get(generic) orelse self.trait_scope(generic);
        if (outer_key) |outer| {
            self.static_scope.put(resolver.allocator, realization, outer) catch @panic("OOM");
            resolver.declarations.open_declaration_scope(true, .none, 0);
            self.bind_static(outer.generic_tuple, outer.args_tuple);
        }
        defer if (outer_key != null) resolver.scopes.close();

        resolver.declarations.ensure_signature(realization);
        self.realization_arguments.put(
            resolver.allocator,
            realization,
            arguments,
        ) catch @panic("OOM");

        // the generic parameters of the realization's signature take the arguments in order
        const value_type = resolver.decl_pool.get(realization, .value_type);
        const function_type = static_pool.get(value_type).function_type;
        const parameters = resolver.temporary_slice(StaticPool.Index, function_type.parameters.len);
        @memcpy(parameters, function_type.parameters);

        var bound: usize = 0;
        for (parameters) |*parameter_slot| {
            var parameter = parameter_slot.*;
            if (!static_pool.is_generic_parameter(parameter)) continue;
            if (bound >= argument_values.len) continue;
            const argument = argument_values[bound];
            bound += 1;

            // a template or trait parameter `T`, `*T` or `&T` becomes the argument, behind the
            // same pointer
            if (static_pool.is_realized_per_type(parameter)) {
                if (static_pool.get(parameter) != .pointer_type) {
                    parameter_slot.* = argument;
                } else {
                    const is_mutable = static_pool.get(parameter).pointer_type.is_mutable;
                    parameter_slot.* = static_pool.pointer_to(argument, is_mutable);
                }
            }
            if (static_pool.get(parameter) == .pointer_type) {
                parameter = static_pool.get(parameter).pointer_type.pointee;
            }
            if (static_pool.get(parameter) == .array_type) {
                _ = static_pool.unify(static_pool.get(parameter).array_type.length, argument);
            }
        }

        const specialized = StaticPool.FunctionType{
            .category = function_type.category,
            .parameters = parameters,
            .return_type = function_type.return_type,
        };
        const specialized_type = static_pool.intern(.{ .function_type = specialized });
        resolver.decl_pool.set(realization, .value_type, specialized_type);
        resolver.declarations.check_body(realization);
        return function_value;
    }

    var context = FunctionContext{ .declaration = generic, .is_static_context = true };
    resolver.declarations.open_declaration_scope(true, .none, 0);
    defer resolver.scopes.close();

    const parameter_nodes = resolver.tree.params_of(value_node);
    self.bind_static(generic, arguments);
    for (parameter_nodes) |parameter_node| {
        const where = ParseTree.Param.from_node(resolver.tree, parameter_node).where;
        if (where == 0) continue;
        if (resolver.interpreter.evaluate_static(&context, where) != .bool_false) continue;
        _ = resolver.report(.stcwhere_violated, where, generic, arguments);
    }

    const unit = resolver.tree.arg(value_node, 1);
    const kind = resolver.declarations.declared_type_kind(unit);
    if (kind != .variable) {
        // memoized before its body, so the type can mention itself (`Stream(Child)` inside Stream)
        const decl_pool = &resolver.decl_pool;
        const realization = decl_pool.push(decl_pool.get(generic, .name), unit, kind, .none, .{});
        self.realization_arguments.put(
            resolver.allocator,
            realization,
            arguments,
        ) catch @panic("OOM");
        self.template_of.put(resolver.allocator, realization, generic) catch @panic("OOM");

        decl_pool.set(
            realization,
            .static_value,
            resolver.static_pool.reserve_nominal(realization),
        );
        self.memo(key, decl_pool.get(realization, .static_value));
        const diagnostics_mark = resolver.doctor.diagnostics.len();
        defer resolver.doctor.settle(diagnostics_mark);
        return resolver.types.check_type_definition(&context, realization, unit);
    }
    if (resolver.tree.kind(unit) == .def_fun) {
        const decl_pool = &resolver.decl_pool;
        const realization = decl_pool.push(
            decl_pool.get(generic, .name),
            unit,
            .function,
            .none,
            .{},
        );
        const function_value = resolver.static_pool.intern(.{ .function_value = realization });
        self.memo(key, function_value);
        self.static_scope.put(resolver.allocator, realization, key) catch @panic("OOM");

        resolver.declarations.ensure_signature(realization);
        resolver.declarations.check_body(realization);
        return function_value;
    }

    // any other body is checked as a function and then run by the interpreter for its result
    const static_pool = &resolver.static_pool;
    context.is_static_context = false;
    context.is_interpreted = true;
    // an open length of the result (`-> []u32`) is each realization's own, not the first one's
    const header = resolver.tree.arg(value_node, 0);
    const declares_result = resolver.tree.kind(header) == .partial__fun_def_header_ret;
    const signature_result = resolver.types.signature(generic).return_type;
    context.return_type = if (declares_result and static_pool.has_type_variables(signature_result))
        resolver.types.concrete_type_from_node(&context, resolver.tree.arg(header, 1))
    else
        signature_result;

    const first_local = resolver.decl_pool.entries.len();
    const type_variables_before = static_pool.type_variables.count();
    const outer_session = resolver.initialization.enter();
    const diagnostics_mark = resolver.doctor.diagnostics.len();
    resolver.declarations.check_function_result(&context, unit);
    resolver.doctor.settle(diagnostics_mark);
    context.is_interpreted = false;
    resolver.initialization.leave(outer_session);

    if (resolver.doctor.errors_since(resolver.tree, diagnostics_mark, unit)) {
        self.memo(key, .poison_type);
        return .poison_type;
    }
    // a length from a while or loop is only counted when the interpreter runs it
    const type_variables = &static_pool.type_variables;
    for (type_variables_before..type_variables.count()) |i| {
        const origin = type_variables.variables.column(.origin)[i];
        switch (resolver.tree.kind(origin)) {
            .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => {
                if (type_variables.binding_of(@enumFromInt(i)) == .none) {
                    type_variables.bind(@enumFromInt(i), StaticPool.dyn_len);
                }
            },
            else => {},
        }
    }

    // a body that gives nothing failed on the way (it called a function with errors)
    const body = resolver.capture_body(generic, value_node, first_local);
    const ran = resolver.interpreter.run_body(&context, unit, body);
    const result = if (ran == .none) .poison_type else ran;

    // a type the body declared itself is a realization of this template
    const returns_type = static_pool.tag(context.return_type) == .meta_type;
    const made = if (returns_type and static_pool.properties(result).is_type)
        static_pool.nominal_declaration(result)
    else
        .none;
    if (made != .none and @intFromEnum(made) >= first_local) {
        self.template_of.put(resolver.allocator, made, generic) catch @panic("OOM");
    }

    self.memo(key, result);
    return result;
}

// the static parameters of a stcfun as locals holding the arguments of one realization
// a member of a trait realized from a template (`Cmp(Money)`) sees the template's arguments
fn trait_scope(self: *Generics, member: DeclPool.Index) ?AbstractKey {
    const resolver = self.owning_resolver();
    if (resolver.decl_pool.get(member, .kind) != .trait_member) return null;
    const trait = resolver.declarations.owner_of(member);
    if (trait == .none or resolver.static_pool.tag(trait) != .trait_type) return null;
    const declaration = resolver.static_pool.get(trait).trait_type.declaration;
    const template = self.template_of.get(declaration) orelse return null;
    const arguments = self.realization_arguments.get(declaration) orelse return null;
    return .{ .generic_tuple = template, .args_tuple = arguments };
}

fn bind_static(self: *Generics, generic: DeclPool.Index, arguments: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    // copied out of the pool, which may move while realizing interns new entries
    const length = static_pool.get(arguments).aggregate_value.elements.len;
    const argument_values = resolver.temporary_slice(StaticPool.Index, length);
    @memcpy(argument_values, static_pool.get(arguments).aggregate_value.elements);
    const parameter_nodes = resolver.tree.params_of(resolver.declarations.value_node(generic));

    for (parameter_nodes, 0..) |parameter_node, i| {
        const declared_type = resolver.types.signature(generic).parameters[i];
        // an argument that failed is reported already, its parameter is poison in the body
        const parameter_type = if (argument_values[i] == .poison_type)
            .poison_type
        else if (static_pool.has_type_variables(declared_type))
            static_pool.type_of(argument_values[i])
        else
            declared_type;

        const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
        const name = resolver.declarations.parameter_or_position_name(parameter, i);
        const declaration = resolver.declarations.declare_local(
            name,
            parameter_node,
            .static_parameter,
            parameter_type,
        );
        resolver.declarations.link_identifier(parameter.name, declaration, parameter_type);

        const value = resolver.static_values.retyped(argument_values[i], parameter_type);
        resolver.decl_pool.set(declaration, .static_value, value);
    }
}

fn memo(self: *Generics, key: AbstractKey, value: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    self.realizations.put(resolver.allocator, key, value) catch @panic("OOM");
}

pub fn is_template(self: *Generics, declaration: DeclPool.Index) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (declaration == .none) return false;
    if (resolver.decl_pool.get(declaration, .kind) != .static_function) return false;

    const value_type = resolver.decl_pool.get(declaration, .value_type);
    if (value_type == .none) return false;
    if (static_pool.tag(value_type) != .function_type) return false;
    return static_pool.tag(static_pool.get(value_type).function_type.return_type) == .meta_type;
}

pub fn realizes(
    self: *Generics,
    candidate: StaticPool.Index,
    template_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const nominal = static_pool.unwrapped(candidate);
    const template = static_pool.get(template_type).template_type;
    if (nominal == template_type or self.template_source_of(nominal) == template) return true;

    const traits: []const StaticPool.Index = switch (static_pool.get(nominal)) {
        .record_type => |record| record.traits,
        .variant_type => |variant| variant.traits,
        else => &.{},
    };
    for (traits) |trait| {
        if (static_pool.tag(trait) != .trait_type) continue;
        const trait_declaration = static_pool.get(trait).trait_type.declaration;
        if (self.template_of.get(trait_declaration) == template) return true;
    }
    return false;
}

pub fn passes_template_parameter(
    self: *Generics,
    argument_type: StaticPool.Index,
    parameter: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const resolved_type = static_pool.substitute_type_variables(argument_type);
    if (resolved_type == .poison_type) return true;
    if (static_pool.is_pointer(parameter) != static_pool.is_pointer(resolved_type)) return false;

    if (static_pool.get(parameter) == .pointer_type and
        static_pool.get(parameter).pointer_type.is_mutable and
        !static_pool.get(resolved_type).pointer_type.is_mutable) return false;
    return self.realizes(resolved_type, static_pool.template_of(parameter));
}

pub fn template_source_of(self: *Generics, nominal_type: StaticPool.Index) DeclPool.Index {
    const resolver = self.owning_resolver();
    const declaration = resolver.static_pool.nominal_declaration(nominal_type);
    if (declaration == .none) return .none;
    return self.template_of.get(declaration) orelse .none;
}

pub fn is_sibling_realization(
    self: *Generics,
    context: *FunctionContext,
    candidate: StaticPool.Index,
    sibling: StaticPool.Index,
) bool {
    const static_pool = &self.owning_resolver().static_pool;
    if (static_pool.template_of(sibling) != .none) {
        return self.realizes(candidate, static_pool.template_of(sibling));
    }
    if (static_pool.template_of(candidate) != .none) {
        return self.realizes(sibling, static_pool.template_of(candidate));
    }

    // in a realization per argument type a pattern of another argument type never matches, the
    // generic body was checked with the parameter's own type
    const template = self.template_source_of(sibling);
    if (template == .none) return self.is_inside_template_realization(context);
    if (self.template_source_of(candidate) != template) return false;
    return self.is_inside_template_realization(context);
}

pub fn is_inside_template_realization(self: *Generics, context: *FunctionContext) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (context.declaration == .none) return false;
    const template = self.template_of.get(context.declaration) orelse return false;

    const template_type = resolver.decl_pool.get(template, .value_type);
    if (template_type == .none or static_pool.tag(template_type) != .function_type) return false;
    for (static_pool.get(template_type).function_type.parameters) |parameter| {
        if (static_pool.is_realized_per_type(parameter)) return true;
    }
    return false;
}

pub fn template_member(
    self: *Generics,
    node: NodeId,
    template_type: StaticPool.Index,
    name: NamePool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const template = resolver.static_pool.get(template_type).template_type;
    const kind = resolver.declarations.template_kind(template);
    if (kind == .variable) return resolver.report(.generic_member, node, name, template_type);

    const value_node = resolver.declarations.value_node(template);
    const unit = resolver.tree.arg(value_node, 1);
    var context = FunctionContext{ .is_static_context = true };
    resolver.declarations.open_declaration_scope(true, .none, 0);
    defer resolver.scopes.close();

    // a member typed by the static parameters has no type before the template is realized
    if (kind == .record) if (self.template_field(template, name)) |field_node| {
        const field = ParseTree.Param.from_node(resolver.tree, field_node);
        if (self.mentions(field.ty, value_node)) {
            return resolver.report(.generic_member, node, name, template_type);
        }
        return resolver.types.type_from_node(&context, field.ty);
    };

    const definition = ParseTree.Def.from_node(resolver.tree, unit);
    const trait_node = if (resolver.declarations.declared_type_kind(definition.core) == .trait)
        definition.core
    else if (definition.body != 0)
        definition.body
    else
        return resolver.report(.unknown_member, node, name, template_type);

    // `!{..}` keeps its members in argument 0, `implof(..) !{..}` in argument 1
    const is_implof = resolver.tree.kind(trait_node) == .def_trait_implof;
    const trait_members = resolver.tree.arg(trait_node, if (is_implof) 1 else 0);
    for (resolver.tree.manychildren(trait_members)) |statement| {
        const parts = Declarations.Stmt.from_node(resolver, statement);
        if (parts.assignees.len != 1) continue;
        if (resolver.name_pool.name_of_node(parts.assignees[0]) != name) continue;
        if (!parts.kind.is_function()) continue;

        const function_node = parts.values[0];
        const signature_mentions = blk: {
            const header = resolver.tree.arg(function_node, 0);
            if (resolver.tree.kind(header) != .partial__fun_def_header_ret) break :blk true;
            if (self.mentions(resolver.tree.arg(header, 1), value_node)) break :blk true;

            for (resolver.tree.params_of(function_node)) |parameter_node| {
                const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
                if (self.mentions(parameter.ty, value_node)) break :blk true;
            }
            break :blk false;
        };
        if (signature_mentions) {
            return resolver.report(.generic_member, node, name, template_type);
        }
        return resolver.types.function_type_of(
            &context,
            function_node,
            .default,
            .poison_type,
            .none,
        );
    }
    return resolver.report(.unknown_member, node, name, template_type);
}

pub fn template_field(self: *Generics, template: DeclPool.Index, name: NamePool.Index) ?NodeId {
    const resolver = self.owning_resolver();
    const unit = resolver.tree.arg(resolver.declarations.value_node(template), 1);
    const fields = resolver.tree.fields_of(ParseTree.Def.from_node(resolver.tree, unit).core);
    const field_index = resolver.declarations.parameter_index(fields, name) orelse return null;
    return fields[field_index];
}

// whether any identifier under `node` names a static parameter of the stcfun `value_node`
fn mentions(self: *Generics, node: NodeId, value_node: NodeId) bool {
    const resolver = self.owning_resolver();
    const parameter_nodes = resolver.tree.params_of(value_node);
    const subtree = resolver.tree.subtree(node);
    for (subtree[0]..subtree[1]) |index| {
        if (resolver.tree.kind(@intCast(index)) != .identifier) continue;
        const name = resolver.name_pool.name_of_node(@intCast(index));
        for (parameter_nodes, 0..) |parameter_node, j| {
            if (resolver.declarations.parameter_name(parameter_node, j) == name) return true;
        }
    }
    return false;
}
