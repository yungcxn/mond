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

    if (resolver.decl_pool.get(generic, .kind) != .static_function) {
        const argument_values = self.copied_arguments(arguments);
        return self.realize_length_generic(generic, arguments, argument_values, key, node);
    }
    return self.realize_static_function(generic, arguments, key);
}

// copied out of the pool, which may move while realizing interns new entries
fn copied_arguments(self: *Generics, arguments: StaticPool.Index) []StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const length = static_pool.get(arguments).aggregate_value.elements.len;
    const argument_values = resolver.temporary_slice(StaticPool.Index, length);
    @memcpy(argument_values, static_pool.get(arguments).aggregate_value.elements);
    return argument_values;
}

// a length-generic function: a new declaration per tuple of lengths, bound in order of appearance
fn realize_length_generic(
    self: *Generics,
    generic: DeclPool.Index,
    arguments: StaticPool.Index,
    argument_values: []const StaticPool.Index,
    key: AbstractKey,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
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

    const outer_key = self.static_scope.get(generic);
    if (outer_key) |outer| {
        self.static_scope.put(resolver.allocator, realization, outer) catch @panic("OOM");
        resolver.declarations.open_declaration_scope(true, .none, 0);
        self.bind_static(outer.generic_tuple, outer.args_tuple);
    }
    defer if (outer_key != null) resolver.scopes.close();

    resolver.declarations.ensure_signature(realization);
    self.realization_arguments.put(resolver.allocator, realization, arguments) catch @panic("OOM");
    self.specialize_parameters(realization, argument_values);
    resolver.declarations.check_body(realization);
    return function_value;
}

// the generic parameters of the realization's signature take the arguments in order
fn specialize_parameters(
    self: *Generics,
    realization: DeclPool.Index,
    argument_values: []const StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const value_type = resolver.decl_pool.get(realization, .value_type);
    const function_type = static_pool.get(value_type).function_type;
    const parameters = resolver.temporary_slice(StaticPool.Index, function_type.parameters.len);
    @memcpy(parameters, function_type.parameters);

    var bound: usize = 0;
    for (parameters) |*parameter_slot| {
        var parameter = parameter_slot.*;
        if (!static_pool.is_generic_parameter(parameter) or bound >= argument_values.len) continue;
        const argument = argument_values[bound];
        bound += 1;

        if (static_pool.template_of(parameter) != .none) {
            parameter_slot.* = realized_template_parameter(static_pool, parameter, argument);
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
}

// a template parameter `T`, `*T` or `&T` becomes the argument, behind the same kind of pointer
fn realized_template_parameter(
    static_pool: *StaticPool,
    parameter: StaticPool.Index,
    argument: StaticPool.Index,
) StaticPool.Index {
    if (static_pool.get(parameter) != .pointer_type) return argument;
    return static_pool.pointer_to(argument, static_pool.get(parameter).pointer_type.is_mutable);
}

fn realize_static_function(
    self: *Generics,
    generic: DeclPool.Index,
    arguments: StaticPool.Index,
    key: AbstractKey,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    var context = FunctionContext{ .declaration = generic, .is_static_context = true };
    resolver.declarations.open_declaration_scope(true, .none, 0);
    defer resolver.scopes.close();

    const value_node = resolver.declarations.value_node(generic);
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
    if (kind != .variable) return self.realize_type(&context, generic, arguments, key, unit, kind);
    if (resolver.tree.kind(unit) == .def_fun) return self.realize_function(generic, key, unit);
    return self.realize_computed(&context, generic, key, unit, value_node);
}

// memoized before its body, so the type can mention itself (`Stream(Child)` inside Stream)
fn realize_type(
    self: *Generics,
    context: *FunctionContext,
    generic: DeclPool.Index,
    arguments: StaticPool.Index,
    key: AbstractKey,
    unit: NodeId,
    kind: DeclPool.Entry.Kind,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const decl_pool = &resolver.decl_pool;
    const realization = decl_pool.push(decl_pool.get(generic, .name), unit, kind, .none, .{});
    self.realization_arguments.put(resolver.allocator, realization, arguments) catch @panic("OOM");
    self.template_of.put(resolver.allocator, realization, generic) catch @panic("OOM");

    decl_pool.set(realization, .static_value, resolver.static_pool.reserve_nominal(realization));
    self.memo(key, decl_pool.get(realization, .static_value));
    return resolver.types.check_type_definition(context, realization, unit);
}

fn realize_function(
    self: *Generics,
    generic: DeclPool.Index,
    key: AbstractKey,
    unit: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const decl_pool = &resolver.decl_pool;
    const realization = decl_pool.push(decl_pool.get(generic, .name), unit, .function, .none, .{});
    const function_value = resolver.static_pool.intern(.{ .function_value = realization });
    self.memo(key, function_value);
    self.static_scope.put(resolver.allocator, realization, key) catch @panic("OOM");

    resolver.declarations.ensure_signature(realization);
    resolver.declarations.check_body(realization);
    return function_value;
}

// any other body is checked as a function and then run by the interpreter for its result
fn realize_computed(
    self: *Generics,
    context: *FunctionContext,
    generic: DeclPool.Index,
    key: AbstractKey,
    unit: NodeId,
    value_node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    context.is_static_context = false;
    context.is_interpreted = true;
    context.return_type = resolver.types.signature(generic).return_type;

    const first_local = resolver.decl_pool.entries.len();
    const type_variables_before = static_pool.type_variables.count();
    const outer_session = resolver.initialization.enter();
    const diagnostics_mark = resolver.doctor.diagnostics.len();
    resolver.declarations.check_function_result(context, unit);
    context.is_interpreted = false;
    resolver.initialization.leave(outer_session);

    if (resolver.doctor.errors_since(resolver.tree, diagnostics_mark, unit)) {
        self.memo(key, .poison_type);
        return .poison_type;
    }
    self.bind_loop_lengths_at_runtime(type_variables_before);

    // a body that gives nothing failed on the way (it called a function with errors)
    const body = resolver.capture_body(generic, value_node, first_local);
    const ran = resolver.interpreter.run_body(context, unit, body);
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

// a length from a while or loop is only counted when the interpreter runs it
fn bind_loop_lengths_at_runtime(self: *Generics, first_variable: usize) void {
    const resolver = self.owning_resolver();
    const type_variables = &resolver.static_pool.type_variables;
    for (first_variable..type_variables.count()) |i| {
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
}

// the static parameters of a stcfun as locals holding the arguments of one realization
fn bind_static(self: *Generics, generic: DeclPool.Index, arguments: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const argument_values = self.copied_arguments(arguments);
    const parameter_nodes = resolver.tree.params_of(resolver.declarations.value_node(generic));

    for (parameter_nodes, 0..) |parameter_node, i| {
        const declared_type = resolver.types.signature(generic).parameters[i];
        const parameter_type = if (static_pool.has_type_variables(declared_type))
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

    const template = self.template_source_of(sibling);
    if (template == .none) return false;
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
        if (static_pool.template_of(parameter) != .none) return true;
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

    for (resolver.tree.manychildren(trait_members(resolver, trait_node))) |statement| {
        const parts = Declarations.Stmt.from_node(resolver, statement);
        if (parts.assignees.len != 1) continue;
        if (resolver.name_pool.name_of_node(parts.assignees[0]) != name) continue;
        if (!parts.kind.is_function()) continue;

        const function_node = parts.values[0];
        if (self.signature_mentions(function_node, value_node)) {
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

// `!{..}` keeps its members in argument 0, `implof(..) !{..}` in argument 1
fn trait_members(resolver: *Resolver, trait_node: NodeId) NodeId {
    const is_implof = resolver.tree.kind(trait_node) == .def_trait_implof;
    return resolver.tree.arg(trait_node, if (is_implof) 1 else 0);
}

pub fn template_field(self: *Generics, template: DeclPool.Index, name: NamePool.Index) ?NodeId {
    const resolver = self.owning_resolver();
    const unit = resolver.tree.arg(resolver.declarations.value_node(template), 1);
    const fields = resolver.tree.fields_of(ParseTree.Def.from_node(resolver.tree, unit).core);
    const field_index = resolver.declarations.parameter_index(fields, name) orelse return null;
    return fields[field_index];
}

fn signature_mentions(self: *Generics, function_node: NodeId, value_node: NodeId) bool {
    const resolver = self.owning_resolver();
    const header = resolver.tree.arg(function_node, 0);
    if (resolver.tree.kind(header) != .partial__fun_def_header_ret) return true;
    if (self.mentions(resolver.tree.arg(header, 1), value_node)) return true;

    for (resolver.tree.params_of(function_node)) |parameter_node| {
        const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
        if (self.mentions(parameter.ty, value_node)) return true;
    }
    return false;
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
