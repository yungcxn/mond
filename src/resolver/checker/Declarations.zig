const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// declarations: names and their scopes, signatures, bodies, statements that declare or assign
const Declarations = @This();

pub const Stmt = struct {
    // the statement below its modifiers, e.g. the assignment inside `pub mut x = ..`
    node: NodeId,

    // all other of these fields may be fully unset
    flags: DeclPool.Entry.Flags,
    kind: DeclPool.Entry.Kind,
    type: NodeId,
    assignees: []const NodeId,
    values: []const NodeId,

    pub fn from_node(resolver: *Resolver, node: NodeId) Stmt {
        const tree = resolver.tree;

        // modifiers wrap the statement, each one becomes a flag
        var flags = DeclPool.Entry.Flags{};
        var root = node;
        while (true) : (root = tree.arg(root, 0)) switch (tree.kind(root)) {
            .mod_pub => flags.is_pub = true,
            .mod_mut => flags.is_mut = true,
            .mod_stc => flags.is_stc = true,
            else => break,
        };

        var type_node: NodeId = 0;
        var value: NodeId = 0;
        var assignees: []const NodeId = &.{};
        switch (tree.kind(root)) {
            .def_var => {
                const def_var = tree.laidout_children(.def_var, root);
                type_node = def_var.type;
                assignees = destructured_or(tree, def_var.identifier, tree.arg_ptr(root, 1)[0..1]);
            },
            .assign_typed => {
                const assign_typed = tree.laidout_children(.assign_typed, root);
                const def_var = tree.laidout_children(.def_var, assign_typed.def_var);
                value = assign_typed.assigned;
                type_node = tree.arg(assign_typed.def_var, 0);
                const single = tree.arg_ptr(assign_typed.def_var, 1)[0..1];
                assignees = destructured_or(tree, def_var.identifier, single);
            },
            .assign => {
                const assign = tree.laidout_children(.assign, root);
                value = tree.arg(root, 1);
                assignees = destructured_or(tree, assign.assignee, tree.arg_ptr(root, 0)[0..1]);
            },
            else => {},
        }

        const existing = if (assignees.len == 1)
            resolver.node_declarations[assignees[0]]
        else
            .none;
        const assignable = assignees.len == 1 and !tree.props(assignees[0]).name;
        const assigns_existing = existing != .none and
            !resolver.decl_pool.get(existing, .kind).is_function();
        const assigns = type_node == 0 and (assignable or assigns_existing);

        var values: []const NodeId = &.{};
        if (value != 0) {
            // the value is the second child of both assignment forms, sliced in place in the tree
            std.debug.assert(value == tree.arg(root, 1));
            values = if (tree.kind(value) == .partial__assign_multival)
                tree.manychildren(value)
            else
                tree.arg_ptr(root, 1)[0..1];
        }

        return .{
            .node = root,
            .flags = flags,
            // the kind a statement declares, read from its type and value
            .kind = if (assigns) .variable else switch (tree.kind(type_node)) {
                .type_fun => .function,
                .type_stcfun => .static_function,
                .type_inlfun => .inlined_function,
                .type_type => resolver.declarations.type_declaration_kind(value, .record),
                .type_variant => resolver.declarations.type_declaration_kind(value, .variant),
                .type_trait => resolver.declarations.type_declaration_kind(value, .trait),
                .none => if (value != 0 and tree.props(value).function) .function else .variable,
                else => .variable,
            },
            .type = type_node,
            .assignees = assignees,
            .values = values,
        };
    }

    fn destructured_or(tree: *ParseTree, assignee: NodeId, single: []const NodeId) []const NodeId {
        if (tree.kind(assignee) == .partial__destructure) return tree.manychildren(assignee);
        return single;
    }

    pub fn is_member(statement: Stmt) bool {
        return statement.assignees.len == 1 and statement.kind.is_function();
    }
};

pub fn owning_resolver(self: *Declarations) *Resolver {
    return @alignCast(@fieldParentPtr("declarations", self));
}

pub fn use_name(self: *Declarations, node: NodeId) DeclPool.Index {
    const resolver = self.owning_resolver();

    const name = resolver.name_pool.name_of_node(node);
    const declaration = resolver.scopes.lookup(&resolver.decl_pool, name);
    if (declaration == .none) {
        if (resolver.doctor.has_report_at(node)) return declaration;
        _ = resolver.report(.undefined_name, node, name, 0);
        return declaration;
    }

    resolver.node_declarations[node] = declaration;
    self.ensure_signature(declaration);
    return declaration;
}

pub fn declare_local(
    self: *Declarations,
    name: NamePool.Index,
    node: NodeId,
    kind: DeclPool.Entry.Kind,
    value_type: StaticPool.Index,
) DeclPool.Index {
    const resolver = self.owning_resolver();
    const declaration = resolver.decl_pool.push(name, node, kind, value_type, .{});
    resolver.scopes.bind(name, declaration);
    return declaration;
}

pub fn report_redeclaration(self: *Declarations, name: NamePool.Index, at: NodeId) void {
    const resolver = self.owning_resolver();
    const earlier = resolver.scopes.in_innermost_scope(name);
    if (earlier != .none) resolver.doctor.report(.duplicate_declaration, at, name, earlier);
}

pub fn link_identifier(
    self: *Declarations,
    identifier: NodeId,
    declaration: DeclPool.Index,
    value_type: StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    if (identifier == 0) return;

    resolver.node_declarations[identifier] = declaration;
    resolver.node_types[identifier] = value_type;
}

pub fn ensure_signature(self: *Declarations, declaration: DeclPool.Index) void {
    const resolver = self.owning_resolver();
    const decl_pool = &resolver.decl_pool;

    const diagnostics_mark = resolver.doctor.diagnostics.len();
    defer resolver.doctor.settle(diagnostics_mark);
    const state = decl_pool.pointer(declaration, .state);
    switch (state.*) {
        .unresolved => {},
        .resolving_signature => {
            const node = decl_pool.get(declaration, .node);
            _ = resolver.report(.declaration_cycle, node, decl_pool.get(declaration, .name), 0);
            state.* = .failed;
            return;
        },
        .signature_ready, .checking_body, .done, .failed => return,
    }
    state.* = .resolving_signature;

    const kind = decl_pool.get(declaration, .kind);
    const statement = Stmt.from_node(resolver, decl_pool.get(declaration, .node));
    // these names are functions by their role already, a `fun` type on them is redundant
    if (statement.type != 0 and resolver.tree.kind(statement.type) == .type_fun) {
        const implied = switch (decl_pool.get(declaration, .name)) {
            .init, .deinit, .main, .has_next, .next => true,
            else => false,
        };
        if (implied) _ = resolver.report(.redundant_fun, statement.type, 0, 0);
    }

    const flags = decl_pool.get(declaration, .flags);
    var context = FunctionContext{
        .declaration = declaration,
        .self_type = self.owner_of(declaration),
        .is_static_context = flags.is_stc,
    };
    const value = self.value_node(declaration);
    const self_type = if (decl_pool.implicit_self_count(declaration) == 1)
        context.self_type
    else
        .none;
    self.open_declaration_scope(flags.is_global, self_type, value);
    if (!flags.is_global and kind.is_type_declaration()) resolver.scopes.bind(.wall, .none);

    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => {
            if (resolver.tree.props(value).function) {
                self.resolve_function_signature(&context, declaration, value);
            } else {
                self.resolve_produced_function(&context, declaration, value);
            }
        },
        .record, .variant, .trait => {
            _ = resolver.types.check_type_definition(&context, declaration, value);
        },
        .type_alias => self.resolve_type_alias(&context, declaration, value),
        .variable,
        .parameter,
        .static_parameter,
        .field,
        .variant_case,
        .pattern_binder,
        .arrow_binder,
        .loop_variable,
        .self,
        .autoins_arg,
        .autoins_it,
        => _ = self.check_statement(&context, decl_pool.get(declaration, .node)),
    }
    resolver.scopes.close();

    if (decl_pool.get(declaration, .state) == .resolving_signature) {
        decl_pool.set(declaration, .state, .signature_ready);
    }
}

fn resolve_function_signature(
    self: *Declarations,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    value: NodeId,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;
    const kind = decl_pool.get(declaration, .kind);

    // stcfun: the first tuple is static, the body's product is the result
    // a second tuple of a stcfun belongs to the function it produces
    const result = resolver.tree.arg(value, 1);
    const produced_kind = self.template_kind(declaration);
    const result_kind = self.declared_type_kind(result);
    if (kind == .static_function and produced_kind == .variable and result_kind != .variable) {
        _ = resolver.report(.missing_ret, result, 0, 0);
    }

    const return_type: StaticPool.Index = blk: {
        const tree = resolver.tree;
        if (kind == .static_function) {
            const produced = if (tree.kind(result) == .ret) tree.arg(result, 0) else result;
            const otherwise: StaticPool.Index = if (tree.props(produced).function)
                .fun_type
            else
                .poison_type;
            break :blk self.declared_type_kind(produced).meta_type(otherwise);
        }

        const without_result = tree.kind(value) == .def_fun_declaration or
            tree.kind(tree.arg(value, 0)) == .partial__fun_def_header_ret;
        if (without_result) break :blk .unit_type;
        break :blk static_pool.fresh_type_variable(value);
    };
    if (produced_kind != .variable and result_kind == .variable) {
        _ = resolver.report(.redundant_ret, result, 0, 0);
    } else if (produced_kind != .variable and result_kind != produced_kind) {
        const expected = produced_kind.meta_type(.trait_type);
        _ = resolver.report(.type_mismatch, result, return_type, expected);
    }

    // a method's first parameter is the induced `*Self`, `init` constructs and has none
    const category: StaticPool.FunctionType.Category = switch (kind) {
        .static_function => .static,
        .inlined_function => .inlined,
        .function,
        .trait_member,
        .variable,
        .parameter,
        .static_parameter,
        .field,
        .type_alias,
        .record,
        .variant,
        .variant_case,
        .trait,
        .pattern_binder,
        .arrow_binder,
        .loop_variable,
        .self,
        .autoins_arg,
        .autoins_it,
        => .default,
    };
    const induced_self = if (decl_pool.implicit_self_count(declaration) == 1)
        static_pool.pointer_to(context.self_type, true)
    else
        .none;
    const function_type = resolver.types.function_type_of(
        context,
        value,
        category,
        return_type,
        induced_self,
    );
    decl_pool.set(declaration, .value_type, function_type);

    if (!resolver.generics.template_of.contains(declaration)) {
        const parameters = resolver.tree.params_of(value);
        for (parameters, 0..) |parameter, i| {
            for (parameters[0..i], 0..) |earlier, j| {
                const earlier_name = self.parameter_name(earlier, j);
                const name = self.parameter_name(parameter, i);
                if (earlier_name != name) continue;
                resolver.doctor.report(.duplicate_declaration, parameter, name, declaration);
            }
        }
    }

    const flags = decl_pool.get(declaration, .flags);
    if (flags.is_global and decl_pool.get(declaration, .name) == .main) {
        const declared_type = decl_pool.get(declaration, .value_type);
        const runtime_type = resolver.types.with_runtime_lengths(declared_type);
        decl_pool.set(declaration, .value_type, runtime_type);
    }

    const static_value = if (kind == .static_function)
        static_pool.intern(.{ .static_function = .{
            .declaration = declaration,
            .result_kind = if (static_pool.tag(return_type) == .meta_type)
                static_pool.get(return_type).meta_type
            else
                .stcfun,
        } })
    else
        static_pool.intern(.{ .function_value = declaration });
    decl_pool.set(declaration, .static_value, static_value);
}

// a function produced by a static expression (`fun sub_from_templ = my_templ(i32, false)`)
fn resolve_produced_function(
    self: *Declarations,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    value: NodeId,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const produced = resolver.interpreter.evaluate_static(context, value);
    if (static_pool.tag(produced) == .function_value) {
        const function = static_pool.get(produced).function_value;
        resolver.decl_pool.set(declaration, .static_value, produced);
        const function_type = resolver.decl_pool.get(function, .value_type);
        resolver.decl_pool.set(declaration, .value_type, function_type);
        return;
    }
    if (produced != .poison_type) {
        _ = resolver.report(.type_mismatch, value, static_pool.type_of(produced), .fun_type);
    }
}

fn resolve_type_alias(
    self: *Declarations,
    context: *FunctionContext,
    declaration: DeclPool.Index,
    value: NodeId,
) void {
    const resolver = self.owning_resolver();

    const aliased = resolver.types.type_from_node(context, value);
    resolver.decl_pool.set(declaration, .static_value, aliased);
    resolver.decl_pool.set(declaration, .value_type, resolver.static_pool.type_of(aliased));
}

pub fn check_body(self: *Declarations, declaration: DeclPool.Index) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;

    const state = decl_pool.pointer(declaration, .state);
    if (state.* != .signature_ready) return;

    const kind = decl_pool.get(declaration, .kind);
    const value = self.value_node(declaration);
    const function_type = decl_pool.get(declaration, .value_type);

    // stcfun bodies are checked per realization, length-generic ones per length (`instantiate`)
    // `main` is realized once, by the runtime
    const generic = static_pool.is_length_generic(function_type) and
        !resolver.generics.template_of.contains(declaration);
    const abstract = generic and static_pool.has_only_template_parameters(function_type);
    const checked_elsewhere = kind == .static_function or
        !kind.is_function() or
        resolver.tree.kind(value) != .def_fun or
        generic and !abstract;
    if (checked_elsewhere) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;

    const first_row = decl_pool.entries.len();
    const diagnostics_mark = resolver.doctor.diagnostics.len();
    const outer = resolver.initialization.enter();
    defer resolver.initialization.leave(outer);

    // a local function sees which enclosing locals are not written yet
    const is_global = decl_pool.get(declaration, .flags).is_global;
    if (kind == .function and !is_global) resolver.initialization.import_outer(0, outer, 0);

    const self_count = decl_pool.implicit_self_count(declaration);
    var context = FunctionContext{
        .declaration = declaration,
        .return_type = static_pool.get(function_type).function_type.return_type,
        .self_type = self.owner_of(declaration),
        .is_abstract = abstract,
    };
    const self_type = if (self_count == 1) context.self_type else .none;
    self.open_declaration_scope(decl_pool.get(declaration, .flags).is_global, self_type, value);

    // a where clause sees its own parameter and the ones before it
    // realized `type` parameters are static values
    const template = resolver.generics.template_of.get(declaration);
    const realized_arguments = resolver.generics.realization_arguments.get(declaration);
    const realizes_view = if (template) |template_declaration|
        !static_pool.has_only_template_parameters(decl_pool.get(template_declaration, .value_type))
    else
        false;

    var generic_slot: usize = 0;
    for (resolver.tree.params_of(value), 0..) |parameter_node, i| {
        const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
        const parameter_types = static_pool.get(function_type).function_type.parameters;
        const parameter_type = parameter_types[i + self_count];
        if (parameter.default != 0) {
            _ = resolver.expressions.check(&context, parameter.default, parameter_type);
        }

        const parameter_declaration = self.declare_local(
            self.parameter_or_position_name(parameter, i),
            parameter_node,
            .parameter,
            parameter_type,
        );
        resolver.node_declarations[parameter_node] = parameter_declaration;

        const template_parameter_type = if (template) |template_declaration|
            resolver.types.signature(template_declaration).parameters[i + self_count]
        else
            parameter_type;
        const is_view = realizes_view and static_pool.template_of(template_parameter_type) != .none;
        decl_pool.pointer(parameter_declaration, .flags).is_view = is_view;

        const takes_generic_argument = realized_arguments != null and
            static_pool.is_generic_parameter(template_parameter_type);
        if (takes_generic_argument) {
            if (static_pool.tag(template_parameter_type) == .meta_type) {
                const elements = static_pool.get(realized_arguments.?).aggregate_value.elements;
                decl_pool.set(parameter_declaration, .static_value, elements[generic_slot]);
            }
            generic_slot += 1;
        }

        self.link_identifier(parameter.name, parameter_declaration, parameter_type);
        self.check_parameter_guards(&context, parameter, parameter_type);
    }
    self.check_function_result(&context, resolver.tree.arg(value, 1));
    resolver.scopes.close();

    // the first row of a method body is its `self`, a write to it makes the method a writing one
    if (self_count == 1 and decl_pool.get(@enumFromInt(first_row), .flags).writes) {
        decl_pool.pointer(declaration, .flags).writes = true;
    }

    const failed = resolver.doctor.errors_since(resolver.tree, diagnostics_mark, value);
    resolver.doctor.settle(diagnostics_mark);
    decl_pool.set(declaration, .state, if (failed) .failed else .done);
    if (!abstract) resolver.bodies.register(resolver.capture_body(declaration, value, first_row));
}

pub fn check_function_result(self: *Declarations, context: *FunctionContext, body: NodeId) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    if (resolver.tree.kind(body) != .block) {
        _ = resolver.expressions.check(context, body, context.return_type);
        return;
    }

    const body_type = resolver.expressions.infer(context, body, .none);
    const return_type = static_pool.substitute_type_variables(context.return_type);
    if (return_type == .none) return;

    // a `{}` body that never returns a value returns unit
    // a body with a result returns it on every path (`$main` falls off with 0)
    if (static_pool.tag(return_type) == .type_variable) {
        _ = static_pool.unify(context.return_type, .unit_type);
        return;
    }
    const is_main = context.declaration != .none and
        resolver.decl_pool.get(context.declaration, .name) == .main;
    const may_fall_off = is_main or
        return_type == .unit_type or
        return_type == .runit_type or
        return_type == .poison_type;
    if (may_fall_off) return;
    if (body_type == .never_type or body_type == .poison_type) return;
    if (resolver.doctor.has_report_at(body)) return;
    _ = resolver.report(.missing_ret, body, 0, 0);
}

pub fn check_statement(
    self: *Declarations,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;
    const statement = Stmt.from_node(resolver, node);

    // in an interpreted body a type declaration is evaluated right away
    if (context.is_interpreted and statement.kind.is_type_declaration()) {
        const value = statement.values[0];

        _ = resolver.expressions.infer(context, value, .none);
        const declared_type = resolver.static_values.evaluate_or_defer(context, value);

        for (statement.assignees) |assignee| {
            const meta_type = if (declared_type) |known|
                static_pool.type_of(known)
            else
                resolver.types.meta_type_of_node(value);
            const declaration = self.declare(
                assignee,
                statement.node,
                statement.kind,
                meta_type,
                statement.flags,
            );
            decl_pool.set(declaration, .state, .done);
            decl_pool.set(declaration, .static_value, declared_type orelse .none);
        }
        return .unit_type;
    }

    // a name holding a function value is assigned, not declared as a function again
    const function_variable: DeclPool.Index = blk: {
        if (statement.kind != .function or statement.type != 0) break :blk .none;
        if (statement.assignees.len != 1) break :blk .none;

        const name = resolver.name_pool.name_of_node(statement.assignees[0]);
        const visible = resolver.scopes.lookup(decl_pool, name);
        if (visible == .none) break :blk .none;
        if (decl_pool.get(visible, .kind).is_function()) break :blk .none;

        const visible_type = decl_pool.get(visible, .value_type);
        if (visible_type == .none) break :blk .none;
        const is_function_type =
            static_pool.tag(static_pool.substitute_type_variables(visible_type)) == .function_type;
        if (!is_function_type) break :blk .none;
        break :blk visible;
    };
    if (function_variable != .none) {
        resolver.node_declarations[statement.assignees[0]] = function_variable;
        return self.check_statement(context, node);
    }

    // a local function, type or trait
    if (statement.kind != .variable) {
        for (statement.assignees) |assignee| {
            const declaration = self.declare(
                assignee,
                statement.node,
                statement.kind,
                .none,
                statement.flags,
            );
            self.ensure_signature(declaration);
            self.check_body(declaration);
        }
        return .unit_type;
    }

    // a write into an assignable (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    const writes_place = statement.assignees.len == 1 and
        resolver.name_pool.name_of_node(statement.assignees[0]) == .none;
    if (writes_place) {
        const place = statement.assignees[0];

        const place_type = resolver.mutability.check_assignable(context, place);
        const expected = if (resolver.tree.macros)
            resolver.macros.tree_place_type(place, place_type)
        else
            place_type;
        for (statement.values) |value| _ = resolver.expressions.check(context, value, expected);
        return .unit_type;
    }

    const declaring = statement.type != 0 or statement.flags.any();
    var declared_type: StaticPool.Index = if (statement.type != 0)
        resolver.types.concrete_type_from_node(context, statement.type)
    else
        .none;

    // untyped: visible names are assigned, their type is shared by the new ones
    const existing = resolver.temporary_slice(DeclPool.Index, statement.assignees.len);
    for (statement.assignees, 0..) |assignee, i| {
        // global rows and hoisted local functions of this very statement are reused, not redeclared
        const known = resolver.node_declarations[assignee];
        const fresh = declaring or known != .none and
            decl_pool.get(known, .node) == statement.node and
            (decl_pool.get(known, .flags).is_global or
                resolver.scopes.lookup(decl_pool, decl_pool.get(known, .name)) == known);
        existing[i] = if (fresh)
            .none
        else
            resolver.scopes.lookup(decl_pool, resolver.name_pool.name_of_node(assignee));
        if (existing[i] == .none) continue;

        // an assigned name is not read, so it must not count as a use before its initialization
        const initialization = &resolver.initialization;
        const outer = initialization.save(0);
        initialization.clear(0);
        const assigned_type = resolver.mutability.check_assignable(context, assignee);
        initialization.copy(0, outer);
        initialization.release(outer);

        if (declared_type == .none) {
            declared_type = assigned_type;
        } else if (assigned_type != declared_type and assigned_type != .poison_type) {
            _ = resolver.report(.destructure_type_conflict, assignee, assigned_type, declared_type);
        }
    }

    resolver.scopes.open();
    if (statement.values.len > 1) {
        // `a, b = x, y`: without a declared type the values join, literals last
        const values = statement.values;
        var shared_type = declared_type;
        const is_deferred_literal = resolver.temporary_slice(bool, values.len);
        for (values, 0..) |value, i| {
            const assigns_existing = i < statement.assignees.len and existing[i] != .none;
            const expected = if (assigns_existing)
                decl_pool.get(existing[i], .value_type)
            else
                declared_type;
            is_deferred_literal[i] = expected == .none and resolver.tree.is_literal(value);
            if (is_deferred_literal[i]) continue;

            const value_type = resolver.expressions.check(context, value, expected);
            if (shared_type == .none) {
                shared_type = value_type;
            } else if (declared_type == .none) {
                const joined = static_pool.join(shared_type, value_type).joined_type;
                shared_type = if (joined == .none)
                    resolver.report(.destructure_type_conflict, value, shared_type, value_type)
                else
                    joined;
            }
        }

        if (declared_type == .none) {
            for (values, 0..) |value, i| {
                if (is_deferred_literal[i]) _ = resolver.expressions.infer(context, value, .none);
            }

            if (shared_type == .none) shared_type = resolver.flow.common_literal_type(values);
            if (shared_type == .none) shared_type = resolver.node_types[values[0]];

            for (values, 0..) |value, i| {
                if (!is_deferred_literal[i] or shared_type == .poison_type) continue;

                const literal_type = resolver.static_values.literal_type(value, shared_type);
                const joined = static_pool.join(shared_type, literal_type).joined_type;
                shared_type = if (joined == .none)
                    resolver.report(.destructure_type_conflict, value, shared_type, literal_type)
                else
                    joined;
            }

            for (values, 0..) |value, i| {
                if (!is_deferred_literal[i] or shared_type == .poison_type) continue;
                _ = resolver.expressions.expect_type(
                    value,
                    resolver.node_types[value],
                    shared_type,
                );
            }
        }
        declared_type = shared_type;
    } else if (statement.values.len == 1) {
        const value = statement.values[0];

        // a fresh var as expectation wants a value (loops, ifs as values) without fixing its type
        const expected = if (declared_type != .none)
            declared_type
        else
            static_pool.fresh_type_variable(statement.node);
        const value_type = resolver.expressions.check(context, value, expected);

        if (declared_type == .none) {
            declared_type = static_pool.substitute_type_variables(value_type);
        }

        const unrealized = declared_type != .none and
            static_pool.tag(declared_type) == .function_type and
            static_pool.contains_template(declared_type);
        if (unrealized) {
            declared_type = resolver.report(.unrealized_template, value, declared_type, 0);
        }
    }
    resolver.scopes.close();

    // trees and what holds them exist at compile-time only, so their variables are static
    // an interpreted body needs no flag, everything in it is static already
    var kept_flags = statement.flags;
    kept_flags.is_stc = statement.flags.is_stc or
        resolver.tree.macros and
            !context.is_interpreted and
            static_pool.contains_trees(static_pool.substitute_type_variables(declared_type));

    for (statement.assignees, 0..) |assignee, i| {
        const declaration = if (existing[i] != .none)
            existing[i]
        else
            self.declare(
                assignee,
                statement.node,
                .variable,
                if (declared_type == .none) .poison_type else declared_type,
                kept_flags,
            );
        const assigns_existing = existing[i] != .none;
        const values = statement.values;

        const value_type = decl_pool.get(declaration, .value_type);

        // scalars declared without a value must be written before they are read
        const flags = decl_pool.get(declaration, .flags);
        const scalar = value_type != .none and
            value_type != .poison_type and
            static_pool.tag(value_type) != .record_type and
            static_pool.tag(value_type) != .array_type;
        if (assigns_existing) {
            resolver.initialization.mark_written(declaration);
        } else if (values.len == 0 and !flags.is_global and scalar) {
            resolver.initialization.track(declaration);
        }

        if (values.len == 0) continue;
        const inside_evaluation = resolver.interpreter.depth > 0 and !context.is_interpreted;
        if (assigns_existing and !inside_evaluation) continue;
        const is_static = decl_pool.get(declaration, .flags).is_stc or
            context.is_static_context;
        if (!is_static) continue;

        const value = values[@min(i, values.len - 1)];
        const static_value = if (resolver.node_types[value] == .poison_type)
            .poison_type
        else
            resolver.static_values.retyped(
                resolver.static_values.value_of(context, value),
                value_type,
            );
        decl_pool.set(declaration, .static_value, static_value);

        // an unlengthed static takes the length of its value
        const stored = decl_pool.get(declaration, .static_value);
        if (stored == .none or static_pool.tag(stored) != .aggregate_value) continue;
        if (static_pool.has_type_variables(value_type)) {
            _ = static_pool.unify(value_type, static_pool.type_of(stored));
        }

        const length = static_pool.static_length(value_type) orelse continue;
        if (length != static_pool.get(stored).aggregate_value.elements.len) {
            _ = resolver.report(.type_mismatch, value, static_pool.type_of(stored), value_type);
        }
    }
    return .unit_type;
}

pub fn check_parameter_guards(
    self: *Declarations,
    context: *FunctionContext,
    parameter: ParseTree.Param,
    parameter_type: StaticPool.Index,
) void {
    const resolver = self.owning_resolver();

    if (parameter.where != 0) _ = resolver.expressions.check(context, parameter.where, .bool_type);
    if (parameter.@"else" == 0) return;

    if (resolver.tree.kind(parameter.@"else") == .assign) {
        _ = resolver.expressions.infer(context, parameter.@"else", .none);
    } else {
        _ = resolver.expressions.check(context, parameter.@"else", parameter_type);
    }
}

// a declared global row is reused, anything else becomes a new local
fn declare(
    self: *Declarations,
    identifier: NodeId,
    statement_node: NodeId,
    kind: DeclPool.Entry.Kind,
    value_type: StaticPool.Index,
    flags: DeclPool.Entry.Flags,
) DeclPool.Index {
    const resolver = self.owning_resolver();
    const decl_pool = &resolver.decl_pool;

    var declaration = resolver.node_declarations[identifier];
    // global rows and hoisted local functions of this very statement are reused, not redeclared
    const pre_declared = declaration != .none and
        decl_pool.get(declaration, .node) == statement_node and
        (decl_pool.get(declaration, .flags).is_global or
            resolver.scopes.lookup(decl_pool, decl_pool.get(declaration, .name)) == declaration);
    if (!pre_declared) {
        self.report_redeclaration(resolver.name_pool.name_of_node(identifier), identifier);
        const name = resolver.name_pool.name_of_node(identifier);
        declaration = self.declare_local(name, statement_node, kind, value_type);
        resolver.decl_pool.set(declaration, .flags, flags);
        resolver.node_declarations[identifier] = declaration;
    } else if (value_type != .none) {
        resolver.decl_pool.set(declaration, .value_type, value_type);
    }

    _ = resolver.set_node_type(identifier, if (value_type == .none) .unit_type else value_type);
    return declaration;
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
pub fn open_declaration_scope(
    self: *Declarations,
    barrier: bool,
    self_type: StaticPool.Index,
    node: NodeId,
) void {
    const resolver = self.owning_resolver();

    resolver.scopes.open();
    if (barrier) resolver.scopes.bind(.none, .none);
    if (self_type == .none) return;

    const self_pointer = resolver.static_pool.pointer_to(self_type, true);
    const self_declaration = self.declare_local(.self, node, .self, self_pointer);
    resolver.decl_pool.pointer(self_declaration, .flags).is_mut = true;
}

// a method's owner is the value of the trait row right before its members
// realizations ask their template
fn owner_of(self: *Declarations, declaration: DeclPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    const decl_pool = &resolver.decl_pool;

    if (resolver.generics.template_of.get(declaration)) |template| return self.owner_of(template);
    if (decl_pool.get(declaration, .kind) != .trait_member) return .none;

    // a trait body row always precedes its members, so the walk ends before row 0
    var row = @intFromEnum(declaration);
    while (decl_pool.get(@enumFromInt(row), .kind) != .trait) {
        std.debug.assert(row > 0);
        row -= 1;
    }
    return decl_pool.get(@enumFromInt(row), .static_value);
}

// the kind of type a definition node declares, `variable` for anything else
pub fn declared_type_kind(self: *Declarations, node: NodeId) DeclPool.Entry.Kind {
    const resolver = self.owning_resolver();
    return switch (resolver.tree.kind(ParseTree.Def.from_node(resolver.tree, node).core)) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

// `type T = ..`: a stcfun for a function value, a definition of the declared kind, else an alias
fn type_declaration_kind(
    self: *Declarations,
    value: NodeId,
    declared_kind: DeclPool.Entry.Kind,
) DeclPool.Entry.Kind {
    const tree = self.owning_resolver().tree;

    if (value != 0 and tree.kind(value) == .def_fun) return .static_function;
    if (self.declared_type_kind(value) == declared_kind) return declared_kind;
    return .type_alias;
}

// what a stcfun declared as `type` / `variant` / `trait` produces
pub fn template_kind(self: *Declarations, declaration: DeclPool.Index) DeclPool.Entry.Kind {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;

    const declaration_node = resolver.decl_pool.get(declaration, .node);
    if (tree.kind(declaration_node) != .assign_typed) return .variable;
    if (tree.kind(tree.arg(declaration_node, 1)) != .def_fun) return .variable;

    return switch (tree.kind(tree.arg(tree.arg(declaration_node, 0), 0))) {
        .type_type => .record,
        .type_variant => .variant,
        .type_trait => .trait,
        else => .variable,
    };
}

pub fn value_node(self: *Declarations, declaration: DeclPool.Index) NodeId {
    const resolver = self.owning_resolver();
    const node = resolver.decl_pool.get(declaration, .node);
    return switch (resolver.tree.kind(node)) {
        .assign, .assign_typed => resolver.tree.arg(node, 1),
        else => node,
    };
}

pub fn parameter_name(self: *Declarations, parameter_node: NodeId, i: usize) NamePool.Index {
    const resolver = self.owning_resolver();
    const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
    return self.parameter_or_position_name(parameter, i);
}

// the index of the parameter or field `name` among `parameters`
pub fn parameter_index(
    self: *Declarations,
    parameters: []const NodeId,
    name: NamePool.Index,
) ?u32 {
    for (parameters, 0..) |parameter_node, j| {
        if (self.parameter_name(parameter_node, j) == name) return @intCast(j);
    }
    const name_pool = &self.owning_resolver().name_pool;
    for (parameters, 0..) |parameter_node, j| {
        const text = name_pool.text_of(self.parameter_name(parameter_node, j));
        const written = text[0 .. std.mem.indexOfScalar(u8, text, '`') orelse continue];
        if (std.mem.eql(u8, written, name_pool.text_of(name))) return @intCast(j);
    }
    return null;
}

pub fn parameter_or_position_name(
    self: *Declarations,
    parameter: ParseTree.Param,
    i: usize,
) NamePool.Index {
    const resolver = self.owning_resolver();
    if (parameter.name != 0) return resolver.name_pool.name_of_node(parameter.name);
    return resolver.name_pool.positional_name(i);
}

// a closure holds a pointer to a mutable or aggregate local, a copy of anything else
pub fn is_captured_by_reference(self: *Declarations, declaration: DeclPool.Index) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const declared_type = resolver.decl_pool.get(declaration, .value_type);
    const value_type = static_pool.substitute_type_variables(declared_type);
    if (resolver.decl_pool.get(declaration, .flags).is_mut) return true;
    if (value_type == .none) return false;
    if (static_pool.tag(value_type) == .record_type) return true;
    return static_pool.tag(value_type) == .array_type and
        static_pool.get(value_type).array_type.length != StaticPool.dyn_len;
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
pub fn realized(self: *Declarations, declaration: DeclPool.Index) DeclPool.Index {
    const resolver = self.owning_resolver();
    const static_value = resolver.decl_pool.get(declaration, .static_value);
    if (static_value == .none) return declaration;
    if (resolver.static_pool.tag(static_value) != .function_value) return declaration;
    return resolver.static_pool.get(static_value).function_value;
}

// every root declares its names globally, overloads of a name are chained in dispatch order
pub fn collect_globals(self: *Declarations) void {
    const resolver = self.owning_resolver();

    for (resolver.roots) |root| {
        // the parser knows no statements, every root is read as one here
        const statement = Stmt.from_node(resolver, root);
        var flags = statement.flags;
        flags.is_global = true;
        const declares = statement.type != 0 or
            statement.flags.any() or
            statement.kind != .variable;

        for (statement.assignees) |assignee| {
            const name = resolver.name_pool.name_of_node(assignee);
            if (name == .none) continue;

            const globals = &resolver.scopes.globals;
            const entry = globals.getOrPut(resolver.allocator, name) catch @panic("OOM");
            // functions overload each other, any other repeated global name is a duplicate
            const overloads = entry.found_existing and
                statement.kind.is_function() and
                resolver.decl_pool.get(entry.value_ptr.*, .kind).is_function();
            if (entry.found_existing and !overloads) {
                if (declares) {
                    _ = resolver.report(.duplicate_declaration, assignee, name, entry.value_ptr.*);
                    if (resolver.node_declarations[root] == .none) {
                        resolver.node_declarations[root] = entry.value_ptr.*;
                    }
                }
                continue;
            }

            const declaration = resolver.decl_pool.push(
                name,
                statement.node,
                statement.kind,
                .none,
                flags,
            );
            if (entry.found_existing) {
                // where-clause overloads go first: a group dispatches its clauses in order
                // the where-less overload of a group comes last as its runtime fallback
                var at = entry.value_ptr;
                while (at.* != .none) : (at = resolver.decl_pool.pointer(at.*, .next_overload)) {
                    const goes_before = resolver.calls.has_where(declaration) and
                        !resolver.calls.has_where(at.*);
                    if (goes_before) break;
                }
                resolver.decl_pool.set(declaration, .next_overload, at.*);
                at.* = declaration;
            } else {
                entry.value_ptr.* = declaration;
            }

            resolver.node_declarations[assignee] = declaration;
            if (resolver.node_declarations[root] == .none) {
                resolver.node_declarations[root] = declaration;
            }
        }
    }
}

// `main` is declared once with a signature the runtime can call
pub fn check_main(self: *Declarations) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;

    const main = resolver.scopes.globals.get(.main) orelse
        return resolver.doctor.report(.missing_main, 0, 0, 0);
    const node = decl_pool.get(main, .node);

    const second_main = decl_pool.get(main, .next_overload);
    if (second_main != .none) {
        const second_node = decl_pool.get(second_main, .node);
        const name = NamePool.Index.main;
        return resolver.doctor.report(.duplicate_declaration, second_node, name, main);
    }

    const main_type = decl_pool.get(main, .value_type);
    // no parameters or `(count, arguments)`, a unit, never or integer result
    if (main_type != .none and static_pool.tag(main_type) == .function_type) {
        const function = static_pool.get(main_type).function_type;
        const parameters = function.parameters;
        const parameters_fit = parameters.len == 0 or (parameters.len == 2 and
            static_pool.properties(parameters[0]).is_integer and
            static_pool.properties(parameters[1]).is_pointer);

        const return_type = function.return_type;
        const runnable = parameters_fit and (return_type == .unit_type or
            return_type == .runit_type or
            return_type == .never_type or
            static_pool.properties(return_type).is_integer);
        if (runnable) return;
    }
    _ = resolver.report(.type_mismatch, node, main_type, .none);
}
