const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Value = @import("../interpreter/Value.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// calls: overloads, dispatch groups, arguments bound to parameters, stcfun and generic calls
const Calls = @This();

// the arguments of a declared call after the self argument, with their types and parameters
const CallArguments = struct {
    nodes: []const NodeId,
    types: []StaticPool.Index,
    // the parameter index each argument binds to
    parameter_of: []u32,
    // 1 for a method with an induced `self` parameter that no argument binds to
    self_count: usize,
};

// the overload a call picks among the chain of candidates
const OverloadChoice = struct {
    best: DeclPool.Index,
    candidate_count: u32,
    ambiguous: bool,
};

pub fn owning_resolver(self: *Calls) *Resolver {
    return @alignCast(@fieldParentPtr("calls", self));
}

pub fn check_call(self: *Calls, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    const arguments = tree.manychildren(tree.arg(node, 1));

    // a copy of a record, the named arguments must be its fields
    if (tree.kind(node) == .with) {
        const original_type = resolver.expressions.infer(context, tree.arg(node, 0), .none);
        const record_type = static_pool.through_pointer(original_type);

        // of a tree: its children by their field names, known once it is evaluated
        if (tree.macros and static_pool.is_tree(record_type)) {
            for (arguments) |argument| {
                _ = resolver.expressions.check(context, tree.arg_value(argument), .ast_type);
            }
            return static_pool.pointee(record_type);
        }

        for (arguments) |argument| {
            const name_node = tree.arg_name(argument);
            const name = resolver.name_pool.name_of_node(name_node);

            const member = if (name_node != 0 and record_type != .poison_type)
                static_pool.lookup_member(record_type, name)
            else
                StaticPool.Member.none;

            if (member == .field) {
                const field_type = self.type_named_argument(argument, member.field.field_type);
                _ = resolver.expressions.check(context, tree.arg_value(argument), field_type);
                continue;
            }
            if (record_type == .poison_type) continue;
            _ = resolver.report(.unknown_named_argument, argument, name, record_type);
        }
        return record_type;
    }

    // `$fresh(..)` and `$error(..)` belong to the macros
    const callee = tree.arg(node, 0);
    const names_builtin = tree.macros and
        tree.kind(callee) == .identifier and
        tree.text(callee, resolver.src_bytes)[0] == '$';
    if (names_builtin) {
        const name = resolver.name_pool.name_of_node(callee);
        switch (name) {
            .fresh, .@"error" => {
                return resolver.macros.check_builtin(context, node, name, arguments);
            },
            else => {},
        }
    }

    const callee_type = resolver.expressions.infer(context, callee, .none);
    // a call making a function (of a stcfun, or of a `fun` taking only types) is called like it
    const declaration: DeclPool.Index = blk: {
        if (tree.kind(callee) != .fun_call) break :blk resolver.node_declarations[callee];

        const inner_callee = resolver.node_declarations[tree.arg(callee, 0)];
        const calls_stcfun = inner_callee != .none and
            resolver.decl_pool.get(inner_callee, .kind) == .static_function;
        const made = resolver.node_static_values[callee];
        const made_function = made != .none and static_pool.tag(made) == .function_value;
        if (!calls_stcfun and !made_function) break :blk .none;
        break :blk resolver.node_declarations[callee];
    };
    // `x.m(..)` binds x as the self argument, `Type.m(x.&, ..)` passes it like any other argument
    const receiver: NodeId = if (tree.kind(callee) == .member and
        static_pool.tag(resolver.node_types[tree.arg(callee, 0)]) != .meta_type)
        tree.arg(callee, 0)
    else
        0;

    const calls_declared_function = callee_type != .poison_type and
        declaration != .none and
        resolver.decl_pool.get(declaration, .kind).is_function();
    if (calls_declared_function) {
        return self.call_declared(context, node, declaration, arguments, receiver);
    }

    const callee_is_type = static_pool.tag(callee_type) == .meta_type;
    const target_type = if (callee_is_type)
        resolver.static_values.evaluate_or_defer(context, callee) orelse {
            for (arguments) |argument| {
                _ = resolver.expressions.infer(context, tree.arg_value(argument), .none);
            }
            return .poison_type;
        }
    else
        static_pool.substitute_type_variables(callee_type);
    const called_as_value = !callee_is_type and (tree.kind(callee) != .member or receiver != 0);

    switch (static_pool.tag(target_type)) {
        // type constructors: records (`Person(name = ..)`) and variant cases (`Event.Key(13)`)
        .record_type, .variant_case_type => {
            if (!called_as_value) {
                return self.check_constructor(context, node, target_type, arguments);
            }
        },
        .ast_type => return resolver.macros.check_tree_call(context, node, target_type, arguments),
        .function_type => {
            return self.check_function_value_call(context, node, target_type, arguments);
        },
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .pointer_type,
        .mutable_pointer_type,
        .variant_type,
        .variant_union_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .aggregate_value,
        .variant_value,
        .function_value,
        .tree_value,
        => {},
    }

    // anything else is not callable, its arguments are inferred alone
    for (arguments) |argument| {
        _ = resolver.expressions.infer(context, tree.arg_value(argument), .none);
    }
    if (target_type == .poison_type) return target_type;
    return resolver.report(.not_callable, callee, callee_type, .none);
}

fn check_constructor(
    self: *Calls,
    context: *FunctionContext,
    node: NodeId,
    target_type: StaticPool.Index,
    arguments: []const NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const record_type = if (static_pool.tag(target_type) == .variant_case_type)
        static_pool.get(target_type).variant_case_type.payload
    else
        target_type;
    const parameter_of = resolver.temporary_slice(u32, arguments.len);

    if (record_type == .none and arguments.len > 0) {
        return resolver.report(.wrong_arity, node, arguments.len, 0);
    }
    if (record_type != .none) {
        const fields = resolver.types.field_nodes_of(record_type);
        if (!self.bind_arguments(fields, arguments, parameter_of, false)) {
            return self.report_bad_arguments(node, fields, arguments);
        }
    }

    for (arguments, 0..) |argument, i| {
        const field_type = static_pool.field_type(record_type, parameter_of[i]);
        const expected = self.type_named_argument(argument, field_type);
        _ = resolver.expressions.check(context, resolver.tree.arg_value(argument), expected);
    }
    return target_type;
}

// a value of function type (`op(a, b)`, `make_adder(1)(2)`, a lambda called directly)
fn check_function_value_call(
    self: *Calls,
    context: *FunctionContext,
    node: NodeId,
    function_type: StaticPool.Index,
    arguments: []const NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const parameter_count = static_pool.get(function_type).function_type.parameters.len;
    if (parameter_count != arguments.len) {
        return resolver.report(.wrong_arity, node, arguments.len, parameter_count);
    }

    for (arguments, 0..) |argument, i| {
        const parameter_type = static_pool.get(function_type).function_type.parameters[i];
        _ = resolver.expressions.check(context, resolver.tree.arg_value(argument), parameter_type);
    }
    return static_pool.get(function_type).function_type.return_type;
}

// calls of declared functions: overload resolution, stcfun realization, length-generic realization
fn call_declared(
    self: *Calls,
    context: *FunctionContext,
    node: NodeId,
    first: DeclPool.Index,
    all_arguments: []const NodeId,
    receiver: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    // a stcfun runs at compile time: the realization for its argument values is the call's result
    if (resolver.decl_pool.get(first, .kind) == .static_function) {
        const expressions = &resolver.expressions;
        const parameter_count = resolver.types.signature(first).parameters.len;
        if (all_arguments.len != parameter_count) {
            return resolver.report(.wrong_arity, node, all_arguments.len, parameter_count);
        }
        const return_type = resolver.types.signature(first).return_type;

        var any_failed = false;
        for (all_arguments, 0..) |argument, i| {
            const parameter_type = resolver.types.signature(first).parameters[i];
            const value = resolver.tree.arg_value(argument);
            const fails = blk: {
                if (static_pool.template_of(parameter_type) != .none) {
                    const argument_type = expressions.infer(context, value, .none);
                    const passes =
                        resolver.generics.passes_template_parameter(argument_type, parameter_type);
                    if (passes) break :blk false;

                    _ = resolver.report(.type_mismatch, value, argument_type, parameter_type);
                    break :blk true;
                }

                if (static_pool.tag(parameter_type) != .meta_type) {
                    if (!static_pool.has_type_variables(parameter_type)) {
                        break :blk expressions.check(
                            context,
                            value,
                            parameter_type,
                        ) == .poison_type;
                    }

                    const argument_type = expressions.infer(context, value, parameter_type);
                    if (argument_type == .poison_type) break :blk true;
                    if (static_pool.argument_length(argument_type, parameter_type) != .none) {
                        break :blk false;
                    }

                    _ = resolver.report(.type_mismatch, value, argument_type, parameter_type);
                    break :blk true;
                }

                // a `type` parameter takes any type, any other meta type exactly itself
                const argument_type = expressions.infer(context, value, parameter_type);
                if (argument_type == .poison_type) break :blk true;

                const fits = static_pool.tag(argument_type) == .meta_type and
                    (parameter_type == .type_type or argument_type == parameter_type);
                if (fits) break :blk false;

                _ = resolver.report(.type_mismatch, value, argument_type, parameter_type);
                break :blk true;
            };
            if (fails) any_failed = true;
        }
        if (any_failed) return .poison_type;
        if (context.is_interpreted and return_type != .fun_type) return return_type;

        const values = resolver.temporary_slice(StaticPool.Index, all_arguments.len);
        for (all_arguments, 0..) |argument, i| {
            const value_node = resolver.tree.arg_value(argument);
            const evaluated = resolver.interpreter.evaluate_static(context, value_node);
            const parameter_type = resolver.types.signature(first).parameters[i];
            values[i] = resolver.static_values.retyped(evaluated, parameter_type);
            if (static_pool.contains_template(values[i])) return .poison_type;

            // a tree for `ast.Kind` has a root of that kind, known now that it is evaluated
            const tree_misfits = resolver.tree.macros and
                values[i] != .poison_type and
                !resolver.interpreter.trees.admits(.of(static_pool, values[i]), parameter_type);
            if (tree_misfits) {
                const trees = &resolver.interpreter.trees;
                const misfit: Value = .of(static_pool, values[i]);
                const found, const wanted = trees.rejection(misfit, parameter_type);
                return resolver.report(.type_mismatch, value_node, found, wanted);
            }
        }

        if (resolver.interpreter.depth == 0) resolver.interpreter.evaluation_root = node;
        const realization_key = static_pool.intern(.{ .aggregate_value = .{
            .value_type = .none,
            .elements = values,
        } });
        const realization = resolver.generics.realize(first, realization_key);
        if (static_pool.tag(return_type) != .meta_type) {
            resolver.node_static_values[node] = realization;
        }

        if (static_pool.tag(realization) != .function_value) {
            const produces_type = static_pool.tag(return_type) == .meta_type or
                return_type == .poison_type;
            if (produces_type and realization == .poison_type) return .poison_type;
            if (produces_type) return static_pool.type_of(realization);
            // an open length of the result (`-> []u32`) is this call's own
            const has_own_length = static_pool.has_type_variables(return_type) and
                realization != .poison_type;
            if (has_own_length) return static_pool.type_of(realization);
            return return_type;
        }

        const produced_function = static_pool.get(realization).function_value;
        resolver.node_declarations[node] = produced_function;
        return resolver.decl_pool.get(produced_function, .value_type);
    }

    // the self argument of a method: the receiver, or the first argument when called via the type
    const self_count = resolver.decl_pool.implicit_self_count(first);
    var argument_nodes = all_arguments;
    if (self_count == 1) {
        if (receiver == 0 and argument_nodes.len == 0) {
            return resolver.report(.wrong_arity, node, 0, 1);
        }

        const method_type =
            resolver.decl_pool.get(resolver.declarations.realized(first), .value_type);
        const self_parameter: StaticPool.Index = if (method_type != .none and
            static_pool.tag(method_type) == .function_type)
            static_pool.get(method_type).function_type.parameters[0]
        else
            .poison_type;

        if (receiver == 0) {
            // a method that does not write `self` takes a read only one as well
            const expected = if (static_pool.is_pointer(self_parameter))
                static_pool.pointer_to(static_pool.pointee(self_parameter), false)
            else
                self_parameter;
            _ = resolver.expressions.check(
                context,
                resolver.tree.arg_value(argument_nodes[0]),
                expected,
            );
            argument_nodes = argument_nodes[1..];
        } else {
            const receiver_type =
                static_pool.substitute_type_variables(resolver.node_types[receiver]);
            const self_type = static_pool.pointee(self_parameter);
            const mismatch = receiver_type != .poison_type and
                self_parameter != .poison_type and
                receiver_type != self_type and
                !static_pool.implements(receiver_type, self_type) and
                static_pool.coercion(receiver_type, self_parameter) == .incompatible;
            if (mismatch) {
                _ = resolver.report(.type_mismatch, receiver, receiver_type, self_parameter);
            }
        }
    }

    const arguments = CallArguments{
        .nodes = argument_nodes,
        .types = resolver.temporary_slice(StaticPool.Index, argument_nodes.len),
        .parameter_of = resolver.temporary_slice(u32, argument_nodes.len),
        .self_count = self_count,
    };
    const first_function = resolver.declarations.realized(first);

    // argument types once, with the first candidate's parameters as expectation
    const first_node = resolver.declarations.value_node(first_function);
    const first_parameters = resolver.tree.params_of(first_node);
    const first_binds = resolver.decl_pool.get(first_function, .value_type) != .none and
        self.bind_arguments(first_parameters, arguments.nodes, arguments.parameter_of, false);

    for (arguments.nodes, 0..) |argument, i| {
        const hint: StaticPool.Index = if (first_binds)
            resolver.types.signature(first_function).parameters[
                arguments.parameter_of[i] + arguments.self_count
            ]
        else
            .none;
        const value = resolver.tree.arg_value(argument);
        arguments.types[i] = resolver.expressions.infer(context, value, hint);
    }

    // most specific candidate: exact > coercion > unlengthed, a where clause beats none
    var choice = OverloadChoice{ .best = .none, .candidate_count = 0, .ambiguous = false };
    var best_score: i32 = -1;
    var candidate = first;
    while (candidate != .none) : (candidate = resolver.decl_pool.get(candidate, .next_overload)) {
        choice.candidate_count += 1;

        const candidate_score = self.score(candidate, arguments);
        if (candidate_score > best_score) {
            choice.best = candidate;
            best_score = candidate_score;
            choice.ambiguous = false;
            continue;
        }

        const ties = candidate_score == best_score and candidate_score >= 0;
        if (ties and
            !self.has_where(resolver.declarations.realized(candidate)) and
            !self.has_where(resolver.declarations.realized(choice.best)))
        {
            choice.ambiguous = true;
        }
    }
    // a poisoned argument fits every candidate, its error is reported already
    if (std.mem.indexOfScalar(StaticPool.Index, arguments.types, .poison_type) != null) {
        choice.ambiguous = false;
    }

    if (choice.best == .none) {
        if (choice.candidate_count > 1) {
            return resolver.report(.no_matching_overload, node, arguments.nodes.len, 0);
        }
        if (!first_binds) {
            const parameters = resolver.tree.params_of(first_node);
            return self.report_bad_arguments(node, parameters, arguments.nodes);
        }

        for (arguments.nodes, 0..) |argument, i| {
            const parameter_index = arguments.parameter_of[i] + arguments.self_count;
            const parameter_type =
                resolver.types.signature(first_function).parameters[parameter_index];
            const value = resolver.tree.arg_value(argument);
            const argument_type = arguments.types[i];

            if (!static_pool.has_type_variables(parameter_type)) {
                _ = resolver.expressions.expect_type(value, argument_type, parameter_type);
            } else if (static_pool.argument_length(argument_type, parameter_type) == .none) {
                _ = resolver.report_mismatch(value, argument_type, parameter_type);
            }
        }
        return .poison_type;
    }
    if (choice.ambiguous) _ = resolver.report(.ambiguous_overload, node, choice.best, 0);

    // a method writing `self` needs it writable: a read-only pointer cannot be written through
    const callee = resolver.declarations.realized(choice.best);
    if (self_count == 1 and resolver.decl_pool.get(callee, .flags).writes) {
        const self_node = if (receiver != 0)
            receiver
        else
            resolver.tree.arg_value(all_arguments[0]);
        const self_type = static_pool.substitute_type_variables(resolver.node_types[self_node]);
        const assignable = resolver.tree.props(self_node).assignable;

        if (receiver == 0) {
            if (static_pool.tag(self_type) == .pointer_type) {
                const self_parameter = resolver.types.signature(callee).parameters[0];
                _ = resolver.report(.type_mismatch, self_node, self_type, self_parameter);
            }
        } else if (static_pool.is_pointer(self_type)) {
            const read_only = static_pool.tag(self_type) == .pointer_type;
            resolver.mutability.record_write_access(
                self_node,
                if (read_only) .through_ptr else .ok,
            );
        } else if (assignable) {
            resolver.mutability.record_write_access(
                self_node,
                resolver.mutability.writable(self_node),
            );
        }
    }

    const parameter_nodes = resolver.tree.params_of(resolver.declarations.value_node(callee));
    _ = self.bind_arguments(parameter_nodes, arguments.nodes, arguments.parameter_of, false);
    self.check_stcwhere(
        context,
        node,
        callee,
        parameter_nodes,
        arguments.nodes,
        arguments.parameter_of,
    );

    // the argument lengths, in parameter order, pick the realization
    if (static_pool.is_length_generic(resolver.decl_pool.get(callee, .value_type))) {
        const generic_buffer = resolver.temporary_slice(StaticPool.Index, arguments.nodes.len + 1);
        var generic_count: usize = 0;
        // a trait's method realizes its `self` for the receiver's type
        if (self_count == 1) {
            const self_parameter = resolver.types.signature(callee).parameters[0];
            if (static_pool.trait_of(self_parameter) != .none) {
                const self_node = if (receiver != 0)
                    receiver
                else
                    resolver.tree.arg_value(all_arguments[0]);
                const self_type = static_pool.substitute_type_variables(
                    resolver.node_types[self_node],
                );
                generic_buffer[0] = static_pool.unwrapped(self_type);
                generic_count = 1;
            }
        }
        for (0..parameter_nodes.len) |j| {
            const parameter_index = j + arguments.self_count;
            const parameter_type = resolver.types.signature(callee).parameters[parameter_index];
            if (!static_pool.is_generic_parameter(parameter_type)) continue;

            for (0..arguments.nodes.len) |i| {
                if (arguments.parameter_of[i] != j) continue;

                // what a generic parameter takes from its argument
                const argument_type = arguments.types[i];
                generic_buffer[generic_count] = blk: {
                    if (static_pool.is_realized_per_type(parameter_type)) {
                        break :blk static_pool.unwrapped(argument_type);
                    }
                    if (static_pool.tag(parameter_type) != .meta_type) {
                        break :blk static_pool.argument_length(argument_type, parameter_type);
                    }

                    const value = resolver.tree.arg_value(arguments.nodes[i]);
                    if (resolver.static_values.try_evaluate(context, value)) |static_value| {
                        break :blk static_value;
                    }
                    if (context.is_interpreted) break :blk .none;
                    return resolver.report(.not_static, arguments.nodes[i], 0, 0);
                };
                generic_count += 1;
            }
        }
        const generic_arguments = generic_buffer[0..generic_count];

        if (std.mem.indexOfScalar(StaticPool.Index, generic_arguments, .none) != null) {
            if (context.is_interpreted) resolver.node_declarations[node] = callee;
            return .poison_type;
        }
        // none is ruled out above. a template or trait argument comes from an abstract body,
        // which is checked once
        for (generic_arguments) |generic| {
            const tag = static_pool.tag(generic);
            if (tag != .template_type and tag != .trait_type) continue;

            resolver.declarations.check_body(callee);
            return resolver.types.signature(callee).return_type;
        }

        const realization_key = static_pool.intern(.{ .aggregate_value = .{
            .value_type = .none,
            .elements = generic_arguments,
        } });
        const realization = resolver.generics.realize(callee, realization_key);
        if (static_pool.tag(realization) != .function_value) return .poison_type;

        const realized_callee = static_pool.get(realization).function_value;
        resolver.node_declarations[node] = realized_callee;
        // a `fun` taking only types made a function: the call is that function, as of a `stcfun`
        const made_function = resolver.decl_pool.get(realized_callee, .node) ==
            resolver.tree.arg(resolver.declarations.value_node(callee), 1);
        if (made_function) {
            resolver.node_static_values[node] = realization;
            return resolver.decl_pool.get(realized_callee, .value_type);
        }
        return resolver.types.signature(realized_callee).return_type;
    }

    for (arguments.nodes, 0..) |argument, i| {
        const parameter_index = arguments.parameter_of[i] + self_count;
        const parameter_type = resolver.types.signature(callee).parameters[parameter_index];
        _ = resolver.expressions.expect_type(
            resolver.tree.arg_value(argument),
            arguments.types[i],
            self.type_named_argument(argument, parameter_type),
        );
    }

    // the call names its dispatch group's head: the lowerer walks `next_overload` from there
    // the lowerer tests the where clauses of same-typed overloads in order, the where-less one last
    var group = first;
    while (group != choice.best and !self.has_same_parameters(group, choice.best)) {
        group = resolver.decl_pool.get(group, .next_overload);
    }
    resolver.node_declarations[node] = resolver.declarations.realized(group);
    return resolver.types.signature(callee).return_type;
}

// stcwhere holds at every call: a scope of its own binds the parameters to the static arguments
fn check_stcwhere(
    self: *Calls,
    context: *FunctionContext,
    node: NodeId,
    callee: DeclPool.Index,
    parameter_nodes: []const NodeId,
    arguments: []const NodeId,
    parameter_of: []const u32,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (context.is_interpreted) return;
    for (parameter_nodes) |parameter_node| {
        if (ParseTree.Param.from_node(resolver.tree, parameter_node).stc) break;
    } else return;

    const static_values = resolver.temporary_slice(StaticPool.Index, parameter_nodes.len);
    @memset(static_values, .none);
    const argument_types = resolver.temporary_slice(StaticPool.Index, parameter_nodes.len);
    @memset(argument_types, .none);

    for (arguments, 0..) |argument, i| {
        const value = resolver.tree.arg_value(argument);
        const static_value = resolver.static_values.try_evaluate(context, value) orelse .none;
        static_values[parameter_of[i]] = static_value;
        argument_types[parameter_of[i]] = resolver.node_types[value];
    }

    resolver.declarations.open_declaration_scope(true, .none, 0);
    defer resolver.scopes.close();

    for (parameter_nodes, 0..) |parameter_node, j| {
        const argument_type = argument_types[j];
        const static_value = static_values[j];
        const callee_type = resolver.decl_pool.get(callee, .value_type);
        const self_count = resolver.decl_pool.implicit_self_count(callee);
        const declared_type = static_pool.get(callee_type).function_type.parameters[j + self_count];
        const parameter_type = if (static_pool.template_of(declared_type) != .none and
            argument_type != .none)
            argument_type
        else
            declared_type;

        const parameter = resolver.declarations.declare_local(
            resolver.declarations.parameter_name(parameter_node, j),
            parameter_node,
            .static_parameter,
            parameter_type,
        );
        const value = if (static_value == .none)
            .none
        else
            resolver.static_values.retyped(static_value, parameter_type);
        resolver.decl_pool.set(parameter, .static_value, value);
    }
    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
        if (!parameter.stc) continue;

        const holds = resolver.static_values.try_evaluate(context, parameter.where) orelse {
            _ = resolver.report(.not_static, node, 0, 0);
            continue;
        };
        if (holds == .bool_false) _ = resolver.report(.stcwhere_violated, node, callee, .none);
    }
}

// overloads that differ only by where clauses dispatch at runtime and need a where-less fallback
pub fn check_dispatch_groups(self: *Calls) void {
    const resolver = self.owning_resolver();

    // overload lists in declaration order, reports then come in an order independent of hashing
    const names = resolver.decl_pool.entries.column(.name);
    for (0..names.len) |i| {
        const declaration: DeclPool.Index = @enumFromInt(i);
        const head = resolver.scopes.globals.get(names[i]) orelse continue;
        if (head != declaration) continue;

        var candidate = head;
        while (candidate != .none) {
            // the first overload in the chain with the same parameters as `candidate`
            var group_head = head;
            while (group_head != candidate and !self.has_same_parameters(group_head, candidate)) {
                group_head = resolver.decl_pool.get(group_head, .next_overload);
            }
            if (group_head == candidate) self.check_dispatch_group(candidate);
            candidate = resolver.decl_pool.get(candidate, .next_overload);
        }
    }
}

fn check_dispatch_group(self: *Calls, head: DeclPool.Index) void {
    const resolver = self.owning_resolver();

    var size: u32 = 0;
    var fallback_count: u32 = 0;
    var member = head;
    while (member != .none) : (member = resolver.decl_pool.get(member, .next_overload)) {
        if (!self.has_same_parameters(member, head)) continue;
        size += 1;

        // a where clause without `else` that is not static picks the overload at runtime
        const value_node = resolver.declarations.value_node(resolver.declarations.realized(member));
        const is_fallback = for (resolver.tree.params_of(value_node)) |parameter_node| {
            const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
            if (parameter.where != 0 and parameter.@"else" == 0 and !parameter.stc) break false;
        } else true;
        fallback_count += @intFromBool(is_fallback);
        if (is_fallback and fallback_count > 1) {
            const member_node = resolver.decl_pool.get(member, .node);
            const member_name = resolver.decl_pool.get(member, .name);
            resolver.doctor.report(.duplicate_declaration, member_node, member_name, head);
        }
    }

    if (size > 1 and fallback_count == 0) {
        _ = resolver.report(.no_matching_overload, resolver.decl_pool.get(head, .node), size, 0);
    }
}

// how well a candidate fits the argument types, -1 when it does not
fn score(self: *Calls, candidate: DeclPool.Index, arguments: CallArguments) i32 {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    resolver.declarations.ensure_signature(candidate);
    const function = resolver.declarations.realized(candidate);
    const function_type = resolver.decl_pool.get(function, .value_type);
    if (function_type == .none or static_pool.tag(function_type) != .function_type) return -1;

    const parameter_of = resolver.temporary_slice(u32, arguments.nodes.len);
    const parameter_nodes = resolver.tree.params_of(resolver.declarations.value_node(function));
    if (!self.bind_arguments(parameter_nodes, arguments.nodes, parameter_of, false)) return -1;

    var total: i32 = 0;
    for (arguments.nodes, arguments.types, 0..) |argument, argument_type, i| {
        const parameter_index = parameter_of[i] + arguments.self_count;
        const parameters = static_pool.get(function_type).function_type.parameters;
        const parameter_type = parameters[parameter_index];

        // exact 6 (5 for an integer literal taking a float), template 5, coercion 4, unlengthed 2
        const argument_score: i32 = blk: {
            if (static_pool.template_of(parameter_type) != .none) {
                if (!resolver.generics.passes_template_parameter(argument_type, parameter_type)) {
                    return -1;
                }
                break :blk 5;
            }
            if (static_pool.has_type_variables(parameter_type) and argument_type != .poison_type) {
                if (static_pool.argument_length(argument_type, parameter_type) == .none) return -1;
                break :blk 2;
            }

            const value = resolver.tree.arg_value(argument);
            const fits_exactly = argument_type == parameter_type or
                argument_type == .poison_type or
                resolver.tree.is_literal(value) and static_pool.coercion(
                    resolver.static_values.literal_type(value, parameter_type),
                    parameter_type,
                ) == .identity;
            if (fits_exactly) {
                const widens_to_float = static_pool.properties(parameter_type).is_float and
                    !static_pool.properties(argument_type).is_float;
                break :blk @as(i32, 6) - @intFromBool(widens_to_float);
            }
            if (static_pool.coercion(argument_type, parameter_type) != .incompatible) break :blk 4;
            return -1;
        };
        total += argument_score;

        const parameter_node = parameter_nodes[parameter_of[i]];
        if (ParseTree.Param.from_node(resolver.tree, parameter_node).where != 0) total += 1;
    }
    return total;
}

pub fn has_where(self: *Calls, declaration: DeclPool.Index) bool {
    const resolver = self.owning_resolver();

    for (resolver.tree.params_of(resolver.declarations.value_node(declaration))) |parameter_node| {
        if (ParseTree.Param.from_node(resolver.tree, parameter_node).where != 0) return true;
    }
    return false;
}

// one dispatch group: the same parameter types under the same names
pub fn has_same_parameters(
    self: *Calls,
    first_declaration: DeclPool.Index,
    second_declaration: DeclPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const first = resolver.declarations.realized(first_declaration);
    const second = resolver.declarations.realized(second_declaration);
    const first_type = resolver.decl_pool.get(first, .value_type);
    const second_type = resolver.decl_pool.get(second, .value_type);
    if (first_type != second_type) {
        if (first_type == .none or second_type == .none) return false;
        if (static_pool.tag(first_type) != .function_type) return false;
        if (static_pool.tag(second_type) != .function_type) return false;

        const same_types = std.mem.eql(
            StaticPool.Index,
            static_pool.get(first_type).function_type.parameters,
            static_pool.get(second_type).function_type.parameters,
        );
        if (!same_types) return false;
    }

    const first_parameters = resolver.tree.params_of(resolver.declarations.value_node(first));
    const second_parameters = resolver.tree.params_of(resolver.declarations.value_node(second));
    if (first_parameters.len != second_parameters.len) return false;

    for (first_parameters, second_parameters, 0..) |first_parameter, second_parameter, i| {
        const first_name = resolver.declarations.parameter_name(first_parameter, i);
        const second_name = resolver.declarations.parameter_name(second_parameter, i);
        if (first_name != second_name) return false;
    }
    return true;
}

pub fn bind_arguments(
    self: *Calls,
    parameters: []const NodeId,
    arguments: []const NodeId,
    parameter_of: []u32,
    partial: bool,
) bool {
    const resolver = self.owning_resolver();
    if (arguments.len > parameters.len) return false;

    for (arguments, 0..) |argument, i| {
        // a named argument binds by its name, any other by its position
        const name_node = resolver.tree.arg_name(argument);
        const parameter_index: u32 = if (name_node == 0)
            @intCast(i)
        else
            resolver.declarations.parameter_index(
                parameters,
                resolver.name_pool.name_of_node(name_node),
            ) orelse return false;
        if (std.mem.indexOfScalar(u32, parameter_of[0..i], parameter_index) != null) return false;
        parameter_of[i] = parameter_index;
    }
    if (partial) return true;

    // every parameter without a default needs an argument
    for (parameters, 0..) |parameter_node, j| {
        const bound = parameter_of[0..arguments.len];
        const is_bound = std.mem.indexOfScalar(u32, bound, @intCast(j)) != null;
        if (is_bound) continue;
        if (ParseTree.Param.from_node(resolver.tree, parameter_node).default == 0) return false;
    }
    return true;
}

pub fn type_named_argument(
    self: *Calls,
    argument: NodeId,
    argument_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const name_node = resolver.tree.arg_name(argument);
    if (name_node != 0) resolver.node_types[name_node] = argument_type;
    return argument_type;
}

// an unknown argument name is the more precise error, a wrong count the fallback
fn report_bad_arguments(
    self: *Calls,
    node: NodeId,
    parameters: []const NodeId,
    arguments: []const NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();

    for (arguments) |argument| {
        const name_node = resolver.tree.arg_name(argument);
        if (name_node == 0) continue;

        const name = resolver.name_pool.name_of_node(name_node);
        if (resolver.declarations.parameter_index(parameters, name) == null) {
            return resolver.report(.unknown_named_argument, argument, name, .none);
        }
    }
    return resolver.report(.wrong_arity, node, arguments.len, parameters.len);
}

// an overloaded function as a value is the overload of the expected type
pub fn overload_for(
    self: *Calls,
    node: NodeId,
    declaration: DeclPool.Index,
    expected: StaticPool.Index,
) DeclPool.Index {
    const resolver = self.owning_resolver();

    const expected_type = resolver.static_pool.substitute_type_variables(expected);
    if (declaration == .none or expected_type == .none) return declaration;
    if (resolver.static_pool.tag(expected_type) != .function_type) return declaration;
    if (!resolver.decl_pool.get(declaration, .kind).is_function()) return declaration;

    var candidate = declaration;
    while (candidate != .none) : (candidate = resolver.decl_pool.get(candidate, .next_overload)) {
        if (resolver.types.declaration_type(candidate) != expected_type) continue;
        resolver.node_declarations[node] = candidate;
        return candidate;
    }
    return declaration;
}

// `T.$init()` / `x.$deinit()` of a type that declares neither: a default value, nothing
pub fn builtin_member_of(
    self: *Calls,
    callee: NodeId,
    object_type: StaticPool.Index,
    call_type: StaticPool.Index,
) StaticPool.Member {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (object_type == .none or object_type == .poison_type or call_type == .none) return .none;

    const owner_type = if (static_pool.tag(object_type) == .meta_type)
        call_type
    else
        static_pool.through_pointer(object_type);
    const member_name = resolver.name_pool.name_of_node(resolver.tree.arg(callee, 1));
    return static_pool.lookup_member(owner_type, member_name);
}

pub fn field_index_of(
    self: *Calls,
    record_type: StaticPool.Index,
    argument: NodeId,
    position: usize,
) ?u32 {
    const resolver = self.owning_resolver();

    const name_node = resolver.tree.arg_name(argument);
    if (name_node == 0) return @intCast(position);

    const name = resolver.name_pool.name_of_node(name_node);
    return switch (resolver.static_pool.lookup_member(record_type, name)) {
        .field => |field| field.index,
        else => null,
    };
}
