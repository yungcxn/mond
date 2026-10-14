const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

// calls: functions and methods invoked, closures, values built by constructors and `with`
const Calls = @This();

pub fn owning_interpreter(self: *Calls) *Interpreter {
    return @alignCast(@fieldParentPtr("calls", self));
}

pub fn member(self: *Calls, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const parent = resolver.tree.arg(node, 0);
    const name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));

    // a static length is known without evaluating the parent
    if (name == .len and !interpreter.has_body_frame()) {
        const inferred = resolver.expressions.infer(interpreter.function_context, parent, .none);
        const parent_type = static_pool.pointee(static_pool.substitute_type_variables(inferred));
        if (static_pool.static_length(parent_type)) |length| return .int(.u64_type, length);
    }

    const parent_value = interpreter.dereference(interpreter.evaluate(parent));
    if (parent_value.is(.poison_type)) return parent_value;
    if (resolver.tree.macros) {
        if (interpreter.trees.node_of(parent_value) != null) {
            return interpreter.trees.member(node, parent_value);
        }
        if (parent_value.is(.ast_type)) return interpreter.trees.case(node);
    }
    if (name == .len) {
        if (interpreter.element_count(parent_value)) |count| return .int(.u64_type, count);
    }
    // a union of variants numbers its cases after the cases of the variants before them
    if (name == .tag) {
        const case = interpreter.patterns.case_of(parent_value);
        if (case == .none) return interpreter.fail(node, .not_static, 0, 0);

        const variant_type = static_pool.through_pointer(interpreter.checked_type(parent));
        const case_type = static_pool.get(case).variant_case_type;
        const tag_type = static_pool.tag_type_of(variant_type);
        const case_number = static_pool.get(case_type.tag).int_value.bits;
        const offset = if (static_pool.tag(variant_type) == .variant_union_type)
            static_pool.union_offset(variant_type, case_type.variant)
        else
            0;
        return .int(tag_type, case_number + offset);
    }

    const parent_type = interpreter.value_type(parent_value);
    // a pooled variant value holds its fields in its payload
    const fields: Value = blk: {
        if (!parent_value.is_pooled()) break :blk parent_value;
        if (static_pool.tag(parent_type) != .variant_case_type) break :blk parent_value;
        if (static_pool.tag(parent_value.index()) != .variant_value) break :blk parent_value;
        break :blk .of(static_pool, static_pool.get(parent_value.index()).variant_value.payload);
    };
    const parent_tag = static_pool.tag(parent_type);
    const has_fields = parent_value.is_heap() or
        parent_tag == .record_type or
        parent_tag == .variant_case_type;
    if (has_fields) switch (static_pool.lookup_member(parent_type, name)) {
        .field => |field| return interpreter.element(fields, field.index),
        else => {},
    };

    if (!parent_value.is_pooled() or !static_pool.properties(parent_value.index()).is_type) {
        return interpreter.fail(node, .not_static, 0, 0);
    }
    const parent_type_value = parent_value.index();
    switch (static_pool.lookup_member(parent_type_value, name)) {
        .case => |case| return .pooled(case),
        .method => |method| {
            resolver.declarations.ensure_signature(method);
            return .of(static_pool, resolver.decl_pool.get(method, .static_value));
        },
        else => return interpreter.fail(node, .unknown_member, name, parent_type_value),
    }
}

pub fn call(self: *Calls, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const callee = resolver.tree.arg(node, 0);
    const arguments = resolver.tree.manychildren(resolver.tree.arg(node, 1));
    // `$fresh` and `$error` are builtins of macro bodies
    if (resolver.tree.macros and
        resolver.tree.kind(callee) == .identifier and
        resolver.tree.text(callee, resolver.src_bytes)[0] == '$')
    {
        const name = resolver.name_pool.name_of_node(callee);
        if (name == .fresh or name == .@"error") {
            return interpreter.trees.builtin(node, name, arguments);
        }
    }

    const declaration = interpreter.node_info(.declaration, node);
    const callee_declaration = interpreter.node_info(.declaration, callee);
    // a `fun` taking only types made the function this call is (`f(u32)`), the checker kept it
    const made = interpreter.node_info(.static_value, node);
    const is_made_function = made != .none and
        resolver.static_pool.tag(made) == .function_value and
        callee_declaration != .none and
        resolver.decl_pool.get(callee_declaration, .kind) != .static_function;
    if (is_made_function) return .of(&resolver.static_pool, made);
    // a call the checker resolved to a function, unless the callee is a `stcfun` value
    const is_declared_call = declaration != .none and
        resolver.decl_pool.get(declaration, .kind).is_function() and
        (callee_declaration == .none or
            resolver.decl_pool.get(callee_declaration, .kind) != .static_function);
    if (is_declared_call) {
        const realized = resolver.declarations.realized(declaration);
        const self_count = resolver.decl_pool.implicit_self_count(realized);
        // `value.method(..)` passes the value as `self`, `Type.method(value, ..)` as an argument
        const passes_receiver = self_count != 0 and resolver.tree.kind(callee) == .member and blk: {
            const receiver_type = interpreter.node_info(.node_type, resolver.tree.arg(callee, 0));
            break :blk static_pool.tag(receiver_type) != .meta_type;
        };
        if (!passes_receiver) return self.invoke(node, declaration, arguments, .empty, .empty);

        // the receiver is passed by reference, so the method can change it in place
        // a method that never writes `self` reads a static outside the frames by its value,
        // only writing it would be impure (`INV.get()` in a `stcfun`)
        const receiver_node = resolver.tree.arg(callee, 0);
        const reads_outer_static = blk: {
            if (resolver.decl_pool.get(realized, .flags).writes) break :blk false;
            if (!interpreter.has_body_frame()) break :blk false;
            if (!resolver.tree.props(receiver_node).name) break :blk false;
            const receiver_declaration = interpreter.node_info(.declaration, receiver_node);
            if (receiver_declaration == .none) break :blk false;
            break :blk interpreter.variables.cell_of_declaration(receiver_declaration) == null;
        };
        const cell = if (reads_outer_static)
            interpreter.push_cell(interpreter.evaluate(receiver_node))
        else
            interpreter.variables.cell_of_place(receiver_node) orelse return .poison;
        const held = interpreter.memory.buffer[cell];
        const receiver: Value = if (held.is_ref())
            held
        else
            .ref(static_pool.pointer_to(interpreter.value_type(held), true), cell);
        return self.invoke(node, declaration, arguments, receiver, .empty);
    }
    if (declaration == .none and resolver.tree.kind(callee) == .member) {
        const receiver_type = interpreter.node_info(.node_type, resolver.tree.arg(callee, 0));
        const result_type = interpreter.node_info(.node_type, node);
        switch (resolver.calls.builtin_member_of(callee, receiver_type, result_type)) {
            .builtin_init => return interpreter.zero_value(result_type),
            .builtin_deinit => return .unit,
            else => {},
        }
    }

    const callee_value = interpreter.evaluate(callee);
    // a closure is a heap block whose first cell holds the function
    if (callee_value.is_heap() and static_pool.tag(callee_value.value_type) == .function_type) {
        const function_index = interpreter.memory.buffer[callee_value.cell()].index();
        const function = static_pool.get(function_index).function_value;
        return self.invoke(node, function, arguments, .empty, callee_value);
    }
    if (callee_value.is(.poison_type)) return callee_value;
    if (!callee_value.is_pooled()) return interpreter.fail(node, .not_static, 0, 0);

    const callee_index = callee_value.index();
    // a `stcfun` met while interpreting its own declaration has no value yet
    const is_recursive_static_call = !interpreter.has_body_frame() and
        interpreter.function_context.is_interpreted and
        static_pool.tag(callee_index) == .static_function and
        static_pool.get(callee_index).static_function.declaration ==
            interpreter.function_context.declaration;
    if (is_recursive_static_call) return .poison;
    switch (static_pool.tag(callee_index)) {
        .record_type, .variant_case_type => return self.construct(callee_index, arguments),
        .ast_type => return interpreter.trees.call(node, callee_index, arguments),
        .function_value => {
            const function = static_pool.get(callee_index).function_value;
            return self.invoke(node, function, arguments, .empty, .empty);
        },
        .static_function => return self.call_static_function(node, callee_index, arguments),
        .int_type, .float_type, .simple_type, .meta_type, .array_type => {},
        .pointer_type, .mutable_pointer_type, .function_type, .variant_type => {},
        .variant_union_type, .trait_type, .template_type, .type_variable => {},
        .int_value, .float_value, .simple_value, .string_value => {},
        .aggregate_value, .variant_value, .tree_value => {},
    }
    return interpreter.fail(node, .not_static, 0, 0);
}

// a `stcfun` is realized for the interned values of its arguments
fn call_static_function(
    self: *Calls,
    node: NodeId,
    callee_index: Index,
    arguments: []const NodeId,
) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const declaration = static_pool.get(callee_index).static_function.declaration;
    const function_type = resolver.decl_pool.get(declaration, .value_type);
    const parameter_count = static_pool.get(function_type).function_type.parameters.len;
    if (arguments.len != parameter_count) {
        return interpreter.fail(node, .wrong_arity, arguments.len, parameter_count);
    }

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    for (arguments, 0..) |argument, i| {
        // read per argument: evaluating interns, which may move the pool's parameter lists
        const parameter_type = static_pool.get(function_type).function_type.parameters[i];
        const value_node = resolver.tree.arg_value(argument);
        const value = interpreter.evaluate(value_node);
        if (value.is(.poison_type)) return value;
        if (interpreter.escapes(value)) return interpreter.fail(value_node, .not_static, 0, 0);

        const argument_index = interpreter.interned(value);
        const admitted = blk: {
            if (static_pool.tag(parameter_type) == .meta_type) {
                if (parameter_type == .type_type and
                    static_pool.properties(argument_index).is_type) break :blk true;
                break :blk static_pool.type_of(argument_index) == parameter_type;
            }

            const parameter_properties = static_pool.properties(parameter_type);
            if (parameter_properties.is_integer or parameter_properties.is_float) {
                break :blk static_pool.fits(argument_index, parameter_type);
            }
            const needs_exact_type = parameter_type == .bool_type or
                static_pool.tag(parameter_type) == .record_type;
            if (needs_exact_type and static_pool.type_of(argument_index) != parameter_type) {
                break :blk false;
            }
            if (!resolver.tree.macros) break :blk true;
            break :blk interpreter.trees.admits(.of(static_pool, argument_index), parameter_type);
        };
        if (!admitted) {
            const found, const wanted = if (resolver.tree.macros)
                interpreter.trees.rejection(.of(static_pool, argument_index), parameter_type)
            else
                .{ static_pool.type_of(argument_index), parameter_type };
            return interpreter.fail(value_node, .type_mismatch, found, wanted);
        }
        const retyped = resolver.static_values.retyped(argument_index, parameter_type);
        interpreter.pool_indices.push(retyped);
    }
    // the ids pushed since `mark` as one pooled tuple
    const tuple = static_pool.intern(.{ .aggregate_value = .{
        .value_type = .none,
        .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
    } });
    return .of(static_pool, resolver.generics.realize(declaration, tuple));
}

pub fn call_method(
    self: *Calls,
    node: NodeId,
    receiver_type: Index,
    name: NamePool.Index,
    self_value: Value,
) Value {
    const interpreter = self.owning_interpreter();
    return switch (interpreter.owning_resolver().static_pool.lookup_member(receiver_type, name)) {
        .method => |method| self.invoke(node, method, &.{}, self_value, .empty),
        else => interpreter.fail(node, .not_static, 0, 0),
    };
}

pub fn deinit_cell(self: *Calls, node: NodeId, cell: u32) void {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const held_type = interpreter.value_type(interpreter.memory.buffer[cell]);
    switch (static_pool.lookup_member(held_type, .deinit)) {
        .method => |method| {
            const receiver: Value = .ref(static_pool.pointer_to(held_type, true), cell);
            _ = self.invoke(node, method, &.{}, receiver, .empty);
        },
        else => {},
    }
}

fn invoke(
    self: *Calls,
    node: NodeId,
    declaration: DeclPool.Index,
    all_arguments: []const NodeId,
    given_self: Value,
    environment: Value,
) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (interpreter.frames.len > Interpreter.max_depth) {
        return interpreter.fail(interpreter.failure_origin(node), .static_eval_failed, 0, 0);
    }

    const mark = interpreter.argument_values.len;
    defer interpreter.argument_values.len = mark;
    for (all_arguments) |argument| {
        const value = interpreter.evaluate(resolver.tree.arg_value(argument));
        if (value.is(.poison_type) or interpreter.unwind != .none) return value;
        interpreter.argument_values.push(value);
    }

    var target = resolver.declarations.realized(declaration);
    var self_value = given_self;
    var arguments = all_arguments;
    // where the values of `arguments` start in `list`
    var values_start = mark;
    // without a receiver the first argument is `self`
    if (self_value.is(.none) and resolver.decl_pool.implicit_self_count(target) == 1) {
        if (arguments.len == 0) return interpreter.fail(node, .wrong_arity, 0, 1);
        self_value = interpreter.argument_values.buffer[mark];
        arguments = arguments[1..];
        values_start += 1;
    }

    // a trait member called on a reference runs the method of the referenced value's type
    if (resolver.decl_pool.get(target, .kind) == .trait_member and self_value.is_ref()) {
        const receiver_type = interpreter.value_type(interpreter.memory.buffer[self_value.cell()]);
        const name = resolver.decl_pool.get(target, .name);
        target = switch (static_pool.lookup_member(receiver_type, name)) {
            .method => |method| method,
            else => target,
        };
    }
    resolver.declarations.ensure_signature(target);
    if (static_pool.is_length_generic(resolver.decl_pool.get(target, .value_type))) {
        target = self.realize(node, target, arguments, values_start) orelse return .poison;
    }

    // overloads with the same parameters are tried in order, the first whose `where` holds runs
    var overload = target;
    while (overload != .none) : (overload = resolver.decl_pool.get(overload, .next_overload)) {
        if (overload != target and !resolver.calls.has_same_parameters(overload, target)) continue;
        const realized = resolver.declarations.realized(overload);
        const attempted = self.attempt(
            node,
            realized,
            arguments,
            values_start,
            self_value,
            environment,
        );
        if (attempted) |result| return result;
    }
    return interpreter.fail(node, .no_matching_overload, arguments.len, 0);
}

// a function generic over lengths is realized for the types, values and lengths of its arguments
fn realize(
    self: *Calls,
    node: NodeId,
    declaration: DeclPool.Index,
    arguments: []const NodeId,
    values_start: u32,
) ?DeclPool.Index {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const parameter_nodes = resolver.tree.params_of(resolver.declarations.value_node(declaration));
    const parameter_of_argument = resolver.temporary_slice(u32, arguments.len);
    if (!resolver.calls.bind_arguments(parameter_nodes, arguments, parameter_of_argument, false)) {
        return null;
    }

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    for (0..parameter_nodes.len) |j| {
        const function_type = resolver.decl_pool.get(declaration, .value_type);
        const parameters = static_pool.get(function_type).function_type.parameters;
        const self_count = resolver.decl_pool.implicit_self_count(declaration);
        const parameter_type = parameters[j + self_count];
        if (!static_pool.is_generic_parameter(parameter_type)) continue;

        for (0..arguments.len) |i| {
            if (parameter_of_argument[i] != j) continue;
            const argument_value = interpreter.argument_values.buffer[values_start + i];
            // a template takes the argument's type, a meta type the argument, a length its count
            const generic: Index = blk: {
                if (static_pool.template_of(parameter_type) != .none) {
                    break :blk interpreter.value_type(interpreter.dereference(argument_value));
                }
                if (static_pool.tag(parameter_type) == .meta_type) {
                    break :blk interpreter.interned(argument_value);
                }

                const dereferenced = interpreter.dereference(argument_value);
                const length = interpreter.element_count(dereferenced) orelse return null;
                break :blk static_pool.intern(.{
                    .int_value = .{ .value_type = .u64_type, .bits = length },
                });
            };
            interpreter.pool_indices.push(generic);
        }
    }

    // the ids pushed since `mark` as one pooled tuple
    const tuple = static_pool.intern(.{ .aggregate_value = .{
        .value_type = .none,
        .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
    } });
    const realized = resolver.generics.realize(declaration, tuple);
    if (static_pool.tag(realized) != .function_value) {
        _ = interpreter.fail(node, .not_static, 0, 0);
        return null;
    }
    return static_pool.get(realized).function_value;
}

// one overload run on the argument values, null when a `where` without `else` rejects them
fn attempt(
    self: *Calls,
    node: NodeId,
    declaration: DeclPool.Index,
    arguments: []const NodeId,
    values_start: u32,
    self_value: Value,
    environment: Value,
) ?Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    resolver.declarations.ensure_signature(declaration);
    resolver.declarations.check_body(declaration);
    const body = resolver.bodies.body_of(declaration) orelse {
        return interpreter.fail(node, .not_static, 0, 0);
    };
    const function_node = resolver.declarations.value_node(declaration);
    if (resolver.decl_pool.get(declaration, .state) == .failed) return Value.poison;

    const parameter_nodes = resolver.tree.params_of(function_node);
    const parameter_of_argument = resolver.temporary_slice(u32, arguments.len);
    if (!resolver.calls.bind_arguments(parameter_nodes, arguments, parameter_of_argument, false)) {
        return interpreter.fail(node, .wrong_arity, arguments.len, parameter_nodes.len);
    }
    // calls inside a `stcfun` are not checked, so a violated `stcwhere` is diagnosed here
    const caller = interpreter.frames.buffer[interpreter.frames.len - 1].body.declaration;
    const caller_unchecked = caller != .none and
        resolver.decl_pool.get(caller, .kind) == .static_function;

    interpreter.enter_frame(body);
    interpreter.frames.buffer[interpreter.frames.len - 1].env = environment;
    var keep = false;
    defer interpreter.leave_frame(keep);

    if (resolver.decl_pool.implicit_self_count(declaration) == 1) {
        interpreter.variables.bind(@enumFromInt(body.first_local), self_value);
    }
    const signature = resolver.types.signature(declaration);
    // the arguments stored into their parameters, the others take their default
    const self_count = resolver.decl_pool.implicit_self_count(declaration);
    for (0..arguments.len) |i| {
        const parameter_position = parameter_of_argument[i];
        const parameter_node = parameter_nodes[parameter_position];
        // read per argument: storing may intern, which may move the pool's parameter lists
        const parameters = resolver.types.signature(declaration).parameters;
        const parameter_type = parameters[parameter_position + self_count];
        const argument_value = interpreter.argument_values.buffer[values_start + i];
        if (resolver.tree.macros and !interpreter.trees.admits(argument_value, parameter_type)) {
            const value_node = resolver.tree.arg_value(arguments[i]);
            const found, const wanted = interpreter.trees.rejection(argument_value, parameter_type);
            return interpreter.fail(value_node, .type_mismatch, found, wanted);
        }
        const parameter_declaration = interpreter.node_info(.declaration, parameter_node);
        _ = interpreter.variables.store(parameter_node, parameter_declaration, argument_value);
    }

    for (parameter_nodes, 0..) |parameter_node, j| {
        const is_bound = std.mem.indexOfScalar(u32, parameter_of_argument, @intCast(j)) != null;
        if (is_bound) continue;
        const parameter_declaration = interpreter.node_info(.declaration, parameter_node);
        const default_node = ParseTree.Param.from_node(resolver.tree, parameter_node).default;
        const default_value = interpreter.evaluate(default_node);
        _ = interpreter.variables.store(parameter_node, parameter_declaration, default_value);
    }

    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(resolver.tree, parameter_node);
        if (parameter.where == 0) continue;
        const condition = interpreter.evaluate(parameter.where);
        if (condition.value_type != .bool_type) return Value.poison;
        if (condition.bits != 0) continue;

        if (parameter.stc) {
            if (caller_unchecked) {
                return interpreter.fail(node, .stcwhere_violated, declaration, .none);
            }
            return Value.poison;
        }
        if (parameter.@"else" == 0) return null;
        const replacement = interpreter.evaluate(parameter.@"else");
        if (interpreter.unwind == .ret) return interpreter.finish_unwind(replacement);
        // an assignment in `else` writes the parameter itself
        if (resolver.tree.kind(parameter.@"else") != .assign) {
            const parameter_declaration = interpreter.node_info(.declaration, parameter_node);
            _ = interpreter.variables.store(parameter_node, parameter_declaration, replacement);
        }
    }

    const function_body = resolver.tree.arg(function_node, 1);
    const result = interpreter.finish_unwind(interpreter.evaluate(function_body));
    const coerced = interpreter.coerce(result, signature.return_type);
    // a boxed result may live in the frame's cells, so they stay
    keep = coerced.is_boxed();
    return coerced;
}

pub fn construct(self: *Calls, target: Index, arguments: []const NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const is_case = static_pool.tag(target) == .variant_case_type;
    const record = if (is_case) static_pool.get(target).variant_case_type.payload else target;
    // a case without payload is its own value
    if (record == .none) return .pooled(target);

    const field_count: u32 = @intCast(resolver.types.field_nodes_of(record).len);
    const first_cell = interpreter.allocate_cells(field_count);
    if (self.fill_arguments(record, first_cell, arguments)) |failure| return failure;
    if (!self.complete(record, first_cell)) return .poison;

    const payload: Value = .block(record, first_cell, field_count);
    if (!is_case) return payload;
    // a payload that cannot be interned keeps the case value a heap block
    if (interpreter.escapes(payload)) return .block(target, first_cell, field_count);
    const payload_index = interpreter.interned(payload);
    return .pooled(static_pool.intern(.{ .variant_value = .{
        .case = target,
        .payload = payload_index,
    } }));
}

pub fn with(self: *Calls, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const original = interpreter.dereference(interpreter.evaluate(resolver.tree.arg(node, 0)));
    if (original.is(.poison_type)) return original;
    if (resolver.tree.macros and interpreter.trees.node_of(original) != null) {
        return interpreter.trees.with(node, original);
    }

    const record = interpreter.value_type(original);
    const field_count = interpreter.aggregate_length(original) orelse {
        return interpreter.fail(node, .not_static, 0, 0);
    };
    if (resolver.static_pool.tag(record) != .record_type) {
        return interpreter.fail(node, .not_static, 0, 0);
    }

    const first_cell = interpreter.allocate_cells(field_count);
    for (0..field_count) |i| {
        const field_copy = interpreter.owned_copy(interpreter.element(original, @intCast(i)));
        interpreter.memory.buffer[first_cell + i] = field_copy;
    }
    const arguments = resolver.tree.manychildren(resolver.tree.arg(node, 1));
    if (self.fill_arguments(record, first_cell, arguments)) |failure| return failure;
    if (!self.complete(record, first_cell)) return .poison;
    return .block(record, first_cell, field_count);
}

// constructor or `with` arguments written into the fields at `first_cell`, returns a failure
fn fill_arguments(self: *Calls, record: Index, first_cell: u32, arguments: []const NodeId) ?Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    for (arguments, 0..) |argument, i| {
        const field_index = resolver.calls.field_index_of(record, argument, i) orelse {
            const argument_name = resolver.name_pool.name_of_node(resolver.tree.arg_name(argument));
            return interpreter.fail(argument, .unknown_named_argument, argument_name, record);
        };
        const value = interpreter.evaluate(resolver.tree.arg_value(argument));
        if (value.is(.poison_type)) return value;
        const field_type = resolver.static_pool.field_type(record, field_index);
        interpreter.store_converted(first_cell + field_index, value, field_type);
    }
    return null;
}

// defaults and `where .. else` of fields run in the frame of the record, whose locals are fields
fn complete(self: *Calls, record: Index, first_cell: u32) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const field_nodes = resolver.types.field_nodes_of(record);
    // the record's frame is needed when a default or `else` of a field has to run
    const needs_record_frame = blk: {
        for (field_nodes, 0..) |field_node, i| {
            const field = ParseTree.Param.from_node(resolver.tree, field_node);
            if (field.@"else" != 0) break :blk true;
            if (field.default != 0 and interpreter.memory.buffer[first_cell + i].is(.none)) {
                break :blk true;
            }
        }
        break :blk false;
    };
    if (!needs_record_frame) {
        for (0..field_nodes.len) |i| {
            if (!interpreter.memory.buffer[first_cell + i].is(.none)) continue;
            const zero = interpreter.zero_value(resolver.static_pool.field_type(record, i));
            const field_type = resolver.static_pool.field_type(record, i);
            interpreter.store_converted(first_cell + i, zero, field_type);
        }
        return true;
    }

    const record_declaration = resolver.static_pool.get(record).record_type.declaration;
    const body = resolver.bodies.body_of(record_declaration) orelse {
        _ = interpreter.fail(resolver.decl_pool.get(record_declaration, .node), .not_static, 0, 0);
        return false;
    };
    interpreter.enter_frame(body);
    defer interpreter.leave_frame(false);

    const frame_base = interpreter.current_frame().base;
    for (0..field_nodes.len) |i| {
        interpreter.memory.buffer[frame_base + i] = interpreter.memory.buffer[first_cell + i];
    }
    for (field_nodes, 0..) |field_node, i| {
        if (!interpreter.memory.buffer[frame_base + i].is(.none)) continue;
        const default_node = ParseTree.Param.from_node(resolver.tree, field_node).default;
        const value = if (default_node != 0)
            interpreter.evaluate(default_node)
        else
            interpreter.zero_value(resolver.static_pool.field_type(record, i));
        if (value.is(.poison_type)) return false;
        const field_type = resolver.static_pool.field_type(record, i);
        interpreter.store_converted(frame_base + i, value, field_type);
    }
    for (field_nodes, 0..) |field_node, i| {
        const field = ParseTree.Param.from_node(resolver.tree, field_node);
        if (field.where == 0 or field.@"else" == 0) continue;
        const condition = interpreter.evaluate(field.where);
        if (condition.value_type != .bool_type) return false;
        if (condition.bits != 0) continue;

        const replacement = interpreter.evaluate(field.@"else");
        if (replacement.is(.poison_type)) return false;
        // an assignment in `else` writes the field itself
        if (resolver.tree.kind(field.@"else") != .assign) {
            const field_type = resolver.static_pool.field_type(record, i);
            interpreter.store_converted(frame_base + i, replacement, field_type);
        }
    }
    for (0..field_nodes.len) |i| {
        const field_type = resolver.static_pool.field_type(record, i);
        const field_value = interpreter.memory.buffer[frame_base + i];
        interpreter.store_converted(first_cell + i, field_value, field_type);
    }
    return true;
}

// with captures a function value is a block: the function, then its environment, as in the lowerer
pub fn closure(self: *Calls, declaration: DeclPool.Index) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const function_index = resolver.decl_pool.get(declaration, .static_value);
    const function: Value = .of(&resolver.static_pool, function_index);
    const captures = resolver.bodies.captures_of(&resolver.decl_pool, declaration);
    if (captures.len == 0) return function;

    const first_cell = interpreter.allocate_cells(@intCast(captures.len + 1));
    interpreter.memory.buffer[first_cell] = function;
    for (captures, 1..) |capture, i| {
        const captured: Value = blk: {
            const cell = interpreter.variables.cell_of_declaration(capture);
            if (cell != null and resolver.declarations.is_captured_by_reference(capture)) {
                const capture_type = resolver.decl_pool.get(capture, .value_type);
                break :blk .ref(resolver.static_pool.pointer_to(capture_type, true), cell.?);
            }
            break :blk interpreter.owned_copy(interpreter.variables.peek(capture));
        };
        interpreter.memory.buffer[first_cell + i] = captured;
    }
    const function_type = resolver.decl_pool.get(declaration, .value_type);
    return .block(function_type, first_cell, @intCast(captures.len + 1));
}

// the cell of a capture of the closure a frame runs in
pub fn captured_cell(self: *Calls, frame: Interpreter.Frame, declaration: DeclPool.Index) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (!frame.env.is_heap() or frame.body.declaration == .none) return null;

    const captures = resolver.bodies.captures_of(&resolver.decl_pool, frame.body.declaration);
    const capture_position = std.mem.indexOfScalar(DeclPool.Index, captures, declaration) orelse {
        return null;
    };
    // the environment follows the function in the closure's block
    const cell = frame.env.cell() + 1 + @as(u32, @intCast(capture_position));
    const held = interpreter.memory.buffer[cell];
    if (held.is_ref() and resolver.declarations.is_captured_by_reference(declaration)) {
        return held.cell();
    }
    return cell;
}
