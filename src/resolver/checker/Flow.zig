const std = @import("std");
const DynamicBuffer = @import("../../containers.zig").DynamicBuffer;
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const NamePool = @import("../NamePool.zig");
const Doctor = @import("../Doctor.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// control flow: if, loops and unwraps, the types branches join to, the written locals they leave
const Flow = @This();

// brks and conts seen so far, at `brk_slot` and `cont_slot`
// a loop without a brk never ends, one without either yields one element per step
jumps: [2]u32 = .{ 0, 0 },
// per open loop the set of unwritten locals its exits merge into
exits: DynamicBuffer(u32),

const brk_slot = 0;
const cont_slot = 1;

// indices of the two sets `check_condition` returns
const when_true = 0;
const when_false = 1;

pub fn init(alloc: std.mem.Allocator) Flow {
    return .{ .exits = .init(alloc, 16) };
}

pub fn deinit(self: *Flow) void {
    self.exits.deinit();
}

pub fn owning_resolver(self: *Flow) *Resolver {
    return @alignCast(@fieldParentPtr("flow", self));
}

pub fn check_if(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const branch = ParseTree.Branch.from_node(resolver.tree, node);

    const condition_value = self.static_condition_value(context, node, branch.cond);
    const is_decided = condition_value == .bool_true or condition_value == .bool_false or
        condition_value != .none and !context.is_interpreted;
    if (is_decided) return self.check_decided_if(context, branch, condition_value, expected);

    // binders of the condition (`x ?<- v`) are visible in the then branch only
    const initialization_mark = resolver.initialization.count;
    defer resolver.initialization.release(initialization_mark);
    resolver.scopes.open();
    const unwritten = self.check_condition(context, branch.cond);
    resolver.initialization.copy(0, unwritten[when_true]);

    const expected_was_concrete = resolver.static_pool.is_concrete(expected);
    const then_type = self.check_branch(context, branch.then, expected);
    const after_then = resolver.initialization.new_set();
    if (then_type != .never_type) resolver.initialization.copy(after_then, 0);
    resolver.initialization.copy(0, unwritten[when_false]);
    resolver.scopes.close();

    if (branch.@"else" == 0) {
        resolver.initialization.merge(0, after_then);
        return self.type_without_else(node, then_type, expected);
    }

    const else_type = self.check_branch(context, branch.@"else", expected);
    if (else_type == .never_type) {
        resolver.initialization.copy(0, after_then);
    } else {
        resolver.initialization.merge(0, after_then);
    }

    const settled_then = if (expected_was_concrete)
        then_type
    else
        self.settle(branch.then, then_type, expected);
    const adapted_then = self.adapt(branch.then, settled_then, else_type);
    const adapted_else = self.adapt(branch.@"else", else_type, settled_then);
    return self.merge_branch_types(node, adapted_then, adapted_else, expected);
}

// the condition known while checking: a stc one always, any one in interpreted code if it can be
fn static_condition_value(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    condition: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const is_stc = resolver.tree.props(node).stc;
    if (context.is_interpreted or is_stc and context.is_abstract) {
        return resolver.static_values.try_evaluate(context, condition) orelse .none;
    }
    if (is_stc) return resolver.interpreter.evaluate_static(context, condition);
    return .none;
}

// only the branch the condition takes is checked
fn check_decided_if(
    self: *Flow,
    context: *FunctionContext,
    branch: ParseTree.Branch,
    condition_value: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    _ = resolver.set_node_type(branch.cond, .bool_type);
    if (condition_value == .bool_true) return self.check_branch(context, branch.then, expected);

    if (condition_value != .bool_false) {
        if (condition_value == .poison_type) return condition_value;
        const condition_type = resolver.static_pool.type_of(condition_value);
        return resolver.report(.type_mismatch, branch.cond, condition_type, .bool_type);
    }

    if (branch.@"else" == 0) return .unit_type;
    return self.check_branch(context, branch.@"else", expected);
}

// a missing else yields unit, so a then branch with a value cannot be the value of the if
fn type_without_else(
    self: *Flow,
    node: NodeId,
    then_type: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const has_value = then_type != .never_type and then_type != .runit_type and
        then_type != .poison_type and then_type != .unit_type;
    if (resolver.static_pool.is_concrete(expected) and has_value) {
        return resolver.report(.runit_mixing, node, then_type, .unit_type);
    }

    const merge_expected: StaticPool.Index = if (has_value) .none else expected;
    return self.merge_branch_types(node, then_type, .unit_type, merge_expected);
}

// the unwritten locals when a condition is true and false: `and` runs its right after a true left
pub fn check_condition(self: *Flow, context: *FunctionContext, node: NodeId) [2]u32 {
    const resolver = self.owning_resolver();
    const kind = resolver.tree.kind(node);
    if (kind == .capture) {
        const inner = resolver.tree.arg(node, 0);
        const unwritten = self.check_condition(context, inner);
        _ = resolver.set_node_type(node, resolver.node_types[inner]);
        return unwritten;
    }

    if (kind != .binary_logic_and and kind != .binary_logic_or) {
        _ = resolver.expressions.check(context, node, .bool_type);
        const unwritten = resolver.initialization.save(0);
        return .{ unwritten, unwritten };
    }

    const is_and = kind == .binary_logic_and;
    const left = self.check_condition(context, resolver.tree.arg(node, 0));
    const left_running_right = if (is_and) left[when_true] else left[when_false];
    resolver.initialization.copy(0, left_running_right);
    const right = self.check_condition(context, resolver.tree.arg(node, 1));
    _ = resolver.set_node_type(node, .bool_type);

    // the outcome the left side can decide alone is reached through the right side too
    const left_deciding = if (is_and) left[when_false] else left[when_true];
    const either = resolver.initialization.save(left_deciding);
    const right_same_outcome = if (is_and) right[when_false] else right[when_true];
    resolver.initialization.merge(either, right_same_outcome);

    if (is_and) return .{ right[when_true], either };
    return .{ either, right[when_false] };
}

// the first type of the literals among `nodes` that every one of them fits
pub fn common_literal_type(self: *Flow, nodes: []const NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    for (nodes) |candidate| {
        if (!resolver.tree.is_literal(candidate)) continue;
        const candidate_type = resolver.node_types[candidate];
        if (self.all_literals_fit(nodes, candidate_type)) return candidate_type;
    }
    return .none;
}

fn all_literals_fit(self: *Flow, nodes: []const NodeId, literal_type: StaticPool.Index) bool {
    const resolver = self.owning_resolver();
    for (nodes) |node| {
        if (!resolver.tree.is_literal(node)) continue;
        if (resolver.static_values.literal_type(node, literal_type) != literal_type) return false;
    }
    return true;
}

// a literal branch takes the type of the others (`if c: n else: 3`)
pub fn adapt(
    self: *Flow,
    node: NodeId,
    node_type: StaticPool.Index,
    other_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (!resolver.tree.is_literal(node) or other_type == .none) return node_type;
    if (resolver.static_values.literal_type(node, other_type) != other_type) return node_type;
    return resolver.set_node_type(node, other_type);
}

pub fn check_loop(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const loop = ParseTree.Loop.from_node(resolver.tree, node);
    const expected_array = resolver.static_pool.substitute_type_variables(expected);
    const element_hint = resolver.static_pool.array_element(expected_array);

    resolver.scopes.open();
    defer resolver.scopes.close();
    self.check_loop_head(context, loop, expected_array, element_hint);

    const initialization_mark = resolver.initialization.count;
    defer resolver.initialization.release(initialization_mark);
    const at_exit = resolver.initialization.save(0);
    self.exits.push(resolver.initialization.new_set());

    context.loop_depth += 1;
    const outer_jumps = self.jumps;
    const body_type = self.check_loop_body(context, node, loop.body, expected, element_hint);
    context.loop_depth -= 1;
    const broke = self.jumps[brk_slot] != outer_jumps[brk_slot];
    const stepped = !broke and self.jumps[cont_slot] == outer_jumps[cont_slot];
    self.jumps = outer_jumps;

    self.exits.len -= 1;
    const is_endless = loop.cond == 0 and loop.seq == 0;
    // an endless loop is left through its brks only
    if (is_endless) resolver.initialization.clear(at_exit);
    resolver.initialization.merge(at_exit, self.exits.buffer[self.exits.len]);
    resolver.initialization.copy(0, at_exit);

    const is_stc = resolver.tree.props(node).stc;
    if (!context.is_interpreted and !context.is_abstract and is_stc) {
        _ = resolver.static_values.value_of(context, node);
    }

    // used as a value: an array of the body values; brk ends it without adding one, cont skips one
    if (is_endless and !broke and element_hint == .none) return .never_type;
    if (expected == .none) return .unit_type;
    return self.loop_array_type(context, node, loop, stepped, body_type, element_hint);
}

fn check_loop_head(
    self: *Flow,
    context: *FunctionContext,
    loop: ParseTree.Loop,
    expected_array: StaticPool.Index,
    element_hint: StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    if (loop.cond != 0) _ = resolver.expressions.check(context, loop.cond, .bool_type);
    if (loop.repeat != 0) _ = resolver.expressions.infer(context, loop.repeat, .none);
    if (loop.cond != 0 and loop.repeat != 0) _ = resolver.set_node_type(loop.head, .unit_type);
    if (loop.seq != 0) self.check_sequence(context, loop, expected_array, element_hint);
}

// `for x in seq`: the loop variable (or the implicit `it`) takes the elements of the sequence
fn check_sequence(
    self: *Flow,
    context: *FunctionContext,
    loop: ParseTree.Loop,
    expected_array: StaticPool.Index,
    element_hint: StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    // a range yielding integers is checked against the expected array to type its bounds
    const yields_integers = element_hint != .none and
        static_pool.properties(element_hint).is_integer and
        resolver.tree.props(loop.seq).range;
    const sequence_hint: StaticPool.Index = if (yields_integers) expected_array else .none;
    const inferred = resolver.expressions.infer(context, loop.seq, sequence_hint);
    const sequence_type = static_pool.pointee(static_pool.substitute_type_variables(inferred));

    const element_type = self.sequence_element_type(loop.seq, sequence_type);
    self.declare_loop_variable(loop, element_type);
}

// arrays are stepped through by their length, anything else by its `next` method
fn sequence_element_type(
    self: *Flow,
    sequence: NodeId,
    sequence_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const is_array = static_pool.get(sequence_type) == .array_type;
    const stepper: NamePool.Index = if (is_array) .len else .next;
    return switch (static_pool.lookup_member(sequence_type, stepper)) {
        .builtin_len => static_pool.get(sequence_type).array_type.element,
        .method => |method| self.return_type_of(method),
        .trait_method => |method| self.return_type_of(static_pool.trait_method_declaration(method)),
        .none,
        .field,
        .case,
        .builtin_tag,
        .builtin_init,
        .builtin_deinit,
        => resolver.report_mismatch(sequence, sequence_type, .none),
    };
}

fn declare_loop_variable(self: *Flow, loop: ParseTree.Loop, element_type: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    const variable = loop.variable;
    const has_variable = variable != 0;

    const name = if (has_variable) resolver.name_pool.name_of_node(variable) else .it;
    const declared_at = if (has_variable) variable else loop.head;
    const kind: DeclPool.Entry.Kind = if (has_variable) .loop_variable else .autoins_it;
    const declaration = resolver.declarations.declare_local(name, declared_at, kind, element_type);
    resolver.node_declarations[loop.head] = declaration;
    if (!has_variable) return;

    resolver.node_declarations[variable] = declaration;
    _ = resolver.set_node_type(variable, element_type);
    _ = resolver.set_node_type(loop.head, .unit_type);
}

// a stc loop body is static per iteration: checked like a stcfun body, evaluated with the loop
fn check_loop_body(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    body: NodeId,
    expected: StaticPool.Index,
    element_hint: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const outer_is_interpreted = context.is_interpreted;
    context.is_interpreted = outer_is_interpreted or resolver.tree.props(node).stc;
    const body_type = resolver.expressions.infer(
        context,
        body,
        self.body_hint(body, expected, element_hint),
    );
    context.is_interpreted = outer_is_interpreted;
    return body_type;
}

// the body of a loop used as a value is checked as an element of the array it yields
fn body_hint(
    self: *Flow,
    body: NodeId,
    expected: StaticPool.Index,
    element_hint: StaticPool.Index,
) StaticPool.Index {
    if (expected == .none) return .none;
    if (element_hint != .none) return element_hint;
    return self.owning_resolver().static_pool.fresh_type_variable(body);
}

fn loop_array_type(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    loop: ParseTree.Loop,
    stepped: bool,
    body_type: StaticPool.Index,
    element_hint: StaticPool.Index,
) StaticPool.Index {
    const static_pool = &self.owning_resolver().static_pool;
    const step_count = if (stepped and loop.seq != 0) self.steps(context, loop.seq) else null;
    const length = if (step_count) |count|
        static_pool.intern(.{ .int_value = .{ .value_type = .u64_type, .bits = count } })
    else
        static_pool.fresh_type_variable(node);
    const element = loop_element_type(body_type, element_hint);
    return static_pool.intern(.{ .array_type = .{ .length = length, .element = element } });
}

fn loop_element_type(body_type: StaticPool.Index, element_hint: StaticPool.Index) StaticPool.Index {
    if (body_type != .never_type and body_type != .runit_type) return body_type;
    if (element_hint != .none) return element_hint;
    return .unit_type;
}

// the static step count of a `for` over a range with static bounds or an array of static length
fn steps(self: *Flow, context: *FunctionContext, sequence: NodeId) ?u64 {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (!resolver.tree.props(sequence).range) {
        const sequence_type = static_pool.substitute_type_variables(resolver.node_types[sequence]);
        return static_pool.static_length(static_pool.pointee(sequence_type));
    }

    const range = ParseTree.Range.from_node(resolver.tree, sequence);
    if (range.hi == 0) return null;
    const low = if (range.lo == 0)
        0
    else
        resolver.static_values.static_integer(context, range.lo) orelse return null;
    const high = resolver.static_values.static_integer(context, range.hi) orelse return null;
    const high_exclusive = high + @intFromBool(range.incl);
    return if (high_exclusive > low) @intCast(high_exclusive - low) else 0;
}

pub fn check_jump(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    kind: ParseTree.Node.Kind,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (context.loop_depth == 0) {
        const disorder: Doctor.Disorder =
            if (kind == .brk) .brk_outside_loop else .cont_outside_loop;
        return resolver.report(disorder, node, 0, 0);
    }

    const slot: usize = if (kind == .cont) cont_slot else brk_slot;
    self.jumps[slot] += 1;
    if (kind == .brk and self.exits.len > 0) {
        const innermost_exit = self.exits.buffer[self.exits.len - 1];
        resolver.initialization.merge(innermost_exit, 0);
    }
    return .never_type;
}

// binders belong to their statement: blocks scope non-declaring ones, declarations their values
pub fn check_unwrap(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const kind = resolver.tree.kind(node);
    const operand = resolver.tree.arg(node, 0);
    const operand_hint = if (kind == .labelarrow) expected else .none;
    const operand_type = resolver.static_pool.substitute_type_variables(
        resolver.expressions.infer(context, operand, operand_hint),
    );
    if (kind == .labelarrow) {
        self.bind_label(resolver.tree.arg(node, 1), operand_type);
        return operand_type;
    }

    const payload_type = resolver.static_pool.payload_of(operand_type);
    if (payload_type == .none) return resolver.report_mismatch(operand, operand_type, .none);

    switch (kind) {
        .selftag_unwrap => return payload_type,
        .selftag_unwrap_fallback => {
            const before_fallback = resolver.initialization.save(0);
            _ = resolver.expressions.check(context, resolver.tree.arg(node, 1), payload_type);
            resolver.initialization.copy(0, before_fallback);
            resolver.initialization.release(before_fallback);
            return payload_type;
        },
        .selftag_arrow => {
            self.bind_label(resolver.tree.arg(node, 1), payload_type);
            return .bool_type;
        },
        // the construct table sends only unwrap kinds here, `<-` is bound above
        else => unreachable,
    }
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
pub fn check_branch(
    self: *Flow,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const inferred = resolver.expressions.infer(context, node, expected);
    const branch_type = static_pool.substitute_type_variables(inferred);
    return self.settle(node, branch_type, static_pool.substitute_type_variables(expected));
}

pub fn settle(
    self: *Flow,
    node: NodeId,
    branch_type: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const is_runit = branch_type == .unit_type and resolver.tree.props(node).runit;
    const settled_type = if (is_runit) .runit_type else branch_type;
    if (!resolver.static_pool.is_concrete(expected)) return settled_type;

    const fits_any = settled_type == .never_type or settled_type == .runit_type or
        settled_type == .poison_type;
    if (fits_any) return settled_type;
    if (settled_type == .unit_type and expected != .unit_type) {
        return resolver.report(.runit_mixing, node, settled_type, expected);
    }
    return resolver.expressions.expect_type(node, settled_type, expected);
}

pub fn merge_branch_types(
    self: *Flow,
    node: NodeId,
    accumulated: StaticPool.Index,
    branch_type: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (resolver.static_pool.is_concrete(expected)) return expected;
    if (accumulated == .none) return branch_type;

    const join = resolver.static_pool.join(accumulated, branch_type);
    if (join.joined_type != .none) return join.joined_type;

    const mixes_unit = accumulated == .unit_type or branch_type == .unit_type;
    if (expected == .none) {
        if (mixes_unit) return .unit_type;
        return resolver.report(.type_mismatch, node, accumulated, branch_type);
    }
    const disorder: Doctor.Disorder = if (mixes_unit) .runit_mixing else .type_mismatch;
    return resolver.report(disorder, node, accumulated, branch_type);
}

// `<- name` binds the value, `<- a, b` destructures a record in field order
pub fn bind_label(self: *Flow, label: NodeId, value_type: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    if (resolver.tree.kind(label) != .partial__destructure) {
        self.bind_arrow_name(label, value_type);
        return;
    }

    const record_type = resolver.static_pool.substitute_type_variables(value_type);
    for (resolver.tree.manychildren(label), 0..) |field_label, i| {
        const field_type = self.destructured_field_type(field_label, record_type, i);
        self.bind_arrow_name(field_label, field_type);
    }
}

fn destructured_field_type(
    self: *Flow,
    field_label: NodeId,
    record_type: StaticPool.Index,
    field_index: usize,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const has_field = static_pool.tag(record_type) == .record_type and
        field_index < static_pool.get(record_type).record_type.field_types.len;
    if (has_field) return static_pool.field_type(record_type, field_index);
    return resolver.report_mismatch(field_label, record_type, .none);
}

fn bind_arrow_name(self: *Flow, label: NodeId, bound_type: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    const name = resolver.name_pool.name_of_node(label);
    resolver.declarations.report_redeclaration(name, label);
    const declaration = resolver.declarations.declare_local(name, label, .arrow_binder, bound_type);
    resolver.node_declarations[label] = declaration;
    _ = resolver.set_node_type(label, bound_type);
}

fn return_type_of(self: *Flow, declaration: DeclPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    const function_type = resolver.types.declaration_type(declaration);
    if (resolver.static_pool.tag(function_type) != .function_type) return .poison_type;
    return resolver.static_pool.get(function_type).function_type.return_type;
}
