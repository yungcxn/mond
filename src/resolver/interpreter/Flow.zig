const std = @import("std");
const DynamicBuffer = @import("../../containers.zig").DynamicBuffer;
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// control flow: blocks, branches, loops, unwraps, jumps and defers
const Flow = @This();

const Defer = struct { node: NodeId, cell: u32 };

// the defers of the open blocks
defers: DynamicBuffer(Defer),

pub fn init(allocator: std.mem.Allocator) Flow {
    return .{ .defers = .init(allocator, 16) };
}

pub fn deinit(self: *Flow) void {
    self.defers.deinit();
}

pub fn owning_interpreter(self: *Flow) *Interpreter {
    return @alignCast(@fieldParentPtr("flow", self));
}

pub fn jump(self: *Flow, node: NodeId, kind: Kind) Value {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;

    const result: Value = if (kind == .ret) interpreter.evaluate(tree.arg(node, 0)) else .unit;
    if (interpreter.unwind != .none) return result;
    interpreter.jumped = result;
    interpreter.unwind = switch (kind) {
        .brk => .brk,
        .cont => .cont,
        else => .ret,
    };
    // what a jump leaves is poison, `finish_unwind` returns the value of a `ret`
    return .poison;
}

pub fn defer_statement(self: *Flow, node: NodeId, kind: Kind) Value {
    const interpreter = self.owning_interpreter();
    const deferred = interpreter.owning_resolver().tree.arg(node, 0);

    if (kind == .@"defer") {
        self.defers.push(.{ .node = deferred, .cell = Interpreter.no_cell });
        return .unit;
    }

    // an inlined `defer deinit` takes its value now and deinitializes the kept copy at block end
    const value = interpreter.evaluate(deferred);
    const cell = interpreter.push_cell(interpreter.owned_copy(value));
    self.defers.push(.{ .node = node, .cell = cell });
    return value;
}

pub fn branch(self: *Flow, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const parts = ParseTree.Branch.from_node(interpreter.owning_resolver().tree, node);

    const condition = interpreter.evaluate(parts.cond);
    if (boolean_failure(interpreter, parts.cond, condition)) |failure| return failure;

    if (condition.bits != 0) return interpreter.evaluate(parts.then);
    if (parts.@"else" == 0) return .unit;
    return interpreter.evaluate(parts.@"else");
}

// null for a boolean, else the failure of a condition that is none
inline fn boolean_failure(interpreter: *Interpreter, at: NodeId, value: Value) ?Value {
    if (value.value_type == .bool_type) return null;
    if (value.is(.poison_type)) return value;
    return interpreter.fail(at, .type_mismatch, interpreter.interned(value), .bool_type);
}

pub fn block(self: *Flow, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();

    // a body frame already holds the block's variables
    const scoped = !interpreter.has_body_frame();
    if (scoped) resolver.scopes.open();
    defer if (scoped) resolver.scopes.close();

    const defers_mark = self.defers.len;
    var result: Value = .unit;
    const statement_count = resolver.tree.manychildren(node).len;
    // by index: evaluating a quote grows the tree, which may move its child lists
    for (0..statement_count) |statement_index| {
        const statement = resolver.tree.manychildren(node)[statement_index];
        result = interpreter.evaluate(statement);
        if (interpreter.unwind != .none or result.is(.poison_type)) break;
    }

    const unwind = interpreter.unwind;
    const jumped = interpreter.jumped;
    // latest first; each defer runs as if no jump were under way
    while (self.defers.len > defers_mark) {
        self.defers.len -= 1;
        const pending = self.defers.buffer[self.defers.len];
        interpreter.unwind = .none;

        if (pending.cell == Interpreter.no_cell) {
            _ = interpreter.evaluate(pending.node);
        } else {
            interpreter.calls.deinit_cell(pending.node, pending.cell);
        }
    }
    interpreter.unwind = unwind;
    interpreter.jumped = jumped;
    return result;
}

// what a `for` runs over: the integers of a range, the elements of a sequence or an iterator
const LoopSource = struct {
    range_start: Value = .empty,
    range_end: Value = .empty,
    range_inclusive: bool = false,
    range_current: Value = .empty,
    // an inclusive range stops at its end instead of stepping past it, which could wrap
    range_finished: bool = false,

    sequence: Value = .empty,
    sequence_length: u32 = 0,

    iterator_type: Index = .none,
    // the iterator is advanced through a mutable reference to the cell holding it
    receiver: Value = .empty,

    variable: DeclPool.Index = .none,
};

pub fn loop(self: *Flow, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;

    const framed = interpreter.has_body_frame();
    if (!framed) resolver.scopes.open();
    defer if (!framed) resolver.scopes.close();

    const parts = ParseTree.Loop.from_node(resolver.tree, node);
    // a `loop .. repeat` without a condition runs its repeat statement before the body
    const repeat_first = parts.repeat != 0 and parts.cond == 0;

    var source: LoopSource = .{};
    if (parts.seq != 0) {
        const sequence = parts.seq;
        if (resolver.tree.props(sequence).range) {
            const range = ParseTree.Range.from_node(resolver.tree, sequence);

            var start: Value = if (range.lo != 0)
                interpreter.evaluate(range.lo)
            else
                .int(.u64_type, 0);
            var end: Value = .empty;
            if (range.hi != 0) end = interpreter.evaluate(range.hi);

            const end_is_int = end.is(.none) or Value.is_int(end.value_type);
            if (!Value.is_int(start.value_type) or !end_is_int) {
                if (start.is(.poison_type) or end.is(.poison_type)) return .poison;
                return interpreter.fail(sequence, .not_static, 0, 0);
            }

            const range_type = interpreter.node_info(.node_type, sequence);
            start = .fit(start, static_pool.element_type(range_type));

            source.range_start = start;
            source.range_end = end;
            source.range_inclusive = range.incl;
        } else {
            // a sequence with elements goes by index, any other value through `has_next` and `next`
            const assignable = resolver.tree.props(sequence).assignable;

            var in_place = assignable and !resolver.tree.props(sequence).name;
            if (in_place and framed) {
                const sequence_type = static_pool.substitute_type_variables(
                    interpreter.node_info(.node_type, sequence),
                );
                in_place = static_pool.tag(static_pool.pointee(sequence_type)) != .array_type;
            }
            const place_cell: ?u32 = if (in_place)
                interpreter.variables.cell_of_place(sequence) orelse return .poison
            else
                null;
            const evaluated = if (place_cell) |cell|
                interpreter.memory.buffer[cell]
            else
                interpreter.evaluate(sequence);

            source.sequence = interpreter.dereference(evaluated);
            if (source.sequence.is(.poison_type)) return source.sequence;
            if (interpreter.element_count(source.sequence) == null) {
                const cell = place_cell orelse if (assignable)
                    interpreter.variables.cell_of_place(sequence) orelse return .poison
                else
                    interpreter.push_cell(evaluated);
                const held = interpreter.memory.buffer[cell];

                source.receiver = if (held.is_ref())
                    held
                else
                    .ref(static_pool.pointer_to(interpreter.value_type(held), true), cell);
                source.iterator_type = interpreter.value_type(interpreter.dereference(held));
                source.sequence = .empty;
            }
        }
        // `for xs` without a variable binds `it`
        source.variable = if (framed) interpreter.node_info(.declaration, parts.head) else blk: {
            const name = if (parts.variable != 0)
                resolver.name_pool.name_of_node(parts.variable)
            else
                .it;
            break :blk resolver.declarations.declare_local(name, node, .loop_variable, .none);
        };
    }

    // a loop typed as an array collects the values of its body
    const collects = !framed or blk: {
        const declared_type = interpreter.node_info(.node_type, node);
        const loop_type = static_pool.substitute_type_variables(declared_type);
        break :blk static_pool.tag(loop_type) == .array_type;
    };
    const list_mark = interpreter.argument_values.len;
    defer interpreter.argument_values.len = list_mark;

    if (!source.sequence.is(.none)) {
        source.sequence_length = interpreter.element_count(source.sequence).?;
    }
    source.range_current = source.range_start;

    var index: u32 = 0;
    while (!source.range_finished) : (index += 1) {
        // the next item of the source bound to the loop variable, a loop without one just proceeds
        if (!source.range_start.is(.none)) {
            const current = source.range_current;
            const end = source.range_end;

            if (!end.is(.none)) {
                const past_end = if (source.range_inclusive)
                    Value.less(end, current)
                else
                    !Value.less(current, end);
                if (past_end) break;
            }

            interpreter.variables.bind(source.variable, current);
            source.range_finished = source.range_inclusive and current.bits == end.bits;
            source.range_current = .int(current.value_type, current.bits +% 1);
        } else if (!source.sequence.is(.none)) {
            if (index >= source.sequence_length) break;
            interpreter.variables.bind(
                source.variable,
                interpreter.element(source.sequence, index),
            );
        } else if (source.iterator_type != .none) {
            const calls = &interpreter.calls;
            const sequence = parts.seq;

            const more =
                calls.call_method(sequence, source.iterator_type, .has_next, source.receiver);
            if (boolean_failure(interpreter, sequence, more)) |failure| return failure;
            if (more.bits == 0) break;

            const item = calls.call_method(sequence, source.iterator_type, .next, source.receiver);
            if (item.is(.poison_type)) return item;
            interpreter.variables.bind(source.variable, item);
        }

        if (repeat_first and interpreter.evaluate(parts.repeat).is(.poison_type)) return .poison;

        if (parts.cond != 0) {
            const condition = interpreter.evaluate(parts.cond);
            if (boolean_failure(interpreter, parts.cond, condition)) |failure| return failure;
            if (condition.bits == 0) break;
        }

        // a jump leaves poison, what it does is in `unwind`
        const value = interpreter.evaluate(parts.body);
        switch (interpreter.unwind) {
            .brk => {
                interpreter.unwind = .none;
                break;
            },
            .ret => return value,
            .cont => interpreter.unwind = .none,
            .none => {
                if (value.is(.poison_type)) return value;
                if (collects) interpreter.argument_values.push(value);
            },
        }

        const repeat_after = !repeat_first and parts.repeat != 0;
        if (repeat_after and interpreter.evaluate(parts.repeat).is(.poison_type)) return .poison;
    }

    if (!collects) return .unit;

    // the values the body produced since `list_mark`, as an array of the loop's element type
    const length = interpreter.argument_values.len - list_mark;

    var element_type = static_pool.element_type(interpreter.node_info(.node_type, node));
    if (element_type == .none) {
        const elements = interpreter.argument_values.buffer[list_mark..][0..length];
        element_type = interpreter.types.joined_type(elements);
    }

    const start = interpreter.allocate_cells(length);
    for (0..length) |j| {
        const element = interpreter.argument_values.buffer[list_mark + j];
        interpreter.store_converted(start + j, element, element_type);
    }
    return .block(static_pool.array_of(length, element_type), start, length);
}

pub fn unwrap(self: *Flow, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    const kind = tree.kind(node);
    const operand = tree.arg(node, 0);

    const binds_label = kind == .labelarrow or kind == .selftag_arrow;
    if (!interpreter.has_body_frame() and binds_label) {
        return interpreter.fail(node, .not_static, 0, 0);
    }

    const value = interpreter.evaluate(operand);
    if (value.is(.poison_type) or interpreter.unwind != .none) return value;

    if (kind == .labelarrow) {
        interpreter.patterns.bind_label(tree.arg(node, 1), value);
        return value;
    }

    // a self-tagged variant unwraps to its first payload case, its other cases to nothing
    const payload: ?Value = blk: {
        const static_pool = &interpreter.owning_resolver().static_pool;

        const case = interpreter.patterns.case_of(value);
        if (case == .none) break :blk interpreter.patterns.payload_of(value);

        const operand_type = interpreter.checked_type(operand);
        if (static_pool.tag(operand_type) == .variant_case_type) {
            break :blk interpreter.patterns.payload_of(value);
        }

        // a subset unwraps the first payload case it keeps
        const kept_type = static_pool.through_pointer(operand_type);
        const variant = if (static_pool.tag(kept_type) == .variant_subset_type)
            kept_type
        else
            static_pool.get(case).variant_case_type.variant;
        if (static_pool.first_payload_case(variant) == case) {
            break :blk interpreter.patterns.payload_of(value);
        }
        break :blk null;
    };
    return switch (kind) {
        .selftag_arrow => blk: {
            if (payload) |unwrapped| interpreter.patterns.bind_label(tree.arg(node, 1), unwrapped);
            break :blk .boolean(payload != null);
        },
        .selftag_unwrap_fallback => payload orelse interpreter.evaluate(tree.arg(node, 1)),
        else => payload orelse blk: {
            // in a function a failed bare unwrap returns the fallback of its result
            const resolver = interpreter.owning_resolver();
            const function = interpreter.current_frame().body.declaration;
            const in_function = interpreter.has_body_frame() and function != .none and
                resolver.decl_pool.get(function, .kind).is_function();
            if (!in_function) {
                const failed = interpreter.interned(value);
                break :blk interpreter.fail(node, .static_eval_failed, failed, 0);
            }
            const static_pool = &resolver.static_pool;
            const declared = static_pool.substitute_type_variables(
                resolver.types.signature(function).return_type,
            );
            // a stcfun without a declared result returns what its body makes
            const result = if (declared == .poison_type)
                interpreter.node_info(.node_type, resolver.declarations.produced_node(function))
            else
                declared;
            const failing = interpreter.patterns.case_of(value);
            const fallback = interpreter.fallback_value(result, failing);
            if (fallback.is(.poison_type)) break :blk fallback;
            interpreter.jumped = fallback;
            interpreter.unwind = .ret;
            break :blk .poison;
        },
    };
}
