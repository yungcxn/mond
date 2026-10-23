const std = @import("std");
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const StaticPool = @import("StaticPool.zig");
const BodyPool = @import("BodyPool.zig");
const Disorder = @import("Doctor.zig").Disorder;
const Value = @import("interpreter/Value.zig");
const Variables = @import("interpreter/Variables.zig");
const Flow = @import("interpreter/Flow.zig");
const Patterns = @import("interpreter/Patterns.zig");
const Calls = @import("interpreter/Calls.zig");
const Types = @import("interpreter/Types.zig");
const Trees = @import("interpreter/Trees.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const constructs = @import("../language/constructs.zig");
const operators = @import("../language/operators.zig");

const Interpreter = @This();

const step_budget: u32 = 1_000_000;
pub const max_depth: u32 = 256;
pub const no_cell = std.math.maxInt(u32);

// env: the closure a frame was called through, its captures resolve to the closure's cells
pub const Frame = struct { body: BodyPool.Body, base: u32, env: Value = .empty };

// what an evaluation replaces and restores when it ends
const Session = struct {
    outer_context: *Resolver.FunctionContext,
    memory_length: u32,
    adopted_length: u32,
};

budget: u32 = step_budget,
depth: u32 = 0,
// the node whose evaluation is running, an exhausted budget or depth is its failure
evaluation_root: NodeId = 0,
unwind: enum { none, ret, brk, cont } = .none,
function_context: *Resolver.FunctionContext = undefined,
frames: DynamicBuffer(Frame),
memory: DynamicBuffer(Value),
argument_values: DynamicBuffer(Value),
pool_indices: DynamicBuffer(Index),
// a block stored into a cell older than its frame stays until that cell is gone
floor: u32 = 0,
floor_cell: u32 = no_cell,
// the value of a `ret` under way, the operations it leaves get poison
jumped: Value = .unit,
// evaluation by kind of node
variables: Variables,
flow: Flow,
patterns: Patterns = .{},
calls: Calls = .{},
types: Types = .{},
trees: Trees = .{},

pub fn init(allocator: std.mem.Allocator) Interpreter {
    return .{
        .frames = .init(allocator, 64),
        .memory = .init(allocator, 1024),
        .argument_values = .init(allocator, 256),
        .pool_indices = .init(allocator, 256),
        .variables = .init(allocator),
        .flow = .init(allocator),
    };
}

pub fn deinit(self: *Interpreter) void {
    self.frames.deinit();
    self.memory.deinit();
    self.argument_values.deinit();
    self.pool_indices.deinit();
    self.variables.deinit();
    self.flow.deinit();
}

pub fn owning_resolver(self: *Interpreter) *Resolver {
    return @alignCast(@fieldParentPtr("interpreter", self));
}

pub fn export_value(self: *Interpreter, node: NodeId, value: Value) Index {
    if (self.escapes(value)) return self.report(.not_static, node, 0, 0);
    return self.interned(value);
}

pub fn evaluate_static(self: *Interpreter, context: *Resolver.FunctionContext, node: NodeId) Index {
    if (self.depth == 0) self.evaluation_root = node;
    const session = self.open(context, .{});
    defer self.close(session);

    const static_value = self.export_value(node, self.evaluate(node));
    if (static_value != .poison_type) {
        self.owning_resolver().node_static_values[node] = static_value;
    }
    return static_value;
}

pub fn matches_static(
    self: *Interpreter,
    context: *Resolver.FunctionContext,
    pattern: NodeId,
    static_value: Index,
) bool {
    if (self.depth == 0) self.evaluation_root = pattern;
    const session = self.open(context, .{});
    defer self.close(session);

    const value = Value.of(&self.owning_resolver().static_pool, static_value);
    return self.patterns.matches(pattern, value);
}

pub fn run_body(
    self: *Interpreter,
    context: *Resolver.FunctionContext,
    root: NodeId,
    body: BodyPool.Body,
) Index {
    const session = self.open(context, body);
    defer self.close(session);

    const result = self.finish_unwind(self.evaluate(root));
    return self.export_value(root, self.coerce(result, context.return_type));
}

fn open(self: *Interpreter, context: *Resolver.FunctionContext, body: BodyPool.Body) Session {
    if (self.depth == 0) self.budget = step_budget;
    self.depth += 1;

    const session: Session = .{
        .outer_context = self.function_context,
        .memory_length = self.memory.len,
        .adopted_length = self.variables.adopted.len,
    };
    self.function_context = context;
    self.enter_frame(body);
    return session;
}

fn close(self: *Interpreter, session: Session) void {
    self.variables.flush(session.adopted_length);
    self.depth -= 1;
    self.frames.len -= 1;
    self.truncate(session.memory_length);
    self.function_context = session.outer_context;
}

pub fn enter_frame(self: *Interpreter, body: BodyPool.Body) void {
    self.frames.push(.{ .body = body, .base = self.allocate_cells(body.local_count) });
}

pub fn leave_frame(self: *Interpreter, keep: bool) void {
    self.frames.len -= 1;
    if (!keep) self.truncate(self.frames.buffer[self.frames.len].base);
}

fn truncate(self: *Interpreter, new_length: u32) void {
    if (self.floor_cell < new_length) {
        self.memory.len = @max(new_length, @min(self.floor, self.memory.len));
        return;
    }
    self.memory.len = new_length;
    self.floor = 0;
    self.floor_cell = no_cell;
}

pub fn store_cell(self: *Interpreter, cell: usize, value: Value) void {
    self.memory.buffer[cell] = value;
    // a cell of an outer frame, or one kept past its frame below the floor, keeps what it holds
    const outlives_frame = cell < self.current_frame().base or cell < self.floor;
    if (!value.is_heap() or !outlives_frame) return;

    self.floor = @max(self.floor, self.memory.len);
    self.floor_cell = @min(self.floor_cell, @as(u32, @intCast(cell)));
}

pub fn current_frame(self: *Interpreter) Frame {
    return self.frames.buffer[self.frames.len - 1];
}

pub fn finish_unwind(self: *Interpreter, value: Value) Value {
    defer self.unwind = .none;
    return switch (self.unwind) {
        .none => value,
        .ret => self.jumped,
        .brk, .cont => .unit,
    };
}

pub fn charge_steps(self: *Interpreter, node: NodeId, cost: u32) bool {
    if (self.depth == 0) self.budget = step_budget;
    if (self.budget > cost) {
        self.budget -= cost;
        return true;
    }

    if (self.budget > 0) _ = self.fail(self.failure_origin(node), .static_eval_failed, 0, 0);
    self.budget = 0;
    return false;
}

pub fn failure_origin(self: *const Interpreter, node: NodeId) NodeId {
    return if (self.depth > 0) self.evaluation_root else node;
}

pub fn fail(
    self: *Interpreter,
    node: NodeId,
    code: Disorder,
    first_argument: anytype,
    second_argument: anytype,
) Value {
    const resolver = self.owning_resolver();
    const already_diagnosed = resolver.doctor.errors_since(resolver.tree, 0, node);
    if (!already_diagnosed) _ = self.report(code, node, first_argument, second_argument);
    return .poison;
}

// checking is over for evaluated nodes: report without poisoning types, `try_static` may rewind it
pub fn report(
    self: *Interpreter,
    code: Disorder,
    node: NodeId,
    first_argument: anytype,
    second_argument: anytype,
) Index {
    self.owning_resolver().doctor.report(code, node, first_argument, second_argument);
    return .poison_type;
}

pub fn has_body_frame(self: *Interpreter) bool {
    return self.current_frame().body.node_count != 0;
}

pub fn checked_type(self: *Interpreter, node: NodeId) Index {
    if (self.has_body_frame()) return self.node_info(.node_type, node);
    return self.owning_resolver().expressions.infer(self.function_context, node, .none);
}

pub fn node_info(
    self: *Interpreter,
    comptime field: @EnumLiteral(),
    node: NodeId,
) @FieldType(BodyPool.NodeInfo, @tagName(field)) {
    return self.owning_resolver().node_info(self.current_frame().body, field, node);
}

pub fn allocate_cells(self: *Interpreter, count: u32) u32 {
    const first_cell = self.memory.len;
    self.memory.push_repeated(count, .empty);
    return first_cell;
}

pub fn push_cell(self: *Interpreter, value: Value) u32 {
    self.memory.push(value);
    return self.memory.len - 1;
}

pub fn store_converted(self: *Interpreter, cell: usize, value: Value, target_type: Index) void {
    self.store_cell(cell, self.owned_copy(self.coerce(value, target_type)));
}

pub fn value_type(self: *Interpreter, value: Value) Index {
    if (!value.is_pooled()) return value.value_type;
    if (value.is(.none)) return .none;

    const static_pool = &self.owning_resolver().static_pool;
    const pool_index = value.index();
    // a case without payload is its own value
    if (static_pool.tag(pool_index) == .variant_case_type) return pool_index;
    return static_pool.type_of(pool_index);
}

pub fn dereference(self: *Interpreter, value: Value) Value {
    return if (value.is_ref()) self.memory.buffer[value.cell()] else value;
}

pub fn element_count(self: *Interpreter, value: Value) ?u32 {
    const aggregate_type = self.value_type(value);
    if (aggregate_type == .none) return null;

    // records and variant cases have fields, not elements
    const type_tag = self.owning_resolver().static_pool.tag(aggregate_type);
    if (type_tag == .record_type or type_tag == .variant_case_type) return null;
    return self.aggregate_length(value);
}

pub fn aggregate_length(self: *Interpreter, value: Value) ?u32 {
    if (value.is_heap()) return value.len();
    if (!value.is_pooled() or value.is(.none)) return null;

    const static_pool = &self.owning_resolver().static_pool;
    return switch (static_pool.get(value.index())) {
        .aggregate_value => |aggregate| @intCast(aggregate.elements.len),
        .string_value => |string| @intCast(string.len),
        else => null,
    };
}

pub fn element(self: *Interpreter, value: Value, position: u32) Value {
    if (value.is_heap()) return self.memory.buffer[value.cell() + position];

    const static_pool = &self.owning_resolver().static_pool;
    return switch (static_pool.get(value.index())) {
        .aggregate_value => |aggregate| .of(static_pool, aggregate.elements[position]),
        .string_value => |string| .int(.u8_type, string[position]),
        else => .poison,
    };
}

// a value escapes when it refers to cells of the evaluation, which end with it
pub fn escapes(self: *Interpreter, value: Value) bool {
    if (value.is_ref()) return true;
    if (!value.is_heap()) return false;
    if (self.owning_resolver().static_pool.tag(value.value_type) == .function_type) return true;

    for (0..value.len()) |i| {
        const element_value = self.memory.buffer[value.cell() + i];
        if (element_value.is(.none) or self.escapes(element_value)) return true;
    }
    return false;
}

pub fn interned(self: *Interpreter, value: Value) Index {
    if (value.is_pooled()) return value.index();
    if (value.is_ref()) return .poison_type;

    const static_pool = &self.owning_resolver().static_pool;
    if (!value.is_heap()) return Value.scalar(static_pool, value);

    const mark = self.pool_indices.len;
    defer self.pool_indices.len = mark;
    for (0..value.len()) |i| {
        const element_index = self.interned(self.memory.buffer[value.cell() + i]);
        self.pool_indices.push(element_index);
    }
    return static_pool.intern(.{ .aggregate_value = .{
        .value_type = value.value_type,
        .elements = self.pool_indices.buffer[mark..self.pool_indices.len],
    } });
}

pub fn owned_copy(self: *Interpreter, value: Value) Value {
    if (!value.is_heap()) {
        if (self.owning_resolver().tree.macros) return self.trees.keep(value);
        return value;
    }

    const first_cell = self.allocate_cells(value.len());
    for (0..value.len()) |i| {
        // the copy may grow `mem`, so the buffer is indexed after it
        const element_copy = self.owned_copy(self.memory.buffer[value.cell() + i]);
        self.memory.buffer[first_cell + i] = element_copy;
    }
    return .block(value.value_type, first_cell, value.len());
}

// a pooled aggregate in a cell becomes a heap block, so its elements can be written
pub fn thaw_cell(self: *Interpreter, cell: u32) Value {
    const value = self.memory.buffer[cell];
    if (!value.is_pooled()) return value;
    const length = self.aggregate_length(value) orelse return value;

    const first_cell = self.allocate_cells(length);
    for (0..length) |i| self.memory.buffer[first_cell + i] = self.element(value, @intCast(i));
    self.store_cell(cell, .block(self.value_type(value), first_cell, length));
    return self.memory.buffer[cell];
}

pub fn coerce(self: *Interpreter, value: Value, target_type: Index) Value {
    const static_pool = &self.owning_resolver().static_pool;
    const untyped_target = target_type == .none or target_type == .poison_type;
    if (untyped_target or value.is_pooled() or value.is_heap()) return .fit(value, target_type);
    if (value.is_ref()) {
        if (!static_pool.is_pointer(target_type)) return value;

        const cell = value.cell();
        if (static_pool.tag(static_pool.pointee(target_type)) == .array_type) {
            return .ref(target_type, cell);
        }
        if (self.element_count(self.memory.buffer[cell]) == null) return .ref(target_type, cell);
        // any other pointer is to the aggregate's elements, so it points at the first one
        return .ref(target_type, self.thaw_cell(cell).cell());
    }
    if (static_pool.single_payload(target_type) == .none) return .fit(value, target_type);

    // a scalar given for a variant with a single payload case becomes that case
    const payload_case = static_pool.first_payload_case(target_type);
    const payload_record = static_pool.get(payload_case).variant_case_type.payload;
    const payload_field = self.interned(.fit(value, static_pool.field_type(payload_record, 0)));
    const payload = static_pool.intern(.{ .aggregate_value = .{
        .value_type = payload_record,
        .elements = &.{payload_field},
    } });
    const niche = static_pool.niche_case(payload_case, payload);
    if (niche != .none) return .pooled(niche);
    return .pooled(static_pool.intern(.{ .variant_value = .{
        .case = payload_case,
        .payload = payload,
    } }));
}

pub fn zero_value(self: *Interpreter, zeroed_type: Index) Value {
    const static_pool = &self.owning_resolver().static_pool;
    if (Value.is_int(zeroed_type)) return .int(zeroed_type, 0);
    if (Value.is_float(zeroed_type)) return .float(zeroed_type, 0);
    if (zeroed_type == .bool_type) return .boolean(false);
    if (zeroed_type == .none or zeroed_type == .poison_type) return .empty;
    if (static_pool.tag(zeroed_type) == .record_type) {
        return self.calls.construct(zeroed_type, &.{});
    }
    if (static_pool.tag(zeroed_type) == .variant_type) {
        // all-zero bytes: the case tagged 0, or for `tagof self` the payload holding 0
        const variant = static_pool.get(zeroed_type).variant_type;
        var payload_case: Index = .none;
        for (variant.cases) |case| {
            const case_type = static_pool.get(case).variant_case_type;
            if (variant.tag_mode == .self and case_type.payload != .none) {
                payload_case = case;
                continue;
            }
            const tag_is_zero = static_pool.tag(case_type.tag) == .int_value and
                static_pool.get(case_type.tag).int_value.bits == 0;
            if (tag_is_zero) return self.calls.construct(case, &.{});
        }

        if (payload_case != .none) return self.calls.construct(payload_case, &.{});
        return .empty;
    }
    if (static_pool.tag(zeroed_type) != .array_type) return .empty;

    const array_type = static_pool.get(zeroed_type).array_type;
    if (static_pool.tag(array_type.length) != .int_value) return .empty;
    const length: u32 = @intCast(static_pool.get(array_type.length).int_value.bits);
    const first_cell = self.allocate_cells(length);
    for (0..length) |i| {
        const zero_element = self.zero_value(array_type.element);
        self.memory.buffer[first_cell + i] = zero_element;
    }
    return .block(zeroed_type, first_cell, length);
}

// what a failed bare `x??` returns, the rules of `Flow.missing_fallback`: numbers 0, `false`, every
// element, every field its default or fallback, the case `fallback_case` picks for `failing`
pub fn fallback_value(self: *Interpreter, fallback_type: Index, failing: Index) Value {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (fallback_type == .unit_type or fallback_type == .runit_type) return .unit;
    switch (static_pool.tag(fallback_type)) {
        .array_type => {
            const array_type = static_pool.get(fallback_type).array_type;
            const length: u32 = @intCast(static_pool.get(array_type.length).int_value.bits);
            const first_cell = self.allocate_cells(length);
            for (0..length) |i| {
                const fallback_element = self.fallback_value(array_type.element, .none);
                self.memory.buffer[first_cell + i] = fallback_element;
            }
            return .block(fallback_type, first_cell, length);
        },
        .record_type, .variant_type, .unified_variant_type, .variant_case_type => {},
        else => return self.zero_value(fallback_type),
    }

    // a record is built like a case, a member of a unified variant that is one case is itself
    const case = if (static_pool.tag(fallback_type) == .record_type)
        fallback_type
    else
        static_pool.fallback_case(fallback_type, failing);
    const is_case = static_pool.tag(case) == .variant_case_type;
    if (!is_case and case != fallback_type) return self.fallback_value(case, .none);
    const record = if (is_case) static_pool.get(case).variant_case_type.payload else case;
    if (record == .none) return .pooled(case);

    const field_nodes = resolver.types.field_nodes_of(record);
    const first_cell = self.allocate_cells(@intCast(field_nodes.len));
    for (field_nodes, 0..) |field_node, i| {
        if (ParseTree.Param.from_node(resolver.tree, field_node).default != 0) continue;
        const field_type = static_pool.field_type(record, i);
        const value = self.fallback_value(field_type, .none);
        if (value.is(.poison_type)) return value;
        self.store_converted(first_cell + i, value, field_type);
    }
    return self.calls.constructed(case, record, first_cell);
}

pub fn evaluate(self: *Interpreter, node: NodeId) Value {
    const resolver = self.owning_resolver();
    if (!self.charge_steps(node, 1)) return .poison;

    // a node the checker folded keeps its static value
    const body = self.current_frame().body;
    if (node -% body.first_node < body.node_count) {
        const row = body.first_row + node - body.first_node;
        const folded = resolver.bodies.node_rows.column(.static_value)[row];
        if (folded != .none) return .of(&resolver.static_pool, folded);
    }

    const kind = resolver.tree.kind(node);
    const first_operand = resolver.tree.arg(node, 0);
    const second_operand = resolver.tree.arg(node, 1);
    return switch (constructs.construct_of(kind)) {
        .literal => self.literal(node, node, false),
        .numeric_negation => if (resolver.tree.is_literal(node))
            self.literal(node, first_operand, true)
        else
            self.unary(node, .negate, self.evaluate(first_operand)),
        .logical_not => self.unary(node, .not, self.evaluate(first_operand)),
        .grouping, .do => self.evaluate(first_operand),
        .return_value, .return_void, .loop_jump => self.flow.jump(node, kind),
        .name => self.variables.load(node),
        .block => self.flow.block(node),
        .declaration => self.variables.declare(node),
        .compound_assignment, .increment => self.variables.update(node, kind),
        .short_circuit_logic => self.short_circuit(node, kind, first_operand, second_operand),
        .arithmetic, .comparison, .logical_xor => blk: {
            const left = self.evaluate(first_operand);
            // a left operand that jumped leaves the right one
            if (left.is(.poison_type)) break :blk left;
            const operator = operators.binary_operator_of(kind);
            break :blk self.evaluate_binary(node, operator, left, self.evaluate(second_operand));
        },
        .branch => self.flow.branch(node),
        .match => self.patterns.match(node),
        .loop => self.flow.loop(node),
        .unwrap => self.flow.unwrap(node),
        .array_literal => self.array(node),
        .index => self.index(node),
        .member_access => self.calls.member(node),
        .call => self.calls.call(node),
        .record_update => self.calls.with(node),
        .address_of => self.variables.address(node),
        .dereference => self.variables.dereference(node),
        .deinit => self.variables.deinit_place(node),
        .@"defer", .deferred_deinit => self.flow.defer_statement(node, kind),
        .cast => self.types.cast(node),
        .bit_cast => self.types.bit_cast(node),
        .type_test => self.types.type_test(node),
        .size_of => self.types.size_of(node),
        .length_or_tag => self.calls.length_or_tag(node),
        .macro => self.trees.evaluate(node),
        .lambda,
        .type_expression,
        .type_definition,
        .type_of,
        .range,
        .part,
        => self.types.static_value(node, kind),
    };
}

// a negative literal is read as one literal, so its minimum fits
inline fn literal(self: *Interpreter, node: NodeId, literal_node: NodeId, negated: bool) Value {
    const resolver = self.owning_resolver();
    const literal_value = resolver.static_values.literal_value(literal_node, negated);
    return .fit(.of(&resolver.static_pool, literal_value), self.node_info(.node_type, node));
}

// `and` and `or` skip the right operand once the left one decides the result
inline fn short_circuit(
    self: *Interpreter,
    node: NodeId,
    kind: Kind,
    left_node: NodeId,
    right_node: NodeId,
) Value {
    const operator = operators.binary_operator_of(kind);
    const left = self.evaluate(left_node);
    if (left.is(.poison_type)) return left;
    const decided = left.value_type == .bool_type and (left.bits != 0) == (operator == .logic_or);
    if (decided) return left;
    return self.evaluate_binary(node, operator, left, self.evaluate(right_node));
}

fn unary(
    self: *Interpreter,
    node: NodeId,
    operator: operators.UnaryOperator,
    operand: Value,
) Value {
    if (operand.is(.poison_type)) return operand;
    const result_type = self.node_info(.node_type, node);
    return Value.unary(operator, operand, result_type) catch |err| self.fail(
        node,
        if (err == error.Invalid) .static_eval_failed else .not_static,
        self.interned(operand),
        0,
    );
}

pub fn evaluate_binary(
    self: *Interpreter,
    node: NodeId,
    operator: operators.BinaryOperator,
    left: Value,
    right: Value,
) Value {
    if (left.is(.poison_type) or right.is(.poison_type)) return .poison;

    // pointer arithmetic: an integer plus a reference is the reference plus the integer
    if (right.is_ref() and Value.is_int(left.value_type) and operator == .add) {
        return self.evaluate_binary(node, operator, right, left);
    }
    const moves_reference = operator == .add or operator == .subtract;
    if (left.is_ref() and Value.is_int(right.value_type) and moves_reference) {
        const offset: u32 = @truncate(right.bits);
        const target_cell = if (operator == .add) left.cell() +% offset else left.cell() -% offset;
        return .ref(left.value_type, target_cell);
    }

    if (left.is_ref() != right.is_ref()) {
        const left_value = self.dereference(left);
        const right_value = self.dereference(right);
        return self.evaluate_binary(node, operator, left_value, right_value);
    }
    // references into the same memory order by their cells
    if (left.is_ref() and right.is_ref()) {
        const left_cell: Value = .int(.u64_type, left.cell());
        const right_cell: Value = .int(.u64_type, right.cell());
        return Value.binary(operator, left_cell, right_cell, .bool_type) catch
            self.fail(node, .not_static, 0, 0);
    }

    const left_operand: Value = if (left.is_heap()) .pooled(self.interned(left)) else left;
    const right_operand: Value = if (right.is_heap()) .pooled(self.interned(right)) else right;
    const result_type = self.node_info(.node_type, node);

    // a string and an array of the same bytes are pooled apart, yet equal (`"ab" == [97, 98]`)
    const static_pool = &self.owning_resolver().static_pool;
    const is_equality = operator == .equal or operator == .not_equal;
    const pooled_apart = left_operand.is_pooled() and right_operand.is_pooled() and
        left_operand.index() != right_operand.index();
    if (is_equality and pooled_apart) {
        const left_index, const right_index = .{ left_operand.index(), right_operand.index() };
        const left_is_text = static_pool.tag(left_index) == .string_value;
        const text, const other = if (left_is_text)
            .{ left_index, right_index }
        else
            .{ right_index, left_index };
        const compares_text = static_pool.tag(text) == .string_value and
            static_pool.tag(other) == .aggregate_value;
        if (compares_text) {
            const bytes = static_pool.get(text).string_value;
            const elements = static_pool.get(other).aggregate_value.elements;
            const same = bytes.len == elements.len and for (bytes, elements) |byte, element_index| {
                if (Value.of(static_pool, element_index).bits != byte) break false;
            } else true;
            return .boolean(same == (operator == .equal));
        }
    }
    return Value.binary(operator, left_operand, right_operand, result_type) catch |err| self.fail(
        node,
        // a division by zero or an oversized shift is invalid, any other failure is not static
        if (err == error.Invalid) .static_eval_failed else .not_static,
        self.interned(left_operand),
        self.interned(right_operand),
    );
}

fn array(self: *Interpreter, node: NodeId) Value {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const element_nodes = if (resolver.tree.kind(node) == .array)
        resolver.tree.manychildren(node)
    else
        &[_]NodeId{};
    const length: u32 = @intCast(element_nodes.len);
    const array_type = static_pool.substitute_type_variables(self.node_info(.node_type, node));
    var element_type = static_pool.element_type(array_type);

    const first_cell = self.allocate_cells(length);
    for (element_nodes, 0..) |element_node, i| {
        const element_value = self.evaluate(element_node);
        if (element_value.is(.poison_type)) return element_value;
        self.store_converted(first_cell + i, element_value, element_type);
    }

    // without a known element type the array takes the joined type of its elements
    const keeps_checked_type = element_type != .none and
        !static_pool.has_type_variables(array_type);
    if (element_type == .none) {
        element_type = self.types.joined_type(self.memory.buffer[first_cell..][0..length]);
    }
    const block_type = if (keeps_checked_type)
        array_type
    else
        static_pool.array_of(length, element_type);
    return .block(block_type, first_cell, length);
}

fn index(self: *Interpreter, node: NodeId) Value {
    const resolver = self.owning_resolver();
    const base = self.evaluate(resolver.tree.arg(node, 0));
    if (base.is(.poison_type)) return base;
    const aggregate = self.dereference(base);
    const position = self.evaluate(resolver.tree.arg(node, 1));
    if (position.is(.poison_type)) return position;
    if (!Value.is_int(position.value_type)) return self.fail(node, .not_static, 0, 0);

    const length = self.element_count(aggregate) orelse {
        // a reference to a scalar indexes the cells after it, as far as there are cells
        if (!base.is_ref()) return self.fail(node, .not_static, 0, 0);
        const cells_after = self.memory.len - base.cell();
        if (position.bits >= cells_after) {
            return self.fail(node, .static_eval_failed, self.interned(position), cells_after);
        }
        return self.memory.buffer[base.cell() + @as(u32, @intCast(position.bits))];
    };
    if (position.bits >= length) {
        return self.fail(node, .static_eval_failed, self.interned(position), length);
    }
    return self.element(aggregate, @intCast(position.bits));
}
