const std = @import("std");
const DynamicBuffer = @import("../../containers.zig").DynamicBuffer;
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Declarations = @import("../checker/Declarations.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const constructs = @import("../../language/constructs.zig");
const operators = @import("../../language/operators.zig");

// variables: names mapped to cells, reads and writes of locals and statics
const Variables = @This();

const Adopted = struct { decl: DeclPool.Index, cell: u32 };

// statics written by an evaluation, held in cells until it ends
adopted: DynamicBuffer(Adopted),

pub fn init(allocator: std.mem.Allocator) Variables {
    return .{ .adopted = .init(allocator, 16) };
}

pub fn deinit(self: *Variables) void {
    self.adopted.deinit();
}

pub fn owning_interpreter(self: *Variables) *Interpreter {
    return @alignCast(@fieldParentPtr("variables", self));
}

pub fn cell_of_declaration(self: *Variables, declaration: DeclPool.Index) ?u32 {
    const interpreter = self.owning_interpreter();
    const declaration_number = @intFromEnum(declaration);
    var i = interpreter.frames.len;
    while (i > 0) {
        i -= 1;
        const frame = interpreter.frames.buffer[i];
        // a frame without a body starts a static evaluation, the frames below are out of reach
        if (frame.body.node_count == 0) break;
        if (declaration_number -% frame.body.first_local < frame.body.local_count) {
            return frame.base + declaration_number - frame.body.first_local;
        }
        if (interpreter.calls.captured_cell(frame, declaration)) |cell| return cell;
    }

    var j = self.adopted.len;
    while (j > 0) {
        j -= 1;
        const entry = self.adopted.buffer[j];
        if (entry.decl == declaration) return entry.cell;
    }
    return null;
}

// writing a static outside its own frames is a side effect a `stcfun` may not have
fn rejects_impure_write(self: *Variables, node: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    var i = interpreter.frames.len;
    while (i > 0) {
        i -= 1;
        const frame = interpreter.frames.buffer[i];
        if (frame.body.node_count == 0) return false;

        const declaration = frame.body.declaration;
        if (declaration == .none) continue;
        if (resolver.decl_pool.get(declaration, .kind) != .static_function) continue;
        _ = interpreter.report(.impure_stcfun, node, 0, 0);
        return true;
    }
    return false;
}

pub fn flush(self: *Variables, mark: u32) void {
    const interpreter = self.owning_interpreter();
    while (self.adopted.len > mark) {
        self.adopted.len -= 1;
        const entry = self.adopted.buffer[self.adopted.len];
        self.set_static_value(entry.decl, interpreter.memory.buffer[entry.cell]);
    }
}

// a static keeps its exported value, retyped to its declared type
inline fn set_static_value(self: *Variables, declaration: DeclPool.Index, value: Value) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const declaration_node = resolver.decl_pool.get(declaration, .node);
    const exported = interpreter.export_value(declaration_node, value);
    const declared_type = resolver.decl_pool.get(declaration, .value_type);
    const retyped = resolver.static_values.retyped(exported, declared_type);
    resolver.decl_pool.set(declaration, .static_value, retyped);
}

fn declaration_of(self: *Variables, node: NodeId) DeclPool.Index {
    const interpreter = self.owning_interpreter();
    if (interpreter.has_body_frame()) return interpreter.node_info(.declaration, node);
    return interpreter.owning_resolver().declarations.use_name(node);
}

fn stored_value(self: *Variables, node: NodeId, declaration: DeclPool.Index) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_value = resolver.decl_pool.get(declaration, .static_value);
    if (static_value != .none) return .of(&resolver.static_pool, static_value);

    // a failed declaration is already diagnosed
    if (resolver.decl_pool.get(declaration, .state) == .failed) return .poison;
    return interpreter.fail(node, .not_static, resolver.name_pool.name_of_node(node), 0);
}

pub fn peek(self: *Variables, declaration: DeclPool.Index) Value {
    const interpreter = self.owning_interpreter();
    if (self.cell_of_declaration(declaration)) |cell| {
        const held = interpreter.memory.buffer[cell];
        if (!held.is(.none)) return held;
    }

    const resolver = interpreter.owning_resolver();
    return .of(&resolver.static_pool, resolver.decl_pool.get(declaration, .static_value));
}

pub fn load(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const declaration = self.declaration_of(node);
    if (declaration == .none) {
        if (!interpreter.has_body_frame()) return .poison;
        const name = interpreter.owning_resolver().name_pool.name_of_node(node);
        return interpreter.fail(node, .undefined_name, name, 0);
    }
    if (interpreter.has_body_frame() and self.is_local_function(declaration)) {
        return interpreter.calls.closure(declaration);
    }

    const value = self.peek(declaration);
    if (value.is(.none)) return self.stored_value(node, declaration);
    return value;
}

// a local function is a value only together with the cells it captures
inline fn is_local_function(self: *Variables, declaration: DeclPool.Index) bool {
    const decl_pool = &self.owning_interpreter().owning_resolver().decl_pool;
    if (decl_pool.get(declaration, .kind) != .function) return false;
    return !decl_pool.get(declaration, .flags).is_global;
}

pub fn bind(self: *Variables, declaration: DeclPool.Index, value: Value) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (declaration == .none) return;
    if (self.cell_of_declaration(declaration)) |cell| return interpreter.store_cell(cell, value);

    if (resolver.decl_pool.get(declaration, .value_type) == .none) {
        resolver.decl_pool.set(declaration, .value_type, interpreter.value_type(value));
    }
    resolver.decl_pool.set(declaration, .static_value, interpreter.interned(value));
}

pub fn store(self: *Variables, node: NodeId, declaration: DeclPool.Index, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (declaration == .none) return true;
    if (self.cell_of_declaration(declaration)) |cell| {
        interpreter.store_converted(cell, value, resolver.decl_pool.get(declaration, .value_type));
        return true;
    }

    if (self.rejects_impure_write(node)) return false;
    self.set_static_value(declaration, value);
    return true;
}

fn write(self: *Variables, node: NodeId, value: Value) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (resolver.tree.macros and interpreter.trees.write(node, value)) return;
    if (resolver.tree.kind(node) == .capture) return self.write(resolver.tree.arg(node, 0), value);
    if (resolver.tree.props(node).name) {
        _ = self.store(node, self.declaration_of(node), value);
        return;
    }

    const mark = self.adopted.len;
    const cell = self.cell_of_place(node) orelse return;
    const fitted = value.fit(interpreter.memory.buffer[cell].value_type);
    interpreter.store_cell(cell, interpreter.owned_copy(fitted));
    self.flush(mark);
}

pub fn cell_of_place(self: *Variables, node: NodeId) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const kind = resolver.tree.kind(node);
    if (kind == .capture) return self.cell_of_place(resolver.tree.arg(node, 0));
    if (resolver.tree.props(node).name) return self.cell_of_name(node);
    if (kind == .dereference) return self.cell_of_pointee(node);
    if (kind == .array_index) return self.cell_of_component(node, kind);
    if (kind == .member and !self.is_member_of_type(node)) {
        return self.cell_of_component(node, kind);
    }

    // a constant of a type (`Light.Green`) is a value like any other
    const value = interpreter.evaluate(node);
    if (value.is(.poison_type)) return null;
    return interpreter.push_cell(interpreter.owned_copy(value));
}

inline fn is_member_of_type(self: *Variables, node: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const parent_type = interpreter.checked_type(resolver.tree.arg(node, 0));
    return resolver.static_pool.tag(parent_type) == .meta_type;
}

// a static outside the running frames is adopted into a cell until the evaluation ends
inline fn cell_of_name(self: *Variables, node: NodeId) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const declaration = self.declaration_of(node);
    if (declaration == .none) return null;
    if (self.cell_of_declaration(declaration)) |cell| return cell;

    const is_static_parameter = resolver.decl_pool.get(declaration, .kind) == .static_parameter;
    if (!is_static_parameter and self.rejects_impure_write(node)) return null;
    const adopted_cell = interpreter.push_cell(self.stored_value(node, declaration));
    self.adopted.push(.{ .decl = declaration, .cell = adopted_cell });
    return adopted_cell;
}

inline fn cell_of_pointee(self: *Variables, node: NodeId) ?u32 {
    const interpreter = self.owning_interpreter();
    const pointer = interpreter.evaluate(interpreter.owning_resolver().tree.arg(node, 0));
    if (pointer.is_ref()) return pointer.cell();
    if (!pointer.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
    return null;
}

// an element or field of a place, a pooled aggregate is thawed so it can be written
fn cell_of_component(self: *Variables, node: NodeId, kind: Kind) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    var aggregate_cell = self.cell_of_place(resolver.tree.arg(node, 0)) orelse return null;
    const through_reference = interpreter.memory.buffer[aggregate_cell].is_ref();
    if (through_reference) aggregate_cell = interpreter.memory.buffer[aggregate_cell].cell();
    const aggregate = interpreter.thaw_cell(aggregate_cell);
    const position = self.component_position(node, kind, aggregate) orelse return null;

    if (!aggregate.is_heap()) {
        // a reference to a scalar indexes the cells after it
        if (through_reference and kind == .array_index) {
            const cells_after = interpreter.memory.len - aggregate_cell;
            if (position < cells_after) return aggregate_cell + @as(u32, @intCast(position));
            const shown_position: u32 = @truncate(position);
            _ = interpreter.report(.static_eval_failed, node, shown_position, cells_after);
            return null;
        }
        if (!aggregate.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
        return null;
    }
    if (position >= aggregate.len()) {
        const shown_position: u32 = @truncate(position);
        _ = interpreter.report(.static_eval_failed, node, shown_position, aggregate.len());
        return null;
    }
    return aggregate.cell() + @as(u32, @intCast(position));
}

// a member of a value that is not a heap block is rejected by the caller
inline fn component_position(self: *Variables, node: NodeId, kind: Kind, aggregate: Value) ?u64 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (kind == .array_index) {
        const position = interpreter.evaluate(resolver.tree.arg(node, 1));
        if (Value.is_int(position.value_type)) return position.bits;
        // a poisoned index is reported already
        if (!position.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
        return null;
    }
    if (!aggregate.is_heap()) return 0;

    const field_name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));
    return switch (resolver.static_pool.lookup_member(aggregate.value_type, field_name)) {
        .field => |field| field.index,
        else => null,
    };
}

pub fn declare(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (!interpreter.has_body_frame()) {
        _ = resolver.declarations.check_statement(interpreter.function_context, node);
        return .unit;
    }

    const statement = Declarations.Stmt.from_node(resolver, node);
    if (statement.kind != .variable) return self.declare_type(statement);
    return self.declare_variables(statement);
}

inline fn declare_type(self: *Variables, statement: Declarations.Stmt) Value {
    const interpreter = self.owning_interpreter();
    if (!statement.kind.is_type_declaration()) return .unit;

    const declared_type = interpreter.evaluate(statement.values[0]);
    for (statement.assignees) |assignee| {
        _ = self.store(assignee, interpreter.node_info(.declaration, assignee), declared_type);
    }
    if (declared_type.is(.poison_type)) return declared_type;
    return .unit;
}

inline fn declare_variables(self: *Variables, statement: Declarations.Stmt) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const values = statement.values;
    const assignees = statement.assignees;

    // one value is given to every assignee
    const single_value: Value = if (values.len == 1) interpreter.evaluate(values[0]) else .empty;
    if (interpreter.unwind != .none or single_value.is(.poison_type)) return single_value;
    if (assignees.len == 1 and !resolver.tree.props(assignees[0]).name) {
        self.write(assignees[0], single_value);
        return .unit;
    }

    const first_declaration = if (assignees.len > 0)
        interpreter.node_info(.declaration, assignees[0])
    else
        .none;
    const mark = interpreter.argument_values.len;
    defer interpreter.argument_values.len = mark;
    if (values.len > 1) {
        for (values) |value_node| {
            const value = interpreter.evaluate(value_node);
            if (interpreter.unwind != .none or value.is(.poison_type)) return value;
            interpreter.argument_values.push(value);
        }
    }

    var evaluated_type: Index = .none;
    if (self.has_unresolved_annotation(statement, first_declaration)) {
        evaluated_type = interpreter.types.type_of_node(statement.type) orelse return .poison;
    }

    for (assignees, 0..) |assignee, i| {
        const declaration = interpreter.node_info(.declaration, assignee);
        if (declaration == .none) continue;

        const value = switch (values.len) {
            0 => interpreter.zero_value(self.zeroed_type(declaration, evaluated_type)),
            1 => single_value,
            else => interpreter.argument_values.buffer[mark + i],
        };
        if (value.is(.poison_type)) return value;

        const checks_evaluated_type = evaluated_type != .none and values.len > 0;
        if (checks_evaluated_type and !interpreter.types.admits(value, evaluated_type)) {
            const value_node = values[@min(i, values.len - 1)];
            const found_type = interpreter.value_type(value);
            return interpreter.fail(value_node, .type_mismatch, found_type, evaluated_type);
        }
        const coerced = interpreter.coerce(value, evaluated_type);
        if (!self.store(assignee, declaration, coerced)) return .poison;
    }
    return .unit;
}

// an annotation the checker left unresolved (the declared type is poisoned) is evaluated now
inline fn has_unresolved_annotation(
    self: *Variables,
    statement: Declarations.Stmt,
    first_declaration: DeclPool.Index,
) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (statement.type == 0 or first_declaration == .none) return false;
    if (interpreter.node_info(.static_value, statement.type) != .none) return false;
    return resolver.static_pool.is_poisoned(resolver.decl_pool.get(first_declaration, .value_type));
}

inline fn zeroed_type(self: *Variables, declaration: DeclPool.Index, evaluated_type: Index) Index {
    if (evaluated_type != .none) return evaluated_type;
    return self.owning_interpreter().owning_resolver().decl_pool.get(declaration, .value_type);
}

pub fn update(self: *Variables, node: NodeId, kind: Kind) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const target = resolver.tree.arg(node, 0);
    if (kind == .assign_add and resolver.tree.macros) {
        if (interpreter.trees.append(node)) |appended| return appended;
    }

    const compound = constructs.construct_of(kind) == .compound_assignment;
    const operand: Value = if (compound)
        interpreter.evaluate(resolver.tree.arg(node, 1))
    else
        .empty;
    if (operand.is(.poison_type) or interpreter.unwind != .none) return operand;

    // a name is updated through its declaration, any other place through its cell
    const mark = self.adopted.len;
    const target_cell: ?u32 = if (resolver.tree.props(target).name)
        null
    else
        self.cell_of_place(target) orelse return .poison;
    const old_value = if (target_cell) |cell|
        interpreter.memory.buffer[cell]
    else
        interpreter.evaluate(target);
    if (old_value.is(.poison_type) or interpreter.unwind != .none) return old_value;

    const operator = operators.assigned_operator_of(kind);
    const right: Value = if (compound) operand else increment_step(old_value);
    const new_value = interpreter.evaluate_binary(node, operator, old_value, right);
    if (new_value.is(.poison_type)) return new_value;

    if (target_cell) |cell| {
        interpreter.store_cell(cell, interpreter.owned_copy(new_value.fit(old_value.value_type)));
        self.flush(mark);
    } else {
        self.write(target, new_value);
    }

    if (compound) return .unit;
    if (operators.returns_old_value(kind)) return old_value;
    return new_value;
}

inline fn increment_step(old_value: Value) Value {
    const step_type = if (Value.is_int(old_value.value_type)) old_value.value_type else .u64_type;
    return .int(step_type, 1);
}

pub fn address(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (resolver.tree.macros) {
        if (interpreter.trees.address(node)) |tree_address| return tree_address;
    }

    const cell = self.cell_of_place(resolver.tree.arg(node, 0)) orelse return .poison;
    if (interpreter.has_body_frame()) return .ref(interpreter.node_info(.node_type, node), cell);
    const pointee_type = interpreter.value_type(interpreter.memory.buffer[cell]);
    return .ref(resolver.static_pool.pointer_to(pointee_type, true), cell);
}

pub fn dereference(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const pointer = interpreter.evaluate(resolver.tree.arg(node, 0));
    if (resolver.tree.macros) {
        if (interpreter.trees.node_of(pointer)) |tree_node| {
            const pointee_type = resolver.static_pool.pointee(interpreter.value_type(pointer));
            return interpreter.trees.tree_value(pointee_type, tree_node);
        }
    }

    if (pointer.is_ref()) return interpreter.memory.buffer[pointer.cell()];
    if (pointer.is(.poison_type)) return pointer;
    return interpreter.fail(node, .not_static, interpreter.interned(pointer), 0);
}

pub fn deinit_place(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const cell = self.cell_of_place(resolver.tree.arg(node, 0)) orelse return .poison;

    // a place holding a reference deinitializes what it points to
    const held = interpreter.memory.buffer[cell];
    const target_cell = if (held.is_ref()) held.cell() else cell;
    interpreter.calls.deinit_cell(node, target_cell);
    return .unit;
}
