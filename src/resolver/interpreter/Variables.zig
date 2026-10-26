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
// the labels (`<-`, `?<-`) of the running frames and the cells of the places they name; a view
// is a cell of its own holding the payload record of a case, whose fields it shares
alias_declarations: DynamicBuffer(DeclPool.Index),
alias_cells: DynamicBuffer(u32),
alias_views: DynamicBuffer(bool),

pub fn init(allocator: std.mem.Allocator) Variables {
    return .{
        .adopted = .init(allocator, 16),
        .alias_declarations = .init(allocator, 16),
        .alias_cells = .init(allocator, 16),
        .alias_views = .init(allocator, 16),
    };
}

pub fn deinit(self: *Variables) void {
    self.adopted.deinit();
    self.alias_declarations.deinit();
    self.alias_cells.deinit();
    self.alias_views.deinit();
}

// `declaration` names the place in `cell`, again when bound again in the same frame
pub fn alias(self: *Variables, declaration: DeclPool.Index, cell: u32, view: bool) void {
    const first = self.owning_interpreter().current_frame().aliases;
    const own = self.alias_declarations.items()[first..];
    if (std.mem.lastIndexOfScalar(DeclPool.Index, own, declaration)) |i| {
        self.alias_cells.buffer[first + i] = cell;
        self.alias_views.buffer[first + i] = view;
        return;
    }
    self.alias_declarations.push(declaration);
    self.alias_cells.push(cell);
    self.alias_views.push(view);
}

pub fn forget_aliases(self: *Variables, mark: u32) void {
    self.alias_declarations.len = mark;
    self.alias_cells.len = mark;
    self.alias_views.len = mark;
}

fn alias_of(self: *Variables, declaration: DeclPool.Index) ?usize {
    if (self.alias_declarations.len == 0) return null;
    return std.mem.lastIndexOfScalar(DeclPool.Index, self.alias_declarations.items(), declaration);
}

// the cell of a place, a new one holding the value of anything else
pub fn cell_of_operand(self: *Variables, node: NodeId) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    // a static outside the running frames is a value here
    const in_frame = !resolver.tree.props(node).name or
        self.cell_of_declaration(self.declaration_of(node)) != null;
    if (resolver.tree.names_place(node) and in_frame) return self.cell_of_place(node);
    const value = interpreter.evaluate(node);
    if (value.is(.poison_type) or interpreter.unwind != .none) return null;
    return interpreter.push_cell(interpreter.owned_copy(value));
}

pub fn owning_interpreter(self: *Variables) *Interpreter {
    return @alignCast(@fieldParentPtr("variables", self));
}

pub fn cell_of_declaration(self: *Variables, declaration: DeclPool.Index) ?u32 {
    if (self.alias_of(declaration)) |i| return self.alias_cells.buffer[i];
    const interpreter = self.owning_interpreter();
    const declaration_number = @backingInt(declaration);
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
    const resolver = interpreter.owning_resolver();
    while (self.adopted.len > mark) {
        self.adopted.len -= 1;
        const entry = self.adopted.buffer[self.adopted.len];
        const value = interpreter.memory.buffer[entry.cell];
        // a static keeps its exported value, retyped to its declared type
        const declaration_node = resolver.decl_pool.get(entry.decl, .node);
        const exported = interpreter.export_value(declaration_node, value);
        const declared_type = resolver.decl_pool.get(entry.decl, .value_type);
        const retyped = resolver.static_values.retyped(exported, declared_type);
        resolver.decl_pool.set(entry.decl, .static_value, retyped);
    }
}

fn declaration_of(self: *Variables, node: NodeId) DeclPool.Index {
    const interpreter = self.owning_interpreter();
    if (interpreter.has_body_frame()) return interpreter.node_info(.declaration, node);
    // of overloaded stcfuns the one the checker picked for the arguments, the name means the first
    const resolver = interpreter.owning_resolver();
    const picked = resolver.node_declarations[node];
    if (picked != .none and resolver.decl_pool.get(picked, .kind) == .static_function) return picked;
    return resolver.declarations.use_name(node);
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
    const resolver = interpreter.owning_resolver();
    const declaration = self.declaration_of(node);
    if (declaration == .none) {
        if (!interpreter.has_body_frame()) return .poison;
        const name = interpreter.owning_resolver().name_pool.name_of_node(node);
        return interpreter.fail(node, .undefined_name, name, 0);
    }
    // a local function is a value only together with the cells it captures
    const is_local_function = interpreter.has_body_frame() and
        resolver.decl_pool.get(declaration, .kind) == .function and
        !resolver.decl_pool.get(declaration, .flags).is_global;
    if (is_local_function) return interpreter.calls.closure(declaration);

    const value = self.peek(declaration);
    // an array a slice may be taken of keeps its own cells, so writes through the slice reach it
    const is_mutable_array = value.is_pooled() and !value.is(.none) and
        resolver.decl_pool.get(declaration, .flags).is_mut and
        resolver.static_pool.tag(interpreter.value_type(value)) == .array_type;
    if (is_mutable_array) {
        if (self.cell_of_declaration(declaration)) |cell| return interpreter.thaw_cell(cell);
    }
    if (value.is(.none)) {
        const static_value = resolver.decl_pool.get(declaration, .static_value);
        if (static_value != .none) return .of(&resolver.static_pool, static_value);

        // a failed declaration is already diagnosed
        if (resolver.decl_pool.get(declaration, .state) == .failed) return .poison;
        return interpreter.fail(node, .not_static, resolver.name_pool.name_of_node(node), 0);
    }
    return value;
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
    // a view writes the fields it shares
    if (self.alias_of(declaration)) |i| if (self.alias_views.buffer[i]) {
        const fields = interpreter.memory.buffer[self.alias_cells.buffer[i]];
        for (0..fields.len()) |j| {
            const field = interpreter.element(value, @intCast(j));
            interpreter.store_cell(fields.cell() + j, interpreter.owned_copy(field));
        }
        return true;
    };
    if (self.cell_of_declaration(declaration)) |cell| {
        interpreter.store_converted(cell, value, resolver.decl_pool.get(declaration, .value_type));
        return true;
    }

    if (self.rejects_impure_write(node)) return false;
    // a static keeps its exported value, retyped to its declared type
    const declaration_node = resolver.decl_pool.get(declaration, .node);
    const exported = interpreter.export_value(declaration_node, value);
    const declared_type = resolver.decl_pool.get(declaration, .value_type);
    const retyped = resolver.static_values.retyped(exported, declared_type);
    resolver.decl_pool.set(declaration, .static_value, retyped);
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
    // a static outside the running frames is adopted into a cell until the evaluation ends
    if (resolver.tree.props(node).name) {
        const declaration = self.declaration_of(node);
        if (declaration == .none) return null;
        if (self.cell_of_declaration(declaration)) |cell| return cell;

        const is_static_parameter = resolver.decl_pool.get(declaration, .kind) == .static_parameter;
        if (!is_static_parameter and self.rejects_impure_write(node)) return null;
        const stored_value: Value = blk: {
            const static_value = resolver.decl_pool.get(declaration, .static_value);
            if (static_value != .none) break :blk .of(&resolver.static_pool, static_value);

            // a failed declaration is already diagnosed
            if (resolver.decl_pool.get(declaration, .state) == .failed) break :blk .poison;
            const name = resolver.name_pool.name_of_node(node);
            break :blk interpreter.fail(node, .not_static, name, 0);
        };
        const adopted_cell = interpreter.push_cell(stored_value);
        self.adopted.push(.{ .decl = declaration, .cell = adopted_cell });
        return adopted_cell;
    }
    if (kind == .dereference) {
        const pointer = interpreter.evaluate(resolver.tree.arg(node, 0));
        if (pointer.is_ref()) return pointer.cell();
        if (!pointer.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
        return null;
    }
    if (kind == .array_index) {
        const aggregate_cell = self.cell_of_place(resolver.tree.arg(node, 0)) orelse return null;
        return self.cell_of_component(aggregate_cell, node, kind);
    }
    if (kind == .member) {
        const parent_type = interpreter.checked_type(resolver.tree.arg(node, 0));
        const is_member_of_type = resolver.static_pool.tag(parent_type) == .meta_type;
        if (!is_member_of_type) {
            const parent = resolver.tree.arg(node, 0);
            const aggregate_cell = self.cell_of_place(parent) orelse return null;
            return self.cell_of_component(aggregate_cell, node, kind);
        }
    }

    // a constant of a type (`Light.Green`) is a value like any other
    const value = interpreter.evaluate(node);
    if (value.is(.poison_type)) return null;
    return interpreter.push_cell(interpreter.owned_copy(value));
}

// an element or field of the aggregate in a cell, a pooled aggregate is thawed so it can be written
pub fn cell_of_component(self: *Variables, place_cell: u32, node: NodeId, kind: Kind) ?u32 {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    // an element of a slice is one of the cells it refers to, as far as its length goes
    const held = interpreter.memory.buffer[place_cell];
    if (kind == .array_index and interpreter.is_slice(held)) {
        const position = interpreter.evaluate(resolver.tree.arg(node, 1));
        if (!Value.is_int(position.value_type)) {
            if (!position.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
            return null;
        }
        if (position.bits >= held.slice_len()) {
            const shown_position: u32 = @truncate(position.bits);
            _ = interpreter.report(.static_eval_failed, node, shown_position, held.slice_len());
            return null;
        }
        return held.cell() + @as(u32, @intCast(position.bits));
    }
    var aggregate_cell = place_cell;
    const through_reference = interpreter.memory.buffer[aggregate_cell].is_ref();
    if (through_reference) aggregate_cell = interpreter.memory.buffer[aggregate_cell].cell();
    const aggregate = interpreter.thaw_cell(aggregate_cell);
    // a member of a value that is not a heap block is rejected below
    const position: u64 = blk: {
        if (kind == .array_index) {
            const position = interpreter.evaluate(resolver.tree.arg(node, 1));
            if (Value.is_int(position.value_type)) break :blk position.bits;
            // a poisoned index is reported already
            if (!position.is(.poison_type)) _ = interpreter.report(.not_static, node, 0, 0);
            return null;
        }
        if (!aggregate.is_heap()) break :blk 0;

        const field_name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));
        break :blk switch (resolver.static_pool.lookup_member(aggregate.value_type, field_name)) {
            .field => |field| field.index,
            else => return null,
        };
    };

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

pub fn declare(self: *Variables, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (!interpreter.has_body_frame()) {
        _ = resolver.declarations.check_statement(interpreter.function_context, node);
        return .unit;
    }

    const statement = Declarations.Stmt.from_node(resolver, node);
    if (statement.kind != .variable) {
        if (!statement.kind.is_type_declaration()) return .unit;

        const declared_type = interpreter.evaluate(statement.values[0]);
        for (statement.assignees) |assignee| {
            _ = self.store(assignee, interpreter.node_info(.declaration, assignee), declared_type);
        }
        if (declared_type.is(.poison_type)) return declared_type;
        return .unit;
    }

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

    // an annotation the checker left unresolved (the declared type is poisoned) is evaluated now
    const has_unresolved_annotation = statement.type != 0 and
        first_declaration != .none and
        interpreter.node_info(.static_value, statement.type) == .none and
        resolver.static_pool.is_poisoned(resolver.decl_pool.get(first_declaration, .value_type));
    var evaluated_type: Index = .none;
    if (has_unresolved_annotation) {
        evaluated_type = interpreter.types.type_of_node(statement.type) orelse return .poison;
    }

    for (assignees, 0..) |assignee, i| {
        const declaration = interpreter.node_info(.declaration, assignee);
        if (declaration == .none) continue;

        const value = switch (values.len) {
            0 => blk: {
                const zeroed_type = if (evaluated_type != .none)
                    evaluated_type
                else
                    resolver.decl_pool.get(declaration, .value_type);
                break :blk interpreter.zero_value(zeroed_type);
            },
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
    const step_type = if (Value.is_int(old_value.value_type)) old_value.value_type else .u64_type;
    const right: Value = if (compound) operand else .int(step_type, 1);
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
