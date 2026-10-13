const std = @import("std");
const DynamicBuffer = @import("containers.zig").DynamicBuffer;
const ParseTree = @import("ParseTree.zig");
const Resolver = @import("Resolver.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const NamePool = @import("resolver/NamePool.zig");
const BodyPool = @import("resolver/BodyPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const Declarations = @import("resolver/checker/Declarations.zig");
const HighIr = @import("high_lowerer/HighIr.zig");
const FunctionBuilder = @import("high_lowerer/FunctionBuilder.zig");
const Ref = HighIr.Ref;
const Op = HighIr.Op;
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const NodeKind = ParseTree.Node.Kind;
const constructs = @import("language/constructs.zig");
const operators = @import("language/operators.zig");

// lowers the checked program into `HighIr`: the mond-specific half of it, `builder` building
// the ssa form without knowing the language
const HighLowerer = @This();
const none: u32 = std.math.maxInt(u32);

// where `brk` and `cont` of the innermost loop go, and how many defers they leave running
const Loop = struct { break_block: u32, continue_block: u32, defers: u32 };

// a `defer` statement, or with `pointer` set: the deinit of the value of `value_type` stored there
const Defer = struct { node: NodeId, pointer: Ref, value_type: Index };

// how an arm of a `match` takes part in a `switch`: by its keys, or as the default
const SwitchArm = enum { keyed, catch_all };

const LoopBlocks = struct { head: u32, body: u32, next: u32, exit: u32 };

// how a `for` walks its sequence
const SequenceWalk = struct {
    // the index into a range or an array, stepped after each iteration
    counter: u32 = none,
    counter_type: Index = .none,
    element: DeclPool.Index = .none,
    // the array walked or the iterator asked for its elements, `none` for a range
    sequence: Ref = .none,
    // the element type of an array, the iterator's type otherwise
    sequence_type: Index = .none,
};

// the sequence of a `for` and the array a loop collects into
const ForLoop = struct {
    sequence: NodeId,
    sequence_type: Index,
    result_type: Index,
    collects_dynamic: bool,
    collected: *Ref,
    blocks: LoopBlocks,
};

// the array a loop collects its body's values into
const Collection = struct {
    array: Ref,
    array_type: Index,
    // the temporary counting the values collected
    count: u32,
    is_dynamic: bool,
    // the length of a fixed-size array
    capacity: u64,
    exit: u32,
};

const Receiver = struct { node: NodeId, is_bound: bool };

// one bit per field of a record, sized to the record so any field count fits
const FieldSet = std.DynamicBitSetUnmanaged;

allocator: std.mem.Allocator,
resolver: *Resolver,
static_pool: *StaticPool,
ir: HighIr,
// ssa variables below this number are declarations, the ones above temporaries of the lowerer
first_temporary: u32,
// the ir function of each lowered declaration
function_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
// an overload with the same parameters as an earlier one is lowered into the earlier's function
overload_group_head_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
// the overload tried next when the guards of this one fail
next_overload_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
global_index_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
// declarations with an ir function that is not lowered yet
function_queue: DynamicBuffer(DeclPool.Index),
scratch: DynamicBuffer(u32),
builder: FunctionBuilder,
temporary_types: DynamicBuffer(Index),
parameters: DynamicBuffer(Ref),
defers: DynamicBuffer(Defer),
loops: DynamicBuffer(Loop),
// variables living in memory, by the pointer to them
stack_slots: std.AutoHashMapUnmanaged(DeclPool.Index, Ref) = .empty,
// variables of the current body whose address is taken, they must live in memory
address_taken: std.AutoHashMapUnmanaged(DeclPool.Index, void) = .empty,
return_type: Index = .unit_type,
body: BodyPool.Body = .{},

pub fn init(allocator: std.mem.Allocator, resolver: *Resolver) HighLowerer {
    return .{
        .allocator = allocator,
        .resolver = resolver,
        .static_pool = &resolver.static_pool,
        .ir = .init(allocator),
        .first_temporary = resolver.decl_pool.entries.len(),
        .function_queue = .init(allocator, 256),
        .scratch = .init(allocator, 256),
        .builder = .init(allocator, &resolver.static_pool),
        .temporary_types = .init(allocator, 64),
        .parameters = .init(allocator, 16),
        .defers = .init(allocator, 16),
        .loops = .init(allocator, 16),
    };
}

pub fn deinit(self: *HighLowerer) void {
    self.function_of.deinit(self.allocator);
    self.overload_group_head_of.deinit(self.allocator);
    self.next_overload_of.deinit(self.allocator);
    self.global_index_of.deinit(self.allocator);
    self.stack_slots.deinit(self.allocator);
    self.address_taken.deinit(self.allocator);

    self.ir.deinit();

    self.function_queue.deinit();
    self.scratch.deinit();
    self.builder.deinit();
    self.temporary_types.deinit();
    self.parameters.deinit();
    self.defers.deinit();
    self.loops.deinit();
}

pub fn lower(self: *HighLowerer) void {
    const bodies = self.resolver.bodies.bodies.columns();
    var overload_lists = self.resolver.scopes.globals.valueIterator();
    while (overload_lists.next()) |first| self.group_overloads(first.*);

    self.declare_globals();

    for (bodies.declaration) |declaration| {
        if (self.is_lowered_function(declaration)) _ = self.ensure_function(declaration);
    }

    self.ir.init_fn = self.ir.functions.len();
    const initializer_type = self.static_pool.intern(.{ .function_type = .{
        .category = .default,
        .parameters = &.{},
        .return_type = .unit_type,
    } });
    self.ir.functions.push(.{
        .decl = .none,
        .ty = initializer_type,
        .first_block = 0,
        .blocks = 0,
        .first_inst = 0,
        .insts = 0,
        .captures = 0,
    });

    var i: u32 = 0;
    while (i < self.function_queue.len) : (i += 1) {
        self.lower_function(self.function_queue.buffer[i]);
    }
    self.lower_initializer();
}

fn put_entry(
    allocator: std.mem.Allocator,
    map: anytype,
    key: @FieldType(@TypeOf(map.*).KV, "key"),
    value: @FieldType(@TypeOf(map.*).KV, "value"),
) void {
    map.put(allocator, key, value) catch @panic("OOM");
}

// overloads and globals

fn group_overloads(self: *HighLowerer, first: DeclPool.Index) void {
    var overload = first;
    while (overload != .none) : (overload = self.resolver.decl_pool.get(overload, .next_overload)) {
        const realized = self.resolver.declarations.realized(overload);
        if (!self.resolver.bodies.body_index_of.contains(realized)) continue;
        self.join_earlier_overload(first, overload, realized);
    }
}

// joins the group of the first earlier overload taking the same parameters, if there is one
fn join_earlier_overload(
    self: *HighLowerer,
    first: DeclPool.Index,
    overload: DeclPool.Index,
    realized: DeclPool.Index,
) void {
    var earlier = first;
    while (earlier != overload) : (earlier = self.resolver.decl_pool.get(earlier, .next_overload)) {
        const realized_earlier = self.resolver.declarations.realized(earlier);
        if (!self.resolver.bodies.body_index_of.contains(realized_earlier)) continue;
        if (!self.resolver.calls.has_same_parameters(realized_earlier, realized)) continue;

        put_entry(self.allocator, &self.overload_group_head_of, realized, realized_earlier);
        var last = realized_earlier;
        while (self.next_overload_of.get(last)) |next| last = next;
        put_entry(self.allocator, &self.next_overload_of, last, realized);
        return;
    }
}

// trees and what holds them are compile-time only, nothing of them is lowered
fn holds_trees(self: *HighLowerer, value_type: Index) bool {
    return self.resolver.tree.macros and self.static_pool.contains_trees(value_type);
}

fn declare_globals(self: *HighLowerer) void {
    const declarations = self.resolver.decl_pool.entries.columns();
    for (0..declarations.name.len) |i| {
        const flags = declarations.flags[i];
        if (!flags.is_global or declarations.kind[i] != .variable) continue;
        if (self.holds_trees(declarations.value_type[i])) continue;

        const declaration: DeclPool.Index = @enumFromInt(i);
        put_entry(self.allocator, &self.global_index_of, declaration, self.ir.globals.len());
        self.ir.globals.push(.{
            .decl = declaration,
            .ty = self.substituted(declarations.value_type[i]),
            .init = if (flags.is_stc) declarations.static_value[i] else .none,
        });
    }
}

fn is_lowered_function(self: *HighLowerer, declaration: DeclPool.Index) bool {
    if (!self.resolver.decl_pool.get(declaration, .kind).is_function()) return false;
    if (self.overload_group_head_of.contains(declaration)) return false;
    return !self.holds_trees(self.resolver.decl_pool.get(declaration, .value_type));
}

// the ir function of a declaration, made and queued for lowering when first asked for
fn ensure_function(self: *HighLowerer, declaration: DeclPool.Index) u32 {
    const head = self.overload_group_head_of.get(declaration) orelse declaration;
    const entry = self.function_of.getOrPut(self.allocator, head) catch @panic("OOM");
    if (entry.found_existing) return entry.value_ptr.*;

    entry.value_ptr.* = self.ir.functions.len();
    const function_type = self.substituted(self.resolver.decl_pool.get(head, .value_type));
    const captures = self.resolver.bodies.captures_of(&self.resolver.decl_pool, head);
    self.ir.functions.push(.{
        .decl = head,
        .ty = function_type,
        .first_block = 0,
        .blocks = 0,
        .first_inst = 0,
        .insts = 0,
        .captures = @intCast(captures.len),
    });
    if (self.resolver.bodies.body_index_of.contains(head)) self.function_queue.push(head);
    return entry.value_ptr.*;
}

// types and nodes

fn substituted(self: *HighLowerer, value_type: Index) Index {
    if (value_type == .none) return value_type;
    return self.static_pool.substitute_type_variables(value_type);
}

fn type_of(self: *HighLowerer, node: NodeId) Index {
    return self.substituted(self.resolver.node_info(self.body, .node_type, node));
}

fn declaration_of(self: *HighLowerer, node: NodeId) DeclPool.Index {
    return self.resolver.node_info(self.body, .declaration, node);
}

fn static_value_of(self: *HighLowerer, node: NodeId) ?Index {
    const value = self.resolver.node_info(self.body, .static_value, node);
    if (value == .none or value == .poison_type) return null;
    return value;
}

fn pointer_to(self: *HighLowerer, pointee: Index) Index {
    return self.static_pool.pointer_to(pointee, true);
}

fn is_pointer(self: *HighLowerer, value_type: Index) bool {
    return value_type != .none and self.static_pool.get(value_type) == .pointer_type;
}

fn pointee_of(self: *HighLowerer, pointer_type: Index) Index {
    return self.static_pool.get(pointer_type).pointer_type.pointee;
}

fn dereferenced_type(self: *HighLowerer, value_type: Index) Index {
    if (self.is_pointer(value_type)) return self.pointee_of(value_type);
    return value_type;
}

fn has_value(value_type: Index) bool {
    return switch (value_type) {
        .none, .unit_type, .runit_type, .never_type, .poison_type => false,
        else => true,
    };
}

fn is_aggregate(self: *HighLowerer, value_type: Index) bool {
    if (value_type == .none) return false;
    if (self.static_pool.tag(value_type) == .record_type) return true;
    return self.static_pool.tag(value_type) == .array_type and !self.is_dynamic_array(value_type);
}

fn is_dynamic_array(self: *HighLowerer, value_type: Index) bool {
    if (value_type == .none or self.static_pool.get(value_type) != .array_type) return false;
    return self.static_pool.get(value_type).array_type.length == StaticPool.dyn_len;
}

fn is_scalar(self: *HighLowerer, value_type: Index) bool {
    if (value_type == .bool_type) return true;
    if (value_type == .none) return false;
    const properties = self.static_pool.properties(value_type);
    return properties.is_integer or properties.is_float or self.is_pointer(value_type);
}

fn type_of_ref(self: *HighLowerer, ref: Ref) Index {
    if (ref == .none) return .none;
    if (ref.is_const()) return self.static_pool.type_of(ref.value());
    if (ref.is_global()) return self.pointer_to(self.ir.globals.column(.ty)[ref.index()]);
    return self.builder.result_type_of(ref);
}

// read anew each time: the slice moves when the pool grows
fn parameter_type(self: *HighLowerer, function_type: Index, parameter_index: usize) Index {
    return self.static_pool.get(function_type).function_type.parameters[parameter_index];
}

fn field_index(self: *HighLowerer, record: Index, argument: NodeId, position: usize) u32 {
    return self.resolver.calls.field_index_of(record, argument, position) orelse @intCast(position);
}

// variables

fn variable_type(self: *HighLowerer, variable: u32) Index {
    if (variable < self.first_temporary) {
        const declaration: DeclPool.Index = @enumFromInt(variable);
        return self.substituted(self.resolver.decl_pool.get(declaration, .value_type));
    }
    return self.temporary_types.buffer[variable - self.first_temporary];
}

fn new_temporary(self: *HighLowerer, value_type: Index) u32 {
    self.temporary_types.push(value_type);
    return self.first_temporary + self.temporary_types.len - 1;
}

fn read_current(self: *HighLowerer, variable: u32) Ref {
    const current_block = self.builder.current_block;
    return self.builder.read_variable(variable, self.variable_type(variable), current_block);
}

fn write_current(self: *HighLowerer, variable: u32, value: Ref) void {
    self.builder.write_variable(variable, self.builder.current_block, value);
}

// the value of a temporary where branches met again, unit when none of them gave one
fn merged_result(self: *HighLowerer, result: u32) Ref {
    if (result == none or self.builder.is_unreachable) return unit();
    return self.read_current(result);
}

fn needs_memory(self: *HighLowerer, declaration: DeclPool.Index) bool {
    if (self.address_taken.contains(declaration)) return true;
    const declared_type = self.resolver.decl_pool.get(declaration, .value_type);
    return self.is_aggregate(self.substituted(declared_type));
}

// slots go to the entry block, allocated once per call however often their code runs
fn alloca(self: *HighLowerer, value_type: Index) Ref {
    if (self.builder.is_unreachable) return .none;
    return self.builder.emit_raw(.alloca, self.pointer_to(value_type), none, 0, 0);
}

fn store(self: *HighLowerer, pointer: Ref, value: Ref) void {
    _ = self.builder.emit_refs(.store, .unit_type, pointer, value);
}

fn load(self: *HighLowerer, value_type: Index, pointer: Ref) Ref {
    return self.builder.emit_refs(.load, value_type, pointer, .none);
}

fn unit() Ref {
    return Ref.of(.unit_value);
}

fn emit_unreachable(self: *HighLowerer) void {
    _ = self.builder.emit(.@"unreachable", .unit_type, 0, 0);
}

// branches to `block` and continues there
fn branch_and_enter(self: *HighLowerer, block_index: u32) void {
    self.builder.branch(block_index);
    self.builder.go_to(block_index);
}

fn default_value(self: *HighLowerer, value_type: Index) Ref {
    if (self.static_pool.tag(value_type) == .record_type) return self.construct(value_type, &.{});
    return self.builder.emit(.zeroed, value_type, 0, 0);
}

fn declare_variable(self: *HighLowerer, declaration: DeclPool.Index, value: Ref) void {
    if (declaration == .none or self.builder.is_unreachable) return;
    if (self.global_index_of.contains(declaration)) return self.store_variable(declaration, value);

    const variable = @intFromEnum(declaration);
    if (self.needs_memory(declaration)) {
        const slot = self.alloca(self.variable_type(variable));
        put_entry(self.allocator, &self.stack_slots, declaration, slot);
        if (value != .none) self.store(slot, value);
        return;
    }

    if (value != .none) return self.write_current(variable, value);
    const current = self.builder.current_block;
    const undef = self.builder.emit_raw(.undef, self.variable_type(variable), 0, 0, current);
    self.builder.write_variable(variable, current, undef);
}

fn load_variable(self: *HighLowerer, declaration: DeclPool.Index) Ref {
    if (self.builder.is_unreachable) return .none;
    const value_type = self.variable_type(@intFromEnum(declaration));
    if (self.global_index_of.get(declaration)) |global| {
        return self.load(value_type, Ref.global(global));
    }
    if (self.stack_slots.get(declaration)) |slot| return self.load(value_type, slot);
    return self.read_current(@intFromEnum(declaration));
}

fn store_variable(self: *HighLowerer, declaration: DeclPool.Index, value: Ref) void {
    if (self.builder.is_unreachable or value == .none) return;
    if (self.global_index_of.get(declaration)) |global| {
        return self.store(Ref.global(global), value);
    }
    if (self.stack_slots.get(declaration)) |slot| return self.store(slot, value);
    self.write_current(@intFromEnum(declaration), value);
}

fn is_ssa_variable(self: *HighLowerer, node: NodeId) bool {
    const declaration = self.declaration_of(node);
    return switch (self.resolver.tree.kind(node)) {
        .identifier, .identifier_self => declaration != .none and
            !self.global_index_of.contains(declaration) and
            !self.stack_slots.contains(declaration),
        else => false,
    };
}

// a function as a value: a constant when it captures nothing, a closure of its captures otherwise
fn function_value(self: *HighLowerer, declaration: DeclPool.Index) Ref {
    const realized = self.resolver.declarations.realized(declaration);
    const function = self.ensure_function(realized);
    const head = self.ir.functions.column(.decl)[function];
    const captures = self.resolver.bodies.captures_of(&self.resolver.decl_pool, head);
    if (captures.len == 0) return Ref.of(self.static_pool.intern(.{ .function_value = head }));

    const mark = self.scratch.len;
    self.push_captures(captures);
    const captured = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;

    const closure_type = self.substituted(self.resolver.decl_pool.get(head, .value_type));
    return self.builder.emit(.closure, closure_type, function, captured);
}

// variables captured by reference are passed as the pointer to them
fn push_captures(self: *HighLowerer, captures: []const DeclPool.Index) void {
    for (captures) |captured| {
        const value = if (self.resolver.declarations.is_captured_by_reference(captured))
            self.stack_slots.get(captured) orelse .none
        else
            self.load_variable(captured);
        self.scratch.push(@intFromEnum(value));
    }
}

// functions

fn reset_function_state(self: *HighLowerer) void {
    self.builder.reset();
    inline for (.{
        &self.scratch,
        &self.temporary_types,
        &self.parameters,
        &self.defers,
        &self.loops,
    }) |buffer| buffer.len = 0;
    self.stack_slots.clearRetainingCapacity();
    self.address_taken.clearRetainingCapacity();
}

// `&x`, a receiver passed by pointer and a capture by reference of a local function take `x`
fn find_address_taken(self: *HighLowerer) void {
    const body = self.body;
    for (body.first_node..body.first_node + body.node_count) |i| {
        const node: NodeId = @intCast(i);
        self.mark_address_taken(self.address_target(node));
        self.mark_captured_by_reference(node);
    }
}

// the variable node whose address `node` takes, 0 when it takes none
fn address_target(self: *HighLowerer, node: NodeId) NodeId {
    const tree = self.resolver.tree;
    var target: NodeId = 0;
    if (tree.kind(node) == .address_of) target = tree.arg(node, 0);

    const calls_member = tree.kind(node) == .fun_call and tree.kind(tree.arg(node, 0)) == .member;
    if (calls_member) {
        const method = self.declaration_of(node);
        const takes_receiver = method != .none and
            self.resolver.decl_pool.implicit_self_count(method) == 1;
        if (takes_receiver) target = tree.arg(tree.arg(node, 0), 0);
    }

    while (target != 0 and tree.kind(target) == .capture) target = tree.arg(target, 0);
    return target;
}

fn mark_address_taken(self: *HighLowerer, target: NodeId) void {
    if (target == 0 or self.resolver.tree.kind(target) != .identifier) return;
    if (self.is_pointer(self.type_of(target))) return;
    put_entry(self.allocator, &self.address_taken, self.declaration_of(target), {});
}

fn mark_captured_by_reference(self: *HighLowerer, node: NodeId) void {
    const function = self.declaration_of(node);
    if (function == .none or !self.resolver.decl_pool.get(function, .kind).is_function()) return;
    if (!self.resolver.bodies.body_index_of.contains(function)) return;

    const definition = self.resolver.decl_pool.get(function, .node);
    const body = self.body;
    if (definition < body.first_node or definition >= body.first_node + body.node_count) return;

    for (self.resolver.bodies.captures_of(&self.resolver.decl_pool, function)) |captured| {
        if (!self.resolver.declarations.is_captured_by_reference(captured)) continue;
        put_entry(self.allocator, &self.address_taken, captured, {});
    }
}

fn lower_function(self: *HighLowerer, declaration: DeclPool.Index) void {
    self.reset_function_state();
    const function = self.function_of.get(declaration).?;
    const function_type = self.substituted(self.resolver.decl_pool.get(declaration, .value_type));
    self.return_type = self.static_pool.get(function_type).function_type.return_type;
    self.builder.go_to(self.builder.new_block());

    const captures = self.resolver.bodies.captures_of(&self.resolver.decl_pool, declaration);
    self.bind_capture_parameters(captures);
    const parameter_count = self.static_pool.get(function_type).function_type.parameters.len;
    for (0..parameter_count) |j| {
        const position: u32 = @intCast(captures.len + j);
        const value_type = self.parameter_type(function_type, j);
        self.parameters.push(self.builder.emit(.param, value_type, position, 0));
    }

    // an overload whose guards fail continues with the next one of its group
    var overload: ?DeclPool.Index = declaration;
    while (overload) |current| : (overload = self.next_overload_of.get(current)) {
        if (!self.lower_overload(current)) break;
    }
    self.emit_unreachable();
    self.builder.freeze(&self.ir, function);
}

fn bind_capture_parameters(self: *HighLowerer, captures: []const DeclPool.Index) void {
    for (captures, 0..) |captured, i| {
        const captured_type = self.variable_type(@intFromEnum(captured));
        const by_reference = self.resolver.declarations.is_captured_by_reference(captured);
        const value_type = if (by_reference) self.pointer_to(captured_type) else captured_type;
        const parameter = self.builder.emit(.param, value_type, @intCast(i), 0);
        if (by_reference) {
            put_entry(self.allocator, &self.stack_slots, captured, parameter);
        } else {
            self.write_current(@intFromEnum(captured), parameter);
        }
    }
}

// lowers one overload of a group and tells whether it has guards that may fail
fn lower_overload(self: *HighLowerer, overload: DeclPool.Index) bool {
    self.body = self.resolver.bodies.body_of(overload).?;
    self.find_address_taken();

    const value_node = self.resolver.declarations.value_node(overload);
    const implicit_self_count = self.resolver.decl_pool.implicit_self_count(overload);
    if (implicit_self_count == 1) self.declare_receiver(value_node);
    const parameter_nodes = self.resolver.tree.params_of(value_node);
    for (parameter_nodes, 0..) |parameter_node, i| {
        const argument = self.parameters.buffer[i + implicit_self_count];
        self.declare_variable(self.declaration_of(parameter_node), argument);
    }

    const guard_failed = self.builder.new_block();
    const has_guards = self.lower_parameter_guards(parameter_nodes, guard_failed);
    self.lower_parameter_repairs(parameter_nodes);
    self.lower_overload_body(overload, value_node);
    self.builder.go_to(guard_failed);
    return has_guards;
}

// `self` is declared by a node of the body pointing back at the function
fn declare_receiver(self: *HighLowerer, value_node: NodeId) void {
    const body = self.body;
    for (body.first_node..body.first_node + body.node_count) |i| {
        const declaration = self.declaration_of(@intCast(i));
        if (declaration == .none) continue;
        if (self.resolver.decl_pool.get(declaration, .kind) != .self) continue;
        if (self.resolver.decl_pool.get(declaration, .node) != value_node) continue;
        return self.declare_variable(declaration, self.parameters.buffer[0]);
    }
}

// guards without an `else` reject the overload
fn lower_parameter_guards(self: *HighLowerer, parameter_nodes: []const NodeId, failed: u32) bool {
    var has_guards = false;
    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(self.resolver.tree, parameter_node);
        if (parameter.where == 0 or parameter.@"else" != 0 or parameter.stc) continue;

        has_guards = true;
        const passed = self.builder.new_block();
        self.builder.branch_if(self.expression_as(parameter.where, .bool_type), passed, failed);
        self.builder.go_to(passed);
    }
    return has_guards;
}

// guards with an `else` repair the argument instead: the `else` assigns, returns or is the value
fn lower_parameter_repairs(self: *HighLowerer, parameter_nodes: []const NodeId) void {
    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(self.resolver.tree, parameter_node);
        if (parameter.where == 0 or parameter.@"else" == 0 or parameter.stc) continue;

        const holds = self.enter_guard_failure(parameter.where);
        const repair = parameter.@"else";
        const repair_kind = self.resolver.tree.kind(repair);
        if (repair_kind == .assign or repair_kind == .ret) {
            _ = self.expression(repair);
        } else {
            const repaired_type = self.type_of(parameter_node);
            const repaired = self.expression_as(repair, repaired_type);
            self.store_variable(self.declaration_of(parameter_node), repaired);
        }
        self.branch_and_enter(holds);
    }
}

// continues where `guard` fails and returns the block where it holds
fn enter_guard_failure(self: *HighLowerer, guard: NodeId) u32 {
    const holds = self.builder.new_block();
    const fails = self.builder.new_block();
    self.builder.branch_if(self.expression_as(guard, .bool_type), holds, fails);
    self.builder.go_to(fails);
    return holds;
}

fn lower_overload_body(self: *HighLowerer, overload: DeclPool.Index, value_node: NodeId) void {
    const body = self.resolver.tree.arg(value_node, 1);
    if (self.resolver.tree.kind(body) != .block) {
        return self.emit_return(self.expression_as(body, self.return_type));
    }

    _ = self.expression(body);
    if (self.builder.is_unreachable) return;
    if (!has_value(self.return_type)) return self.emit_return(.none);
    // `main` falling off its end exits with 0
    if (self.resolver.decl_pool.get(overload, .name) == .main) {
        return self.emit_return(self.builder.constant_int(self.return_type, 0));
    }
    self.emit_unreachable();
}

// the initializers of the globals and the other top-level statements, in order
fn lower_initializer(self: *HighLowerer) void {
    self.reset_function_state();
    self.body = .{};
    self.return_type = .unit_type;
    self.builder.go_to(self.builder.new_block());
    for (self.resolver.roots) |root| {
        if (is_declaration_statement(self.resolver.tree.kind(root))) {
            self.lower_assignment(root);
        } else {
            _ = self.expression(root);
        }
    }
    self.emit_return(.none);
    self.builder.freeze(&self.ir, self.ir.init_fn);
}

fn is_declaration_statement(kind: NodeKind) bool {
    return switch (kind) {
        .assign, .assign_typed, .def_var, .mod_pub, .mod_mut, .mod_stc => true,
        else => false,
    };
}

fn emit_return(self: *HighLowerer, value: Ref) void {
    self.run_defers(0);
    const returned = if (has_value(self.return_type)) value else Ref.none;
    _ = self.builder.emit(.ret, .unit_type, @intFromEnum(returned), 0);
}

// runs the defers registered after the first `mark` ones, innermost first
fn run_defers(self: *HighLowerer, mark: u32) void {
    var i = self.defers.len;
    while (i > mark and !self.builder.is_unreachable) {
        i -= 1;
        const deferred = self.defers.buffer[i];
        if (deferred.pointer == .none) {
            _ = self.expression(deferred.node);
        } else {
            self.call_deinit(deferred.pointer, deferred.value_type);
        }
    }
}

fn call_deinit(self: *HighLowerer, pointer: Ref, value_type: Index) void {
    switch (self.static_pool.lookup_member(value_type, .deinit)) {
        .method => |method| {
            const callee = self.function_value(method);
            const arguments = self.builder.list(&.{@intFromEnum(pointer)});
            _ = self.builder.emit(.call, .unit_type, @intFromEnum(callee), arguments);
        },
        else => {},
    }
}

// values

fn coerce(self: *HighLowerer, value: Ref, unsubstituted_from: Index, unsubstituted_to: Index) Ref {
    const from = self.substituted(unsubstituted_from);
    const to = self.substituted(unsubstituted_to);
    if (value == .none or from == to or to == .none or from == .none) return value;
    if (!has_value(to)) return value;

    const kind = self.static_pool.coercion(from, to);
    return switch (kind) {
        .identity,
        .unified,
        .ptr_mut_to_ptr,
        .never_to_any,
        .poison,
        .unit_to_runit,
        .incompatible,
        => value,
        .case_to_variant => {
            if (self.static_pool.tag(to) == .variant_type) return value;
            const into_union = StaticPool.CoercionKind.variant_to_union;
            return self.builder.emit(.convert, to, @intFromEnum(value), @intFromEnum(into_union));
        },
        .payload_to_self_tagged => self.wrap_in_payload_case(value, from, to),
        .int_widen,
        .float_widen,
        .string_to_ptr,
        .array_ptr_to_elem_ptr,
        .to_dyn,
        .variant_to_union,
        .impl_to_trait,
        => self.builder.emit(.convert, to, @intFromEnum(value), @intFromEnum(kind)),
    };
}

fn wrap_in_payload_case(self: *HighLowerer, value: Ref, from: Index, variant: Index) Ref {
    const case_index = self.payload_case_index(variant);
    const case_type = self.static_pool.get(variant).variant_type.cases[case_index];
    const payload_type = self.static_pool.get(case_type).variant_case_type.payload;
    const payload_record = self.static_pool.get(payload_type).record_type;
    const field = self.coerce(value, from, payload_record.field_types[0]);
    const fields = self.builder.list(&.{@intFromEnum(field)});
    const payload = self.builder.emit(.aggregate, payload_type, 0, fields);
    return self.builder.emit(.variant_make, variant, @intCast(case_index), @intFromEnum(payload));
}

// the case of a self-tagged variant that carries the payload
fn payload_case_index(self: *HighLowerer, variant: Index) u32 {
    const cases = self.static_pool.get(variant).variant_type.cases;
    for (cases, 0..) |case, i| {
        if (self.static_pool.get(case).variant_case_type.payload != .none) return @intCast(i);
    }
    return 0;
}

fn constant_of(self: *HighLowerer, value: Index, value_type: Index) Ref {
    const pool = self.static_pool;
    if (value_type == .none) return Ref.of(value);

    const is_int = pool.tag(value) == .int_value;
    if (is_int and pool.properties(value_type).is_integer) {
        return self.builder.constant_int(value_type, pool.get(value).int_value.bits);
    }

    const is_number = is_int or pool.tag(value) == .float_value;
    if (!is_number or !pool.properties(value_type).is_float) return Ref.of(value);
    const float: f64 = if (pool.tag(value) == .float_value)
        pool.get(value).float_value.value
    else
        @floatFromInt(@as(i64, @bitCast(pool.get(value).int_value.bits)));
    return Ref.of(pool.intern(.{ .float_value = .{ .value_type = value_type, .value = float } }));
}

// the instruction computing a binary operator, short-circuit logic branches instead
fn operation_of(operator: operators.BinaryOperator) Op {
    return switch (operator) {
        .add => .add,
        .subtract => .sub,
        .multiply => .mul,
        .divide => .div,
        .remainder => .rem,
        .shift_left => .shl,
        .shift_right => .shr,
        .bit_and, .logic_and => .bit_and,
        .bit_or, .logic_or => .bit_or,
        .bit_xor => .bit_xor,
        .equal => .eq,
        .not_equal, .logic_xor => .ne,
        .less => .lt,
        .greater => .gt,
        .less_equal => .le,
        .greater_equal => .ge,
    };
}

// expressions

fn expression_as(self: *HighLowerer, node: NodeId, target_type: Index) Ref {
    return self.coerce(self.expression(node), self.type_of(node), target_type);
}

fn expression(self: *HighLowerer, node: NodeId) Ref {
    const value_type = self.type_of(node);
    if (self.static_value_of(node)) |value| return self.constant_of(value, value_type);
    const first = self.resolver.tree.arg(node, 0);
    const second = self.resolver.tree.arg(node, 1);
    const kind = self.resolver.tree.kind(node);

    return switch (constructs.construct_of(kind)) {
        .comparison => {
            const operation = operation_of(operators.binary_operator_of(kind));
            return self.comparison(operation, first, second);
        },
        .compound_assignment => self.compound_assignment(kind, first, second),
        .increment => self.increment(kind, value_type, first),
        .arithmetic => self.arithmetic(kind, value_type, first, second),
        .literal => {
            const literal = self.resolver.static_values.literal_value(node, false);
            return self.constant_of(literal, value_type);
        },
        .numeric_negation => self.numeric_negation(node, value_type, first),
        .name => self.name_value(node),
        .grouping => self.expression(first),
        .block => self.block(node),
        .declaration => {
            self.lower_assignment(node);
            return unit();
        },
        .short_circuit_logic => {
            const is_and = operators.binary_operator_of(kind) == .logic_and;
            return self.short_circuit(node, is_and);
        },
        .logical_xor => {
            const left = self.expression_as(first, .bool_type);
            const right = self.expression_as(second, .bool_type);
            return self.builder.emit_refs(.ne, .bool_type, left, right);
        },
        .logical_not => {
            const operand = self.expression_as(first, value_type);
            return self.builder.emit_refs(.not, value_type, operand, .none);
        },
        .call => self.call(node, value_type),
        .record_update => self.record_update(node),
        .member_access => self.member_access(node),
        .index => self.load(value_type, self.place(node)),
        .dereference => self.load(value_type, self.expression(first)),
        .address_of => self.place(first),
        .array_literal => self.array_literal(node, kind, value_type),
        .cast => self.cast(node, value_type, first),
        .bit_cast => self.bit_cast(value_type, first),
        .branch => self.if_else(node),
        .loop => self.loop(node),
        .match => self.match_expression(node),
        .return_value => {
            const value = self.expression_as(first, self.return_type);
            self.emit_return(value);
            return .none;
        },
        .return_void => {
            self.emit_return(.none);
            return .none;
        },
        .loop_jump => self.loop_jump(kind),
        .do => {
            _ = self.expression(first);
            return unit();
        },
        .@"defer" => {
            self.defers.push(.{ .node = first, .pointer = .none, .value_type = .none });
            return unit();
        },
        .deinit => {
            const pointer = self.place(first);
            self.call_deinit(pointer, self.dereferenced_type(self.type_of(first)));
            return unit();
        },
        .deferred_deinit => self.deferred_deinit(node, first),
        .unwrap => self.unwrap(node),
        .type_test => {
            const value = self.expression(first);
            const tested_type = self.static_value_of(second) orelse self.type_of(second);
            const tested = @intFromEnum(tested_type);
            return self.builder.emit(.type_test, .bool_type, @intFromEnum(value), tested);
        },
        .lambda => self.function_value(self.declaration_of(node)),
        // compile-time only: their value, if any, is static and was taken above
        .range,
        .type_expression,
        .type_definition,
        .type_of,
        .size_of,
        .macro,
        .part,
        => {
            if (!has_value(value_type)) return unit();
            return self.builder.emit_raw(.undef, value_type, 0, 0, self.builder.current_block);
        },
    };
}

fn compound_assignment(self: *HighLowerer, kind: NodeKind, target: NodeId, operand: NodeId) Ref {
    const operation = operation_of(operators.assigned_operator_of(kind));
    const target_type = self.type_of(target);
    const value = self.expression_as(operand, target_type);
    _ = self.update_place(target, operation, value, false);
    return unit();
}

// pointers step by one element, counted in an u64
fn increment(self: *HighLowerer, kind: NodeKind, value_type: Index, target: NodeId) Ref {
    const operation = operation_of(operators.assigned_operator_of(kind));
    const step_type: Index = if (self.is_pointer(value_type)) .u64_type else value_type;
    const one = self.builder.constant_int(step_type, 1);
    return self.update_place(target, operation, one, operators.returns_old_value(kind));
}

fn arithmetic(
    self: *HighLowerer,
    kind: NodeKind,
    value_type: Index,
    left: NodeId,
    right: NodeId,
) Ref {
    const operator = operators.binary_operator_of(kind);
    const operation = operation_of(operator);
    const offsets_pointer = (operator == .add or operator == .subtract) and
        self.is_pointer(value_type);
    if (!offsets_pointer) {
        const left_value = self.expression_as(left, value_type);
        const right_value = self.expression_as(right, value_type);
        return self.builder.emit_refs(operation, value_type, left_value, right_value);
    }

    const left_value = self.expression(left);
    const right_value = self.expression(right);
    if (self.is_pointer(self.type_of(left))) {
        return self.offset_pointer(value_type, left_value, operator == .subtract, right_value);
    }
    return self.offset_pointer(value_type, right_value, false, left_value);
}

fn numeric_negation(self: *HighLowerer, node: NodeId, value_type: Index, operand: NodeId) Ref {
    if (self.resolver.tree.is_literal(node)) {
        return self.constant_of(self.resolver.static_values.literal_value(node, false), value_type);
    }
    const value = self.expression_as(operand, value_type);
    return self.builder.emit_refs(.neg, value_type, value, .none);
}

fn block(self: *HighLowerer, node: NodeId) Ref {
    const mark = self.defers.len;
    var last = unit();
    for (self.resolver.tree.manychildren(node)) |statement| last = self.expression(statement);
    self.run_defers(mark);
    self.defers.len = mark;
    return last;
}

// `array_empty` has no children
fn array_literal(self: *HighLowerer, node: NodeId, kind: NodeKind, array_type: Index) Ref {
    const element_type = if (self.static_pool.get(array_type) == .array_type)
        self.static_pool.get(array_type).array_type.element
    else
        array_type;
    const mark = self.scratch.len;
    const elements = if (kind == .array) self.resolver.tree.manychildren(node) else &[_]NodeId{};
    for (elements) |element| {
        const value = self.expression_as(element, element_type);
        self.scratch.push(@intFromEnum(value));
    }
    const values = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    return self.builder.emit(.aggregate, array_type, 0, values);
}

fn cast(self: *HighLowerer, node: NodeId, target_type: Index, operand: NodeId) Ref {
    const from = self.type_of(operand);
    const kind = self.static_pool.cast_kind(from, target_type);
    if (kind == .array_narrow or kind == .pointer_relength) {
        return self.narrowing_cast(node, target_type);
    }
    const value = self.expression(operand);
    if (kind == .identity) return value;
    return self.builder.emit(.cast, target_type, @intFromEnum(value), @intFromEnum(kind));
}

fn bit_cast(self: *HighLowerer, target_type: Index, operand: NodeId) Ref {
    if (self.type_of(operand) == target_type) return self.expression(operand);
    const value = self.expression(operand);
    const target_size = self.static_pool.layout(target_type).size;
    const widens = target_size > self.static_pool.layout(self.type_of(operand)).size;
    const kind: StaticPool.CastKind = if (widens) .bit_extend else .bit_reinterpret;
    return self.builder.emit(.cast, target_type, @intFromEnum(value), @intFromEnum(kind));
}

fn loop_jump(self: *HighLowerer, kind: NodeKind) Ref {
    if (self.loops.len == 0) return .none;
    const innermost = self.loops.buffer[self.loops.len - 1];
    self.run_defers(innermost.defers);
    const target = if (kind == .brk) innermost.break_block else innermost.continue_block;
    self.builder.branch(target);
    return .none;
}

// the value is stored now, the deinit at the end of the block gets the pointer to it
fn deferred_deinit(self: *HighLowerer, node: NodeId, operand: NodeId) Ref {
    const value = self.expression(operand);
    const slot = self.alloca(self.type_of(operand));
    self.store(slot, value);
    self.defers.push(.{ .node = node, .pointer = slot, .value_type = self.type_of(operand) });
    return value;
}

fn name_value(self: *HighLowerer, node: NodeId) Ref {
    const declaration = self.declaration_of(node);
    if (declaration == .none) return .none;
    const kind = self.resolver.decl_pool.get(declaration, .kind);
    const value = self.resolver.decl_pool.get(declaration, .static_value);
    if (kind.is_function()) return self.function_value(declaration);
    if (value != .none and self.stands_for_static_value(declaration, kind)) {
        return self.constant_of(value, self.type_of(node));
    }
    return self.load_variable(declaration);
}

fn stands_for_static_value(
    self: *HighLowerer,
    declaration: DeclPool.Index,
    kind: DeclPool.Entry.Kind,
) bool {
    if (self.resolver.decl_pool.get(declaration, .flags).is_stc) return true;
    return switch (kind) {
        .static_parameter, .parameter, .type_alias, .record, .variant, .trait => true,
        else => false,
    };
}

fn comparison(self: *HighLowerer, operation: Op, left: NodeId, right: NodeId) Ref {
    var left_type = self.type_of(left);
    var right_type = self.type_of(right);
    const both_types = self.static_pool.tag(left_type) == .meta_type and
        self.static_pool.tag(right_type) == .meta_type;
    if (both_types) {
        const left_static = self.static_value_of(left) orelse left_type;
        const same = left_static == (self.static_value_of(right) orelse right_type);
        return Ref.of(if (same == (operation == .eq)) .bool_true else .bool_false);
    }

    var left_value = self.expression(left);
    var right_value = self.expression(right);
    // pointers that do not join with the other side are compared by what they point to
    if (self.static_pool.join(left_type, right_type).joined_type == .none) {
        if (self.is_pointer(left_type)) {
            left_value = self.load(self.pointee_of(left_type), left_value);
            left_type = self.pointee_of(left_type);
        }
        if (self.is_pointer(right_type)) {
            right_value = self.load(self.pointee_of(right_type), right_value);
            right_type = self.pointee_of(right_type);
        }
    }

    const joined_type = self.static_pool.join(left_type, right_type).joined_type;
    const left_joined = self.coerce(left_value, left_type, joined_type);
    const right_joined = self.coerce(right_value, right_type, joined_type);
    return self.builder.emit_refs(operation, .bool_type, left_joined, right_joined);
}

// applies `operation` with `operand` to `target`, giving the new value or, `returns_old`, the old
fn update_place(
    self: *HighLowerer,
    target: NodeId,
    operation: Op,
    operand: Ref,
    returns_old: bool,
) Ref {
    const target_type = self.type_of(target);
    if (self.is_ssa_variable(target)) {
        const old = self.load_variable(self.declaration_of(target));
        const new = self.updated_value(target_type, operation, old, operand);
        self.store_variable(self.declaration_of(target), new);
        return if (returns_old) old else new;
    }

    const pointer = self.place(target);
    const old = self.load(target_type, pointer);
    const new = self.updated_value(target_type, operation, old, operand);
    self.store(pointer, new);
    return if (returns_old) old else new;
}

fn updated_value(self: *HighLowerer, value_type: Index, operation: Op, old: Ref, operand: Ref) Ref {
    if (self.is_pointer(value_type)) {
        return self.offset_pointer(value_type, old, operation == .sub, operand);
    }
    return self.builder.emit_refs(operation, value_type, old, operand);
}

fn assign_to(self: *HighLowerer, target: NodeId, value: Ref) void {
    if (self.is_ssa_variable(target) or self.is_global_name(target)) {
        return self.store_variable(self.declaration_of(target), value);
    }
    self.store(self.place(target), value);
}

fn is_global_name(self: *HighLowerer, node: NodeId) bool {
    if (!self.global_index_of.contains(self.declaration_of(node))) return false;
    return self.resolver.tree.kind(node) == .identifier;
}

fn lower_assignment(self: *HighLowerer, statement_node: NodeId) void {
    const statement = Declarations.Stmt.from_node(self.resolver, statement_node);
    if (statement.kind != .variable) return;
    const values = statement.values;
    const assignees = statement.assignees;

    // a single place that is not a name: a field, an element, a dereference
    if (assignees.len == 1 and self.resolver.name_pool.name_of_node(assignees[0]) == .none) {
        const target_type = self.type_of(assignees[0]);
        return self.assign_to(assignees[0], self.expression_as(values[0], target_type));
    }

    // every value is computed before the first is stored, so `a, b = b, a` swaps
    const shared = if (values.len == 1) self.expression(values[0]) else Ref.none;
    const mark = self.scratch.len;
    defer self.scratch.len = mark;
    for (assignees, 0..) |assignee, i| {
        const value = self.assigned_value(assignee, i, values, shared);
        self.scratch.push(@intFromEnum(value));
    }

    for (assignees, 0..) |assignee, i| {
        const declaration = self.declaration_of(assignee);
        if (self.is_folded_static(declaration)) continue;

        const value: Ref = @enumFromInt(self.scratch.buffer[mark + i]);
        if (self.resolver.decl_pool.get(declaration, .node) != statement.node) {
            self.store_variable(declaration, value);
        } else if (self.global_index_of.get(declaration)) |global| {
            // a constant initial value of a global is its static data, no code runs for it
            if (value.is_const()) {
                self.ir.globals.column(.init)[global] = value.value();
            } else {
                self.store_variable(declaration, value);
            }
        } else {
            self.declare_variable(declaration, value);
        }
    }
}

// static declarations with a known value are never stored
fn is_folded_static(self: *HighLowerer, declaration: DeclPool.Index) bool {
    if (declaration == .none) return true;
    if (!self.resolver.decl_pool.get(declaration, .flags).is_stc) return false;
    return self.resolver.decl_pool.get(declaration, .static_value) != .none;
}

fn assigned_value(
    self: *HighLowerer,
    assignee: NodeId,
    position: usize,
    values: []const NodeId,
    shared: Ref,
) Ref {
    const declaration = self.declaration_of(assignee);
    if (self.is_folded_static(declaration)) return .none;

    const target_type = self.variable_type(@intFromEnum(declaration));
    if (values.len == 0) {
        const is_local_aggregate = self.is_aggregate(target_type) and
            !self.global_index_of.contains(declaration);
        if (is_local_aggregate) return self.default_value(target_type);
        return .none;
    }
    if (values.len > 1) return self.expression_as(values[position], target_type);
    return self.coerce(shared, self.type_of(values[0]), target_type);
}

fn short_circuit(self: *HighLowerer, node: NodeId, is_and: bool) Ref {
    const left = self.resolver.tree.arg(node, 0);
    const right = self.resolver.tree.arg(node, 1);
    var budget: u8 = 3;
    // a cheap right side is computed anyway, saving the branch
    if (self.is_cheap(right, &budget)) {
        const operation: Op = if (is_and) .bit_and else .bit_or;
        const left_value = self.expression_as(left, .bool_type);
        const right_value = self.expression_as(right, .bool_type);
        return self.builder.emit_refs(operation, .bool_type, left_value, right_value);
    }

    const result = self.new_temporary(.bool_type);
    const left_value = self.expression_as(left, .bool_type);
    self.write_current(result, left_value);
    const evaluate_right = self.builder.new_block();
    const done = self.builder.new_block();
    if (is_and) {
        self.builder.branch_if(left_value, evaluate_right, done);
    } else {
        self.builder.branch_if(left_value, done, evaluate_right);
    }

    self.builder.go_to(evaluate_right);
    const right_value = self.expression_as(right, .bool_type);
    if (!self.builder.is_unreachable) self.write_current(result, right_value);
    self.branch_and_enter(done);
    if (self.builder.is_unreachable) return .none;
    return self.read_current(result);
}

// a scalar without calls, memory or control flow is cheaper computed than branched around
fn is_cheap(self: *HighLowerer, node: NodeId, budget: *u8) bool {
    if (!self.is_scalar(self.type_of(node))) return false;
    if (self.static_value_of(node) != null) return true;

    const tree = self.resolver.tree;
    const kind = tree.kind(node);
    switch (kind) {
        .identifier, .identifier_self => {
            if (!self.is_ssa_variable(node)) return false;
            return !self.resolver.decl_pool.get(self.declaration_of(node), .kind).is_function();
        },
        .capture => return self.is_cheap(tree.arg(node, 0), budget),
        .int, .char, .float, .string, .boolean_true, .boolean_false => return true,
        .neg_num => if (tree.is_literal(node)) return true,
        .if_else => return self.is_cheap_if_else(node, budget),
        .block => {
            const statements = tree.manychildren(node);
            return statements.len == 1 and self.is_cheap(statements[0], budget);
        },
        else => {},
    }

    const is_binary = switch (kind) {
        .binary_add,
        .binary_sub,
        .binary_mul,
        .binary_num_and,
        .binary_num_or,
        .binary_num_xor,
        .binary_eq,
        .binary_neq,
        .binary_less,
        .binary_greater,
        .binary_less_eq,
        .binary_greater_eq,
        .binary_logic_and,
        .binary_logic_or,
        .binary_logic_xor,
        => true,
        .neg_num, .neg_logic => false,
        else => return false,
    };
    return self.is_cheap_operator(node, is_binary, budget);
}

// pointer arithmetic is never cheap: it has to scale its offset
fn is_cheap_operator(self: *HighLowerer, node: NodeId, is_binary: bool, budget: *u8) bool {
    const tree = self.resolver.tree;
    if (budget.* == 0) return false;
    if (self.is_pointer(self.type_of(tree.arg(node, 0)))) return false;
    if (is_binary and self.is_pointer(self.type_of(tree.arg(node, 1)))) return false;

    budget.* -= 1;
    if (!self.is_cheap(tree.arg(node, 0), budget)) return false;
    return !is_binary or self.is_cheap(tree.arg(node, 1), budget);
}

fn is_cheap_if_else(self: *HighLowerer, node: NodeId, budget: *u8) bool {
    const tree = self.resolver.tree;
    if (budget.* == 0) return false;
    budget.* -= 1;

    const condition_and_then = tree.arg(node, 0);
    if (!self.is_cheap(tree.arg(condition_and_then, 0), budget)) return false;
    if (!self.is_cheap(tree.arg(condition_and_then, 1), budget)) return false;
    return self.is_cheap(tree.arg(node, 1), budget);
}

// conditionals

// one way through a conditional: its value goes into `result` (unless `none`), then to `merge`
fn arm_into(self: *HighLowerer, node: NodeId, result_type: Index, result: u32, merge: u32) void {
    const value = self.expression(node);
    const value_type = self.type_of(node);
    if (result != none and !self.builder.is_unreachable and has_value(value_type)) {
        self.write_current(result, self.coerce(value, value_type, result_type));
    }
    self.builder.branch(merge);
}

fn if_else(self: *HighLowerer, node: NodeId) Ref {
    const result_type = self.type_of(node);
    const parts = ParseTree.Branch.from_node(self.resolver.tree, node);
    const has_else = parts.@"else" != 0;
    if (self.resolver.tree.props(node).stc) return self.static_if(parts, result_type, has_else);

    var budgets: [2]u8 = .{ 3, 3 };
    const selects = has_else and self.is_scalar(result_type) and
        self.is_cheap(parts.then, &budgets[0]) and
        self.is_cheap(parts.@"else", &budgets[1]);
    if (selects) return self.select_if(parts, result_type);

    const result = if (has_value(result_type)) self.new_temporary(result_type) else none;
    const then_block = self.builder.new_block();
    const else_block = if (has_else) self.builder.new_block() else none;
    const merge = self.builder.new_block();
    const condition = self.expression_as(parts.cond, .bool_type);
    self.builder.branch_if(condition, then_block, if (has_else) else_block else merge);

    self.builder.go_to(then_block);
    self.arm_into(parts.then, result_type, result, merge);
    if (has_else) {
        self.builder.go_to(else_block);
        self.arm_into(parts.@"else", result_type, result, merge);
    }
    self.builder.go_to(merge);
    return self.merged_result(result);
}

fn static_if(self: *HighLowerer, parts: ParseTree.Branch, result_type: Index, has_else: bool) Ref {
    const takes_then = (self.static_value_of(parts.cond) orelse .bool_false) == .bool_true;
    if (takes_then) return self.expression_as(parts.then, result_type);
    if (has_else) return self.expression_as(parts.@"else", result_type);
    return unit();
}

// both cheap arms are computed and one is selected, no branch needed
fn select_if(self: *HighLowerer, parts: ParseTree.Branch, result_type: Index) Ref {
    const condition = self.expression_as(parts.cond, .bool_type);
    if (condition.is_const()) {
        const taken = if (condition.value() == .bool_true) parts.then else parts.@"else";
        return self.expression_as(taken, result_type);
    }

    const then_value = self.expression_as(parts.then, result_type);
    const else_value = self.expression_as(parts.@"else", result_type);
    if (then_value == else_value) return then_value;
    const choices = self.builder.list(&.{ @intFromEnum(then_value), @intFromEnum(else_value) });
    return self.builder.emit(.select, result_type, @intFromEnum(condition), choices);
}

// match

fn match_expression(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const result_type = self.type_of(node);
    const arms = tree.manychildren(tree.arg(node, 1));
    if (tree.kind(node) == .stcmatch) {
        for (arms) |arm| {
            if ((self.static_value_of(arm) orelse .none) != .bool_true) continue;
            return self.expression_as(tree.arg(arm, 1), result_type);
        }
    }

    var scrutinee_type = self.type_of(tree.arg(node, 0));
    var scrutinee = self.expression(tree.arg(node, 0));
    const is_pointer_to_nominal = self.is_pointer(scrutinee_type) and
        self.static_pool.through_pointer(scrutinee_type) != scrutinee_type;
    if (is_pointer_to_nominal) {
        scrutinee = self.load(self.pointee_of(scrutinee_type), scrutinee);
        scrutinee_type = self.pointee_of(scrutinee_type);
    }

    const result = if (has_value(result_type)) self.new_temporary(result_type) else none;
    const merge = self.builder.new_block();
    if (self.lower_as_switch(arms, scrutinee, scrutinee_type, result_type, result, merge)) {
        self.builder.go_to(merge);
        return self.merged_result(result);
    }

    for (arms) |arm| {
        const arm_body = self.builder.new_block();
        const next_arm = self.builder.new_block();
        self.match_pattern(tree.arg(arm, 0), scrutinee, scrutinee_type, arm_body, next_arm);
        self.builder.go_to(arm_body);
        self.arm_into(tree.arg(arm, 1), result_type, result, merge);
        self.builder.go_to(next_arm);
    }
    self.emit_unreachable();
    self.builder.go_to(merge);
    return self.merged_result(result);
}

fn tag_type(self: *HighLowerer, scrutinee_type: Index, variant: Index) Index {
    if (scrutinee_type != .none and self.static_pool.tag(scrutinee_type) == .variant_union_type) {
        return self.static_pool.union_tag_type(scrutinee_type);
    }
    const variant_type = self.static_pool.get(variant).variant_type;
    if (variant_type.tag_type == .none or variant_type.tag_type == .poison_type) return .u8_type;
    return variant_type.tag_type;
}

// a union flattens its members: a member's tags are moved into the member's own range
fn tag_constant(self: *HighLowerer, scrutinee_type: Index, case: Index) Ref {
    const case_type = self.static_pool.get(case).variant_case_type;
    const case_tag_type = self.tag_type(scrutinee_type, case_type.variant);
    if (scrutinee_type != .none and self.static_pool.tag(scrutinee_type) == .variant_union_type) {
        const bits = self.static_pool.get(case_type.tag).int_value.bits;
        const offset = self.static_pool.union_offset(scrutinee_type, case_type.variant);
        return self.builder.constant_int(case_tag_type, bits + offset);
    }
    return self.constant_of(case_type.tag, case_tag_type);
}

// whether a value of `scrutinee_type` may be of `case`
fn can_hold_case(self: *HighLowerer, scrutinee_type: Index, case: Index) bool {
    const variant = self.static_pool.get(case).variant_case_type.variant;
    if (scrutinee_type == .none or scrutinee_type == variant) return true;
    return switch (self.static_pool.get(scrutinee_type)) {
        .variant_union_type => |members| std.mem.indexOfScalar(Index, members, variant) != null,
        .variant_case_type => |case_type| case_type.variant == variant,
        .variant_type => false,
        else => true,
    };
}

fn tests_case(self: *HighLowerer, value: Ref, scrutinee_type: Index, case: Index) Ref {
    const tag = self.tag_constant(scrutinee_type, case);
    const value_tag = self.builder.emit_refs(.variant_tag, self.type_of_ref(tag), value, .none);
    return self.builder.emit_refs(.eq, .bool_type, value_tag, tag);
}

// a union member is a variant of its own again once its tag is moved back into its range
fn narrow_to_variant(self: *HighLowerer, value: Ref, scrutinee_type: Index, variant: Index) Ref {
    if (scrutinee_type == .none) return value;
    if (self.static_pool.tag(scrutinee_type) != .variant_union_type) return value;
    const retag = StaticPool.CastKind.variant_retag;
    return self.builder.emit(.cast, variant, @intFromEnum(value), @intFromEnum(retag));
}

// a `match` whose arms test constants, up to the first catch-all, becomes one `switch`
fn lower_as_switch(
    self: *HighLowerer,
    arms: []const NodeId,
    scrutinee: Ref,
    scrutinee_type: Index,
    result_type: Index,
    result: u32,
    merge: u32,
) bool {
    const tagged = self.has_tag(scrutinee_type);
    // the properties are read only for a real type, `.none` has no pool entry
    const switchable = tagged or scrutinee_type != .none and
        self.static_pool.properties(scrutinee_type).is_integer;
    if (!switchable) return false;
    const arm_count = self.switch_arm_count(arms, scrutinee_type, tagged) orelse return false;
    const switched_arms = arms[0..arm_count];

    const mark = self.scratch.len;
    const first_arm_block = self.builder.block_count();
    const default_block = self.collect_switch_cases(switched_arms, scrutinee_type, tagged, mark);
    self.emit_switch(scrutinee, tagged, default_block, mark);
    self.scratch.len = mark;

    for (switched_arms, 0..) |arm, i| {
        self.builder.go_to(first_arm_block + @as(u32, @intCast(i)));
        self.bind_pattern(self.resolver.tree.arg(arm, 0), scrutinee, scrutinee_type);
        self.arm_into(self.resolver.tree.arg(arm, 1), result_type, result, merge);
    }
    // without a catch-all arm the default block is a fresh one nothing reaches
    if (default_block == first_arm_block + arm_count) {
        self.builder.go_to(default_block);
        self.emit_unreachable();
    }
    return true;
}

// self-tagged variants keep their tag inside the payload, there is no tag to switch on
fn has_tag(self: *HighLowerer, scrutinee_type: Index) bool {
    if (scrutinee_type == .none) return false;
    if (self.static_pool.tag(scrutinee_type) == .variant_union_type) return true;
    if (self.static_pool.tag(scrutinee_type) != .variant_type) return false;
    return self.static_pool.get(scrutinee_type).variant_type.tag_mode != .self;
}

// how many leading arms go into the switch, null when it is not worth one
fn switch_arm_count(
    self: *HighLowerer,
    arms: []const NodeId,
    scrutinee_type: Index,
    tagged: bool,
) ?u32 {
    var count: u32 = 0;
    var keyed_count: u32 = 0;
    for (arms) |arm| {
        const pattern = self.resolver.tree.arg(arm, 0);
        const arm_kind = self.switch_arm_kind(pattern, scrutinee_type, tagged) orelse return null;
        count += 1;
        keyed_count += @intFromBool(arm_kind == .keyed);
        if (arm_kind == .catch_all) break;
    }
    if (keyed_count < 2) return null;
    return count;
}

// null when the pattern needs more than comparing the key, so no switch is possible
fn switch_arm_kind(
    self: *HighLowerer,
    pattern: NodeId,
    scrutinee_type: Index,
    tagged: bool,
) ?SwitchArm {
    const tree = self.resolver.tree;
    const pattern_type = self.type_of(pattern);
    const is_case = pattern_type != .none and
        self.static_pool.tag(pattern_type) == .variant_case_type;
    if (is_case and !self.can_hold_case(scrutinee_type, pattern_type)) return null;

    return switch (tree.kind(pattern)) {
        .identifier => .catch_all,
        .partial__match_case_pattern_or => {
            for (tree.manychildren(pattern)) |alternative| {
                const alternative_kind = self.switch_arm_kind(alternative, scrutinee_type, tagged);
                if (alternative_kind != .keyed) return null;
            }
            return .keyed;
        },
        .labelarrow => {
            const labelled = tree.arg(pattern, 0);
            if (self.switch_arm_kind(labelled, scrutinee_type, tagged) == .keyed) return .keyed;
            return null;
        },
        // a case taking its payload apart, as long as the parts only bind names
        .fun_call => {
            if (!is_case or !tagged) return null;
            for (tree.manychildren(tree.arg(pattern, 1))) |argument| {
                if (tree.kind(tree.arg_value(argument)) != .identifier) return null;
            }
            return .keyed;
        },
        .partial__match_case_pattern_typecast,
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
        .string,
        => null,
        else => {
            if (is_case != tagged) return null;
            if (is_case or tree.is_literal(pattern) or self.static_value_of(pattern) != null) {
                return .keyed;
            }
            return null;
        },
    };
}

// pushes the default block, then the key and block pairs, from scratch[mark]. gives the default
fn collect_switch_cases(
    self: *HighLowerer,
    arms: []const NodeId,
    scrutinee_type: Index,
    tagged: bool,
    mark: u32,
) u32 {
    self.scratch.push(none);
    for (arms) |arm| {
        const arm_block = self.builder.new_block();
        const pattern = self.resolver.tree.arg(arm, 0);
        if (self.switch_arm_kind(pattern, scrutinee_type, tagged) == .keyed) {
            self.push_switch_keys(pattern, scrutinee_type, arm_block, mark);
        } else {
            self.scratch.buffer[mark] = arm_block;
        }
    }
    const default_block = if (self.scratch.buffer[mark] == none)
        self.builder.new_block()
    else
        self.scratch.buffer[mark];
    self.scratch.buffer[mark] = default_block;
    return default_block;
}

fn push_switch_keys(
    self: *HighLowerer,
    pattern: NodeId,
    scrutinee_type: Index,
    arm_block: u32,
    mark: u32,
) void {
    const tree = self.resolver.tree;
    switch (tree.kind(pattern)) {
        .partial__match_case_pattern_or => for (tree.manychildren(pattern)) |alternative| {
            self.push_switch_keys(alternative, scrutinee_type, arm_block, mark);
        },
        .labelarrow => {
            self.push_switch_keys(tree.arg(pattern, 0), scrutinee_type, arm_block, mark);
        },
        else => self.push_switch_key(pattern, scrutinee_type, arm_block, mark),
    }
}

fn push_switch_key(
    self: *HighLowerer,
    pattern: NodeId,
    scrutinee_type: Index,
    arm_block: u32,
    mark: u32,
) void {
    const pattern_type = self.type_of(pattern);
    const key_ref = if (self.static_pool.tag(pattern_type) == .variant_case_type)
        self.tag_constant(scrutinee_type, pattern_type)
    else
        self.constant_of(self.static_pattern_value(pattern), scrutinee_type);
    const key: u32 = @intFromEnum(key_ref);

    // a key goes to the first arm listing it
    var i = mark + 1;
    while (i < self.scratch.len) : (i += 2) if (self.scratch.buffer[i] == key) return;
    self.scratch.push(key);
    self.scratch.push(arm_block);
}

fn static_pattern_value(self: *HighLowerer, pattern: NodeId) Index {
    if (self.static_value_of(pattern)) |value| return value;
    return self.resolver.static_values.literal_value(pattern, false);
}

fn emit_switch(
    self: *HighLowerer,
    scrutinee: Ref,
    tagged: bool,
    default_block: u32,
    mark: u32,
) void {
    const cases = self.scratch.buffer[mark..self.scratch.len];
    const key = if (tagged) blk: {
        const key_type = self.type_of_ref(@enumFromInt(cases[1]));
        break :blk self.builder.emit_refs(.variant_tag, key_type, scrutinee, .none);
    } else scrutinee;

    if (key.is_const()) {
        var target = default_block;
        var i: usize = 1;
        while (i < cases.len) : (i += 2) {
            if (cases[i] == @intFromEnum(key)) target = cases[i + 1];
        }
        return self.builder.branch(target);
    }

    if (self.builder.is_unreachable) return;
    self.builder.add_edge(default_block);
    var i: usize = 2;
    while (i < cases.len) : (i += 2) self.builder.add_edge(cases[i]);
    _ = self.builder.emit(.@"switch", .unit_type, @intFromEnum(key), self.builder.list(cases));
}

// binds the names of a pattern its switch arm already matched
fn bind_pattern(self: *HighLowerer, pattern: NodeId, value: Ref, value_type: Index) void {
    switch (self.resolver.tree.kind(pattern)) {
        .identifier => {
            if (self.resolver.name_pool.name_of_node(pattern) == .underscore) return;
            self.declare_variable(self.declaration_of(pattern), value);
        },
        .labelarrow => self.bind_arrow_label(pattern, value, value_type),
        .fun_call => self.bind_payload_fields(pattern, value, value_type),
        else => {},
    }
}

fn bind_arrow_label(self: *HighLowerer, pattern: NodeId, value: Ref, value_type: Index) void {
    const label = self.resolver.tree.arg(pattern, 1);
    const case_type = self.type_of(self.resolver.tree.arg(pattern, 0));
    if (self.static_pool.tag(case_type) != .variant_case_type) return self.bind_label(label, value);

    const variant = self.static_pool.get(case_type).variant_case_type.variant;
    const narrowed = self.narrow_to_variant(value, value_type, variant);
    self.bind_label(label, self.case_payload(narrowed, case_type));
}

fn bind_payload_fields(self: *HighLowerer, pattern: NodeId, value: Ref, value_type: Index) void {
    const case_type = self.static_pool.get(self.type_of(pattern)).variant_case_type;
    const record = case_type.payload;
    if (record == .none or self.static_pool.tag(record) != .record_type) return;

    const narrowed = self.narrow_to_variant(value, value_type, case_type.variant);
    const case_index: Ref = @enumFromInt(case_type.case_index);
    const payload = self.builder.emit_refs(.variant_payload, record, narrowed, case_index);
    const arguments = self.resolver.tree.manychildren(self.resolver.tree.arg(pattern, 1));
    for (arguments, 0..) |argument, i| {
        const field = self.field_index(record, argument, i);
        const field_type = self.static_pool.field_type(record, field);
        const field_value = self.builder.emit(.extract, field_type, @intFromEnum(payload), field);
        self.bind_pattern(self.resolver.tree.arg_value(argument), field_value, field_type);
    }
}

// tests `value` against `pattern`, binding its names, and continues in `matched` or `failed`
fn match_pattern(
    self: *HighLowerer,
    pattern: NodeId,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    const tree = self.resolver.tree;
    const pattern_type = self.type_of(pattern);
    switch (tree.kind(pattern)) {
        .identifier => {
            if (self.resolver.name_pool.name_of_node(pattern) != .underscore) {
                self.declare_variable(self.declaration_of(pattern), value);
            }
            self.builder.branch(matched);
        },
        .partial__match_case_pattern_or => {
            for (tree.manychildren(pattern)) |alternative| {
                const next_alternative = self.builder.new_block();
                self.match_pattern(alternative, value, value_type, matched, next_alternative);
                self.builder.go_to(next_alternative);
            }
            self.builder.branch(failed);
        },
        .partial__match_case_pattern_typecast => {
            self.match_type(pattern, value, value_type, matched, failed);
        },
        .labelarrow => {
            const labelled_matched = self.builder.new_block();
            const labelled = tree.arg(pattern, 0);
            self.match_pattern(labelled, value, value_type, labelled_matched, failed);
            self.builder.go_to(labelled_matched);
            self.bind_arrow_label(pattern, value, value_type);
            self.builder.branch(matched);
        },
        .fun_call => {
            self.match_destructuring(pattern, pattern_type, value, value_type, matched, failed);
        },
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => {
            self.match_range(pattern, value, value_type, matched, failed);
        },
        else => self.match_value(pattern, pattern_type, value, value_type, matched, failed),
    }
}

// `x as T` in a pattern: binds the value seen as `T` when it is one
fn match_type(
    self: *HighLowerer,
    pattern: NodeId,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    const binding = self.resolver.tree.arg(pattern, 1);
    const target_type = self.type_of(binding);
    const narrowed = self.narrow_to_type(value, value_type, target_type, failed) orelse {
        return self.builder.branch(failed);
    };
    self.declare_variable(self.declaration_of(binding), narrowed);
    self.builder.branch(matched);
}

// `value` as `target_type` after tests branching to `failed`, null when it never is one
fn narrow_to_type(
    self: *HighLowerer,
    value: Ref,
    value_type: Index,
    target_type: Index,
    failed: u32,
) ?Ref {
    const is_union = value_type != .none and
        self.static_pool.tag(value_type) == .variant_union_type;
    if (is_union and self.static_pool.tag(target_type) == .variant_type) {
        return self.narrow_to_union_member(value, value_type, target_type, failed);
    }
    const converts = value_type == target_type or
        self.static_pool.coercion(value_type, target_type) != .incompatible;
    if (converts) return self.coerce(value, value_type, target_type);

    const is_case = self.static_pool.tag(target_type) == .variant_case_type;
    if (is_case and self.can_hold_case(value_type, target_type)) {
        const is_that_case = self.builder.new_block();
        const test_case = self.tests_case(value, value_type, target_type);
        self.builder.branch_if(test_case, is_that_case, failed);
        self.builder.go_to(is_that_case);
        const variant = self.static_pool.get(target_type).variant_case_type.variant;
        return self.narrow_to_variant(value, value_type, variant);
    }

    if (value_type != .none and self.static_pool.tag(value_type) == .trait_type) {
        const implements = self.builder.new_block();
        const target = @intFromEnum(target_type);
        const test_type = self.builder.emit(.type_test, .bool_type, @intFromEnum(value), target);
        self.builder.branch_if(test_type, implements, failed);
        self.builder.go_to(implements);
        const trait_narrow = @intFromEnum(StaticPool.CastKind.trait_narrow);
        return self.builder.emit(.cast, target_type, @intFromEnum(value), trait_narrow);
    }
    return null;
}

// the member's tags are a range of the union's tags
fn narrow_to_union_member(
    self: *HighLowerer,
    value: Ref,
    union_type: Index,
    member: Index,
    failed: u32,
) Ref {
    const union_tag_type = self.static_pool.union_tag_type(union_type);
    const tag = self.builder.emit_refs(.variant_tag, union_tag_type, value, .none);
    const low = self.static_pool.union_offset(union_type, member);
    const above_low = self.builder.new_block();
    const in_range = self.builder.new_block();

    const low_tag = self.builder.constant_int(union_tag_type, low);
    const is_above_low = self.builder.emit_refs(.ge, .bool_type, tag, low_tag);
    self.builder.branch_if(is_above_low, above_low, failed);
    self.builder.go_to(above_low);

    const end = low + self.static_pool.tag_range(member);
    const end_tag = self.builder.constant_int(union_tag_type, end);
    const is_below_end = self.builder.emit_refs(.lt, .bool_type, tag, end_tag);
    self.builder.branch_if(is_below_end, in_range, failed);
    self.builder.go_to(in_range);
    return self.narrow_to_variant(value, union_type, member);
}

// `Case(..)` or `Record(..)` in a pattern: matches the case, then each field against its pattern
fn match_destructuring(
    self: *HighLowerer,
    pattern: NodeId,
    pattern_type: Index,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    const is_case = self.static_pool.tag(pattern_type) == .variant_case_type;
    if (is_case and !self.can_hold_case(value_type, pattern_type)) {
        return self.builder.branch(failed);
    }
    if (is_case) {
        const case_matched = self.builder.new_block();
        const test_case = self.tests_case(value, value_type, pattern_type);
        self.builder.branch_if(test_case, case_matched, failed);
        self.builder.go_to(case_matched);
    }

    const record = if (is_case)
        self.static_pool.get(pattern_type).variant_case_type.payload
    else
        pattern_type;
    const container = if (is_case)
        self.case_payload_record(value, value_type, pattern_type)
    else
        value;
    if (record != .none and self.static_pool.tag(record) == .record_type) {
        self.match_fields(pattern, record, container, failed);
    }
    self.builder.branch(matched);
}

fn case_payload_record(self: *HighLowerer, value: Ref, value_type: Index, case: Index) Ref {
    const case_type = self.static_pool.get(case).variant_case_type;
    const narrowed = self.narrow_to_variant(value, value_type, case_type.variant);
    const case_index: Ref = @enumFromInt(case_type.case_index);
    return self.builder.emit_refs(.variant_payload, case_type.payload, narrowed, case_index);
}

fn match_fields(
    self: *HighLowerer,
    pattern: NodeId,
    record: Index,
    container: Ref,
    failed: u32,
) void {
    const arguments = self.resolver.tree.manychildren(self.resolver.tree.arg(pattern, 1));
    for (arguments, 0..) |argument, i| {
        const field = self.field_index(record, argument, i);
        const field_type = self.static_pool.field_type(record, field);
        const field_matched = self.builder.new_block();
        const field_value = self.builder.emit(.extract, field_type, @intFromEnum(container), field);
        const field_pattern = self.resolver.tree.arg_value(argument);
        self.match_pattern(field_pattern, field_value, field_type, field_matched, failed);
        self.builder.go_to(field_matched);
    }
}

fn match_range(
    self: *HighLowerer,
    pattern: NodeId,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    const range = ParseTree.Range.from_node(self.resolver.tree, pattern);
    if (range.lo != 0) {
        const above_low = self.builder.new_block();
        const low = self.expression_as(range.lo, value_type);
        const is_above_low = self.builder.emit_refs(.ge, .bool_type, value, low);
        self.builder.branch_if(is_above_low, above_low, failed);
        self.builder.go_to(above_low);
    }
    if (range.hi == 0) return self.builder.branch(matched);

    const high = self.expression_as(range.hi, value_type);
    const operation: Op = if (range.incl) .le else .lt;
    const is_below_high = self.builder.emit_refs(operation, .bool_type, value, high);
    self.builder.branch_if(is_below_high, matched, failed);
}

fn match_value(
    self: *HighLowerer,
    pattern: NodeId,
    pattern_type: Index,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    if (self.static_pool.tag(pattern_type) == .variant_case_type) {
        if (!self.can_hold_case(value_type, pattern_type)) return self.builder.branch(failed);
        const test_case = self.tests_case(value, value_type, pattern_type);
        return self.builder.branch_if(test_case, matched, failed);
    }

    const expected = self.expression_as(pattern, value_type);
    // strings and byte pointers compare their bytes, not their addresses
    const is_text = self.resolver.tree.kind(pattern) == .string or
        (self.is_pointer(value_type) and self.pointee_of(value_type) == .u8_type);
    const operation: Op = if (is_text) .bytes_eq else .eq;
    const equals = self.builder.emit_refs(operation, .bool_type, value, expected);
    self.builder.branch_if(equals, matched, failed);
}

// a payload of one field stands for that field
fn case_payload(self: *HighLowerer, value: Ref, case: Index) Ref {
    const case_type = self.static_pool.get(case).variant_case_type;
    if (case_type.payload == .none) return value;
    const case_index: Ref = @enumFromInt(case_type.case_index);
    const payload = self.builder.emit_refs(.variant_payload, case_type.payload, value, case_index);
    const fields = self.static_pool.get(case_type.payload).record_type.field_types;
    if (fields.len == 1) return self.builder.emit(.extract, fields[0], @intFromEnum(payload), 0);
    return payload;
}

fn bind_label(self: *HighLowerer, label: NodeId, value: Ref) void {
    if (self.resolver.tree.kind(label) != .partial__destructure) {
        return self.declare_variable(self.declaration_of(label), value);
    }
    for (self.resolver.tree.manychildren(label), 0..) |name, i| {
        const part_type = self.type_of(name);
        const part = self.builder.emit(.extract, part_type, @intFromEnum(value), @intCast(i));
        self.declare_variable(self.declaration_of(name), part);
    }
}

// `<-` binds a label, `?<-` tests for the payload and binds it, `??` takes it or the fallback
fn unwrap(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const kind = tree.kind(node);
    const result_type = self.type_of(node);
    const value = self.expression(tree.arg(node, 0));
    const value_type = self.static_pool.through_pointer(self.type_of(tree.arg(node, 0)));
    if (kind == .labelarrow) {
        self.bind_label(tree.arg(node, 1), value);
        return value;
    }

    if (self.static_pool.tag(value_type) != .variant_type) return .none;
    const cases = self.static_pool.get(value_type).variant_type.cases;
    const case = cases[self.payload_case_index(value_type)];
    const has_payload = self.tests_case(value, value_type, case);
    if (kind == .selftag_arrow) {
        self.bind_label(tree.arg(node, 1), self.case_payload(value, case));
        return has_payload;
    }

    const payload_block = self.builder.new_block();
    const empty_block = self.builder.new_block();
    self.builder.branch_if(has_payload, payload_block, empty_block);
    if (kind == .selftag_unwrap) {
        self.builder.go_to(empty_block);
        self.emit_unreachable();
        self.builder.go_to(payload_block);
        return self.case_payload(value, case);
    }

    const result = self.new_temporary(result_type);
    const merge = self.builder.new_block();
    self.builder.go_to(payload_block);
    const payload = self.case_payload(value, case);
    const payload_type = self.static_pool.payload_of(value_type);
    self.write_current(result, self.coerce(payload, payload_type, result_type));
    self.builder.branch(merge);
    self.builder.go_to(empty_block);
    self.arm_into(tree.arg(node, 1), result_type, result, merge);
    self.builder.go_to(merge);
    if (self.builder.is_unreachable) return .none;
    return self.read_current(result);
}

// loops

// a loop of an array type collects the values of its body into that array
fn loop(self: *HighLowerer, node: NodeId) Ref {
    if (self.builder.is_unreachable) return .none;
    const kind = self.resolver.tree.kind(node);
    const result_type = self.type_of(node);
    const static_length = self.static_pool.static_length(result_type);
    var collected: Ref = if (static_length != null) self.alloca(result_type) else .none;
    const capacity: u64 = static_length orelse 0;
    const collects_dynamic = self.is_dynamic_array(result_type);
    const count = self.new_temporary(.u64_type);
    self.write_current(count, self.builder.constant_int(.u64_type, 0));

    const head = self.builder.new_block();
    const body_block = self.builder.new_block();
    const next = self.builder.new_block();
    const exit = self.builder.new_block();

    const parts = ParseTree.Loop.from_node(self.resolver.tree, node);
    var repeat: NodeId = 0;
    var walk: SequenceWalk = .{};
    switch (kind) {
        .@"while", .stcwhile, .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => {
            repeat = parts.repeat;
            self.enter_loop_head(head);
            self.builder.branch_if(self.expression_as(parts.cond, .bool_type), body_block, exit);
        },
        // the repeat statement of a `loop` runs before each iteration
        .loop, .stcloop, .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => {
            self.enter_loop_head(head);
            if (parts.repeat != 0) _ = self.expression(parts.repeat);
            self.builder.branch(body_block);
        },
        .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq => {
            walk = self.enter_for_head(parts, .{
                .sequence = parts.seq,
                .sequence_type = .none,
                .result_type = result_type,
                .collects_dynamic = collects_dynamic,
                .collected = &collected,
                .blocks = .{ .head = head, .body = body_block, .next = next, .exit = exit },
            });
        },
        else => unreachable,
    }

    self.builder.go_to(body_block);
    if (walk.element != .none) self.declare_variable(walk.element, self.next_element(walk));
    self.loops.push(.{ .break_block = exit, .continue_block = next, .defers = self.defers.len });
    const value = self.expression(parts.body);
    const collects = collected != .none and !self.builder.is_unreachable and
        has_value(self.type_of(parts.body));
    if (collects) {
        const value_type = self.type_of(parts.body);
        self.collect(value, value_type, .{
            .array = collected,
            .array_type = result_type,
            .count = count,
            .is_dynamic = collects_dynamic,
            .capacity = capacity,
            .exit = exit,
        });
    }
    self.loops.len -= 1;

    self.branch_and_enter(next);
    if (repeat != 0) _ = self.expression(repeat);
    if (walk.counter != none) self.step_counter(walk.counter, walk.counter_type);
    self.builder.branch(head);
    self.builder.seal(head);
    self.builder.go_to(exit);
    return self.loop_result(result_type, collected, collects_dynamic, count);
}

// the head stays unsealed: the edge back from the end of the body comes later
fn enter_loop_head(self: *HighLowerer, head: u32) void {
    self.builder.branch(head);
    self.builder.enter(head);
}

fn enter_for_head(self: *HighLowerer, parts: ParseTree.Loop, unfinished: ForLoop) SequenceWalk {
    const element_node = if (parts.variable != 0) parts.variable else parts.head;
    var walk: SequenceWalk = .{ .element = self.declaration_of(element_node) };
    var for_loop = unfinished;
    for_loop.sequence_type = self.type_of(for_loop.sequence);

    const array_type = self.dereferenced_type(for_loop.sequence_type);
    if (self.resolver.tree.props(for_loop.sequence).range) {
        self.enter_range_head(for_loop, &walk);
    } else if (self.static_pool.get(array_type) == .array_type) {
        self.enter_array_head(for_loop, &walk);
    } else {
        self.enter_iterator_head(for_loop, &walk);
    }
    return walk;
}

fn enter_range_head(self: *HighLowerer, for_loop: ForLoop, walk: *SequenceWalk) void {
    const range = ParseTree.Range.from_node(self.resolver.tree, for_loop.sequence);
    const element_type = self.static_pool.get(for_loop.sequence_type).array_type.element;
    const counter = self.new_temporary(element_type);
    const start = if (range.lo != 0)
        self.expression_as(range.lo, element_type)
    else
        self.builder.constant_int(element_type, 0);
    // written where the bound ends up, a bound that branches ends in a later block than it began
    self.builder.write_variable(counter, self.builder.current_block, start);
    const end: Ref = if (range.hi == 0) .none else self.expression_as(range.hi, element_type);

    if (for_loop.collects_dynamic and end != .none) {
        const low = self.read_current(counter);
        var span = self.builder.emit_refs(.sub, element_type, end, low);
        if (range.incl) {
            const one = self.builder.constant_int(element_type, 1);
            span = self.builder.emit_refs(.add, element_type, span, one);
        }
        const length = self.to_u64(span, element_type);
        for_loop.collected.* = self.dynamic_alloca(for_loop.result_type, length);
    }

    self.enter_loop_head(for_loop.blocks.head);
    const current = self.read_current(counter);
    if (end != .none) {
        const operation: Op = if (range.incl) .le else .lt;
        const in_range = self.builder.emit_refs(operation, .bool_type, current, end);
        self.builder.branch_if(in_range, for_loop.blocks.body, for_loop.blocks.exit);
    } else {
        self.builder.branch(for_loop.blocks.body);
    }
    walk.counter = counter;
    walk.counter_type = element_type;
}

fn enter_array_head(self: *HighLowerer, for_loop: ForLoop, walk: *SequenceWalk) void {
    const sequence_type = for_loop.sequence_type;
    const array_type = self.dereferenced_type(sequence_type);
    const element_type = self.static_pool.get(array_type).array_type.element;
    const by_value = self.is_pointer(sequence_type) or self.is_dynamic_array(sequence_type);
    const array = if (by_value)
        self.expression(for_loop.sequence)
    else
        self.place(for_loop.sequence);
    const length_value = self.static_pool.get(array_type).array_type.length;
    const length: Ref = if (self.static_pool.tag(length_value) == .int_value)
        self.builder.constant_int(.u64_type, self.static_pool.get(length_value).int_value.bits)
    else
        self.builder.emit_refs(.len, .u64_type, array, .none);
    const counter = self.new_temporary(.u64_type);
    self.write_current(counter, self.builder.constant_int(.u64_type, 0));
    if (for_loop.collects_dynamic) {
        for_loop.collected.* = self.dynamic_alloca(for_loop.result_type, length);
    }

    self.enter_loop_head(for_loop.blocks.head);
    const current = self.read_current(counter);
    const in_range = self.builder.emit_refs(.lt, .bool_type, current, length);
    self.builder.branch_if(in_range, for_loop.blocks.body, for_loop.blocks.exit);
    walk.sequence = array;
    walk.sequence_type = element_type;
    walk.counter = counter;
    walk.counter_type = .u64_type;
}

fn enter_iterator_head(self: *HighLowerer, for_loop: ForLoop, walk: *SequenceWalk) void {
    const iterator = if (self.is_pointer(for_loop.sequence_type))
        self.expression(for_loop.sequence)
    else
        self.place(for_loop.sequence);
    const iterator_type = self.static_pool.through_pointer(for_loop.sequence_type);
    self.enter_loop_head(for_loop.blocks.head);
    const has_next = self.method_call(iterator_type, .has_next, iterator);
    self.builder.branch_if(has_next, for_loop.blocks.body, for_loop.blocks.exit);
    walk.sequence = iterator;
    walk.sequence_type = iterator_type;
}

// an alloca with a length, for the elements of a dynamic array
fn dynamic_alloca(self: *HighLowerer, array_type: Index, length: Ref) Ref {
    const element_pointer = self.pointer_to(self.static_pool.get(array_type).array_type.element);
    return self.builder.emit_refs(.alloca, element_pointer, length, .none);
}

fn next_element(self: *HighLowerer, walk: SequenceWalk) Ref {
    if (walk.counter == none) return self.method_call(walk.sequence_type, .next, walk.sequence);
    if (walk.sequence == .none) return self.read_current(walk.counter);
    const element_pointer = self.pointer_to(walk.sequence_type);
    const index = self.read_current(walk.counter);
    const pointer = self.builder.emit_refs(.index_ptr, element_pointer, walk.sequence, index);
    return self.load(walk.sequence_type, pointer);
}

// stores the body's value at `count` and counts it, a fixed-size array ends the loop once full
fn collect(self: *HighLowerer, value: Ref, value_type: Index, collection: Collection) void {
    const index = self.read_current(collection.count);
    const element_type = self.static_pool.get(collection.array_type).array_type.element;
    const element_pointer = self.pointer_to(element_type);
    const slot = self.builder.emit_refs(.index_ptr, element_pointer, collection.array, index);
    self.store(slot, self.coerce(value, value_type, element_type));
    const one = self.builder.constant_int(.u64_type, 1);
    const new_count = self.builder.emit_refs(.add, .u64_type, index, one);
    self.write_current(collection.count, new_count);
    if (collection.is_dynamic) return;

    const has_room = self.builder.new_block();
    const full = self.builder.constant_int(.u64_type, collection.capacity);
    const is_below_full = self.builder.emit_refs(.lt, .bool_type, new_count, full);
    self.builder.branch_if(is_below_full, has_room, collection.exit);
    self.builder.go_to(has_room);
}

fn step_counter(self: *HighLowerer, counter: u32, counter_type: Index) void {
    const current = self.read_current(counter);
    const one = self.builder.constant_int(counter_type, 1);
    self.write_current(counter, self.builder.emit_refs(.add, counter_type, current, one));
}

fn loop_result(
    self: *HighLowerer,
    result_type: Index,
    collected: Ref,
    collects_dynamic: bool,
    count: u32,
) Ref {
    if (collected == .none) return unit();
    if (!collects_dynamic) return self.load(result_type, collected);

    const start = self.builder.constant_int(.u64_type, 0);
    const end = self.read_current(count);
    const bounds = self.builder.list(&.{ @intFromEnum(start), @intFromEnum(end) });
    return self.builder.emit(.dyn, result_type, @intFromEnum(collected), bounds);
}

// pointers and casts

// offsets are i64 or u64, a subtraction negates the offset
fn offset_pointer(
    self: *HighLowerer,
    pointer_type: Index,
    base: Ref,
    subtracts: bool,
    offset: Ref,
) Ref {
    const offset_type = self.type_of_ref(offset);
    const resize = @intFromEnum(StaticPool.CastKind.int_resize);
    const wide = if (offset_type == .i64_type or offset_type == .u64_type)
        offset
    else
        self.builder.emit(.cast, .i64_type, @intFromEnum(offset), resize);
    const signed_offset = if (subtracts)
        self.builder.emit_refs(.neg, self.type_of_ref(wide), wide, .none)
    else
        wide;
    return self.builder.emit_refs(.index_ptr, pointer_type, base, signed_offset);
}

// a narrowed array or relengthed pointer is the pointer to its first element, seen as shorter
fn narrowing_cast(self: *HighLowerer, node: NodeId, target_type: Index) Ref {
    const operand = self.resolver.tree.arg(node, 0);
    const array_type = self.static_pool.pointee(target_type);
    const range = self.resolver.tree.narrowed(self.resolver.tree.arg(node, 1));
    const start = if (range != 0) self.static_value_of(range) else null;
    const base = if (self.is_pointer(self.type_of(operand)))
        self.expression(operand)
    else
        self.place(operand);
    const mutable = !self.is_pointer(self.type_of(operand)) or
        self.static_pool.get(self.type_of(operand)).pointer_type.is_mutable;
    const array_pointer_type = if (self.is_pointer(target_type))
        target_type
    else
        self.static_pool.pointer_to(array_type, mutable);

    const element_type = self.static_pool.get(array_type).array_type.element;
    const element_pointer = self.static_pool.pointer_to(element_type, mutable);
    const start_index = if (start) |value| self.static_pool.get(value).int_value.bits else 0;
    const index = self.builder.constant_int(.u64_type, start_index);
    const first = self.builder.emit_refs(.index_ptr, element_pointer, base, index);
    const relength = @intFromEnum(StaticPool.CastKind.pointer_relength);
    const pointer = self.builder.emit(.cast, array_pointer_type, @intFromEnum(first), relength);
    if (self.is_pointer(target_type)) return pointer;
    return self.load(target_type, pointer);
}

fn to_u64(self: *HighLowerer, value: Ref, value_type: Index) Ref {
    if (value_type == .u64_type) return value;
    const resize = @intFromEnum(StaticPool.CastKind.int_resize);
    return self.builder.emit(.cast, .u64_type, @intFromEnum(value), resize);
}

// calls

fn method_call(
    self: *HighLowerer,
    receiver_type: Index,
    name: NamePool.Index,
    receiver: Ref,
) Ref {
    return switch (self.static_pool.lookup_member(receiver_type, name)) {
        .method => |method| {
            const return_type = self.return_type_of(method);
            const callee = self.function_value(method);
            const arguments = self.builder.list(&.{@intFromEnum(receiver)});
            return self.builder.emit(.call, return_type, @intFromEnum(callee), arguments);
        },
        else => .none,
    };
}

fn return_type_of(self: *HighLowerer, function: DeclPool.Index) Index {
    const realized = self.resolver.declarations.realized(function);
    const function_type = self.substituted(self.resolver.decl_pool.get(realized, .value_type));
    if (function_type == .none) return .unit_type;
    if (self.static_pool.tag(function_type) != .function_type) return .unit_type;
    return self.static_pool.get(function_type).function_type.return_type;
}

fn call(self: *HighLowerer, node: NodeId, result_type: Index) Ref {
    const tree = self.resolver.tree;
    const callee = tree.arg(node, 0);
    const arguments = tree.manychildren(tree.arg(node, 1));
    if (self.realized_function(node)) |function| return self.function_value(function);

    const declaration = self.declaration_of(node);
    if (declaration != .none and self.resolver.decl_pool.get(declaration, .kind).is_function()) {
        return self.direct_call(declaration, callee, arguments, result_type);
    }
    if (declaration == .none and tree.kind(callee) == .member) {
        const receiver_type = self.type_of(tree.arg(callee, 0));
        switch (self.resolver.calls.builtin_member_of(callee, receiver_type, result_type)) {
            .builtin_init => return self.default_value(result_type),
            .builtin_deinit => return unit(),
            else => {},
        }
    }

    // calling a type or a case constructs a value of it
    const callee_type = self.type_of(callee);
    const callee_tag = self.static_pool.tag(callee_type);
    if (callee_tag == .meta_type or callee_tag == .variant_case_type) {
        return self.construct(result_type, arguments);
    }
    return self.indirect_call(callee, callee_type, arguments, result_type);
}

fn indirect_call(
    self: *HighLowerer,
    callee: NodeId,
    callee_type: Index,
    arguments: []const NodeId,
    result_type: Index,
) Ref {
    const function = self.expression(callee);
    const mark = self.scratch.len;
    for (arguments, 0..) |argument, i| {
        const target_type = self.parameter_type(callee_type, i);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), target_type);
        self.scratch.push(@intFromEnum(value));
    }
    const argument_list = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    return self.builder.emit(.call, result_type, @intFromEnum(function), argument_list);
}

// a stcfun call producing a function stands for its realization
fn realized_function(self: *HighLowerer, node: NodeId) ?DeclPool.Index {
    if (self.resolver.tree.kind(node) != .fun_call) return null;
    const callee = self.declaration_of(self.resolver.tree.arg(node, 0));
    if (callee == .none) return null;
    if (self.resolver.decl_pool.get(callee, .kind) != .static_function) return null;
    const realization = self.declaration_of(node);
    if (realization == .none) return null;
    return realization;
}

// the arguments are the captures, the receiver, then the parameters in declared order
fn direct_call(
    self: *HighLowerer,
    declaration: DeclPool.Index,
    callee: NodeId,
    all_arguments: []const NodeId,
    result_type: Index,
) Ref {
    const realized = self.resolver.declarations.realized(declaration);
    const function = self.ensure_function(realized);
    const head = self.ir.functions.column(.decl)[function];
    const function_ref = Ref.of(self.static_pool.intern(.{ .function_value = head }));
    const function_type = self.substituted(self.resolver.decl_pool.get(realized, .value_type));
    const implicit_self_count = self.resolver.decl_pool.implicit_self_count(realized);
    const value_node = self.resolver.declarations.value_node(realized);
    const parameter_nodes = self.resolver.tree.params_of(value_node);

    const mark = self.scratch.len;
    self.push_captures(self.resolver.bodies.captures_of(&self.resolver.decl_pool, head));
    var arguments = all_arguments;
    var dispatches_dynamically = false;
    if (implicit_self_count == 1) {
        const receiver = self.push_receiver(callee, arguments, function_type);
        if (!receiver.is_bound) arguments = arguments[1..];
        // a trait method called on a trait object is looked up at run time
        dispatches_dynamically = self.resolver.decl_pool.get(realized, .kind) == .trait_member and
            self.is_trait_object(receiver.node);
    }

    const parameters_at = self.scratch.len;
    for (parameter_nodes) |_| self.scratch.push(none);
    for (arguments, 0..) |argument, i| {
        const parameter_index = self.parameter_index_of(argument, parameter_nodes, i);
        const parameter_position = parameter_index + implicit_self_count;
        const target_type = self.parameter_type(function_type, parameter_position);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), target_type);
        self.scratch.buffer[parameters_at + parameter_index] = @intFromEnum(value);
    }
    self.declare_call_parameters(realized, parameter_nodes, .{
        .function_type = function_type,
        .implicit_self_count = implicit_self_count,
        .parameters_at = parameters_at,
    });

    const argument_list = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    const op: Op = if (dispatches_dynamically) .call_dyn else .call;
    const call_type = if (result_type == .none) self.return_type_of(realized) else result_type;
    return self.builder.emit(op, call_type, @intFromEnum(function_ref), argument_list);
}

fn is_trait_object(self: *HighLowerer, node: NodeId) bool {
    const receiver_type = self.static_pool.through_pointer(self.type_of(node));
    return self.static_pool.tag(receiver_type) == .trait_type;
}

// `value.method()` passes the receiver by address, `Type.method(value)` as its first argument
fn push_receiver(
    self: *HighLowerer,
    callee: NodeId,
    arguments: []const NodeId,
    function_type: Index,
) Receiver {
    const tree = self.resolver.tree;
    const is_bound = tree.kind(callee) == .member and
        self.static_pool.tag(self.type_of(tree.arg(callee, 0))) != .meta_type;
    const receiver = if (is_bound) tree.arg(callee, 0) else tree.arg_value(arguments[0]);
    const value = if (!is_bound)
        self.expression_as(receiver, self.parameter_type(function_type, 0))
    else if (self.is_pointer(self.type_of(receiver)))
        self.expression(receiver)
    else
        self.place(receiver);
    self.scratch.push(@intFromEnum(value));
    return .{ .node = receiver, .is_bound = is_bound };
}

fn parameter_index_of(
    self: *HighLowerer,
    argument: NodeId,
    parameter_nodes: []const NodeId,
    position: usize,
) usize {
    const name_node = self.resolver.tree.arg_name(argument);
    if (name_node == 0) return position;
    const name = self.resolver.name_pool.name_of_node(name_node);
    return self.resolver.declarations.parameter_index(parameter_nodes, name) orelse position;
}

const CallParameters = struct {
    function_type: Index,
    implicit_self_count: usize,
    // where the argument of the first parameter is in scratch, `none` for those not passed
    parameters_at: u32,
};

// defaults are expressions of the callee's body and may read the parameters before them
fn declare_call_parameters(
    self: *HighLowerer,
    realized: DeclPool.Index,
    parameter_nodes: []const NodeId,
    call_parameters: CallParameters,
) void {
    const saved_body = self.body;
    if (self.resolver.bodies.body_of(realized)) |body| self.body = body;
    const at = call_parameters.parameters_at;

    for (parameter_nodes, 0..) |parameter_node, j| {
        const passed = self.scratch.buffer[at + j];
        if (passed == none) continue;
        self.declare_variable(self.declaration_of(parameter_node), @enumFromInt(passed));
    }
    for (parameter_nodes, 0..) |parameter_node, j| {
        if (self.scratch.buffer[at + j] != none) continue;
        const default = ParseTree.Param.from_node(self.resolver.tree, parameter_node).default;
        const parameter_position = j + call_parameters.implicit_self_count;
        const function_type = call_parameters.function_type;
        const value = if (default != 0)
            self.expression_as(default, self.parameter_type(function_type, parameter_position))
        else
            Ref.none;
        self.declare_variable(self.declaration_of(parameter_node), value);
        self.scratch.buffer[at + j] = @intFromEnum(value);
    }
    self.body = saved_body;
}

// records

fn construct(self: *HighLowerer, target_type: Index, arguments: []const NodeId) Ref {
    const pool = self.static_pool;
    const is_case = pool.tag(target_type) == .variant_case_type;
    const variant = if (is_case) pool.get(target_type).variant_case_type.variant else target_type;
    const record = if (is_case) pool.get(target_type).variant_case_type.payload else target_type;
    const case_index: u32 = if (is_case) pool.get(target_type).variant_case_type.case_index else 0;
    if (record == .none) {
        return self.builder.emit(.variant_make, variant, case_index, @intFromEnum(Ref.none));
    }

    const mark = self.scratch.len;
    for (self.resolver.types.field_nodes_of(record)) |_| self.scratch.push(none);
    self.place_field_arguments(record, arguments, mark);
    const aggregate = self.finish_record(record, mark);
    if (!is_case) return aggregate;
    return self.builder.emit(.variant_make, variant, case_index, @intFromEnum(aggregate));
}

// `base with (field = ..)`: the fields of `base`, the named ones replaced
fn record_update(self: *HighLowerer, node: NodeId) Ref {
    var base_type = self.type_of(self.resolver.tree.arg(node, 0));
    var base = self.expression(self.resolver.tree.arg(node, 0));
    if (self.is_pointer(base_type)) {
        base = self.load(self.pointee_of(base_type), base);
        base_type = self.pointee_of(base_type);
    }

    const field_count = self.static_pool.get(base_type).record_type.field_types.len;
    const mark = self.scratch.len;
    for (0..field_count) |i| {
        const field_type = self.static_pool.field_type(base_type, i);
        const field = self.builder.emit(.extract, field_type, @intFromEnum(base), @intCast(i));
        self.scratch.push(@intFromEnum(field));
    }
    const arguments = self.resolver.tree.manychildren(self.resolver.tree.arg(node, 1));
    self.place_field_arguments(base_type, arguments, mark);
    return self.finish_record(base_type, mark);
}

fn place_field_arguments(
    self: *HighLowerer,
    record: Index,
    arguments: []const NodeId,
    mark: u32,
) void {
    for (arguments, 0..) |argument, i| {
        const field = self.field_index(record, argument, i);
        const field_type = self.static_pool.field_type(record, field);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), field_type);
        self.scratch.buffer[mark + field] = @intFromEnum(value);
    }
}

fn finish_record(self: *HighLowerer, record: Index, mark: u32) Ref {
    self.complete_fields(record, mark);
    const fields = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    return self.builder.emit(.aggregate, record, 0, fields);
}

// defaults and `where .. else` guards are expressions of the type's body, its locals the fields
fn complete_fields(self: *HighLowerer, record: Index, mark: u32) void {
    const fields = self.resolver.types.field_nodes_of(record);
    const saved_body = self.body;
    defer self.body = saved_body;
    const record_declaration = self.static_pool.get(record).record_type.declaration;
    const record_body = self.resolver.bodies.body_of(record_declaration);
    if (record_body) |body| self.body = body;

    var locals = FieldSet.initEmpty(self.allocator, fields.len) catch @panic("OOM");
    defer locals.deinit(self.allocator);
    var guarded = FieldSet.initEmpty(self.allocator, fields.len) catch @panic("OOM");
    defer guarded.deinit(self.allocator);
    if (record_body != null) self.mark_field_locals(fields, mark, &locals, &guarded);

    self.declare_given_fields(fields.len, &locals, mark);
    self.default_missing_fields(record, fields, &locals, mark);
    self.repair_guarded_fields(record, fields, &guarded);
    for (0..fields.len) |i| {
        if (!guarded.isSet(i)) continue;
        self.scratch.buffer[mark + i] = @intFromEnum(self.load_variable(self.field_local(i)));
    }
}

fn field_local(self: *HighLowerer, field: usize) DeclPool.Index {
    return @enumFromInt(self.body.first_local + field);
}

// only the fields a default or guard reads, or a guard repairs, become locals
fn mark_field_locals(
    self: *HighLowerer,
    fields: []const NodeId,
    mark: u32,
    locals: *FieldSet,
    guarded: *FieldSet,
) void {
    for (fields, 0..) |field, i| {
        const parameter = ParseTree.Param.from_node(self.resolver.tree, field);
        const has_repair = parameter.@"else" != 0;
        if (has_repair) {
            guarded.set(i);
            locals.set(i);
        }
        const default = if (self.scratch.buffer[mark + i] == none) parameter.default else 0;
        const guard = if (has_repair) parameter.where else 0;
        for ([_]NodeId{ default, guard, parameter.@"else" }) |reading| {
            if (reading != 0) self.mark_fields_read_by(reading, fields.len, locals);
        }
    }
}

fn mark_fields_read_by(
    self: *HighLowerer,
    reading: NodeId,
    field_count: usize,
    read: *FieldSet,
) void {
    const subtree = self.resolver.tree.subtree(reading);
    for (subtree[0]..subtree[1]) |i| {
        const node: NodeId = @intCast(i);
        const local = @intFromEnum(self.declaration_of(node)) -% self.body.first_local;
        const is_field = self.resolver.tree.kind(node) == .identifier and local < field_count;
        if (is_field) read.set(local);
    }
}

fn declare_given_fields(
    self: *HighLowerer,
    field_count: usize,
    locals: *const FieldSet,
    mark: u32,
) void {
    for (0..field_count) |i| {
        const given = self.scratch.buffer[mark + i];
        if (!locals.isSet(i) or given == none) continue;
        self.declare_variable(self.field_local(i), @enumFromInt(given));
    }
}

fn default_missing_fields(
    self: *HighLowerer,
    record: Index,
    fields: []const NodeId,
    locals: *const FieldSet,
    mark: u32,
) void {
    for (fields, 0..) |field, i| {
        if (self.scratch.buffer[mark + i] != none) continue;
        const field_type = self.static_pool.field_type(record, i);
        const default = ParseTree.Param.from_node(self.resolver.tree, field).default;
        const value = if (default != 0)
            self.expression_as(default, field_type)
        else
            self.builder.emit(.zeroed, field_type, 0, 0);
        self.scratch.buffer[mark + i] = @intFromEnum(value);
        if (locals.isSet(i)) self.declare_variable(self.field_local(i), value);
    }
}

// a guard's `else` assigns fields or is the field's new value
fn repair_guarded_fields(
    self: *HighLowerer,
    record: Index,
    fields: []const NodeId,
    guarded: *const FieldSet,
) void {
    for (fields, 0..) |field, i| {
        if (!guarded.isSet(i)) continue;
        const parameter = ParseTree.Param.from_node(self.resolver.tree, field);
        if (parameter.where == 0) continue;

        const holds = self.enter_guard_failure(parameter.where);
        const repair = parameter.@"else";
        if (self.resolver.tree.kind(repair) == .assign) {
            _ = self.expression(repair);
        } else {
            const repaired = self.expression_as(repair, self.static_pool.field_type(record, i));
            self.store_variable(self.field_local(i), repaired);
        }
        self.branch_and_enter(holds);
    }
}

// members and places

fn member_access(self: *HighLowerer, node: NodeId) Ref {
    const parent = self.resolver.tree.arg(node, 0);
    const parent_type = self.type_of(parent);
    const name = self.resolver.name_pool.name_of_node(self.resolver.tree.arg(node, 1));
    // a member of a type is looked up in the type it stands for
    const base_type = if (self.static_pool.tag(parent_type) == .meta_type)
        (self.static_value_of(parent) orelse return .none)
    else
        self.static_pool.through_pointer(parent_type);

    return switch (self.static_pool.lookup_member(base_type, name)) {
        .field => |field| {
            return self.member_field(node, parent, parent_type, field.field_type, field.index);
        },
        .case => |case| self.construct(case, &.{}),
        .method => |method| self.function_value(method),
        // a trait's members are declared right after it
        .trait_method => |method| {
            const trait = self.static_pool.get(method.trait).trait_type.declaration;
            return self.function_value(@enumFromInt(@intFromEnum(trait) + 1 + method.index));
        },
        .builtin_len => self.array_length(parent, parent_type),
        .builtin_tag => self.variant_tag_of(parent, parent_type, base_type),
        .none, .builtin_init, .builtin_deinit => .none,
    };
}

// a field of something in memory is loaded from its address rather than extracted from a copy
fn member_field(
    self: *HighLowerer,
    node: NodeId,
    parent: NodeId,
    parent_type: Index,
    field_type: Index,
    field: u32,
) Ref {
    if (self.is_pointer(parent_type) or self.is_place(parent)) {
        return self.load(field_type, self.place(node));
    }
    return self.builder.emit(.extract, field_type, @intFromEnum(self.expression(parent)), field);
}

fn array_length(self: *HighLowerer, array: NodeId, value_type: Index) Ref {
    const array_type = self.dereferenced_type(value_type);
    const length = self.static_pool.get(array_type).array_type.length;
    if (self.static_pool.tag(length) == .int_value) {
        return self.builder.constant_int(.u64_type, self.static_pool.get(length).int_value.bits);
    }
    const by_value = self.is_pointer(value_type) or self.is_dynamic_array(value_type);
    const array_value = if (by_value) self.expression(array) else self.place(array);
    return self.builder.emit_refs(.len, .u64_type, array_value, .none);
}

fn variant_tag_of(self: *HighLowerer, variant: NodeId, value_type: Index, base_type: Index) Ref {
    if (self.static_pool.tag(base_type) == .variant_case_type) {
        return self.tag_constant(base_type, base_type);
    }
    const variant_tag_type = self.static_pool.tag_type_of(base_type);
    const value = if (self.is_pointer(value_type))
        self.load(base_type, self.expression(variant))
    else
        self.expression(variant);
    return self.builder.emit_refs(.variant_tag, variant_tag_type, value, .none);
}

fn is_place(self: *HighLowerer, node: NodeId) bool {
    const tree = self.resolver.tree;
    return switch (tree.kind(node)) {
        .capture => self.is_place(tree.arg(node, 0)),
        .identifier, .identifier_self => {
            const declaration = self.declaration_of(node);
            if (self.global_index_of.contains(declaration)) return true;
            return self.stack_slots.contains(declaration);
        },
        .member => {
            const parent = tree.arg(node, 0);
            return self.is_pointer(self.type_of(parent)) or self.is_place(parent);
        },
        .array_index, .dereference => true,
        else => false,
    };
}

// the address of what `node` names, or of a fresh copy of a value that lives nowhere
fn place(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const value_type = self.type_of(node);
    switch (tree.kind(node)) {
        .capture => return self.place(tree.arg(node, 0)),
        .identifier, .identifier_self => {
            const declaration = self.declaration_of(node);
            if (self.global_index_of.get(declaration)) |global| return Ref.global(global);
            if (self.stack_slots.get(declaration)) |slot| return slot;
        },
        .member => if (self.field_place(node)) |pointer| return pointer,
        .array_index => return self.element_place(node, value_type),
        .dereference => return self.expression(tree.arg(node, 0)),
        else => {},
    }

    const value = self.expression(node);
    const slot = self.alloca(value_type);
    self.store(slot, value);
    return slot;
}

fn field_place(self: *HighLowerer, node: NodeId) ?Ref {
    const parent = self.resolver.tree.arg(node, 0);
    const parent_type = self.type_of(parent);
    const base = if (self.is_pointer(parent_type)) self.expression(parent) else self.place(parent);
    const record_type = self.static_pool.through_pointer(parent_type);
    const name = self.resolver.name_pool.name_of_node(self.resolver.tree.arg(node, 1));
    switch (self.static_pool.lookup_member(record_type, name)) {
        .field => |field| {
            const pointer_type = self.pointer_to(field.field_type);
            return self.builder.emit(.field_ptr, pointer_type, @intFromEnum(base), field.index);
        },
        else => return null,
    }
}

fn element_place(self: *HighLowerer, node: NodeId, element_type: Index) Ref {
    const array = self.resolver.tree.arg(node, 0);
    const array_type = self.type_of(array);
    const by_value = self.is_pointer(array_type) or self.is_dynamic_array(array_type);
    const base = if (by_value) self.expression(array) else self.place(array);
    const element_pointer = self.pointer_to(element_type);
    const index = self.expression(self.resolver.tree.arg(node, 1));
    return self.builder.emit_refs(.index_ptr, element_pointer, base, index);
}
