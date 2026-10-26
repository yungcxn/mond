const std = @import("std");
const DynamicBuffer = @import("containers.zig").DynamicBuffer;
const ParseTree = @import("ParseTree.zig");
const Resolver = @import("Resolver.zig");
const Value = @import("resolver/interpreter/Value.zig");
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
    last: Ref = .none,
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
// the place of what the pattern being lowered tests, when a label names it
matched_place: Ref = .none,
// the constant aliases (`<-`) of the loop conditions lowered, each with the temporary holding its
// value; the temporary after it says whether it was reached
alias_nodes: DynamicBuffer(NodeId),
alias_values: DynamicBuffer(u32),
// variables living in memory, by the pointer to them
stack_slots: std.AutoHashMapUnmanaged(DeclPool.Index, Ref) = .empty,
// variables of the current body whose address is taken, they must live in memory
address_taken: std.AutoHashMapUnmanaged(DeclPool.Index, void) = .empty,
// places of fields sharing a byte with another (`StaticPool.is_bit_field`), read and written
// through their whole record: its address, its type and the field
bit_places: std.AutoHashMapUnmanaged(Ref, struct { Ref, Index, u32 }) = .empty,
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
        .alias_nodes = .init(allocator, 8),
        .alias_values = .init(allocator, 8),
    };
}

pub fn deinit(self: *HighLowerer) void {
    self.function_of.deinit(self.allocator);
    self.overload_group_head_of.deinit(self.allocator);
    self.next_overload_of.deinit(self.allocator);
    self.global_index_of.deinit(self.allocator);
    self.stack_slots.deinit(self.allocator);
    self.bit_places.deinit(self.allocator);
    self.address_taken.deinit(self.allocator);

    self.ir.deinit();

    self.function_queue.deinit();
    self.scratch.deinit();
    self.builder.deinit();
    self.temporary_types.deinit();
    self.parameters.deinit();
    self.defers.deinit();
    self.loops.deinit();
    self.alias_nodes.deinit();
    self.alias_values.deinit();
}

pub fn lower(self: *HighLowerer) void {
    const bodies = self.resolver.bodies.bodies.columns();
    const decl_pool = &self.resolver.decl_pool;
    var overload_lists = self.resolver.scopes.globals.valueIterator();
    while (overload_lists.next()) |first| {
        var overload = first.*;
        while (overload != .none) : (overload = decl_pool.get(overload, .next_overload)) {
            const realized = self.resolver.declarations.realized(overload);
            if (!self.resolver.bodies.body_index_of.contains(realized)) continue;

            // joins the group of the first earlier overload taking the same parameters, if any
            var earlier = first.*;
            while (earlier != overload) : (earlier = decl_pool.get(earlier, .next_overload)) {
                const realized_earlier = self.resolver.declarations.realized(earlier);
                if (!self.resolver.bodies.body_index_of.contains(realized_earlier)) continue;
                if (!self.resolver.calls.has_same_parameters(realized_earlier, realized)) continue;

                put_entry(self.allocator, &self.overload_group_head_of, realized, realized_earlier);
                var last = realized_earlier;
                while (self.next_overload_of.get(last)) |next| last = next;
                put_entry(self.allocator, &self.next_overload_of, last, realized);
                break;
            }
        }
    }

    const declarations = decl_pool.entries.columns();
    for (0..declarations.name.len) |i| {
        const flags = declarations.flags[i];
        if (!flags.is_global or declarations.kind[i] != .variable) continue;
        // trees and what holds them are compile-time only, nothing of them is lowered
        const value_type = declarations.value_type[i];
        if (self.resolver.tree.macros and self.static_pool.contains_trees(value_type)) continue;

        const declaration: DeclPool.Index = @fromBackingInt(@intCast(i));
        put_entry(self.allocator, &self.global_index_of, declaration, self.ir.globals.len());
        self.ir.globals.push(.{
            .decl = declaration,
            .ty = self.substituted(declarations.value_type[i]),
            .init = if (flags.is_stc) self.stored(declarations.static_value[i]) else .none,
        });
    }

    for (bodies.declaration) |declaration| {
        if (!decl_pool.get(declaration, .kind).is_function()) continue;
        if (self.overload_group_head_of.contains(declaration)) continue;
        const value_type = decl_pool.get(declaration, .value_type);
        if (self.resolver.tree.macros and self.static_pool.contains_trees(value_type)) continue;
        _ = self.ensure_function(declaration);
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
        const declaration = self.function_queue.buffer[i];
        self.reset_function_state();
        // the parameters come from the definition
        self.builder.current_origin = decl_pool.get(declaration, .node);
        const function = self.function_of.get(declaration).?;
        const function_type = self.substituted(decl_pool.get(declaration, .value_type));
        self.return_type = self.static_pool.get(function_type).function_type.return_type;
        self.builder.go_to(self.builder.new_block());

        const captures = self.resolver.bodies.captures_of(&self.resolver.decl_pool, declaration);
        for (captures, 0..) |captured, k| {
            const captured_type = self.variable_type(@backingInt(captured));
            const by_reference = self.resolver.declarations.is_captured_by_reference(captured);
            const value_type = if (by_reference) self.pointer_to(captured_type) else captured_type;
            const parameter = self.builder.emit(.param, value_type, @intCast(k), 0);
            if (by_reference) {
                put_entry(self.allocator, &self.stack_slots, captured, parameter);
            } else {
                self.write_current(@backingInt(captured), parameter);
            }
        }
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

    // the initializers of the globals and the other top-level statements, in order
    self.reset_function_state();
    self.body = .{};
    self.return_type = .unit_type;
    self.builder.go_to(self.builder.new_block());
    for (self.resolver.roots) |root| {
        const is_declaration_statement = switch (self.resolver.tree.kind(root)) {
            .assign, .assign_typed, .def_var, .mod_pub, .mod_mut, .mod_stc => true,
            else => false,
        };
        if (is_declaration_statement) {
            self.lower_assignment(root);
        } else {
            _ = self.expression(root);
        }
    }
    self.emit_return(.none);
    self.builder.freeze(&self.ir, self.ir.init_fn);
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

// a subset of a variant is lowered as its whole
fn substituted(self: *HighLowerer, value_type: Index) Index {
    if (value_type == .none) return value_type;
    return self.static_pool.whole_of(self.static_pool.substitute_type_variables(value_type));
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
    return self.static_pool.whole_of(self.static_pool.get(pointer_type).pointer_type.pointee);
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

// records, arrays and tagged variants: a variable of them lives in a stack slot, so a value of
// them is never carried from one pass of a loop into the next
fn lives_in_memory(self: *HighLowerer, value_type: Index) bool {
    if (self.is_aggregate(value_type)) return true;
    if (value_type == .none) return false;
    return switch (self.static_pool.get(value_type)) {
        .unified_variant_type => true,
        .variant_type => |variant| variant.tag_mode != .self or
            self.static_pool.is_field_tagged(value_type),
        .variant_case_type => |case| self.lives_in_memory(case.variant),
        .variant_subset_type => |subset| self.lives_in_memory(subset.whole),
        else => false,
    };
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

// read anew each time: the memory moves when the pool grows
fn parameter_type(self: *HighLowerer, function_type: Index, parameter_index: usize) Index {
    return self.static_pool.get(function_type).function_type.parameters[parameter_index];
}

fn field_index(self: *HighLowerer, record: Index, argument: NodeId, position: usize) u32 {
    return self.resolver.calls.field_index_of(record, argument, position) orelse @intCast(position);
}

// variables

fn variable_type(self: *HighLowerer, variable: u32) Index {
    if (variable < self.first_temporary) {
        const declaration: DeclPool.Index = @fromBackingInt(variable);
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

// slots go to the entry block, allocated once per call however often their code runs
fn alloca(self: *HighLowerer, value_type: Index) Ref {
    if (self.builder.is_unreachable) return .none;
    return self.builder.emit_raw(.alloca, self.pointer_to(value_type), none, 0, 0);
}

fn store(self: *HighLowerer, pointer: Ref, value: Ref) void {
    // a bit field: its record made anew with it and stored whole
    if (self.bit_places.get(pointer)) |bit_place| {
        const record_pointer, const record_type, const field = bit_place;
        const record = self.load(record_type, record_pointer);
        const mark = self.scratch.len;
        const field_count = self.static_pool.get(record_type).record_type.field_types.len;
        for (0..field_count) |i| {
            const field_type = self.static_pool.field_type(record_type, i);
            const part = if (i == field)
                value
            else
                self.builder.emit(.extract, field_type, @backingInt(record), @intCast(i));
            self.scratch.push(@backingInt(part));
        }
        const fields = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
        self.scratch.len = mark;
        const made = self.builder.emit(.aggregate, record_type, 0, fields);
        _ = self.builder.emit_refs(.store, .unit_type, record_pointer, made);
        return;
    }
    _ = self.builder.emit_refs(.store, .unit_type, pointer, value);
}

fn load(self: *HighLowerer, value_type: Index, pointer: Ref) Ref {
    if (self.bit_places.get(pointer)) |bit_place| {
        const record_pointer, const record_type, const field = bit_place;
        const record = self.builder.emit_refs(.load, record_type, record_pointer, .none);
        return self.builder.emit(.extract, value_type, @backingInt(record), field);
    }
    // an immutable value is read where it is, not copied
    if (self.builder.addressed(pointer)) |value| {
        if (self.builder.result_type_of(value) == value_type) return value;
    }
    return self.builder.emit_refs(.load, value_type, pointer, .none);
}

// a field's place, remembered when it is a bit field
fn field_pointer(
    self: *HighLowerer,
    field_type: Index,
    record: Ref,
    record_type: Index,
    field: u32,
) Ref {
    const pointer_type = self.pointer_to(field_type);
    const pointer = self.builder.emit(.field_ptr, pointer_type, @backingInt(record), field);
    const is_bit_field = self.static_pool.tag(record_type) == .record_type and
        self.static_pool.is_bit_field(self.static_pool.get(record_type).record_type, field);
    if (is_bit_field) {
        put_entry(self.allocator, &self.bit_places, pointer, .{ record, record_type, field });
    }
    return pointer;
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

fn declare_variable(self: *HighLowerer, declaration: DeclPool.Index, value: Ref) void {
    if (declaration == .none or self.builder.is_unreachable) return;
    if (self.global_index_of.contains(declaration)) return self.store_variable(declaration, value);

    const variable = @backingInt(declaration);
    const declared_type = self.resolver.decl_pool.get(declaration, .value_type);
    // an immutable value in memory is its own place: read where it is, also through its address
    const is_mut = self.resolver.decl_pool.get(declaration, .flags).is_mut;
    const is_taken = self.address_taken.contains(declaration);
    const in_memory = self.lives_in_memory(self.substituted(declared_type));
    const needs_memory = if (is_mut) is_taken or in_memory else is_taken and !in_memory;
    if (needs_memory) {
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
    const value_type = self.variable_type(@backingInt(declaration));
    if (self.global_index_of.get(declaration)) |global| {
        return self.load(value_type, Ref.global(global));
    }
    if (self.stack_slots.get(declaration)) |slot| return self.load(value_type, slot);
    return self.read_current(@backingInt(declaration));
}

// a local's place: its slot, or the immutable value in memory itself; none for a value in a
// register
fn variable_place(self: *HighLowerer, declaration: DeclPool.Index) Ref {
    if (self.stack_slots.get(declaration)) |slot| return slot;
    const decl_pool = &self.resolver.decl_pool;
    const is_variable = decl_pool.get(declaration, .kind).is_runtime_local() and
        !decl_pool.get(declaration, .flags).is_stc and
        decl_pool.get(declaration, .static_value) == .none;
    const value_type = self.variable_type(@backingInt(declaration));
    if (!is_variable or !self.lives_in_memory(value_type)) return .none;
    const value = self.load_variable(declaration);
    return self.builder.emit_refs(.address, self.pointer_to(value_type), value, .none);
}

fn store_variable(self: *HighLowerer, declaration: DeclPool.Index, value: Ref) void {
    if (self.builder.is_unreachable or value == .none) return;
    if (self.global_index_of.get(declaration)) |global| {
        return self.store(Ref.global(global), value);
    }
    if (self.stack_slots.get(declaration)) |slot| return self.store(slot, value);
    self.write_current(@backingInt(declaration), value);
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
    for (captures) |captured| {
        // variables captured by reference are passed as the pointer to them
        const value = if (self.resolver.declarations.is_captured_by_reference(captured))
            self.variable_place(captured)
        else
            self.load_variable(captured);
        self.scratch.push(@backingInt(value));
    }
    const captured = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;

    const closure_type = self.substituted(self.resolver.decl_pool.get(head, .value_type));
    return self.builder.emit(.closure, closure_type, function, captured);
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
    self.bit_places.clearRetainingCapacity();
    self.address_taken.clearRetainingCapacity();
}

// lowers one overload of a group and tells whether it has guards that may fail
fn lower_overload(self: *HighLowerer, overload: DeclPool.Index) bool {
    self.body = self.resolver.bodies.body_of(overload).?;
    const tree = self.resolver.tree;
    const body = self.body;
    // `&x`, a receiver passed by pointer and a capture by reference of a local function take `x`
    for (body.first_node..body.first_node + body.node_count) |i| {
        const node: NodeId = @intCast(i);
        // the variable node whose address `node` takes, 0 when it takes none
        var target: NodeId = 0;
        switch (constructs.construct_of(tree.kind(node))) {
            .address_of, .deinit => target = tree.arg(node, 0),
            // a narrowed array is a pointer into the one narrowed
            .cast => if (self.lives_in_memory(self.type_of(tree.arg(node, 0)))) {
                target = tree.arg(node, 0);
            },
            else => {},
        }

        const calls_member = tree.kind(node) == .fun_call and
            tree.kind(tree.arg(node, 0)) == .member;
        if (calls_member) {
            const method = self.declaration_of(node);
            const takes_receiver = method != .none and
                self.resolver.decl_pool.implicit_self_count(method) == 1;
            if (takes_receiver) target = tree.arg(tree.arg(node, 0), 0);
        }

        while (target != 0 and tree.kind(target) == .capture) target = tree.arg(target, 0);
        if (target != 0 and tree.kind(target) == .identifier and
            !self.is_pointer(self.type_of(target)))
        {
            put_entry(self.allocator, &self.address_taken, self.declaration_of(target), {});
        }
        // a label is the place it names, so a variable holding that place lives in memory
        const names_place = tree.kind(node) == .labelarrow or tree.kind(node) == .selftag_arrow and
            !self.is_pointer(self.type_of(tree.arg(node, 0))) or
            tree.kind(node) == .match and self.arms_hold_label(node);
        const root = if (names_place) self.place_root(tree.arg(node, 0)) else 0;
        if (root != 0) {
            put_entry(self.allocator, &self.address_taken, self.declaration_of(root), {});
        }

        const function = self.declaration_of(node);
        if (function == .none) continue;
        if (!self.resolver.decl_pool.get(function, .kind).is_function()) continue;
        if (!self.resolver.bodies.body_index_of.contains(function)) continue;

        const definition = self.resolver.decl_pool.get(function, .node);
        if (definition < body.first_node) continue;
        if (definition >= body.first_node + body.node_count) continue;

        for (self.resolver.bodies.captures_of(&self.resolver.decl_pool, function)) |captured| {
            if (!self.resolver.declarations.is_captured_by_reference(captured)) continue;
            put_entry(self.allocator, &self.address_taken, captured, {});
        }
    }

    const value_node = self.resolver.declarations.value_node(overload);
    const implicit_self_count = self.resolver.decl_pool.implicit_self_count(overload);
    if (implicit_self_count == 1) {
        // `self` is declared by a node of the body pointing back at the function
        for (body.first_node..body.first_node + body.node_count) |i| {
            const declaration = self.declaration_of(@intCast(i));
            if (declaration == .none) continue;
            if (self.resolver.decl_pool.get(declaration, .kind) != .self) continue;
            if (self.resolver.decl_pool.get(declaration, .node) != value_node) continue;
            self.declare_variable(declaration, self.parameters.buffer[0]);
            break;
        }
    }
    const parameter_nodes = self.resolver.tree.params_of(value_node);
    for (parameter_nodes, 0..) |parameter_node, i| {
        const argument = self.parameters.buffer[i + implicit_self_count];
        self.declare_variable(self.declaration_of(parameter_node), argument);
    }

    const guard_failed = self.builder.new_block();
    // guards without an `else` reject the overload
    var has_guards = false;
    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(self.resolver.tree, parameter_node);
        if (parameter.where == 0 or parameter.@"else" != 0 or parameter.stc) continue;

        has_guards = true;
        const passed = self.builder.new_block();
        self.builder.branch_if(
            self.expression_as(parameter.where, .bool_type),
            passed,
            guard_failed,
        );
        self.builder.go_to(passed);
    }

    // guards with an `else` repair the argument: the `else` assigns, returns or is the value
    for (parameter_nodes) |parameter_node| {
        const parameter = ParseTree.Param.from_node(self.resolver.tree, parameter_node);
        if (parameter.where == 0 or parameter.@"else" == 0 or parameter.stc) continue;

        // continues where the guard fails, `holds` is the block where it holds
        const holds = self.builder.new_block();
        const fails = self.builder.new_block();
        self.builder.branch_if(self.expression_as(parameter.where, .bool_type), holds, fails);
        self.builder.go_to(fails);
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

    self.lower_overload_body(overload, value_node);
    self.builder.go_to(guard_failed);
    return has_guards;
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

fn emit_return(self: *HighLowerer, value: Ref) void {
    self.run_defers(0);
    const returned = if (has_value(self.return_type)) value else Ref.none;
    _ = self.builder.emit(.ret, .unit_type, @backingInt(returned), 0);
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
            const arguments = self.builder.list(&.{@backingInt(pointer)});
            _ = self.builder.emit(.call, .unit_type, @backingInt(callee), arguments);
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
        .member_to_packed,
        .incompatible,
        => value,
        .case_to_variant => {
            if (self.static_pool.tag(to) == .variant_type) return value;
            const into_unified = StaticPool.CoercionKind.member_to_unified;
            return self.builder.emit(.convert, to, @backingInt(value), @backingInt(into_unified));
        },
        .payload_to_self_tagged => self.wrap_in_payload_case(value, from, to),
        // an array value is the address of its own copy
        .to_slice => {
            const array_type = self.static_pool.pointee(from);
            const length = self.static_pool.static_length(array_type).?;
            return self.slice_from(value, to, self.builder.constant_int(.u64_type, length));
        },
        .int_widen,
        .float_widen,
        .string_to_ptr,
        .array_ptr_to_elem_ptr,
        .to_dyn,
        .member_to_unified,
        .impl_to_trait,
        => self.builder.emit(.convert, to, @backingInt(value), @backingInt(kind)),
    };
}

fn wrap_in_payload_case(self: *HighLowerer, value: Ref, from: Index, variant: Index) Ref {
    const case_index = self.payload_case_index(variant);
    const case_type = self.static_pool.get(variant).variant_type.cases[case_index];
    const payload_type = self.static_pool.get(case_type).variant_case_type.payload;
    const payload_record = self.static_pool.get(payload_type).record_type;
    const field = self.coerce(value, from, payload_record.field_types[0]);
    const fields = self.builder.list(&.{@backingInt(field)});
    const payload = self.builder.emit(.aggregate, payload_type, 0, fields);
    return self.builder.emit(.variant_make, variant, @intCast(case_index), @backingInt(payload));
}

// the case of a self-tagged variant that carries the payload
fn payload_case_index(self: *HighLowerer, variant: Index) u32 {
    const cases = self.static_pool.get(variant).variant_type.cases;
    for (cases, 0..) |case, i| {
        if (self.static_pool.get(case).variant_case_type.payload != .none) return @intCast(i);
    }
    return 0;
}

// a static value with the bits a strategy stores for each value of a variant it stores (constants
// are made without running code), the value itself when it holds none
fn stored(self: *HighLowerer, value: Index) Index {
    const pool = self.static_pool;
    if (value == .none) return value;
    switch (pool.get(value)) {
        // a case without payload is its own value
        .variant_value, .variant_case_type => {
            const variant_value: StaticPool.VariantValue = if (pool.tag(value) == .variant_value)
                pool.get(value).variant_value
            else
                .{ .case = value, .payload = .none };
            const case = pool.get(variant_value.case).variant_case_type;
            if (pool.tag(case.variant) != .variant_type) return value;
            const variant = pool.get(case.variant).variant_type;
            if (variant.tag_mode != .custom) return value;
            const bits = if (variant_value.payload == .none) 0 else blk: {
                const field = pool.get(variant_value.payload).aggregate_value.elements[0];
                break :blk Value.of(pool, field).raw_bits();
            };
            const parts = pool.get(variant.strategy).aggregate_value.elements;
            const storage = parts[0];
            var context = Resolver.FunctionContext{};
            const tag = pool.case_tag(variant_value.case);
            const arguments = [_]Value{ .int(.u32_type, tag), .int(.u64_type, bits) };
            const made = self.resolver.interpreter.call_static(&context, 0, parts[1], &arguments);
            return pool.intern(.{ .int_value = .{ .value_type = storage, .bits = made.bits } });
        },
        .aggregate_value => |aggregate| {
            const elements = self.resolver.temporary_slice(Index, aggregate.elements.len);
            @memcpy(elements, aggregate.elements);
            var changed = false;
            for (elements) |*element| {
                const element_stored = self.stored(element.*);
                changed = changed or element_stored != element.*;
                element.* = element_stored;
            }
            if (!changed) return value;
            const value_type = pool.get(value).aggregate_value.value_type;
            return pool.intern(.{
                .aggregate_value = .{ .value_type = value_type, .elements = elements },
            });
        },
        else => return value,
    }
}

fn constant_of(self: *HighLowerer, given: Index, value_type: Index) Ref {
    const pool = self.static_pool;
    const value = self.stored(given);
    if (value_type == .none) return Ref.of(value);
    // a static slice is of a static array, read-only data: its address and its length
    if (pool.tag(value_type) == .slice_type) {
        const length = pool.static_length(pool.type_of(value)) orelse 0;
        const length_ref = self.builder.constant_int(.u64_type, length);
        return self.slice_from(Ref.of(value), value_type, length_ref);
    }
    // a static value of a unified variant is the value of a member, made one like a run-time one
    if (pool.tag(value_type) == .unified_variant_type) {
        const own_type = if (pool.tag(value) == .variant_case_type) value else pool.type_of(value);
        if (own_type != value_type) return self.coerce(Ref.of(value), own_type, value_type);
    }

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
    // an array is sliced where it lives when it is a place, so writes through the slice reach it
    const target = self.substituted(target_type);
    const node_type = self.type_of(node);
    const slices_place = target != .none and self.static_pool.tag(target) == .slice_type and
        self.static_pool.tag(node_type) == .array_type and self.is_place(node);
    if (slices_place) {
        const length = self.static_pool.static_length(node_type).?;
        const length_ref = self.builder.constant_int(.u64_type, length);
        return self.slice_from(self.place(node), target, length_ref);
    }
    return self.coerce(self.expression(node), node_type, target_type);
}

// `[..]T` of the address of its first element and its length
fn slice_from(self: *HighLowerer, first: Ref, slice_type: Index, length: Ref) Ref {
    const parts = self.builder.list(&.{ @backingInt(first), @backingInt(length) });
    return self.builder.emit(.aggregate, slice_type, 0, parts);
}

// a slice's address of its first element (`part` 0) or its length (1)
fn slice_part(self: *HighLowerer, slice: Ref, slice_type: Index, part: u32) Ref {
    const part_type = self.static_pool.field_type(slice_type, part);
    return self.builder.emit(.extract, part_type, @backingInt(slice), part);
}

// the slice a node is, or the one a pointer to it reaches
fn slice_value(self: *HighLowerer, node: NodeId) Ref {
    const node_type = self.type_of(node);
    const value = self.expression(node);
    return if (self.is_pointer(node_type)) self.load(self.pointee_of(node_type), value) else value;
}

// an index or bound as a `u64`: a negative one wraps past any length
fn as_length(self: *HighLowerer, value: Ref) Ref {
    if (self.type_of_ref(value) == .u64_type) return value;
    const resize = @backingInt(StaticPool.CastKind.int_resize);
    return self.builder.emit(.cast, .u64_type, @backingInt(value), resize);
}

// continues where `holds` is true; the other side stops the program, a trap in the modes that
// keep the runtime checks
fn check(self: *HighLowerer, holds: Ref) void {
    const passed = self.builder.new_block();
    const failed = self.builder.new_block();
    self.builder.branch_if(holds, passed, failed);
    self.builder.go_to(failed);
    self.emit_unreachable();
    self.builder.go_to(passed);
}

// `a[lo..<hi]`: a slice of the elements of a slice, an array or a pointer, or a copy of that
// part as an array; the bounds are checked against the length where there is one
fn range_index(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const base = tree.arg(node, 0);
    const range = ParseTree.Range.from_node(tree, tree.arg(node, 1));
    const result_type = self.type_of(node);
    const base_type = self.type_of(base);
    const container = self.dereferenced_type(base_type);
    const element = switch (self.static_pool.get(container)) {
        .slice_type => |slice| slice.element,
        .array_type => |array| array.element,
        else => container,
    };
    const element_pointer = self.pointer_to(element);
    const first: Ref, const length: ?Ref = switch (self.static_pool.tag(container)) {
        .slice_type => blk: {
            const slice = self.slice_value(base);
            const slice_first = self.slice_part(slice, container, 0);
            break :blk .{ slice_first, self.slice_part(slice, container, 1) };
        },
        else => blk: {
            const by_value = self.is_pointer(base_type) or !self.is_place(base);
            const address = if (by_value) self.expression(base) else self.place(base);
            const static_length = self.static_pool.static_length(container);
            const as_elements = @backingInt(StaticPool.CoercionKind.array_ptr_to_elem_ptr);
            const start = if (static_length != null)
                self.builder.emit(.convert, element_pointer, @backingInt(address), as_elements)
            else
                address;
            const known: ?Ref = if (static_length) |end|
                self.builder.constant_int(.u64_type, end)
            else
                null;
            break :blk .{ start, known };
        },
    };
    const low = if (range.lo != 0)
        self.as_length(self.expression(range.lo))
    else
        self.builder.constant_int(.u64_type, 0);
    const high = if (range.hi == 0) length.? else blk: {
        const bound = self.as_length(self.expression(range.hi));
        if (!range.incl) break :blk bound;
        const one = self.builder.constant_int(.u64_type, 1);
        break :blk self.builder.emit_refs(.add, .u64_type, bound, one);
    };
    self.check(self.builder.emit_refs(.le, .bool_type, low, high));
    if (length) |end| self.check(self.builder.emit_refs(.le, .bool_type, high, end));
    const start = self.builder.emit_refs(.index_ptr, element_pointer, first, low);
    if (self.static_pool.tag(result_type) != .slice_type) return self.load(result_type, start);
    return self.slice_from(start, result_type, self.builder.emit_refs(.sub, .u64_type, high, low));
}

fn expression(self: *HighLowerer, node: NodeId) Ref {
    const outer_origin = self.builder.current_origin;
    self.builder.current_origin = node;
    defer self.builder.current_origin = outer_origin;
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
        .length_or_tag => {
            const operand = self.resolver.tree.arg(node, 0);
            const operand_type = self.type_of(operand);
            const is_length = self.resolver.tree.kind(node) == .lenof;
            const sliced = self.dereferenced_type(operand_type);
            if (is_length and self.static_pool.tag(sliced) == .slice_type) {
                return self.slice_part(self.slice_value(operand), sliced, 1);
            }
            if (is_length) return self.array_length(operand_type);
            const owner = self.static_pool.through_pointer(operand_type);
            return self.variant_tag_of(operand, operand_type, owner);
        },
        .index => if (self.resolver.tree.props(second).range)
            self.range_index(node)
        else
            self.load(value_type, self.place(node)),
        .dereference => self.load(value_type, self.expression(first)),
        .address_of => self.place(first),
        .array_literal => self.array_literal(node, kind, value_type),
        // the checker knew the answer
        .static_test => Ref.of(self.static_value_of(node) orelse .bool_false),
        .join => self.join(value_type, first, second),
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
            // an immutable value in memory is shared, it is deinitialized in a copy
            const operand_type = self.type_of(first);
            const is_shared = !self.is_place(first) and self.lives_in_memory(operand_type);
            const pointer = if (is_shared) self.alloca(operand_type) else self.place(first);
            if (is_shared) self.store(pointer, self.expression(first));
            self.call_deinit(pointer, self.dereferenced_type(self.type_of(first)));
            return unit();
        },
        .deferred_deinit => self.deferred_deinit(node, first),
        .unwrap => self.unwrap(node),
        // a value of a type its case or member is (see `StaticPool.units_covered`), tested on its
        // tag. any other answer was known and taken above
        .type_test => {
            const tested = self.static_value_of(second) orelse return Ref.of(.bool_false);
            const operand_type = self.type_of(first);
            const subject_type = self.static_pool.through_pointer(operand_type);
            var value = self.expression(first);
            if (self.static_pool.is_pointer(operand_type)) value = self.load(subject_type, value);
            const mark = self.scratch.len;
            defer self.scratch.len = mark;
            const pool_mark = self.static_pool.scratch.len;
            self.static_pool.push_units(subject_type);
            const units = self.static_pool.scratch.buffer[pool_mark..self.static_pool.scratch.len];
            for (units) |each| self.scratch.push(@backingInt(each));
            self.static_pool.scratch.len = pool_mark;
            var holds: Ref = .none;
            for (self.scratch.buffer[mark..self.scratch.len]) |bits| {
                const each: Index = @fromBackingInt(bits);
                if (!self.static_pool.covers_unit(tested, each)) continue;
                const is_unit = self.tests_case(value, subject_type, each);
                holds = if (holds == .none)
                    is_unit
                else
                    self.builder.emit_refs(.bit_or, .bool_type, holds, is_unit);
            }
            return if (holds == .none) Ref.of(.bool_false) else holds;
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
    // what follows a `ret`, `brk` or `cont` never runs (and a folding check may have skipped it)
    for (self.resolver.tree.manychildren(node)) |statement| {
        if (self.builder.is_unreachable) break;
        last = self.expression(statement);
    }
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
        self.scratch.push(@backingInt(value));
    }
    const values = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    return self.builder.emit(.aggregate, array_type, 0, values);
}

// `a ~ b` of arrays (behind pointers too): both stored one after the other in a new one
fn join(self: *HighLowerer, joined_type: Index, left: NodeId, right: NodeId) Ref {
    const element = self.static_pool.get(joined_type).array_type.element;
    const element_pointer = self.pointer_to(element);
    const slot = self.alloca(joined_type);
    const as_elements = @backingInt(StaticPool.CoercionKind.array_ptr_to_elem_ptr);
    const first = self.builder.emit(.convert, element_pointer, @backingInt(slot), as_elements);
    var at = first;
    for ([2]NodeId{ left, right }) |operand| {
        const operand_type = self.substituted(self.type_of(operand));
        const array_type = self.dereferenced_type(operand_type);
        const value = if (self.is_pointer(operand_type))
            self.load(array_type, self.expression(operand))
        else
            self.expression_as(operand, array_type);
        self.store(at, value);
        if (operand == right) break;
        const length = self.static_pool.static_length(array_type).?;
        const offset = self.builder.constant_int(.u64_type, length);
        at = self.builder.emit_refs(.index_ptr, element_pointer, first, offset);
    }
    return self.load(joined_type, slot);
}

fn cast(self: *HighLowerer, node: NodeId, target_type: Index, operand: NodeId) Ref {
    const from = self.type_of(operand);
    const kind = self.static_pool.cast_kind(from, target_type);
    // a narrowed array or relengthed pointer is the pointer to its first element, seen as shorter
    if (kind == .array_narrow or kind == .pointer_relength) {
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
        const relength = @backingInt(StaticPool.CastKind.pointer_relength);
        const pointer = self.builder.emit(.cast, array_pointer_type, @backingInt(first), relength);
        if (self.is_pointer(target_type)) return pointer;
        return self.load(target_type, pointer);
    }
    // an array seen whole as a slice, where it lives when it is a place
    if (kind == .array_to_slice) {
        const from_pointer = self.is_pointer(from);
        const array_type = self.static_pool.pointee(from);
        const by_value = from_pointer or !self.is_place(operand);
        const first = if (by_value) self.expression(operand) else self.place(operand);
        const length = self.static_pool.static_length(array_type).?;
        return self.slice_from(first, target_type, self.builder.constant_int(.u64_type, length));
    }
    const value = self.expression(operand);
    if (kind == .identity) return value;
    // the address of a slice's first element
    if (kind == .slice_to_pointer) {
        return self.builder.emit(.extract, target_type, @backingInt(value), 0);
    }
    return self.builder.emit(.cast, target_type, @backingInt(value), @backingInt(kind));
}

fn bit_cast(self: *HighLowerer, target_type: Index, operand: NodeId) Ref {
    if (self.type_of(operand) == target_type) return self.expression(operand);
    const value = self.expression(operand);
    const target_size = self.static_pool.layout(target_type).size;
    const widens = target_size > self.static_pool.layout(self.type_of(operand)).size;
    const kind: StaticPool.CastKind = if (widens) .bit_extend else .bit_reinterpret;
    return self.builder.emit(.cast, target_type, @backingInt(value), @backingInt(kind));
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
    const stands_for_static_value = self.resolver.decl_pool.get(declaration, .flags).is_stc or
        switch (kind) {
            // a binder of a pattern matched or a condition tested while checking has its value
            .static_parameter, .parameter, .pattern_binder, .arrow_binder => true,
            .type_alias, .record, .variant, .trait => true,
            else => false,
        };
    if (value != .none and stands_for_static_value) {
        return self.constant_of(value, self.type_of(node));
    }
    return self.load_variable(declaration);
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
        const new = if (self.is_pointer(target_type))
            self.offset_pointer(target_type, old, operation == .sub, operand)
        else
            self.builder.emit_refs(operation, target_type, old, operand);
        self.store_variable(self.declaration_of(target), new);
        return if (returns_old) old else new;
    }

    const pointer = self.place(target);
    const old = self.load(target_type, pointer);
    const new = if (self.is_pointer(target_type))
        self.offset_pointer(target_type, old, operation == .sub, operand)
    else
        self.builder.emit_refs(operation, target_type, old, operand);
    self.store(pointer, new);
    return if (returns_old) old else new;
}

fn lower_assignment(self: *HighLowerer, statement_node: NodeId) void {
    const statement = Declarations.Stmt.from_node(self.resolver, statement_node);
    if (statement.kind != .variable) return;
    const values = statement.values;
    const assignees = statement.assignees;

    // a single place that is not a name: a field, an element, a dereference
    if (assignees.len == 1 and self.resolver.name_pool.name_of_node(assignees[0]) == .none) {
        const target_type = self.type_of(assignees[0]);
        const value = self.expression_as(values[0], target_type);
        const target = assignees[0];
        const is_global_name = self.global_index_of.contains(self.declaration_of(target)) and
            self.resolver.tree.kind(target) == .identifier;
        if (self.is_ssa_variable(target) or is_global_name) {
            return self.store_variable(self.declaration_of(target), value);
        }
        return self.store(self.place(target), value);
    }

    // every value is computed before the first is stored, so `a, b = b, a` swaps. one value for one
    // name is lowered as it is taken, so an array becomes a slice where it lives
    const is_shared = values.len == 1 and assignees.len > 1;
    const shared = if (is_shared) self.expression(values[0]) else Ref.none;
    const mark = self.scratch.len;
    defer self.scratch.len = mark;
    for (assignees, 0..) |assignee, i| {
        const value: Ref = blk: {
            const declaration = self.declaration_of(assignee);
            // static declarations with a known value are never stored
            if (declaration == .none) break :blk .none;
            const is_stc = self.resolver.decl_pool.get(declaration, .flags).is_stc;
            if (is_stc and self.resolver.decl_pool.get(declaration, .static_value) != .none) {
                break :blk .none;
            }

            const target_type = self.variable_type(@backingInt(declaration));
            if (values.len == 0) {
                const is_local_aggregate = self.is_aggregate(target_type) and
                    !self.global_index_of.contains(declaration);
                if (!is_local_aggregate) break :blk .none;
                if (self.static_pool.tag(target_type) == .record_type) {
                    break :blk self.construct(target_type, &.{});
                }
                break :blk self.builder.emit(.zeroed, target_type, 0, 0);
            }
            if (values.len > 1) break :blk self.expression_as(values[i], target_type);
            if (assignees.len == 1) break :blk self.expression_as(values[0], target_type);
            break :blk self.coerce(shared, self.type_of(values[0]), target_type);
        };
        self.scratch.push(@backingInt(value));
    }

    for (assignees, 0..) |assignee, i| {
        const declaration = self.declaration_of(assignee);
        if (declaration == .none) continue;
        const is_stc = self.resolver.decl_pool.get(declaration, .flags).is_stc;
        if (is_stc and self.resolver.decl_pool.get(declaration, .static_value) != .none) continue;

        const value: Ref = @fromBackingInt(self.scratch.buffer[mark + i]);
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
    // pointer arithmetic is never cheap: it has to scale its offset
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
    // a condition the checker knew (`stcif`, a static `stc?` argument) takes one side only
    const known = self.static_value_of(parts.cond) orelse .none;
    if (self.resolver.tree.props(node).stc or known == .bool_true or known == .bool_false) {
        const takes_then = (self.static_value_of(parts.cond) orelse .bool_false) == .bool_true;
        if (takes_then) return self.expression_as(parts.then, result_type);
        if (has_else) return self.expression_as(parts.@"else", result_type);
        return unit();
    }

    var budgets: [2]u8 = .{ 3, 3 };
    const selects = has_else and self.is_scalar(result_type) and
        self.is_cheap(parts.then, &budgets[0]) and
        self.is_cheap(parts.@"else", &budgets[1]);
    // both cheap arms are computed and one is selected, no branch needed
    if (selects) {
        const condition = self.expression_as(parts.cond, .bool_type);
        if (condition.is_const()) {
            const taken = if (condition.value() == .bool_true) parts.then else parts.@"else";
            return self.expression_as(taken, result_type);
        }

        const then_value = self.expression_as(parts.then, result_type);
        const else_value = self.expression_as(parts.@"else", result_type);
        if (then_value == else_value) return then_value;
        const choices = self.builder.list(&.{ @backingInt(then_value), @backingInt(else_value) });
        return self.builder.emit(.select, result_type, @backingInt(condition), choices);
    }

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

// match

fn match_expression(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const result_type = self.type_of(node);
    const arms = tree.manychildren(tree.arg(node, 1));
    // the arm the checker took for a static scrutinee (`stcmatch`, a static `stc?` argument), its
    // names static values: no other arm is lowered
    for (arms) |arm| {
        if ((self.static_value_of(arm) orelse .none) != .bool_true) continue;
        return self.expression_as(tree.arg(arm, 1), result_type);
    }

    // a label in a pattern names the part of the scrutinee's place it matched
    const labelled = self.arms_hold_label(node);
    const outer_place = self.matched_place;
    defer self.matched_place = outer_place;
    var scrutinee_type = self.type_of(tree.arg(node, 0));
    const of_place = labelled and !self.is_pointer(scrutinee_type);
    self.matched_place = if (of_place) self.place(tree.arg(node, 0)) else .none;
    var scrutinee = if (of_place)
        self.load(scrutinee_type, self.matched_place)
    else
        self.expression(tree.arg(node, 0));
    const is_pointer_to_nominal = self.is_pointer(scrutinee_type) and
        self.static_pool.through_pointer(scrutinee_type) != scrutinee_type;
    if (is_pointer_to_nominal) {
        if (labelled) self.matched_place = scrutinee;
        scrutinee = self.load(self.pointee_of(scrutinee_type), scrutinee);
        scrutinee_type = self.pointee_of(scrutinee_type);
    }

    const result = if (has_value(result_type)) self.new_temporary(result_type) else none;
    const merge = self.builder.new_block();
    // the arms a switch took, the others are tested one after another from its default
    const switched =
        self.lower_as_switch(arms, scrutinee, scrutinee_type, result_type, result, merge);
    if (switched == arms.len) {
        self.builder.go_to(merge);
        return self.merged_result(result);
    }

    for (arms[switched..]) |arm| {
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

// a unified variant flattens its members: a member's tags are moved into the member's own range,
// a member that is one case (only of a unified variant) has one tag
fn tag_constant(self: *HighLowerer, subset_or_scrutinee_type: Index, case_or_member: Index) Ref {
    const pool = self.static_pool;
    const scrutinee_type = pool.whole_of(subset_or_scrutinee_type);
    const is_unified = scrutinee_type != .none and
        pool.tag(scrutinee_type) == .unified_variant_type;
    const container = if (is_unified)
        scrutinee_type
    else
        pool.get(case_or_member).variant_case_type.variant;
    const bits = pool.tag_in(container, case_or_member);
    return self.builder.constant_int(pool.stored_tag_type(container), bits);
}

// whether a value of `scrutinee_type` may be of `case`
fn can_hold_case(self: *HighLowerer, subset_or_scrutinee_type: Index, case: Index) bool {
    const scrutinee_type = self.static_pool.whole_of(subset_or_scrutinee_type);
    const variant = self.static_pool.get(case).variant_case_type.variant;
    if (scrutinee_type == .none or scrutinee_type == variant) return true;
    return switch (self.static_pool.get(scrutinee_type)) {
        .unified_variant_type => self.static_pool.is_member(scrutinee_type, variant),
        // a value of a case is of no other, of any other type (a realization's sibling) no case
        .variant_case_type => scrutinee_type == case,
        else => false,
    };
}

fn tests_case(self: *HighLowerer, value: Ref, scrutinee_type: Index, case: Index) Ref {
    const tag = self.tag_constant(scrutinee_type, case);
    const value_tag = self.builder.emit_refs(.variant_tag, self.type_of_ref(tag), value, .none);
    return self.builder.emit_refs(.eq, .bool_type, value_tag, tag);
}

// a member of a unified variant is a variant of its own again once its tag is moved back into its
// range
fn narrow_to_variant(self: *HighLowerer, value: Ref, value_type: Index, variant: Index) Ref {
    if (value_type == .none) return value;
    const scrutinee_type = self.static_pool.whole_of(value_type);
    if (self.static_pool.tag(scrutinee_type) != .unified_variant_type) return value;
    const retag = StaticPool.CastKind.variant_retag;
    return self.builder.emit(.cast, variant, @backingInt(value), @backingInt(retag));
}

// a `match` whose arms test constants, up to the first catch-all or guarded arm, becomes one
// `switch`. how many arms it took, the arms after a guard continue from its default
fn lower_as_switch(
    self: *HighLowerer,
    arms: []const NodeId,
    scrutinee: Ref,
    scrutinee_type: Index,
    result_type: Index,
    result: u32,
    merge: u32,
) usize {
    // self-tagged variants keep their tag inside the payload, there is no tag to switch on
    const tagged = blk: {
        if (scrutinee_type == .none) break :blk false;
        if (self.static_pool.tag(scrutinee_type) == .unified_variant_type) break :blk true;
        if (self.static_pool.tag(scrutinee_type) != .variant_type) break :blk false;
        break :blk self.static_pool.get(scrutinee_type).variant_type.tag_mode != .self;
    };
    // the properties are read only for a real type, `.none` has no pool entry
    const switchable = tagged or scrutinee_type != .none and
        self.static_pool.properties(scrutinee_type).is_integer;
    if (!switchable) return 0;

    // how many leading arms go into the switch, none when it is not worth one
    var arm_count: u32 = 0;
    var keyed_count: u32 = 0;
    var has_catch_all = false;
    for (arms) |arm| {
        const pattern = self.resolver.tree.arg(arm, 0);
        // a guard or bits are tested one after the other, below the switch
        const kind = self.resolver.tree.kind(pattern);
        if (kind == .partial__match_case_where or kind == .partial__match_case_pattern_bits) break;
        const arm_kind = self.switch_arm_kind(pattern, scrutinee_type, tagged) orelse return 0;
        arm_count += 1;
        keyed_count += @intFromBool(arm_kind == .keyed);
        has_catch_all = arm_kind == .catch_all;
        if (has_catch_all) break;
    }
    if (keyed_count < 2) return 0;
    const switched_arms = arms[0..arm_count];
    const rest = if (has_catch_all) arms.len else arm_count;

    const mark = self.scratch.len;
    const first_arm_block = self.builder.block_count();
    // pushes the default block, then the key and block pairs, from scratch[mark]
    self.scratch.push(none);
    for (switched_arms) |arm| {
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

    const cases = self.scratch.buffer[mark..self.scratch.len];
    const key = if (tagged) blk: {
        const key_type = self.type_of_ref(@fromBackingInt(cases[1]));
        break :blk self.builder.emit_refs(.variant_tag, key_type, scrutinee, .none);
    } else scrutinee;

    if (key.is_const()) {
        var target = default_block;
        var i: usize = 1;
        while (i < cases.len) : (i += 2) {
            if (cases[i] == @backingInt(key)) target = cases[i + 1];
        }
        self.builder.branch(target);
    } else if (!self.builder.is_unreachable) {
        self.builder.add_edge(default_block);
        var i: usize = 2;
        while (i < cases.len) : (i += 2) self.builder.add_edge(cases[i]);
        _ = self.builder.emit(.@"switch", .unit_type, @backingInt(key), self.builder.list(cases));
    }
    self.scratch.len = mark;

    for (switched_arms, 0..) |arm, i| {
        self.builder.go_to(first_arm_block + @as(u32, @intCast(i)));
        self.bind_pattern(self.resolver.tree.arg(arm, 0), scrutinee, scrutinee_type);
        self.arm_into(self.resolver.tree.arg(arm, 1), result_type, result, merge);
    }
    // without a catch-all arm the default block is a fresh one: the arms after a guard continue
    // there, else nothing reaches it
    if (default_block == first_arm_block + arm_count) {
        self.builder.go_to(default_block);
        if (rest == arms.len) self.emit_unreachable();
    }
    return rest;
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
        self.constant_of(
            self.static_value_of(pattern) orelse
                self.resolver.static_values.literal_value(pattern, false),
            scrutinee_type,
        );
    const key: u32 = @backingInt(key_ref);

    // a key goes to the first arm listing it
    var i = mark + 1;
    while (i < self.scratch.len) : (i += 2) if (self.scratch.buffer[i] == key) return;
    self.scratch.push(key);
    self.scratch.push(arm_block);
}

// binds the names of a pattern its switch arm already matched
fn bind_pattern(self: *HighLowerer, pattern: NodeId, value: Ref, value_type: Index) void {
    switch (self.resolver.tree.kind(pattern)) {
        .identifier => {
            if (self.resolver.name_pool.name_of_node(pattern) == .underscore) return;
            self.declare_variable(self.declaration_of(pattern), value);
        },
        .labelarrow => self.label_matched(self.resolver.tree.arg(pattern, 1), value, value_type),
        .fun_call => self.bind_payload_fields(pattern, value, value_type),
        else => {},
    }
}

fn bind_payload_fields(self: *HighLowerer, pattern: NodeId, value: Ref, value_type: Index) void {
    const case_type = self.static_pool.get(self.type_of(pattern)).variant_case_type;
    const record = case_type.payload;
    if (record == .none or self.static_pool.tag(record) != .record_type) return;

    const narrowed = self.narrow_to_variant(value, value_type, case_type.variant);
    const case_index: Ref = @fromBackingInt(case_type.case_index);
    const payload = self.builder.emit_refs(.variant_payload, record, narrowed, case_index);
    const holder = self.payload_place(value_type, self.type_of(pattern));
    const outer_place = self.matched_place;
    defer self.matched_place = outer_place;
    const arguments = self.resolver.tree.manychildren(self.resolver.tree.arg(pattern, 1));
    for (arguments, 0..) |argument, i| {
        const field = self.field_index(record, argument, i);
        const field_type = self.static_pool.field_type(record, field);
        const field_value = self.builder.emit(.extract, field_type, @backingInt(payload), field);
        self.matched_place = self.field_place_in(holder, record, field, field_type);
        self.bind_pattern(self.resolver.tree.arg_value(argument), field_value, field_type);
    }
}

// whether an arm of the match `node` has a label in its pattern
fn arms_hold_label(self: *HighLowerer, node: NodeId) bool {
    const tree = self.resolver.tree;
    for (tree.manychildren(tree.arg(node, 1))) |arm| {
        if (tree.holds_label(tree.arg(arm, 0))) return true;
    }
    return false;
}

// a label in a pattern names the place it matched, a value of its own where that is none
fn label_matched(self: *HighLowerer, label: NodeId, value: Ref, value_type: Index) void {
    if (self.matched_place == .none) return self.bind_label(label, value);
    self.alias_label(label, self.matched_place, value_type);
}

// where the matched value of `value_type` keeps the payload of `case`, none where nothing does
fn payload_place(self: *HighLowerer, value_type: Index, case: Index) Ref {
    if (self.matched_place == .none) return .none;
    const case_type = self.static_pool.get(case).variant_case_type;
    const is_whole = self.static_pool.whole_of(value_type) == case_type.variant;
    if (!is_whole or !self.stores_payloads(case_type.variant)) return .none;
    const pointer_type = self.pointer_to(case_type.payload);
    return self.builder.emit_refs(.payload_ptr, pointer_type, self.matched_place, .none);
}

fn field_place_in(
    self: *HighLowerer,
    holder: Ref,
    record: Index,
    field: u32,
    field_type: Index,
) Ref {
    if (holder == .none) return .none;
    return self.field_pointer(field_type, holder, record, field);
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
            // alternatives share their names, which then are values, not places
            const outer_place = self.matched_place;
            defer self.matched_place = outer_place;
            self.matched_place = .none;
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
        // the guard runs once the pattern matched and bound its names
        .partial__match_case_where => {
            const pattern_matched = self.builder.new_block();
            self.match_pattern(tree.arg(pattern, 0), value, value_type, pattern_matched, failed);
            self.builder.go_to(pattern_matched);
            self.builder.branch_if(self.expression(tree.arg(pattern, 1)), matched, failed);
        },
        .labelarrow => {
            const labelled_matched = self.builder.new_block();
            const labelled = tree.arg(pattern, 0);
            self.match_pattern(labelled, value, value_type, labelled_matched, failed);
            self.builder.go_to(labelled_matched);
            self.label_matched(tree.arg(pattern, 1), value, value_type);
            self.builder.branch(matched);
        },
        .fun_call => {
            self.match_destructuring(pattern, pattern_type, value, value_type, matched, failed);
        },
        .partial__match_case_pattern_bits => {
            self.match_bits(pattern, value, value_type, matched, failed);
        },
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => {
            self.match_range(pattern, value, value_type, matched, failed);
        },
        else => self.match_value(pattern, pattern_type, value, value_type, matched, failed),
    }
}

// `bits(..)`: each part tested on its bits from the lowest up, as its width's type
fn match_bits(
    self: *HighLowerer,
    pattern: NodeId,
    value: Ref,
    value_type: Index,
    matched: u32,
    failed: u32,
) void {
    const tree = self.resolver.tree;
    const resize = @backingInt(StaticPool.CastKind.int_resize);
    var offset: u64 = 0;
    // the bits of a part live in no place
    const outer_place = self.matched_place;
    defer self.matched_place = outer_place;
    self.matched_place = .none;
    for (tree.manychildren(pattern)) |part| {
        const part_type = self.type_of(part);
        const shift = self.builder.constant_int(value_type, offset);
        const shifted = if (offset == 0)
            value
        else
            self.builder.emit_refs(.shr, value_type, value, shift);
        const part_value = if (part_type == value_type)
            shifted
        else
            self.builder.emit(.cast, part_type, @backingInt(shifted), resize);
        offset += self.static_pool.get(part_type).int_type.bits;
        if (tree.kind(part) == .partial__bits_rest) {
            const name = tree.arg(part, 0);
            if (name != 0 and self.resolver.name_pool.name_of_node(name) != .underscore) {
                self.declare_variable(self.declaration_of(name), part_value);
            }
            continue;
        }
        const part_matched = self.builder.new_block();
        self.match_pattern(tree.arg(part, 1), part_value, part_type, part_matched, failed);
        self.builder.go_to(part_matched);
    }
    self.builder.branch(matched);
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
    // `value` as `target_type` after tests branching to `failed`, when it may be one
    const narrowed = blk: {
        const is_member = self.static_pool.is_member(value_type, target_type);
        // a member that is one case has one tag
        if (is_member and !self.static_pool.brings_cases(target_type)) {
            const is_that_member = self.builder.new_block();
            const test_member = self.tests_case(value, value_type, target_type);
            self.builder.branch_if(test_member, is_that_member, failed);
            self.builder.go_to(is_that_member);
            break :blk self.narrow_to_variant(value, value_type, target_type);
        }
        if (is_member) {
            // the member's tags are a range of the unified variant's tags
            const unified_tag_type = self.static_pool.unified_tag_type(value_type);
            const tag = self.builder.emit_refs(.variant_tag, unified_tag_type, value, .none);
            const low = self.static_pool.unified_offset(value_type, target_type);
            const above_low = self.builder.new_block();
            const in_range = self.builder.new_block();

            const low_tag = self.builder.constant_int(unified_tag_type, low);
            const is_above_low = self.builder.emit_refs(.ge, .bool_type, tag, low_tag);
            self.builder.branch_if(is_above_low, above_low, failed);
            self.builder.go_to(above_low);

            const end = low + self.static_pool.tag_range(target_type);
            const end_tag = self.builder.constant_int(unified_tag_type, end);
            const is_below_end = self.builder.emit_refs(.lt, .bool_type, tag, end_tag);
            self.builder.branch_if(is_below_end, in_range, failed);
            self.builder.go_to(in_range);
            break :blk self.narrow_to_variant(value, value_type, target_type);
        }
        const converts = value_type == target_type or
            self.static_pool.coercion(value_type, target_type) != .incompatible;
        if (converts) break :blk self.coerce(value, value_type, target_type);

        const is_case = self.static_pool.tag(target_type) == .variant_case_type;
        if (is_case and self.can_hold_case(value_type, target_type)) {
            const is_that_case = self.builder.new_block();
            const test_case = self.tests_case(value, value_type, target_type);
            self.builder.branch_if(test_case, is_that_case, failed);
            self.builder.go_to(is_that_case);
            const variant = self.static_pool.get(target_type).variant_case_type.variant;
            break :blk self.narrow_to_variant(value, value_type, variant);
        }
        // it never is one
        return self.builder.branch(failed);
    };
    self.declare_variable(self.declaration_of(binding), narrowed);
    self.builder.branch(matched);
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
    // a record a unified variant holds is one of its members
    const is_member = !is_case and self.static_pool.is_member(value_type, pattern_type);
    if (is_case or is_member) {
        const case_matched = self.builder.new_block();
        const test_case = self.tests_case(value, value_type, pattern_type);
        self.builder.branch_if(test_case, case_matched, failed);
        self.builder.go_to(case_matched);
    }

    const record = if (is_case)
        self.static_pool.get(pattern_type).variant_case_type.payload
    else
        pattern_type;
    const container = if (is_case) blk: {
        const case_type = self.static_pool.get(pattern_type).variant_case_type;
        const narrowed = self.narrow_to_variant(value, value_type, case_type.variant);
        const case_index: Ref = @fromBackingInt(case_type.case_index);
        break :blk self.builder.emit_refs(.variant_payload, record, narrowed, case_index);
    } else if (is_member)
        self.narrow_to_variant(value, value_type, pattern_type)
    else
        value;
    const holder = if (is_case)
        self.payload_place(value_type, pattern_type)
    else if (is_member) .none else self.matched_place;
    const outer_place = self.matched_place;
    defer self.matched_place = outer_place;
    if (record != .none and self.static_pool.tag(record) == .record_type) {
        const arguments = self.resolver.tree.manychildren(self.resolver.tree.arg(pattern, 1));
        for (arguments, 0..) |argument, i| {
            const field = self.field_index(record, argument, i);
            const field_type = self.static_pool.field_type(record, field);
            const field_matched = self.builder.new_block();
            const field_value =
                self.builder.emit(.extract, field_type, @backingInt(container), field);
            const field_pattern = self.resolver.tree.arg_value(argument);
            self.matched_place = self.field_place_in(holder, record, field, field_type);
            self.match_pattern(field_pattern, field_value, field_type, field_matched, failed);
            self.builder.go_to(field_matched);
        }
    }
    self.builder.branch(matched);
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
    // strings and byte pointers compare their bytes, not their addresses, a slice its elements
    const is_slice = self.static_pool.tag(value_type) == .slice_type;
    const is_text = !is_slice and (self.resolver.tree.kind(pattern) == .string or
        (self.is_pointer(value_type) and self.pointee_of(value_type) == .u8_type));
    const operation: Op = if (is_text) .bytes_eq else .eq;
    const equals = self.builder.emit_refs(operation, .bool_type, value, expected);
    self.builder.branch_if(equals, matched, failed);
}

// the `A ||| B` the parameter named by `node` was declared as, in a realization for one member
fn packed_operand(self: *HighLowerer, node: NodeId) Index {
    if (self.resolver.tree.kind(node) != .identifier) return .none;
    const parameter = self.declaration_of(node);
    return self.resolver.generics.packed_parameter(self.body.declaration, parameter);
}

// `?<-`, `??`, `x??` whose outcome the realization decides: `value` is the payload, or never holds
// one
fn unwrap_decided(
    self: *HighLowerer,
    node: NodeId,
    value: Ref,
    value_type: Index,
    always: bool,
) Ref {
    const tree = self.resolver.tree;
    const result_type = self.type_of(node);
    switch (tree.kind(node)) {
        .selftag_arrow => {
            const label = tree.arg(node, 1);
            if (always) {
                self.bind_label(label, value);
            } else {
                const destructures = tree.kind(label) == .partial__destructure;
                const names = if (destructures) tree.manychildren(label) else &[1]NodeId{label};
                for (names) |name| self.declare_variable(self.declaration_of(name), .none);
            }
            return Ref.of(if (always) .bool_true else .bool_false);
        },
        .selftag_unwrap_fallback => {
            if (always) return self.coerce(value, value_type, result_type);
            return self.expression_as(tree.arg(node, 1), result_type);
        },
        else => {
            if (always) return value;
            self.return_fallback(value, value_type, value_type, .none);
            return .none;
        },
    }
}

// what `??` and `?<-` unwrap of `value`: the payload of a case, a member that is one case itself
fn success_payload(self: *HighLowerer, value: Ref, value_type: Index, success: Index) Ref {
    if (self.static_pool.tag(success) != .variant_case_type) {
        return self.narrow_to_variant(value, value_type, success);
    }
    const variant = self.static_pool.get(success).variant_case_type.variant;
    return self.case_payload(self.narrow_to_variant(value, value_type, variant), success);
}

// a payload of one field stands for that field
fn case_payload(self: *HighLowerer, value: Ref, case: Index) Ref {
    const case_type = self.static_pool.get(case).variant_case_type;
    if (case_type.payload == .none) return value;
    const case_index: Ref = @fromBackingInt(case_type.case_index);
    const payload = self.builder.emit_refs(.variant_payload, case_type.payload, value, case_index);
    const fields = self.static_pool.get(case_type.payload).record_type.field_types;
    if (fields.len == 1) return self.builder.emit(.extract, fields[0], @backingInt(payload), 0);
    return payload;
}

fn bind_label(self: *HighLowerer, label: NodeId, value: Ref) void {
    if (self.resolver.tree.kind(label) != .partial__destructure) {
        return self.declare_variable(self.declaration_of(label), value);
    }
    for (self.resolver.tree.manychildren(label), 0..) |name, i| {
        const part_type = self.type_of(name);
        const part = self.builder.emit(.extract, part_type, @backingInt(value), @intCast(i));
        self.declare_variable(self.declaration_of(name), part);
    }
}

// the constant aliases of a loop condition, none reached before the loop
fn hold_aliases(self: *HighLowerer, condition: NodeId) void {
    const mark = self.alias_nodes.len;
    self.resolver.tree.labels_of(condition, &self.alias_nodes);
    for (self.alias_nodes.buffer[mark..self.alias_nodes.len]) |alias| {
        const held = self.new_temporary(self.pointer_to(self.type_of(alias)));
        self.write_current(self.new_temporary(.bool_type), Ref.of(.bool_false));
        self.alias_values.push(held);
    }
}

// a constant alias names the place its condition first reached
fn constant_alias(self: *HighLowerer, node: NodeId, held: u32) Ref {
    const reached = held + 1;
    const first = self.builder.new_block();
    const kept = self.builder.new_block();
    self.builder.branch_if(self.read_current(reached), kept, first);
    self.builder.go_to(first);
    self.write_current(held, self.place(self.resolver.tree.arg(node, 0)));
    self.write_current(reached, Ref.of(.bool_true));
    self.branch_and_enter(kept);
    const pointer = self.read_current(held);
    self.alias_label(self.resolver.tree.arg(node, 1), pointer, self.type_of(node));
    return self.load(self.type_of(node), pointer);
}

// a label is the place at `pointer`, a destructuring one each field of the record there
fn alias_label(self: *HighLowerer, label: NodeId, pointer: Ref, value_type: Index) void {
    const tree = self.resolver.tree;
    if (tree.kind(label) != .partial__destructure) {
        return put_entry(self.allocator, &self.stack_slots, self.declaration_of(label), pointer);
    }
    for (tree.manychildren(label), 0..) |name, i| {
        const field = self.field_pointer(self.type_of(name), pointer, value_type, @intCast(i));
        put_entry(self.allocator, &self.stack_slots, self.declaration_of(name), field);
    }
}

// `?<-` names the payload of `case` in the variant at `variant`, a single field that field
fn alias_payload(self: *HighLowerer, label: NodeId, variant: Ref, case: Index) void {
    const payload_type = self.static_pool.get(case).variant_case_type.payload;
    const pointer_type = self.pointer_to(payload_type);
    const payload = self.builder.emit_refs(.payload_ptr, pointer_type, variant, .none);
    const fields = self.static_pool.get(payload_type).record_type.field_types;
    if (fields.len > 1 or self.resolver.tree.kind(label) == .partial__destructure) {
        return self.alias_label(label, payload, payload_type);
    }
    self.alias_label(label, self.field_pointer(fields[0], payload, payload_type, 0), fields[0]);
}

// whether a variant keeps its payloads where they can be written: not one a strategy or bits make
fn stores_payloads(self: *HighLowerer, subset_or_variant: Index) bool {
    const variant = self.static_pool.whole_of(subset_or_variant);
    if (self.static_pool.tag(variant) != .variant_type) return false;
    const declared = self.static_pool.get(variant).variant_type;
    return declared.tag_mode != .custom and !declared.is_packed;
}

// the variable whose memory holds the place `node` names, 0 for one reached through a pointer
fn place_root(self: *HighLowerer, node: NodeId) NodeId {
    const tree = self.resolver.tree;
    var n = node;
    while (true) switch (tree.kind(n)) {
        .capture => n = tree.arg(n, 0),
        .member, .array_index => {
            if (self.is_pointer(self.type_of(tree.arg(n, 0)))) return 0;
            n = tree.arg(n, 0);
        },
        .identifier => return n,
        else => return 0,
    };
}

// `<-` binds a label, `?<-` tests for the payload and binds it, `??` takes it or the fallback
fn unwrap(self: *HighLowerer, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const kind = tree.kind(node);
    if (kind == .labelarrow) {
        const alias = std.mem.lastIndexOfScalar(NodeId, self.alias_nodes.items(), node);
        if (alias) |i| return self.constant_alias(node, self.alias_values.buffer[i]);
    }
    const result_type = self.type_of(node);
    // a label is the place it names, the payload `?<-` names is where its variant keeps it
    if (kind == .labelarrow) {
        const pointer = self.place(tree.arg(node, 0));
        self.alias_label(tree.arg(node, 1), pointer, result_type);
        return self.load(result_type, pointer);
    }
    const operand_type = self.type_of(tree.arg(node, 0));
    const value_type = self.static_pool.through_pointer(operand_type);
    const in_place = kind == .selftag_arrow and self.stores_payloads(value_type);
    const of_place = in_place and value_type == operand_type;
    const operand = if (of_place)
        self.place(tree.arg(node, 0))
    else
        self.expression(tree.arg(node, 0));
    const value = if (in_place or value_type != operand_type)
        self.load(value_type, operand)
    else
        operand;

    // a parameter realized for a member of `A ||| B` has its success always, never, or as tested
    const packed_variant = self.packed_operand(tree.arg(node, 0));
    const decided = if (packed_variant != .none)
        self.static_pool.packed_unwrap(packed_variant, value_type)
    else
        .tested;
    switch (decided) {
        .always => return self.unwrap_decided(node, value, value_type, true),
        .never => return self.unwrap_decided(node, value, value_type, false),
        .tested => {},
    }
    const is_unified = self.static_pool.tag(value_type) == .unified_variant_type;
    if (!is_unified and self.static_pool.tag(value_type) != .variant_type) return .none;
    // a subset unwraps the first payload case it keeps: its own type, before it is lowered as the
    // whole; a unified variant the first member or member's case with a payload
    const operand_node_type = self.resolver.node_info(self.body, .node_type, tree.arg(node, 0));
    const kept_type = self.static_pool.through_pointer(
        self.static_pool.substitute_type_variables(operand_node_type),
    );
    const case = if (is_unified) self.static_pool.success_of(kept_type) else blk: {
        const kept_payload_case = self.static_pool.first_payload_case(kept_type);
        if (kept_payload_case != .none) break :blk kept_payload_case;
        const cases = self.static_pool.get(value_type).variant_type.cases;
        break :blk cases[self.payload_case_index(value_type)];
    };
    const has_payload = self.tests_case(value, value_type, case);
    if (kind == .selftag_arrow) {
        if (in_place) {
            self.alias_payload(tree.arg(node, 1), operand, case);
        } else {
            self.bind_label(tree.arg(node, 1), self.success_payload(value, value_type, case));
        }
        return has_payload;
    }

    const payload_block = self.builder.new_block();
    const empty_block = self.builder.new_block();
    self.builder.branch_if(has_payload, payload_block, empty_block);
    if (kind == .selftag_unwrap) {
        self.builder.go_to(empty_block);
        self.return_fallback(value, value_type, kept_type, case);
        self.builder.go_to(payload_block);
        return self.success_payload(value, value_type, case);
    }

    const result = self.new_temporary(result_type);
    const merge = self.builder.new_block();
    self.builder.go_to(payload_block);
    const payload = self.success_payload(value, value_type, case);
    const payload_type = self.static_pool.payload_of(value_type);
    self.write_current(result, self.coerce(payload, payload_type, result_type));
    self.builder.branch(merge);
    self.builder.go_to(empty_block);
    self.arm_into(tree.arg(node, 1), result_type, result, merge);
    self.builder.go_to(merge);
    if (self.builder.is_unreachable) return .none;
    return self.read_current(result);
}

// a failed bare `x??` returns the fallback of the result, which may be the case `value` holds:
// each failing case that picks itself is tested in turn, the last failing one needs no test
fn return_fallback(
    self: *HighLowerer,
    value: Ref,
    value_type: Index,
    kept_type: Index,
    unwrapped: Index,
) void {
    const pool = self.static_pool;
    // a value of a subset is none of the cases it leaves out, of a unified variant one of the
    // members' cases or a member
    const mark = pool.scratch.len;
    pool.push_units(kept_type);
    const units = self.resolver.temporary_slice(Index, pool.scratch.len - mark);
    @memcpy(units, pool.scratch.buffer[mark..pool.scratch.len]);
    pool.scratch.len = mark;
    const holds_unwrapped = std.mem.indexOfScalar(Index, units, unwrapped) != null;
    const failing_count = units.len - @intFromBool(holds_unwrapped);
    // the unwrapped case alone never fails
    if (failing_count == 0) return self.emit_unreachable();
    var tested: usize = 0;
    var last_failing: Index = .none;
    for (units) |failing| {
        if (failing == unwrapped) continue;
        if (pool.fallback_case(self.return_type, failing) != failing) continue;
        tested += 1;
        if (tested == failing_count) {
            last_failing = failing;
            break;
        }
        const own_block = self.builder.new_block();
        const next_block = self.builder.new_block();
        self.builder.branch_if(self.tests_case(value, value_type, failing), own_block, next_block);
        self.builder.go_to(own_block);
        self.emit_return(self.fallback(self.return_type, failing));
        self.builder.go_to(next_block);
    }
    self.emit_return(self.fallback(self.return_type, last_failing));
}

// the value `Interpreter.fallback_value` makes, built where it is returned
fn fallback(self: *HighLowerer, fallback_type: Index, failing: Index) Ref {
    const pool = self.static_pool;
    if (!has_value(fallback_type)) return unit();
    switch (pool.tag(fallback_type)) {
        .array_type => {
            const element_type = pool.get(fallback_type).array_type.element;
            var innermost = element_type;
            while (pool.tag(innermost) == .array_type) innermost = pool.element_type(innermost);
            // numbers and `false` are zero bits, arrays of them one zeroed value
            const is_built = switch (pool.tag(innermost)) {
                .record_type, .variant_type, .unified_variant_type, .variant_case_type => true,
                .variant_subset_type => true,
                else => false,
            };
            if (!is_built) return self.builder.emit(.zeroed, fallback_type, 0, 0);
            const element = self.fallback(element_type, .none);
            const mark = self.scratch.len;
            const length = pool.static_length(fallback_type).?;
            for (0..length) |_| self.scratch.push(@backingInt(element));
            const elements = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
            self.scratch.len = mark;
            return self.builder.emit(.aggregate, fallback_type, 0, elements);
        },
        .record_type, .variant_type, .unified_variant_type, .variant_case_type => {},
        .variant_subset_type => {},
        else => return self.builder.emit(.zeroed, fallback_type, 0, 0),
    }

    // a record is built like a case, a member of a unified variant that is one case is itself
    const case = if (pool.tag(fallback_type) == .record_type)
        fallback_type
    else
        pool.fallback_case(fallback_type, failing);
    const is_case = pool.tag(case) == .variant_case_type;
    const value = if (!is_case and case != fallback_type) self.fallback(case, .none) else blk: {
        const record = if (is_case) pool.get(case).variant_case_type.payload else case;
        const mark = self.scratch.len;
        const types = &self.resolver.types;
        const field_nodes = if (record == .none) &.{} else types.field_nodes_of(record);
        for (field_nodes, 0..) |field_node, i| {
            if (ParseTree.Param.from_node(self.resolver.tree, field_node).default != 0) {
                self.scratch.push(none);
                continue;
            }
            const field_value = self.fallback(pool.field_type(record, i), .none);
            self.scratch.push(@backingInt(field_value));
        }
        break :blk self.constructed(case, mark);
    };
    if (pool.tag(fallback_type) != .unified_variant_type) return value;
    return self.coerce(value, case, fallback_type);
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
    const alias_mark = self.alias_nodes.len;
    defer self.alias_nodes.len = alias_mark;
    defer self.alias_values.len = alias_mark;
    switch (kind) {
        .@"while", .stcwhile, .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => {
            repeat = parts.repeat;
            self.hold_aliases(parts.cond);
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
            const element_node = if (parts.variable != 0) parts.variable else parts.head;
            walk = .{ .element = self.declaration_of(element_node) };
            const for_loop: ForLoop = .{
                .sequence = parts.seq,
                .sequence_type = self.type_of(parts.seq),
                .result_type = result_type,
                .collects_dynamic = collects_dynamic,
                .collected = &collected,
                .blocks = .{ .head = head, .body = body_block, .next = next, .exit = exit },
            };

            const array_type = self.dereferenced_type(for_loop.sequence_type);
            if (self.resolver.tree.props(for_loop.sequence).range) {
                self.enter_range_head(for_loop, &walk);
            } else if (self.static_pool.get(array_type) == .array_type or
                self.static_pool.tag(array_type) == .slice_type)
            {
                self.enter_array_head(for_loop, &walk);
            } else {
                self.enter_iterator_head(for_loop, &walk);
            }
        },
        else => unreachable,
    }

    self.builder.go_to(body_block);
    if (walk.element != .none) {
        const element = blk: {
            if (walk.counter == none) {
                break :blk self.method_call(walk.sequence_type, .next, walk.sequence);
            }
            if (walk.sequence == .none) break :blk self.read_current(walk.counter);
            const element_pointer = self.pointer_to(walk.sequence_type);
            const index = self.read_current(walk.counter);
            const pointer =
                self.builder.emit_refs(.index_ptr, element_pointer, walk.sequence, index);
            break :blk self.load(walk.sequence_type, pointer);
        };
        self.declare_variable(walk.element, element);
    }
    self.loops.push(.{ .break_block = exit, .continue_block = next, .defers = self.defers.len });
    const value = self.expression(parts.body);
    const collects = collected != .none and !self.builder.is_unreachable and
        has_value(self.type_of(parts.body));
    if (collects) {
        const value_type = self.type_of(parts.body);
        // stores the value at `count` and counts it, a fixed-size array ends the loop once full
        const index = self.read_current(count);
        const element_type = self.static_pool.get(result_type).array_type.element;
        const element_pointer = self.pointer_to(element_type);
        const slot = self.builder.emit_refs(.index_ptr, element_pointer, collected, index);
        self.store(slot, self.coerce(value, value_type, element_type));
        const one = self.builder.constant_int(.u64_type, 1);
        const new_count = self.builder.emit_refs(.add, .u64_type, index, one);
        self.write_current(count, new_count);
        if (!collects_dynamic) {
            const has_room = self.builder.new_block();
            const full = self.builder.constant_int(.u64_type, capacity);
            const is_below_full = self.builder.emit_refs(.lt, .bool_type, new_count, full);
            self.builder.branch_if(is_below_full, has_room, exit);
            self.builder.go_to(has_room);
        }
    }
    self.loops.len -= 1;

    self.branch_and_enter(next);
    if (repeat != 0) _ = self.expression(repeat);
    if (walk.counter != none) {
        const counter = walk.counter;
        const counter_type = walk.counter_type;
        const current = self.read_current(counter);
        if (walk.last != .none) {
            const stepping = self.builder.new_block();
            const is_last = self.builder.emit_refs(.eq, .bool_type, current, walk.last);
            self.builder.branch_if(is_last, exit, stepping);
            self.builder.go_to(stepping);
        }
        const one = self.builder.constant_int(counter_type, 1);
        self.write_current(counter, self.builder.emit_refs(.add, counter_type, current, one));
    }
    self.builder.branch(head);
    self.builder.seal(head);
    self.builder.go_to(exit);

    if (collected == .none) return unit();
    if (!collects_dynamic) return self.load(result_type, collected);
    const start = self.builder.constant_int(.u64_type, 0);
    const end = self.read_current(count);
    const bounds = self.builder.list(&.{ @backingInt(start), @backingInt(end) });
    return self.builder.emit(.dyn, result_type, @backingInt(collected), bounds);
}

// the head stays unsealed: the edge back from the end of the body comes later
fn enter_loop_head(self: *HighLowerer, head: u32) void {
    self.builder.branch(head);
    self.builder.enter(head);
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
        const is_empty = self.builder.emit_refs(if (range.incl) .lt else .le, .bool_type, end, low);
        const zero = self.builder.constant_int(element_type, 0);
        const choices = self.builder.list(&.{ @backingInt(zero), @backingInt(span) });
        span = self.builder.emit(.select, element_type, @backingInt(is_empty), choices);
        const resize = @backingInt(StaticPool.CastKind.int_resize);
        const length = if (element_type == .u64_type)
            span
        else
            self.builder.emit(.cast, .u64_type, @backingInt(span), resize);
        // an alloca with a length, for the elements of a dynamic array
        const element_pointer =
            self.pointer_to(self.static_pool.get(for_loop.result_type).array_type.element);
        for_loop.collected.* = self.builder.emit_refs(.alloca, element_pointer, length, .none);
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
    if (range.incl) walk.last = end;
}

// arrays, and slices from the address of their first element up to their length
fn enter_array_head(self: *HighLowerer, for_loop: ForLoop, walk: *SequenceWalk) void {
    const sequence_type = for_loop.sequence_type;
    const array_type = self.dereferenced_type(sequence_type);
    const is_slice = self.static_pool.tag(array_type) == .slice_type;
    const slice = if (is_slice) self.slice_value(for_loop.sequence) else .none;
    const element_type = if (is_slice)
        self.static_pool.get(array_type).slice_type.element
    else
        self.static_pool.get(array_type).array_type.element;
    const by_value = self.is_pointer(sequence_type) or self.is_dynamic_array(sequence_type);
    const array = if (is_slice)
        self.slice_part(slice, array_type, 0)
    else if (by_value)
        self.expression(for_loop.sequence)
    else
        self.place(for_loop.sequence);
    const length = if (is_slice)
        self.slice_part(slice, array_type, 1)
    else
        self.array_length(sequence_type);
    const counter = self.new_temporary(.u64_type);
    self.write_current(counter, self.builder.constant_int(.u64_type, 0));
    if (for_loop.collects_dynamic) {
        const element_pointer =
            self.pointer_to(self.static_pool.get(for_loop.result_type).array_type.element);
        for_loop.collected.* = self.builder.emit_refs(.alloca, element_pointer, length, .none);
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
    const resize = @backingInt(StaticPool.CastKind.int_resize);
    const wide = if (offset_type == .i64_type or offset_type == .u64_type)
        offset
    else
        self.builder.emit(.cast, .i64_type, @backingInt(offset), resize);
    const signed_offset = if (subtracts)
        self.builder.emit_refs(.neg, self.type_of_ref(wide), wide, .none)
    else
        wide;
    return self.builder.emit_refs(.index_ptr, pointer_type, base, signed_offset);
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
            const arguments = self.builder.list(&.{@backingInt(receiver)});
            return self.builder.emit(.call, return_type, @backingInt(callee), arguments);
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
    const builtin = if (tree.kind(node) == .builtin_call)
        self.resolver.name_pool.name_of_node(callee)
    else
        .none;
    // `asm ".."` with the static text the checker took
    if (builtin == .@"asm") {
        const text = self.static_value_of(tree.arg_value(arguments[0])).?;
        return self.builder.emit(.inline_asm, .unit_type, @backingInt(Ref.of(text)), 0);
    }
    if (builtin == .syscall) {
        const mark = self.scratch.len;
        defer self.scratch.len = mark;
        for (arguments) |argument| {
            self.scratch.push(@backingInt(self.expression(tree.arg_value(argument))));
        }
        const operands = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
        return self.builder.emit(.syscall, .i64_type, 0, operands);
    }
    // a stcfun call producing a function stands for its realization
    if (tree.kind(node) == .fun_call) {
        const callee_declaration = self.declaration_of(callee);
        const is_static_function = callee_declaration != .none and
            self.resolver.decl_pool.get(callee_declaration, .kind) == .static_function;
        if (is_static_function) {
            const realization = self.declaration_of(node);
            if (realization != .none) return self.function_value(realization);
        }
    }

    const declaration = self.declaration_of(node);
    if (declaration != .none and self.resolver.decl_pool.get(declaration, .kind).is_function()) {
        return self.direct_call(declaration, callee, arguments, result_type);
    }
    if (declaration == .none and tree.kind(callee) == .member) {
        const receiver_type = self.type_of(tree.arg(callee, 0));
        switch (self.resolver.calls.builtin_member_of(callee, receiver_type, result_type)) {
            .builtin_init => {
                if (self.static_pool.tag(result_type) == .record_type) {
                    return self.construct(result_type, &.{});
                }
                return self.builder.emit(.zeroed, result_type, 0, 0);
            },
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
    const function = self.expression(callee);
    const mark = self.scratch.len;
    for (arguments, 0..) |argument, i| {
        const target_type = self.parameter_type(callee_type, i);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), target_type);
        self.scratch.push(@backingInt(value));
    }
    const argument_list = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    return self.builder.emit(.call, result_type, @backingInt(function), argument_list);
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
    for (self.resolver.bodies.captures_of(&self.resolver.decl_pool, head)) |captured| {
        // variables captured by reference are passed as the pointer to them
        const value = if (self.resolver.declarations.is_captured_by_reference(captured))
            self.variable_place(captured)
        else
            self.load_variable(captured);
        self.scratch.push(@backingInt(value));
    }
    var arguments = all_arguments;
    if (implicit_self_count == 1) {
        // `value.method()` passes the receiver by address, `Type.method(value)` as first argument
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
        self.scratch.push(@backingInt(value));
        if (!is_bound) arguments = arguments[1..];
    }

    // where the argument of the first parameter is in scratch, `none` for those not passed
    const parameters_at = self.scratch.len;
    for (parameter_nodes) |_| self.scratch.push(none);
    for (arguments, 0..) |argument, i| {
        const name_node = self.resolver.tree.arg_name(argument);
        const parameter_index = if (name_node == 0) i else blk: {
            const name = self.resolver.name_pool.name_of_node(name_node);
            break :blk self.resolver.declarations.parameter_index(parameter_nodes, name) orelse i;
        };
        const parameter_position = parameter_index + implicit_self_count;
        const target_type = self.parameter_type(function_type, parameter_position);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), target_type);
        self.scratch.buffer[parameters_at + parameter_index] = @backingInt(value);
    }

    // defaults are expressions of the callee's body and may read the parameters before them
    const needs_defaults = for (0..parameter_nodes.len) |j| {
        if (self.scratch.buffer[parameters_at + j] == none) break true;
    } else false;
    const saved_body = self.body;
    // a recursive call declares the caller's own parameters, which hold on after the call
    const saved_parameters = self.scratch.len;
    const is_recursive = if (self.resolver.bodies.body_of(realized)) |body|
        body.first_node == saved_body.first_node
    else
        false;
    if (needs_defaults and is_recursive) {
        for (parameter_nodes) |parameter_node| {
            const parameter = self.declaration_of(parameter_node);
            const slot = self.stack_slots.get(parameter) orelse Ref.none;
            const value = if (slot == .none) self.load_variable(parameter) else Ref.none;
            self.scratch.push(@backingInt(slot));
            self.scratch.push(@backingInt(value));
        }
    }
    if (needs_defaults) {
        if (self.resolver.bodies.body_of(realized)) |body| self.body = body;
        for (parameter_nodes, 0..) |parameter_node, j| {
            const passed = self.scratch.buffer[parameters_at + j];
            if (passed == none) continue;
            self.declare_variable(self.declaration_of(parameter_node), @fromBackingInt(passed));
        }
        for (parameter_nodes, 0..) |parameter_node, j| {
            if (self.scratch.buffer[parameters_at + j] != none) continue;
            const default = ParseTree.Param.from_node(self.resolver.tree, parameter_node).default;
            const parameter_position = j + implicit_self_count;
            const value = if (default != 0)
                self.expression_as(default, self.parameter_type(function_type, parameter_position))
            else
                Ref.none;
            self.declare_variable(self.declaration_of(parameter_node), value);
            self.scratch.buffer[parameters_at + j] = @backingInt(value);
        }
    }
    if (needs_defaults and is_recursive) {
        for (parameter_nodes, 0..) |parameter_node, j| {
            const parameter = self.declaration_of(parameter_node);
            const slot: Ref = @fromBackingInt(self.scratch.buffer[saved_parameters + 2 * j]);
            const value: Ref = @fromBackingInt(self.scratch.buffer[saved_parameters + 2 * j + 1]);
            if (slot != .none) {
                put_entry(self.allocator, &self.stack_slots, parameter, slot);
            } else if (value != .none) {
                self.write_current(@backingInt(parameter), value);
            }
        }
        self.scratch.len = saved_parameters;
    }
    self.body = saved_body;

    const argument_list = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    const call_type = if (result_type == .none) self.return_type_of(realized) else result_type;
    return self.builder.emit(.call, call_type, @backingInt(function_ref), argument_list);
}

// records

fn construct(self: *HighLowerer, target_type: Index, arguments: []const NodeId) Ref {
    const pool = self.static_pool;
    const is_case = pool.tag(target_type) == .variant_case_type;
    const record = if (is_case) pool.get(target_type).variant_case_type.payload else target_type;
    const mark = self.scratch.len;
    if (record == .none) return self.constructed(target_type, mark);

    for (self.resolver.types.field_nodes_of(record)) |_| self.scratch.push(none);
    for (arguments, 0..) |argument, i| {
        const field = self.field_index(record, argument, i);
        const field_type = self.static_pool.field_type(record, field);
        const value = self.expression_as(self.resolver.tree.arg_value(argument), field_type);
        self.scratch.buffer[mark + field] = @backingInt(value);
    }
    return self.constructed(target_type, mark);
}

// a record or case of the fields in the scratch at `mark`, those still missing defaulted or zeroed
fn constructed(self: *HighLowerer, target_type: Index, mark: u32) Ref {
    const pool = self.static_pool;
    const is_case = pool.tag(target_type) == .variant_case_type;
    const of_variant = if (is_case)
        pool.get(target_type).variant_case_type.variant
    else
        target_type;
    // a case of a packed variant is a value of its own size, of the case's type
    const variant = if (pool.is_unstorable(of_variant)) target_type else of_variant;
    const record = if (is_case) pool.get(target_type).variant_case_type.payload else target_type;
    const case_index: u32 = if (is_case) pool.get(target_type).variant_case_type.case_index else 0;
    if (record == .none) {
        return self.builder.emit(.variant_make, variant, case_index, @backingInt(Ref.none));
    }

    self.complete_fields(record, mark);
    const fields = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
    const aggregate = self.builder.emit(.aggregate, record, 0, fields);
    if (!is_case) return aggregate;
    return self.builder.emit(.variant_make, variant, case_index, @backingInt(aggregate));
}

// `base with (field = ..)`: the fields of `base`, the named ones replaced, completed by the guards
// of the record
fn record_update(self: *HighLowerer, node: NodeId) Ref {
    var base_type = self.type_of(self.resolver.tree.arg(node, 0));
    var base = self.expression(self.resolver.tree.arg(node, 0));
    if (self.is_pointer(base_type)) {
        base = self.load(self.pointee_of(base_type), base);
        base_type = self.pointee_of(base_type);
    }
    // a case is updated in its payload, made again as that case
    const case = if (self.static_pool.tag(base_type) == .variant_case_type) base_type else .none;
    if (case != .none) {
        const case_type = self.static_pool.get(case).variant_case_type;
        const narrowed = self.narrow_to_variant(base, base_type, case_type.variant);
        const case_index: Ref = @fromBackingInt(case_type.case_index);
        base = self.builder.emit_refs(.variant_payload, case_type.payload, narrowed, case_index);
        base_type = case_type.payload;
    }

    const tree = self.resolver.tree;
    const arguments = tree.manychildren(tree.arg(node, 1));
    // parts of fields (`pos.x = ..`) are written into a copy in memory, in order with the others
    const copy: ?Ref = for (arguments) |argument| {
        const name = tree.arg_name(argument);
        if (name != 0 and tree.kind(name) != .identifier) {
            const slot = self.alloca(base_type);
            self.store(slot, base);
            break slot;
        }
    } else null;
    if (copy) |slot| {
        // as in an assignment the value comes before the place. the records a part passes that
        // have guards are completed again, innermost first, as in `x with (a = x.a with (b = ..))`
        for (arguments) |argument| {
            const part = tree.arg_name(argument);
            const value = self.expression_as(tree.arg_value(argument), self.type_of(part));
            const passed_mark = self.scratch.len;
            self.store(self.with_part_place(slot, base_type, part), value);
            var k = self.scratch.len;
            while (k > passed_mark) {
                k -= 2;
                const record: Index = @fromBackingInt(self.scratch.buffer[k]);
                const record_pointer: Ref = @fromBackingInt(self.scratch.buffer[k + 1]);
                const record_value = self.load(record, record_pointer);
                const mark = self.scratch.len;
                const field_count = self.static_pool.get(record).record_type.field_types.len;
                for (0..field_count) |i| {
                    const field_type = self.static_pool.field_type(record, i);
                    const whole = @backingInt(record_value);
                    const field = self.builder.emit(.extract, field_type, whole, @intCast(i));
                    self.scratch.push(@backingInt(field));
                }
                self.complete_fields(record, mark);
                const fields = self.builder.list(self.scratch.buffer[mark..self.scratch.len]);
                self.scratch.len = mark;
                self.store(record_pointer, self.builder.emit(.aggregate, record, 0, fields));
            }
            self.scratch.len = passed_mark;
        }
        base = self.load(base_type, slot);
    }

    const field_count = self.static_pool.get(base_type).record_type.field_types.len;
    const mark = self.scratch.len;
    for (0..field_count) |i| {
        const field_type = self.static_pool.field_type(base_type, i);
        const field = self.builder.emit(.extract, field_type, @backingInt(base), @intCast(i));
        self.scratch.push(@backingInt(field));
    }
    if (copy == null) for (arguments, 0..) |argument, i| {
        const field = self.field_index(base_type, argument, i);
        const field_type = self.static_pool.field_type(base_type, field);
        const value = self.expression_as(tree.arg_value(argument), field_type);
        self.scratch.buffer[mark + field] = @backingInt(value);
    };
    return self.constructed(if (case != .none) case else base_type, mark);
}

// the address of `a.b[i]` of `x with (a.b[i] = ..)` in the copy at `record`. pushes the type and
// address of each record with guards it passes below the copy, the outermost first
fn with_part_place(self: *HighLowerer, record: Ref, record_type: Index, node: NodeId) Ref {
    const tree = self.resolver.tree;
    const part_type = self.type_of(node);
    const pointer_type = self.pointer_to(part_type);
    switch (tree.kind(node)) {
        .identifier => {
            const name = self.resolver.name_pool.name_of_node(node);
            const field = self.static_pool.lookup_member(record_type, name).field.index;
            return self.field_pointer(part_type, record, record_type, field);
        },
        .member => {
            const parent = tree.arg(node, 0);
            const parent_type = self.type_of(parent);
            const parent_pointer = self.with_part_place(record, record_type, parent);
            for (self.resolver.types.field_nodes_of(parent_type)) |field_node| {
                if (ParseTree.Param.from_node(tree, field_node).@"else" == 0) continue;
                self.scratch.push(@backingInt(parent_type));
                self.scratch.push(@backingInt(parent_pointer));
                break;
            }
            const name = self.resolver.name_pool.name_of_node(tree.arg(node, 1));
            const field = self.static_pool.lookup_member(parent_type, name).field.index;
            return self.field_pointer(part_type, parent_pointer, parent_type, field);
        },
        else => {
            const array_pointer = self.with_part_place(record, record_type, tree.arg(node, 0));
            const index = self.expression(tree.arg(node, 1));
            return self.builder.emit_refs(.index_ptr, pointer_type, array_pointer, index);
        },
    }
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
    // only the fields a default or guard reads, or a guard repairs, become locals
    if (record_body != null) {
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
                if (reading == 0) continue;
                const subtree = self.resolver.tree.subtree(reading);
                for (subtree[0]..subtree[1]) |j| {
                    const node: NodeId = @intCast(j);
                    const local = @backingInt(self.declaration_of(node)) -% self.body.first_local;
                    const is_field = self.resolver.tree.kind(node) == .identifier and
                        local < fields.len;
                    if (is_field) locals.set(local);
                }
            }
        }
    }

    for (0..fields.len) |i| {
        const given = self.scratch.buffer[mark + i];
        if (!locals.isSet(i) or given == none) continue;
        self.declare_variable(self.field_local(i), @fromBackingInt(given));
    }
    for (fields, 0..) |field, i| {
        if (self.scratch.buffer[mark + i] != none) continue;
        const field_type = self.static_pool.field_type(record, i);
        const default = ParseTree.Param.from_node(self.resolver.tree, field).default;
        const value = if (default != 0)
            self.expression_as(default, field_type)
        else
            self.builder.emit(.zeroed, field_type, 0, 0);
        self.scratch.buffer[mark + i] = @backingInt(value);
        if (locals.isSet(i)) self.declare_variable(self.field_local(i), value);
    }
    // a guard's `else` assigns fields or is the field's new value
    for (fields, 0..) |field, i| {
        if (!guarded.isSet(i)) continue;
        const parameter = ParseTree.Param.from_node(self.resolver.tree, field);
        if (parameter.where == 0) continue;

        // continues where the guard fails, `holds` is the block where it holds
        const holds = self.builder.new_block();
        const fails = self.builder.new_block();
        self.builder.branch_if(self.expression_as(parameter.where, .bool_type), holds, fails);
        self.builder.go_to(fails);
        const repair = parameter.@"else";
        if (self.resolver.tree.kind(repair) == .assign) {
            _ = self.expression(repair);
        } else {
            const repaired = self.expression_as(repair, self.static_pool.field_type(record, i));
            self.store_variable(self.field_local(i), repaired);
        }
        self.branch_and_enter(holds);
    }
    for (0..fields.len) |i| {
        if (!guarded.isSet(i)) continue;
        self.scratch.buffer[mark + i] = @backingInt(self.load_variable(self.field_local(i)));
    }
}

fn field_local(self: *HighLowerer, field: usize) DeclPool.Index {
    return @fromBackingInt(@intCast(self.body.first_local + field));
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
            return self.function_value(@fromBackingInt(@backingInt(trait) + 1 + method.index));
        },
        .none, .builtin_len, .builtin_init, .builtin_deinit => .none,
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
    // a payload a strategy or bits make is no place, it is read out of the value
    const base_type = self.static_pool.through_pointer(parent_type);
    const is_case = self.static_pool.tag(base_type) == .variant_case_type;
    const pool = self.static_pool;
    const variant = if (is_case) pool.get(base_type).variant_case_type.variant else .none;
    const is_value = is_case and !self.stores_payloads(variant);
    if (!is_value and (self.is_pointer(parent_type) or self.is_place(parent))) {
        return self.load(field_type, self.place(node));
    }
    const parent_value = self.expression(parent);
    const value =
        if (base_type == parent_type) parent_value else self.load(base_type, parent_value);
    if (!is_case) return self.builder.emit(.extract, field_type, @backingInt(value), field);
    const case_type = self.static_pool.get(base_type).variant_case_type;
    const case_index: Ref = @fromBackingInt(case_type.case_index);
    const payload = self.builder.emit_refs(.variant_payload, case_type.payload, value, case_index);
    return self.builder.emit(.extract, field_type, @backingInt(payload), field);
}

// lengths are static, the checker rejects one of a runtime-length array
fn array_length(self: *HighLowerer, value_type: Index) Ref {
    const array_type = self.dereferenced_type(value_type);
    const length = self.static_pool.get(array_type).array_type.length;
    return self.builder.constant_int(.u64_type, self.static_pool.get(length).int_value.bits);
}

fn variant_tag_of(self: *HighLowerer, variant: NodeId, value_type: Index, base_type: Index) Ref {
    if (self.static_pool.tag(base_type) == .variant_case_type) {
        return self.tag_constant(base_type, base_type);
    }
    const variant_tag_type = self.static_pool.tag_type_of(base_type);
    // through a pointer to a packed variant, which has no size, the tag is read at the address
    const value = if (self.is_pointer(value_type) and !self.static_pool.is_unstorable(base_type))
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
            if (declaration != .none) {
                const local = self.variable_place(declaration);
                if (local != .none) return local;
            }
        },
        .member => if (self.field_place(node)) |pointer| return pointer,
        .array_index => if (tree.names_place(node)) return self.element_place(node, value_type),
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
            return self.field_pointer(field.field_type, base, record_type, field.index);
        },
        else => return null,
    }
}

fn element_place(self: *HighLowerer, node: NodeId, element_type: Index) Ref {
    const array = self.resolver.tree.arg(node, 0);
    const array_type = self.type_of(array);
    // an element of a slice is checked against its length
    const sliced = self.dereferenced_type(array_type);
    if (self.static_pool.tag(sliced) == .slice_type) {
        const slice = self.slice_value(array);
        const index = self.as_length(self.expression(self.resolver.tree.arg(node, 1)));
        const length = self.slice_part(slice, sliced, 1);
        self.check(self.builder.emit_refs(.lt, .bool_type, index, length));
        const first = self.slice_part(slice, sliced, 0);
        return self.builder.emit_refs(.index_ptr, self.pointer_to(element_type), first, index);
    }
    const by_value = self.is_pointer(array_type) or self.is_dynamic_array(array_type);
    const base = if (by_value) self.expression(array) else self.place(array);
    const element_pointer = self.pointer_to(element_type);
    const index = self.expression(self.resolver.tree.arg(node, 1));
    return self.builder.emit_refs(.index_ptr, element_pointer, base, index);
}
