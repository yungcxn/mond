const std = @import("std");
const containers = @import("../containers.zig");
const StaticPool = @import("../resolver/StaticPool.zig");
const HighIr = @import("HighIr.zig");
const Ref = HighIr.Ref;
const Op = HighIr.Op;
const Index = StaticPool.Index;

// builds one function of `HighIr` in ssa form without knowing the language, phis on demand as in
// braun et al., "simple and efficient construction of static single assignment form", 2013
const FunctionBuilder = @This();

pub const none: u32 = std.math.maxInt(u32);

// constants and globals have the top bit of a ref set, instructions never
const constant_bit: u32 = 1 << 31;

const Instruction = struct {
    op: Op,
    result_type: Index,
    a: u32,
    b: u32,
    block: u32,
    origin: u32,
};

const BlockState = struct {
    // all predecessors are known, reading a variable may complete its phis right away
    sealed: bool,
    // head of the block's predecessor edge list
    predecessors: u32,
    // head of the phis waiting for the block to be sealed
    pending_phis: u32,
    predecessor_count: u32,
};

const Edge = struct { from_block: u32, next_edge: u32 };
const PendingPhi = struct { variable: u32, phi: u32, next_pending: u32 };
const ValueKey = struct { op: Op, result_type: Index, a: u32, b: u32 };

// where `freeze` places an instruction inside its block
const Placement = enum(u32) {
    phi_or_param,
    // allocas the lowerer adds to the entry block late must still come before its code
    undef_or_entry_alloca,
    other,
};

const placement_count: u32 = @typeInfo(Placement).@"enum".field_names.len;

allocator: std.mem.Allocator,
pool: *StaticPool,
instructions: containers.StructOfArrays(Instruction),
blocks: containers.StructOfArrays(BlockState),
edges: containers.StructOfArrays(Edge),
pending_phis: containers.StructOfArrays(PendingPhi),
// operand lists of instructions: a length, then the items
operand_lists: containers.DynamicBuffer(u32),
scratch: containers.DynamicBuffer(u32),
// for each instruction: the instruction it turned out to equal (trivial phis), or `none`
aliases: containers.DynamicBuffer(u32),
// old block and instruction numbers to their frozen ones
renumbering: containers.DynamicBuffer(u32),
// the value of a variable at the end of a block, keyed by `variable << 32 | block`
definitions: std.AutoHashMapUnmanaged(u64, Ref) = .empty,
// pure instructions already emitted in the current block, for local value numbering
value_numbers: std.AutoHashMapUnmanaged(ValueKey, Ref) = .empty,
current_block: u32 = 0,
// what the instructions emitted now come from, a tree node for the lowerer, for debug info
current_origin: u32 = 0,
// the current block ended in a terminator, anything emitted now would be dead
is_unreachable: bool = false,

pub fn init(allocator: std.mem.Allocator, pool: *StaticPool) FunctionBuilder {
    return .{
        .allocator = allocator,
        .pool = pool,
        .instructions = .init(allocator, 1024),
        .blocks = .init(allocator, 128),
        .edges = .init(allocator, 256),
        .pending_phis = .init(allocator, 64),
        .operand_lists = .init(allocator, 1024),
        .scratch = .init(allocator, 256),
        .aliases = .init(allocator, 1024),
        .renumbering = .init(allocator, 1024),
    };
}

pub fn deinit(self: *FunctionBuilder) void {
    self.definitions.deinit(self.allocator);
    self.value_numbers.deinit(self.allocator);
    self.instructions.deinit();
    self.blocks.deinit();
    self.edges.deinit();
    self.pending_phis.deinit();
    self.operand_lists.deinit();
    self.scratch.deinit();
    self.aliases.deinit();
    self.renumbering.deinit();
}

// forgets the previous function, keeping the memory
pub fn reset(self: *FunctionBuilder) void {
    self.instructions.truncate(0);
    self.blocks.truncate(0);
    self.edges.truncate(0);
    self.pending_phis.truncate(0);
    self.operand_lists.len = 0;
    self.scratch.len = 0;
    self.aliases.len = 0;
    self.renumbering.len = 0;
    self.definitions.clearRetainingCapacity();
    self.value_numbers.clearRetainingCapacity();
    self.is_unreachable = false;
    self.current_origin = 0;
}

// instructions

pub fn constant_int(self: *FunctionBuilder, int_type: Index, bits: u64) Ref {
    return Ref.of(self.pool.intern(.{ .int_value = .{ .value_type = int_type, .bits = bits } }));
}

pub fn result_type_of(self: *const FunctionBuilder, instruction: Ref) Index {
    return self.instructions.column(.result_type)[@backingInt(instruction)];
}

pub fn block_count(self: *const FunctionBuilder) u32 {
    return self.blocks.len();
}

pub fn list(self: *FunctionBuilder, items: []const u32) u32 {
    const list_start = self.operand_lists.len;
    self.operand_lists.push(@intCast(items.len));
    self.operand_lists.append(items);
    return list_start;
}

// appends to `block` without folding or numbering, for phis, `undef` and `alloca`
pub fn emit_raw(
    self: *FunctionBuilder,
    op: Op,
    result_type: Index,
    a: u32,
    b: u32,
    block: u32,
) Ref {
    self.instructions.push(.{
        .op = op,
        .result_type = result_type,
        .a = a,
        .b = b,
        .block = block,
        .origin = self.current_origin,
    });
    return @fromBackingInt(self.instructions.len() - 1);
}

pub fn emit(self: *FunctionBuilder, op: Op, result_type: Index, a: u32, b: u32) Ref {
    if (self.is_unreachable) return .none;
    // constant operands of integer and boolean operators give a constant, nothing is emitted
    const folded: ?Ref = blk: {
        const folding = op.folding();
        if (folding == .none) break :blk null;
        const unary = folding == .unary;

        const left: Ref = @fromBackingInt(a);
        const right: Ref = if (unary) Ref.of(.unit_value) else @fromBackingInt(b);
        if (!left.is_const() or !right.is_const()) break :blk null;

        const left_value = left.value();
        const right_value = right.value();
        if (left_value == .bool_true or left_value == .bool_false) {
            const right_is_bool = right_value == .bool_true or right_value == .bool_false;
            if (!unary and !right_is_bool) break :blk null;
            const left_is_true = left_value == .bool_true;
            const right_is_true = right_value == .bool_true;
            const result = switch (op) {
                .not => !left_is_true,
                .bit_and => left_is_true and right_is_true,
                .bit_or => left_is_true or right_is_true,
                .bit_xor, .ne => left_is_true != right_is_true,
                .eq => left_is_true == right_is_true,
                else => break :blk null,
            };
            break :blk Ref.of(if (result) .bool_true else .bool_false);
        }

        const pool = self.pool;
        if (pool.tag(left_value) != .int_value) break :blk null;
        if (!unary and pool.tag(right_value) != .int_value) break :blk null;

        const operand_type = pool.get(left_value).int_value.value_type;
        if (pool.get(operand_type) != .int_type) break :blk null;
        if (folding != .comparison and pool.get(result_type) != .int_type) break :blk null;

        const int_type = pool.get(operand_type).int_type;
        const left_bits = normalize(pool.get(left_value).int_value.bits, int_type);
        const right_bits = if (unary)
            0
        else
            normalize(pool.get(right_value).int_value.bits, int_type);

        if (folding == .comparison) {
            const signed = int_type.signedness == .signed;
            const signed_left: i64 = @bitCast(left_bits);
            const signed_right: i64 = @bitCast(right_bits);
            const holds = switch (op) {
                .eq => left_bits == right_bits,
                .ne => left_bits != right_bits,
                .lt => if (signed) signed_left < signed_right else left_bits < right_bits,
                .gt => if (signed) signed_left > signed_right else left_bits > right_bits,
                .le => if (signed) signed_left <= signed_right else left_bits <= right_bits,
                else => if (signed) signed_left >= signed_right else left_bits >= right_bits,
            };
            break :blk Ref.of(if (holds) .bool_true else .bool_false);
        }
        const result = compute_integers(op, int_type, left_bits, right_bits) orelse
            break :blk null;
        break :blk self.constant_int(
            result_type,
            normalize(result, pool.get(result_type).int_type),
        );
    };
    if (folded) |constant| return constant;

    const swap = op.is_commutative() and b < a;
    const key = ValueKey{
        .op = op,
        .result_type = result_type,
        .a = if (swap) b else a,
        .b = if (swap) a else b,
    };
    if (op.is_pure()) if (self.value_numbers.get(key)) |known| return known;

    const instruction = self.emit_raw(op, result_type, key.a, key.b, self.current_block);
    if (op.is_pure()) self.value_numbers.put(self.allocator, key, instruction) catch @panic("OOM");
    if (op.is_terminator()) self.is_unreachable = true;
    return instruction;
}

pub fn emit_refs(self: *FunctionBuilder, op: Op, result_type: Index, a: Ref, b: Ref) Ref {
    return self.emit(op, result_type, @backingInt(a), @backingInt(b));
}

// null when the result is not defined: division by zero, overflowing division, oversized shifts
fn compute_integers(op: Op, int_type: StaticPool.IntType, left: u64, right: u64) ?u64 {
    const signed = int_type.signedness == .signed;
    const signed_left: i64 = @bitCast(left);
    const signed_right: i64 = @bitCast(right);
    return switch (op) {
        .add => left +% right,
        .sub => left -% right,
        .mul => left *% right,
        .bit_and => left & right,
        .bit_or => left | right,
        .bit_xor => left ^ right,
        .neg => 0 -% left,
        .not => ~left,
        .div, .rem => {
            if (right == 0 or signed and signed_right == -1) return null;
            if (!signed) return if (op == .div) left / right else left % right;
            const quotient = if (op == .div)
                @divTrunc(signed_left, signed_right)
            else
                @rem(signed_left, signed_right);
            return @bitCast(quotient);
        },
        .shl, .shr => {
            if (right >= int_type.bits) return null;
            const shift: u6 = @intCast(right);
            if (op == .shl) return left << shift;
            return if (signed) @bitCast(signed_left >> shift) else left >> shift;
        },
        else => null,
    };
}

// the bits of an integer of `int_type`, wrapped to its width and sign-extended to 64 bits
fn normalize(value: u64, int_type: StaticPool.IntType) u64 {
    if (int_type.bits == 0 or int_type.bits >= 64) return value;
    const shift: u6 = @intCast(64 - int_type.bits);
    if (int_type.signedness == .unsigned) return value << shift >> shift;
    const shifted_up: i64 = @bitCast(value << shift);
    return @bitCast(shifted_up >> shift);
}

// blocks and control flow

pub fn new_block(self: *FunctionBuilder) u32 {
    self.blocks.push(.{
        .sealed = false,
        .predecessors = none,
        .pending_phis = none,
        .predecessor_count = 0,
    });
    return self.blocks.len() - 1;
}

pub fn add_edge(self: *FunctionBuilder, to: u32) void {
    const predecessors = self.blocks.column(.predecessors);
    self.edges.push(.{ .from_block = self.current_block, .next_edge = predecessors[to] });
    predecessors[to] = self.edges.len() - 1;
    self.blocks.column(.predecessor_count)[to] += 1;
}

pub fn branch(self: *FunctionBuilder, to: u32) void {
    if (self.is_unreachable) return;
    self.add_edge(to);
    _ = self.emit(.br, .unit_type, to, 0);
}

pub fn branch_if(self: *FunctionBuilder, condition: Ref, then_block: u32, else_block: u32) void {
    if (self.is_unreachable) return;

    const is_true = condition.is_const() and condition.value() == .bool_true;
    const is_false = condition.is_const() and condition.value() == .bool_false;
    if (is_true) return self.branch(then_block);
    if (is_false) return self.branch(else_block);

    self.add_edge(then_block);
    self.add_edge(else_block);
    const targets = self.list(&.{ then_block, else_block });
    _ = self.emit(.cond_br, .unit_type, @backingInt(condition), targets);
}

// continues in `block`, which may still get predecessors
pub fn enter(self: *FunctionBuilder, block: u32) void {
    self.current_block = block;
    self.value_numbers.clearRetainingCapacity();
    const has_no_predecessor = self.blocks.column(.predecessor_count)[block] == 0;
    const has_no_way_in = has_no_predecessor and self.blocks.column(.sealed)[block];
    self.is_unreachable = block != 0 and has_no_way_in;
}

// seals `block` and continues there, or merges it into its one predecessor just branching to it
pub fn go_to(self: *FunctionBuilder, block: u32) void {
    const merges_into_predecessor = blk: {
        const blocks = self.blocks.columns();
        const instructions = self.instructions.columns();
        const last_instruction = self.instructions.len() -% 1;
        if (!self.is_unreachable or last_instruction == none) break :blk false;
        if (blocks.predecessor_count[block] != 1) break :blk false;
        if (blocks.pending_phis[block] != none) break :blk false;

        const ends_in_branch_here = instructions.op[last_instruction] == .br and
            instructions.a[last_instruction] == block;
        if (!ends_in_branch_here) break :blk false;
        const only_predecessor = self.edges.column(.from_block)[blocks.predecessors[block]];
        if (instructions.block[last_instruction] != only_predecessor) break :blk false;

        self.instructions.truncate(last_instruction);
        if (self.current_block != only_predecessor) self.value_numbers.clearRetainingCapacity();
        self.current_block = only_predecessor;
        blocks.predecessor_count[block] = 0;
        blocks.predecessors[block] = none;
        blocks.sealed[block] = true;
        self.is_unreachable = false;
        break :blk true;
    };
    if (merges_into_predecessor) return;
    self.seal(block);
    self.enter(block);
}

// variables

pub fn write_variable(self: *FunctionBuilder, variable: u32, block: u32, value: Ref) void {
    const key = @as(u64, variable) << 32 | block;
    self.definitions.put(self.allocator, key, value) catch @panic("OOM");
}

pub fn read_variable(self: *FunctionBuilder, variable: u32, variable_type: Index, block: u32) Ref {
    if (self.definitions.get(@as(u64, variable) << 32 | block)) |value| return value;
    const value = blk: {
        const state = self.blocks.get(block).?;
        if (!state.sealed) {
            const phi = self.emit_raw(.phi, variable_type, 0, 0, block);
            self.pending_phis.push(.{
                .variable = variable,
                .phi = @backingInt(phi),
                .next_pending = state.pending_phis,
            });
            self.blocks.column(.pending_phis)[block] = self.pending_phis.len() - 1;
            break :blk phi;
        }
        if (state.predecessor_count == 0) {
            break :blk self.emit_raw(.undef, variable_type, 0, 0, block);
        }
        if (state.predecessor_count == 1) {
            const only_predecessor = self.edges.column(.from_block)[state.predecessors];
            break :blk self.read_variable(variable, variable_type, only_predecessor);
        }

        // the phi is the variable's value before its operands are read, so a cycle back here ends
        const phi = self.emit_raw(.phi, variable_type, 0, 0, block);
        self.write_variable(variable, block, phi);
        self.fill_phi_operands(variable, phi);
        break :blk phi;
    };
    self.write_variable(variable, block, value);
    return value;
}

fn fill_phi_operands(self: *FunctionBuilder, variable: u32, phi: Ref) void {
    const phi_type = self.result_type_of(phi);
    const phi_block = self.instructions.column(.block)[@backingInt(phi)];
    const mark = self.scratch.len;

    var edge = self.blocks.column(.predecessors)[phi_block];
    while (edge != none) : (edge = self.edges.column(.next_edge)[edge]) {
        const predecessor = self.edges.column(.from_block)[edge];
        const operand = self.read_variable(variable, phi_type, predecessor);
        self.scratch.push(@backingInt(operand));
    }

    const operands = self.list(self.scratch.buffer[mark..self.scratch.len]);
    self.instructions.column(.b)[@backingInt(phi)] = operands;
    self.scratch.len = mark;
}

// every predecessor of `block` is known now, its waiting phis get their operands
pub fn seal(self: *FunctionBuilder, block: u32) void {
    if (self.blocks.column(.sealed)[block]) return;
    var pending = self.blocks.column(.pending_phis)[block];
    while (pending != none) : (pending = self.pending_phis.column(.next_pending)[pending]) {
        const phi: Ref = @fromBackingInt(self.pending_phis.column(.phi)[pending]);
        self.fill_phi_operands(self.pending_phis.column(.variable)[pending], phi);
    }
    self.blocks.column(.sealed)[block] = true;
}

// freezing into the ir

// positions of the tables `freeze` keeps in `renumbering`, after the frozen block numbers
const FreezeTables = struct {
    // per kept block and placement: first the count, then the start, then the end of its range
    placement_slots: u32,
    // per built instruction: its frozen index
    frozen_index: u32,
    // per frozen index: the built instruction
    order: u32,
};

// trivial phis become their one value, unreachable blocks go, blocks are ordered by `Placement`
pub fn freeze(self: *FunctionBuilder, ir: *HighIr, function_index: u32) void {
    const built_count = self.instructions.len();

    // a phi whose operands are only itself and one other value is that value, until nothing changes
    self.aliases.push_repeated(built_count, none);
    var changed = true;
    while (changed) {
        changed = false;
        phis: for (0..built_count) |i| {
            // read anew each time: emitting an undef below may move the columns
            const instructions = self.instructions.columns();
            if (instructions.op[i] != .phi or self.aliases.buffer[i] != none) continue;

            // the one value other than the phi its operands resolve to, `none` if there is none
            var same: u32 = none;
            const list_start = instructions.b[i];
            const length = self.operand_lists.buffer[list_start];
            for (self.operand_lists.buffer[list_start + 1 ..][0..length]) |operand| {
                const resolved = self.resolve_alias(operand);
                if (resolved == i or resolved == same) continue;
                // a second other value, the phi is not trivial
                if (same != none) continue :phis;
                same = resolved;
            }
            if (same == none) {
                const result_type = instructions.result_type[i];
                const undef = self.emit_raw(.undef, result_type, 0, 0, instructions.block[i]);
                same = @backingInt(undef);
            }
            self.aliases.buffer[i] = same;
            changed = true;
        }
    }

    const first_frozen_block = ir.blocks.len();
    // numbers the blocks with predecessors in order, the entry block is always kept
    const predecessor_counts = self.blocks.column(.predecessor_count);
    self.renumbering.len = 0;
    var kept_blocks: u32 = 0;
    for (0..predecessor_counts.len) |block| {
        const kept = block == 0 or predecessor_counts[block] > 0;
        self.renumbering.push(if (kept) kept_blocks else none);
        if (kept) kept_blocks += 1;
    }

    var tables: FreezeTables = undefined;
    tables.placement_slots = self.renumbering.len;
    // counts the instructions of each block and placement, then turns the counts into start offsets
    const all = self.instructions.columns();
    const slots_at = self.renumbering.len;
    const slot_count = kept_blocks * placement_count;
    self.renumbering.push_repeated(slot_count + 1, 0);

    for (0..all.op.len) |i| {
        const block = self.renumbering.buffer[all.block[i]];
        if (block == none) continue;
        if (i < built_count and self.aliases.buffer[i] != none) continue;
        const slot = placement_slot(slots_at, block, placement_of(all.op[i], all.a[i]));
        self.renumbering.buffer[slot + 1] += 1;
    }
    for (1..slot_count + 1) |k| {
        self.renumbering.buffer[slots_at + k] += self.renumbering.buffer[slots_at + k - 1];
    }

    const slots_end = tables.placement_slots + kept_blocks * placement_count;
    const frozen_count = self.renumbering.buffer[slots_end];
    // fills the frozen index and order tables, leaving each placement slot at its range's end
    tables.frozen_index = self.renumbering.len;
    self.renumbering.push_repeated(@intCast(all.op.len), none);
    tables.order = self.renumbering.len;
    self.renumbering.push_repeated(frozen_count, 0);

    for (0..all.op.len) |i| {
        const block = self.renumbering.buffer[all.block[i]];
        if (block == none) continue;
        if (i < built_count and self.aliases.buffer[i] != none) continue;
        const placement = placement_of(all.op[i], all.a[i]);
        const slot_index = placement_slot(tables.placement_slots, block, placement);
        const slot = &self.renumbering.buffer[slot_index];
        self.renumbering.buffer[tables.frozen_index + i] = slot.*;
        self.renumbering.buffer[tables.order + slot.*] = @intCast(i);
        slot.* += 1;
    }

    const first_frozen_instruction = ir.insts.len();
    for (self.renumbering.buffer[tables.order..][0..frozen_count]) |i| {
        const shape = all.op[i].shape();
        ir.insts.push(.{
            .op = all.op[i],
            .ty = all.result_type[i],
            .a = self.frozen_operand(ir, shape[0], all.a[i], tables.frozen_index),
            .b = self.frozen_operand(ir, shape[1], all.b[i], tables.frozen_index),
            .origin = all.origin[i],
        });
    }

    const blocks = self.blocks.columns();
    var start: u32 = 0;
    for (0..blocks.predecessor_count.len) |block| {
        const frozen_block = self.renumbering.buffer[block];
        if (frozen_block == none) continue;

        const end = self.renumbering.buffer[placement_slot(slots_at, frozen_block, .other)];
        const length = end - start;
        const predecessors_at = ir.extra.len;
        ir.extra.push(0);
        var edge = blocks.predecessors[block];
        while (edge != none) : (edge = self.edges.column(.next_edge)[edge]) {
            ir.extra.push(self.renumbering.buffer[self.edges.column(.from_block)[edge]]);
            ir.extra.buffer[predecessors_at] += 1;
        }

        ir.blocks.push(.{ .start = start, .len = length, .preds = predecessors_at });
        start += length;
    }

    const functions = ir.functions.columns();
    functions.first_block[function_index] = first_frozen_block;
    functions.blocks[function_index] = kept_blocks;
    functions.first_inst[function_index] = first_frozen_instruction;
    functions.insts[function_index] = frozen_count;
}

fn placement_slot(slots_at: u32, block: u32, placement: Placement) u32 {
    return slots_at + block * placement_count + @backingInt(placement);
}

// the lowerer marks the allocas of the entry block with no length (`none`)
fn placement_of(op: Op, a: u32) Placement {
    return switch (op) {
        .phi, .param => .phi_or_param,
        .undef => .undef_or_entry_alloca,
        .alloca => if (a == none) .undef_or_entry_alloca else .other,
        else => .other,
    };
}

fn resolve_alias(self: *const FunctionBuilder, instruction: u32) u32 {
    var current = instruction;
    while (current != none and current & constant_bit == 0 and
        current < self.aliases.len and self.aliases.buffer[current] != none)
    {
        current = self.aliases.buffer[current];
    }
    return current;
}

fn frozen_operand(
    self: *FunctionBuilder,
    ir: *HighIr,
    kind: Op.Operand,
    operand: u32,
    frozen_index_at: u32,
) u32 {
    return switch (kind) {
        .none, .imm => operand,
        .block => self.renumbering.buffer[operand],
        .ref => self.frozen_ref(operand, frozen_index_at),
        .refs, .blocks, .cases => self.frozen_list(ir, kind, operand, frozen_index_at),
    };
}

// a `cases` list is the default block, then pairs of a constant and the block it leads to
fn frozen_list(
    self: *FunctionBuilder,
    ir: *HighIr,
    kind: Op.Operand,
    operand: u32,
    frozen_index_at: u32,
) u32 {
    const list_start = ir.extra.len;
    const length = self.operand_lists.buffer[operand];
    const items = self.operand_lists.buffer[operand + 1 ..][0..length];
    ir.extra.push(@intCast(items.len));
    for (items, 0..) |item, k| {
        const is_block = kind == .blocks or kind == .cases and k % 2 == 0;
        const frozen = if (is_block)
            self.renumbering.buffer[item]
        else
            self.frozen_ref(item, frozen_index_at);
        ir.extra.push(frozen);
    }
    return list_start;
}

fn frozen_ref(self: *const FunctionBuilder, instruction: u32, frozen_index_at: u32) u32 {
    const resolved = self.resolve_alias(instruction);
    if (resolved == none or resolved & constant_bit != 0) return resolved;
    return self.renumbering.buffer[frozen_index_at + resolved];
}
