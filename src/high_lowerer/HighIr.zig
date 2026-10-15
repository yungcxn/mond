const std = @import("std");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const StaticPool = @import("../resolver/StaticPool.zig");
const DeclPool = @import("../resolver/DeclPool.zig");

// the ssa form of a whole program: functions made of blocks made of instructions. operand and
// predecessor lists live in `extra` as a length followed by the items
const HighIr = @This();

// an instruction operand: an instruction of the same function, a pool constant or a global
pub const Ref = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    const const_bit: u32 = 1 << 31;
    const global_bit: u32 = 1 << 30;

    pub fn of(constant: StaticPool.Index) Ref {
        return @enumFromInt(@intFromEnum(constant) | const_bit);
    }

    pub fn global(global_index: u32) Ref {
        return @enumFromInt(global_index | const_bit | global_bit);
    }

    pub fn is_const(ref: Ref) bool {
        return ref != .none and @intFromEnum(ref) & (const_bit | global_bit) == const_bit;
    }

    pub fn is_global(ref: Ref) bool {
        const both_bits = const_bit | global_bit;
        return ref != .none and @intFromEnum(ref) & both_bits == both_bits;
    }

    pub fn value(ref: Ref) StaticPool.Index {
        return @enumFromInt(@intFromEnum(ref) & ~const_bit);
    }

    pub fn index(ref: Ref) u32 {
        return @intFromEnum(ref) & ~(const_bit | global_bit);
    }
};

// every op has one row in `definition_table` below, which all the lookups here read
pub const Op = enum(u8) {
    param,
    phi,
    undef,
    zeroed,
    add,
    sub,
    mul,
    div,
    rem,
    shl,
    shr,
    bit_and,
    bit_or,
    bit_xor,
    eq,
    ne,
    lt,
    gt,
    le,
    ge,
    bytes_eq,
    neg,
    not,
    convert,
    cast,
    alloca,
    load,
    store,
    field_ptr,
    index_ptr,
    dyn,
    aggregate,
    select,
    extract,
    variant_make,
    variant_tag,
    variant_payload,
    call,
    closure,
    // `$asm`: `a` is the constant of its text
    inline_asm,
    // `$syscall`: `b` lists the number and the arguments
    syscall,
    br,
    cond_br,
    @"switch",
    ret,
    @"unreachable",

    // what the `a` and `b` fields of an instruction hold
    pub const Operand = enum(u3) { none, ref, imm, block, refs, blocks, cases };

    pub const Behaviour = enum {
        // the same operands give the same value and nothing else happens: may be numbered
        pure,
        // pure, and the two operands may be swapped
        pure_commutative,
        // touches memory, or is identified by where it stands (params, phis, undefs)
        impure,
        // ends its block
        terminator,
    };

    // what `FunctionBuilder` computes when all operands are constants
    pub const Folding = enum { none, unary, arithmetic, comparison };

    pub fn shape(op: Op) [2]Operand {
        return definitions[@intFromEnum(op)].operands;
    }

    pub fn is_pure(op: Op) bool {
        const behaviour = definitions[@intFromEnum(op)].behaviour;
        return behaviour == .pure or behaviour == .pure_commutative;
    }

    pub fn is_commutative(op: Op) bool {
        return definitions[@intFromEnum(op)].behaviour == .pure_commutative;
    }

    pub fn is_terminator(op: Op) bool {
        return definitions[@intFromEnum(op)].behaviour == .terminator;
    }

    pub fn folding(op: Op) Folding {
        return definitions[@intFromEnum(op)].folding;
    }
};

// one row per op in `Op` order: shapes of `a` and `b`, behaviour, folding. a new op adds a row
const definition_table = .{
    .{ .param, .imm, .none, .impure, .none },
    .{ .phi, .none, .refs, .impure, .none },
    .{ .undef, .none, .none, .impure, .none },
    .{ .zeroed, .none, .none, .pure, .none },
    .{ .add, .ref, .ref, .pure_commutative, .arithmetic },
    .{ .sub, .ref, .ref, .pure, .arithmetic },
    .{ .mul, .ref, .ref, .pure_commutative, .arithmetic },
    .{ .div, .ref, .ref, .pure, .arithmetic },
    .{ .rem, .ref, .ref, .pure, .arithmetic },
    .{ .shl, .ref, .ref, .pure, .arithmetic },
    .{ .shr, .ref, .ref, .pure, .arithmetic },
    .{ .bit_and, .ref, .ref, .pure_commutative, .arithmetic },
    .{ .bit_or, .ref, .ref, .pure_commutative, .arithmetic },
    .{ .bit_xor, .ref, .ref, .pure_commutative, .arithmetic },
    .{ .eq, .ref, .ref, .pure_commutative, .comparison },
    .{ .ne, .ref, .ref, .pure_commutative, .comparison },
    .{ .lt, .ref, .ref, .pure, .comparison },
    .{ .gt, .ref, .ref, .pure, .comparison },
    .{ .le, .ref, .ref, .pure, .comparison },
    .{ .ge, .ref, .ref, .pure, .comparison },
    .{ .bytes_eq, .ref, .ref, .impure, .none },
    .{ .neg, .ref, .none, .pure, .unary },
    .{ .not, .ref, .none, .pure, .unary },
    .{ .convert, .ref, .imm, .pure, .none },
    .{ .cast, .ref, .imm, .pure, .none },
    .{ .alloca, .ref, .none, .impure, .none },
    .{ .load, .ref, .none, .impure, .none },
    .{ .store, .ref, .ref, .impure, .none },
    .{ .field_ptr, .ref, .imm, .pure, .none },
    .{ .index_ptr, .ref, .ref, .pure, .none },
    .{ .dyn, .ref, .refs, .impure, .none },
    .{ .aggregate, .none, .refs, .impure, .none },
    .{ .select, .ref, .refs, .pure, .none },
    .{ .extract, .ref, .imm, .pure, .none },
    .{ .variant_make, .imm, .ref, .pure, .none },
    .{ .variant_tag, .ref, .none, .pure, .none },
    .{ .variant_payload, .ref, .imm, .pure, .none },
    .{ .call, .ref, .refs, .impure, .none },
    .{ .closure, .imm, .refs, .impure, .none },
    .{ .inline_asm, .ref, .none, .impure, .none },
    .{ .syscall, .none, .refs, .impure, .none },
    .{ .br, .block, .none, .terminator, .none },
    .{ .cond_br, .ref, .blocks, .terminator, .none },
    .{ .@"switch", .ref, .cases, .terminator, .none },
    .{ .ret, .ref, .none, .terminator, .none },
    .{ .@"unreachable", .none, .none, .terminator, .none },
};

const Definition = struct {
    operands: [2]Op.Operand,
    behaviour: Op.Behaviour,
    folding: Op.Folding,
};

const definitions = blk: {
    const op_count = @typeInfo(Op).@"enum".fields.len;
    if (definition_table.len != op_count) @compileError("every op needs exactly one row");
    var table: [op_count]Definition = undefined;
    for (definition_table, 0..) |row, i| {
        const op: Op = row[0];
        if (@intFromEnum(op) != i) @compileError("row out of `Op` order: " ++ @tagName(op));
        table[i] = .{ .operands = .{ row[1], row[2] }, .behaviour = row[3], .folding = row[4] };
    }
    break :blk table;
};

// `origin`: what the instruction was lowered from, a tree node, 0 for none
pub const Inst = struct { op: Op, ty: StaticPool.Index, a: u32, b: u32, origin: u32 };

// `preds`: where the block's predecessor list starts in `extra`
pub const Block = struct { start: u32, len: u32, preds: u32 };

// the first `captures` params of a function hold its captured variables
pub const Function = struct {
    decl: DeclPool.Index,
    ty: StaticPool.Index,
    first_block: u32,
    blocks: u32,
    first_inst: u32,
    insts: u32,
    captures: u32,
};

pub const Global = struct { decl: DeclPool.Index, ty: StaticPool.Index, init: StaticPool.Index };

functions: StructOfArrays(Function),
blocks: StructOfArrays(Block),
insts: StructOfArrays(Inst),
globals: StructOfArrays(Global),
extra: DynamicBuffer(u32),
// the function running the global initializers
init_fn: u32 = 0,

pub fn init(allocator: std.mem.Allocator) HighIr {
    return .{
        .functions = .init(allocator, 256),
        .blocks = .init(allocator, 1024),
        .insts = .init(allocator, 8192),
        .globals = .init(allocator, 64),
        .extra = .init(allocator, 4096),
    };
}

pub fn deinit(self: *HighIr) void {
    self.functions.deinit();
    self.blocks.deinit();
    self.insts.deinit();
    self.globals.deinit();
    self.extra.deinit();
}

pub fn list(self: *const HighIr, list_start: u32) []const u32 {
    const length = self.extra.buffer[list_start];
    return self.extra.buffer[list_start + 1 ..][0..length];
}
