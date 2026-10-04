const std = @import("std");
const SoD = @import("../ds/dynbuf.zig").SoD;
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const StaticPool = @import("../resolver/StaticPool.zig");
const Resolver = @import("../Resolver.zig");
const DeclPool = @import("../resolver/DeclPool.zig");

const HighIr = @This();

pub const Ref = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    const const_bit: u32 = 1 << 31;
    const global_bit: u32 = 1 << 30;

    pub fn of(v: StaticPool.Index) Ref {
        return @enumFromInt(@intFromEnum(v) | const_bit);
    }

    pub fn global(g: u32) Ref {
        return @enumFromInt(g | const_bit | global_bit);
    }

    pub fn is_const(r: Ref) bool {
        return r != .none and @intFromEnum(r) & (const_bit | global_bit) == const_bit;
    }

    pub fn is_global(r: Ref) bool {
        return r != .none and @intFromEnum(r) & (const_bit | global_bit) == const_bit | global_bit;
    }

    pub fn value(r: Ref) StaticPool.Index {
        return @enumFromInt(@intFromEnum(r) & ~const_bit);
    }

    pub fn index(r: Ref) u32 {
        return @intFromEnum(r) & ~(const_bit | global_bit);
    }
};

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
    pow,
    eq,
    ne,
    lt,
    gt,
    le,
    ge,
    bytes_eq,
    type_test,
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
    len,
    aggregate,
    select,
    extract,
    variant_make,
    variant_tag,
    variant_payload,
    call,
    call_dyn,
    closure,
    br,
    cond_br,
    @"switch",
    ret,
    @"unreachable",

    pub const Operand = enum(u3) { none, ref, imm, block, refs, blocks, cases };

    pub fn shape(op: Op) [2]Operand {
        return switch (op) {
            .param => .{ .imm, .none },
            .phi, .aggregate => .{ .none, .refs },
            .undef, .zeroed, .@"unreachable" => .{ .none, .none },
            .neg, .not, .load, .len, .variant_tag, .ret, .alloca => .{ .ref, .none },
            .convert, .cast, .field_ptr, .extract, .variant_payload, .type_test => .{ .ref, .imm },
            .variant_make => .{ .imm, .ref },
            .dyn, .call, .call_dyn, .select => .{ .ref, .refs },
            .closure => .{ .imm, .refs },
            .br => .{ .block, .none },
            .cond_br => .{ .ref, .blocks },
            .@"switch" => .{ .ref, .cases },
            else => .{ .ref, .ref },
        };
    }

    pub fn is_pure(op: Op) bool {
        return switch (op) {
            .zeroed, .add, .sub, .mul, .div, .rem, .shl, .shr, .bit_and, .bit_or, .bit_xor, .pow, .eq, .ne, .lt, .gt, .le, .ge, .neg, .not, .type_test, .convert, .cast, .field_ptr, .index_ptr, .len, .select, .extract, .variant_make, .variant_tag, .variant_payload => true,
            else => false,
        };
    }

    pub fn is_commutative(op: Op) bool {
        return switch (op) {
            .add, .mul, .bit_and, .bit_or, .bit_xor, .eq, .ne => true,
            else => false,
        };
    }

    pub fn is_terminator(op: Op) bool {
        return switch (op) {
            .br, .cond_br, .@"switch", .ret, .@"unreachable" => true,
            else => false,
        };
    }
};

pub const Inst = struct { op: Op, ty: StaticPool.Index, a: u32, b: u32 };
pub const Block = struct { start: u32, len: u32, preds: u32 };
pub const Function = struct { decl: DeclPool.Index, ty: StaticPool.Index, first_block: u32, blocks: u32, first_inst: u32, insts: u32, captures: u32 };
pub const Global = struct { decl: DeclPool.Index, ty: StaticPool.Index, init: StaticPool.Index };

functions: SoD(Function),
blocks: SoD(Block),
insts: SoD(Inst),
globals: SoD(Global),
extra: DynBuf(u32),
init_fn: u32 = 0,

pub fn init(alloc: std.mem.Allocator) HighIr {
    return .{ .functions = .init(alloc, 256), .blocks = .init(alloc, 1024), .insts = .init(alloc, 8192), .globals = .init(alloc, 64), .extra = .init(alloc, 4096) };
}

pub fn deinit(self: *HighIr) void {
    self.functions.deinit();
    self.blocks.deinit();
    self.insts.deinit();
    self.globals.deinit();
    self.extra.deinit();
}

pub fn list(self: *const HighIr, at: u32) []const u32 {
    return self.extra.buf[at + 1 ..][0..self.extra.buf[at]];
}
