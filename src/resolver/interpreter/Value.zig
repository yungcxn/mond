const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const Kind = @import("../../ParseTree.zig").Node.Kind;
const Index = StaticPool.Index;

const Value = @This();

ty: Index,
bits: u64,

pub const poison = pooled(.poison_type);
pub const unit = pooled(.unit_value);
pub const empty = pooled(.none);

const widths = [_]u7{ 8, 16, 32, 64, 8, 16, 32, 64 };
const ref_bit: u64 = 1 << 63;

pub fn pooled(i: Index) Value {
    return .{ .ty = .none, .bits = @intFromEnum(i) };
}

pub fn boolean(b: bool) Value {
    return .{ .ty = .bool_type, .bits = @intFromBool(b) };
}

pub fn int(t: Index, bits: u64) Value {
    return .{ .ty = t, .bits = norm(bits, t) };
}

pub fn float(t: Index, x: f64) Value {
    const y: f64 = switch (t) {
        .f16_type => @as(f16, @floatCast(x)),
        .f32_type => @as(f32, @floatCast(x)),
        else => x,
    };
    return .{ .ty = t, .bits = @bitCast(y) };
}

pub fn block(t: Index, start: u32, n: u32) Value {
    return .{ .ty = t, .bits = start | @as(u64, n) << 32 };
}

pub fn ref(t: Index, c: u32) Value {
    return .{ .ty = t, .bits = ref_bit | c };
}

pub fn index(v: Value) Index {
    return @enumFromInt(@as(u32, @truncate(v.bits)));
}

pub fn at(v: Value) u32 {
    return @truncate(v.bits);
}

pub fn len(v: Value) u32 {
    return @intCast(v.bits >> 32);
}

pub fn is_pool(v: Value) bool {
    return v.ty == .none;
}

pub fn is_boxed(v: Value) bool {
    return v.ty != .none and @intFromEnum(v.ty) > @intFromEnum(Index.bool_type);
}

pub fn is_heap(v: Value) bool {
    return v.is_boxed() and v.bits & ref_bit == 0;
}

pub fn is_ref(v: Value) bool {
    return v.is_boxed() and v.bits & ref_bit != 0;
}

pub fn is(v: Value, i: Index) bool {
    return v.ty == .none and v.index() == i;
}

pub fn is_int(t: Index) bool {
    return @intFromEnum(t) <= @intFromEnum(Index.i64_type);
}

pub fn is_float(t: Index) bool {
    return @intFromEnum(t) >= @intFromEnum(Index.f16_type) and @intFromEnum(t) <= @intFromEnum(Index.f64_type);
}

fn signed(t: Index) bool {
    return @intFromEnum(t) >= @intFromEnum(Index.i8_type) and is_int(t);
}

fn norm(bits: u64, t: Index) u64 {
    if (!is_int(t) or widths[@intFromEnum(t)] == 64) return bits;
    const sh: u6 = @intCast(64 - widths[@intFromEnum(t)]);
    return if (signed(t)) @bitCast(@as(i64, @bitCast(bits << sh)) >> sh) else bits << sh >> sh;
}

pub fn f(v: Value) f64 {
    if (is_float(v.ty)) return @bitCast(v.bits);
    return if (signed(v.ty)) @floatFromInt(@as(i64, @bitCast(v.bits))) else @floatFromInt(v.bits);
}

pub fn of(sp: *const StaticPool, i: Index) Value {
    if (i == .none) return empty;
    return switch (sp.tag(i)) {
        .int_value => int(sp.get(i).int.ty, sp.get(i).int.bits),
        .float_value => float(sp.get(i).float.ty, sp.get(i).float.value),
        else => if (i == .bool_true or i == .bool_false) boolean(i == .bool_true) else pooled(i),
    };
}

pub fn scalar(sp: *StaticPool, v: Value) Index {
    if (v.ty == .bool_type) return if (v.bits != 0) .bool_true else .bool_false;
    if (is_float(v.ty)) return sp.intern(.{ .float = .{ .ty = v.ty, .value = v.f() } });
    return sp.intern(.{ .int = .{ .ty = v.ty, .bits = v.bits } });
}

pub fn fit(v: Value, t: Index) Value {
    if (t == v.ty or v.ty == .none or !(is_int(v.ty) or is_float(v.ty))) return v;
    if (is_int(t) and is_int(v.ty)) return int(t, v.bits);
    return if (is_float(t)) float(t, v.f()) else v;
}

pub fn cast(v: Value, t: Index) Value {
    if (v.ty == .none) return v;
    if (is_float(t)) return float(t, v.f());
    if (!is_int(t)) return v;
    if (!is_float(v.ty)) return int(t, v.bits);
    const w: u7 = widths[@intFromEnum(t)];
    const hi = std.math.ldexp(@as(f64, 1), if (signed(t)) w - 1 else w) - 1;
    const x = if (std.math.isNan(v.f())) 0 else std.math.clamp(v.f(), if (signed(t)) -hi - 1 else 0, hi);
    return int(t, if (x < 0) @bitCast(std.math.lossyCast(i64, x)) else std.math.lossyCast(u64, x));
}

fn width(t: Index) u7 {
    return if (is_int(t)) widths[@intFromEnum(t)] else if (is_float(t)) @as(u7, 16) << @intCast(@intFromEnum(t) - @intFromEnum(Index.f16_type)) else 8;
}

pub fn reinterpret(v: Value, t: Index) ?Value {
    if (v.ty == .none or v.is_boxed() or !(is_int(t) or is_float(t) or t == .bool_type)) return null;
    const w = width(v.ty);
    const raw: u64 = if (!is_float(v.ty)) (if (w == 64) v.bits else v.bits & (@as(u64, 1) << @intCast(w)) - 1) else switch (w) {
        16 => @as(u16, @bitCast(@as(f16, @floatCast(v.f())))),
        32 => @as(u32, @bitCast(@as(f32, @floatCast(v.f())))),
        else => v.bits,
    };
    if (t == .bool_type) return boolean(raw != 0);
    if (is_int(t)) return int(t, raw);
    return float(t, switch (width(t)) {
        16 => @as(f16, @bitCast(@as(u16, @truncate(raw)))),
        32 => @as(f32, @bitCast(@as(u32, @truncate(raw)))),
        else => @bitCast(raw),
    });
}

pub fn eql(a: Value, b: Value) bool {
    if (is_int(a.ty) and is_int(b.ty)) return a.bits == b.bits;
    if ((is_float(a.ty) or is_int(a.ty)) and (is_float(b.ty) or is_int(b.ty))) return a.f() == b.f();
    return a.ty == b.ty and a.bits == b.bits;
}

pub fn less(a: Value, b: Value) bool {
    if (is_int(a.ty) and is_int(b.ty)) return if (signed(a.ty) or signed(b.ty)) @as(i64, @bitCast(a.bits)) < @as(i64, @bitCast(b.bits)) else a.bits < b.bits;
    return a.f() < b.f();
}

pub fn unary(k: Kind, v: Value, t: Index) ?Value {
    if (k == .neg_logic) return if (v.ty == .bool_type) boolean(v.bits == 0) else if (is_int(v.ty)) int(v.ty, ~v.bits) else null;
    if (is_float(v.ty)) return float(v.ty, -v.f());
    return if (is_int(v.ty)) int(if (is_int(t)) t else if (signed(v.ty)) v.ty else .i64_type, 0 -% v.bits) else null;
}

pub fn binary(k: Kind, a: Value, b: Value, t: Index) error{ NotStatic, Invalid }!Value {
    if (is_int(a.ty) and is_int(b.ty)) {
        const s = signed(a.ty) or signed(b.ty);
        const x = a.bits;
        const y = b.bits;
        const sx: i64 = @bitCast(x);
        const sy: i64 = @bitCast(y);
        const r = if (is_int(t)) t else a.ty;
        if ((k == .binary_div or k == .binary_mod) and y == 0 or (k == .binary_shift_left or k == .binary_shift_right) and y >= widths[@intFromEnum(r)]) return error.Invalid;
        return switch (k) {
            .binary_add => int(r, x +% y),
            .binary_sub => int(r, x -% y),
            .binary_mul => int(r, x *% y),
            .binary_div => int(r, if (!s) x / y else if (sy == -1) 0 -% x else @bitCast(@divTrunc(sx, sy))),
            .binary_mod => int(r, if (!s) x % y else if (sy == -1) 0 else @bitCast(@rem(sx, sy))),
            .binary_shift_left => int(r, x << @truncate(y)),
            .binary_shift_right => int(r, if (s) @bitCast(sx >> @truncate(y)) else x >> @truncate(y)),
            .binary_num_or => int(r, x | y),
            .binary_num_xor => int(r, x ^ y),
            .binary_num_and => int(r, x & y),
            .binary_pow => blk: {
                var p: u64 = 1;
                for (0..@min(y, 64)) |_| p *%= x;
                break :blk int(r, p);
            },
            else => compare(k, a, b),
        };
    }
    if ((is_float(a.ty) or is_int(a.ty)) and (is_float(b.ty) or is_int(b.ty))) {
        const r = if (is_float(t)) t else if (is_float(a.ty)) a.ty else b.ty;
        return switch (k) {
            .binary_add => float(r, a.f() + b.f()),
            .binary_sub => float(r, a.f() - b.f()),
            .binary_mul => float(r, a.f() * b.f()),
            .binary_div => float(r, a.f() / b.f()),
            else => compare(k, a, b),
        };
    }
    if (a.ty == .bool_type and b.ty == .bool_type) return switch (k) {
        .binary_logic_and, .binary_num_and => boolean(a.bits & b.bits != 0),
        .binary_logic_or, .binary_num_or => boolean(a.bits | b.bits != 0),
        .binary_logic_xor, .binary_num_xor, .binary_neq => boolean(a.bits != b.bits),
        .binary_eq => boolean(a.bits == b.bits),
        else => error.NotStatic,
    };
    return switch (k) {
        .binary_eq => boolean(eql(a, b)),
        .binary_neq => boolean(!eql(a, b)),
        else => error.NotStatic,
    };
}

fn compare(k: Kind, a: Value, b: Value) error{ NotStatic, Invalid }!Value {
    return switch (k) {
        .binary_eq => boolean(eql(a, b)),
        .binary_neq => boolean(!eql(a, b)),
        .binary_less => boolean(less(a, b)),
        .binary_greater => boolean(less(b, a)),
        .binary_less_eq => boolean(!less(b, a)),
        .binary_greater_eq => boolean(!less(a, b)),
        else => error.NotStatic,
    };
}
