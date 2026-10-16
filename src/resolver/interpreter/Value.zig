const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const operators = @import("../../language/operators.zig");
const BinaryOperator = operators.BinaryOperator;
const UnaryOperator = operators.UnaryOperator;
const Index = StaticPool.Index;

const Value = @This();

value_type: Index,
bits: u64,

pub const poison = pooled(.poison_type);
pub const unit = pooled(.unit_value);
pub const empty = pooled(.none);

// indexed by the integer types, which come first in `Index`
const integer_widths = [_]u7{ 8, 16, 32, 64, 8, 16, 32, 64 };
const ref_bit: u64 = 1 << 63;

pub fn pooled(pool_index: Index) Value {
    return .{ .value_type = .none, .bits = @intFromEnum(pool_index) };
}

pub fn boolean(truth: bool) Value {
    return .{ .value_type = .bool_type, .bits = @intFromBool(truth) };
}

pub fn int(int_type: Index, bits: u64) Value {
    // integer bits are kept sign- or zero-extended to 64 bits, so equal values have equal bits
    const normalized: u64 = blk: {
        if (!is_int(int_type)) break :blk bits;
        const bit_width = integer_widths[@intFromEnum(int_type)];
        if (bit_width == 64) break :blk bits;

        const shift: u6 = @intCast(64 - bit_width);
        if (is_signed(int_type)) break :blk @bitCast(@as(i64, @bitCast(bits << shift)) >> shift);
        break :blk bits << shift >> shift;
    };
    return .{ .value_type = int_type, .bits = normalized };
}

pub fn float(float_type: Index, number: f64) Value {
    const rounded: f64 = switch (float_type) {
        .f16_type => @as(f16, @floatCast(number)),
        .f32_type => @as(f32, @floatCast(number)),
        else => number,
    };
    return .{ .value_type = float_type, .bits = @bitCast(rounded) };
}

pub fn block(block_type: Index, first_cell: u32, length: u32) Value {
    return .{ .value_type = block_type, .bits = first_cell | @as(u64, length) << 32 };
}

pub fn ref(pointer_type: Index, target_cell: u32) Value {
    return .{ .value_type = pointer_type, .bits = ref_bit | target_cell };
}

pub fn index(self: Value) Index {
    return @enumFromInt(@as(u32, @truncate(self.bits)));
}

pub fn cell(self: Value) u32 {
    return @truncate(self.bits);
}

pub fn len(self: Value) u32 {
    return @intCast(self.bits >> 32);
}

pub fn is_pooled(self: Value) bool {
    return self.value_type == .none;
}

// integers, floats and booleans hold their value in `bits`, any other type a block or reference
pub fn is_boxed(self: Value) bool {
    if (self.value_type == .none) return false;
    return @intFromEnum(self.value_type) > @intFromEnum(Index.bool_type);
}

pub fn is_heap(self: Value) bool {
    return self.is_boxed() and self.bits & ref_bit == 0;
}

pub fn is_ref(self: Value) bool {
    return self.is_boxed() and self.bits & ref_bit != 0;
}

pub fn is(self: Value, pool_index: Index) bool {
    return self.value_type == .none and self.index() == pool_index;
}

pub fn is_int(value_type: Index) bool {
    return @intFromEnum(value_type) <= @intFromEnum(Index.i64_type);
}

pub fn is_float(value_type: Index) bool {
    const ordinal = @intFromEnum(value_type);
    return ordinal >= @intFromEnum(Index.f16_type) and ordinal <= @intFromEnum(Index.f64_type);
}

fn is_signed(value_type: Index) bool {
    return @intFromEnum(value_type) >= @intFromEnum(Index.i8_type) and is_int(value_type);
}

pub fn as_float(self: Value) f64 {
    if (is_float(self.value_type)) return @bitCast(self.bits);
    if (is_signed(self.value_type)) return @floatFromInt(@as(i64, @bitCast(self.bits)));
    return @floatFromInt(self.bits);
}

pub fn of(static_pool: *const StaticPool, pool_index: Index) Value {
    if (pool_index == .none) return empty;
    switch (static_pool.tag(pool_index)) {
        .int_value => {
            const int_value = static_pool.get(pool_index).int_value;
            return int(int_value.value_type, int_value.bits);
        },
        .float_value => {
            const float_value = static_pool.get(pool_index).float_value;
            return float(float_value.value_type, float_value.value);
        },
        else => {},
    }
    if (pool_index == .bool_true or pool_index == .bool_false) {
        return boolean(pool_index == .bool_true);
    }
    return pooled(pool_index);
}

pub fn scalar(static_pool: *StaticPool, value: Value) Index {
    if (value.value_type == .bool_type) return if (value.bits != 0) .bool_true else .bool_false;
    if (is_float(value.value_type)) {
        return static_pool.intern(.{
            .float_value = .{ .value_type = value.value_type, .value = value.as_float() },
        });
    }
    const int_value = StaticPool.IntValue{ .value_type = value.value_type, .bits = value.bits };
    return static_pool.intern(.{ .int_value = int_value });
}

pub fn fit(self: Value, target_type: Index) Value {
    if (target_type == self.value_type or self.value_type == .none) return self;
    if (!is_number(self.value_type)) return self;
    if (is_int(target_type) and is_int(self.value_type)) return int(target_type, self.bits);
    if (is_float(target_type)) return float(target_type, self.as_float());
    return self;
}

pub fn cast(self: Value, target_type: Index) Value {
    if (self.value_type == .none) return self;
    if (is_float(target_type)) return float(target_type, self.as_float());
    if (!is_int(target_type)) return self;
    if (!is_float(self.value_type)) return int(target_type, self.bits);

    // a float saturates at the bounds of the integer type, NaN becomes zero
    const bit_width: u7 = integer_widths[@intFromEnum(target_type)];
    const magnitude_bits = if (is_signed(target_type)) bit_width - 1 else bit_width;
    const maximum = std.math.ldexp(@as(f64, 1), magnitude_bits) - 1;
    const minimum = if (is_signed(target_type)) -maximum - 1 else 0;
    const number = self.as_float();
    const clamped = if (std.math.isNan(number)) 0 else std.math.clamp(number, minimum, maximum);

    const bits: u64 = if (clamped < 0)
        @bitCast(std.math.lossyCast(i64, clamped))
    else
        std.math.lossyCast(u64, clamped);
    return int(target_type, bits);
}

// booleans take one byte
fn width(value_type: Index) u7 {
    if (is_int(value_type)) return integer_widths[@intFromEnum(value_type)];
    if (is_float(value_type)) {
        const float_rank = @intFromEnum(value_type) - @intFromEnum(Index.f16_type);
        return @as(u7, 16) << @intCast(float_rank);
    }
    return 8;
}

pub fn reinterpret(self: Value, target_type: Index) ?Value {
    const target_is_scalar = is_number(target_type) or target_type == .bool_type;
    if (self.value_type == .none or self.is_boxed() or !target_is_scalar) return null;

    // the bits of a scalar as its type lays them out in memory
    const raw: u64 = blk: {
        const bit_width = width(self.value_type);
        if (is_float(self.value_type)) break :blk switch (bit_width) {
            16 => @as(u16, @bitCast(@as(f16, @floatCast(self.as_float())))),
            32 => @as(u32, @bitCast(@as(f32, @floatCast(self.as_float())))),
            else => self.bits,
        };
        if (bit_width == 64) break :blk self.bits;
        break :blk self.bits & ((@as(u64, 1) << @intCast(bit_width)) - 1);
    };
    if (target_type == .bool_type) return boolean(raw != 0);
    if (is_int(target_type)) return int(target_type, raw);
    const number: f64 = switch (width(target_type)) {
        16 => @as(f16, @bitCast(@as(u16, @truncate(raw)))),
        32 => @as(f32, @bitCast(@as(u32, @truncate(raw)))),
        else => @bitCast(raw),
    };
    return float(target_type, number);
}

pub fn eql(left: Value, right: Value) bool {
    const both_integers = is_int(left.value_type) and is_int(right.value_type);
    if (both_integers) return left.widened() == right.widened();
    const both_numbers = is_number(left.value_type) and is_number(right.value_type);
    if (both_numbers) return left.as_float() == right.as_float();
    return left.value_type == right.value_type and left.bits == right.bits;
}

pub fn less(left: Value, right: Value) bool {
    const both_integers = is_int(left.value_type) and is_int(right.value_type);
    if (!both_integers) return left.as_float() < right.as_float();
    // exact values: a u64 past 2^63 is not a negative i64
    return left.widened() < right.widened();
}

// integers as their exact value, results wrap around the width of their type
fn widened(self: Value) i128 {
    return if (is_signed(self.value_type)) @as(i64, @bitCast(self.bits)) else self.bits;
}

fn wrapped(result_type: Index, exact: i128) Value {
    return int(result_type, @truncate(@as(u128, @bitCast(exact))));
}

pub const EvaluationError = error{ NotStatic, Invalid };

pub fn unary(operator: UnaryOperator, operand: Value, result_type: Index) EvaluationError!Value {
    switch (operator) {
        .not => {
            if (operand.value_type == .bool_type) return boolean(operand.bits == 0);
            if (!is_int(operand.value_type)) return error.NotStatic;
            return int(operand.value_type, ~operand.bits);
        },
        .negate => {
            if (is_float(operand.value_type)) return float(operand.value_type, -operand.as_float());
            if (!is_int(operand.value_type)) return error.NotStatic;
            // without an integer result type a negated unsigned integer becomes an `i64`
            const negation_type: Index = if (is_int(result_type))
                result_type
            else if (is_signed(operand.value_type))
                operand.value_type
            else
                .i64_type;
            return wrapped(negation_type, -operand.widened());
        },
    }
}

pub fn binary(
    operator: BinaryOperator,
    left: Value,
    right: Value,
    result_type: Index,
) EvaluationError!Value {
    if (is_int(left.value_type) and is_int(right.value_type)) {
        // integers wrap around the result type, dividing by zero or shifting too far is invalid
        const left_exact = left.widened();
        const right_exact = right.widened();
        const int_type = if (is_int(result_type)) result_type else left.value_type;

        return switch (operator) {
            .add => int(int_type, left.bits +% right.bits),
            .subtract => int(int_type, left.bits -% right.bits),
            .multiply => int(int_type, left.bits *% right.bits),
            .divide => if (right_exact == 0)
                error.Invalid
            else
                wrapped(int_type, @divTrunc(left_exact, right_exact)),
            .remainder => if (right_exact == 0)
                error.Invalid
            else
                wrapped(int_type, @rem(left_exact, right_exact)),
            .shift_left => int(int_type, left.bits << try shift_amount(right_exact, int_type)),
            .shift_right => shift_right(left, try shift_amount(right_exact, int_type), int_type),
            .bit_or => int(int_type, left.bits | right.bits),
            .bit_xor => int(int_type, left.bits ^ right.bits),
            .bit_and => int(int_type, left.bits & right.bits),
            .equal, .not_equal, .less, .greater => compare(operator, left, right),
            .less_equal, .greater_equal => compare(operator, left, right),
            .logic_and, .logic_or, .logic_xor => error.NotStatic,
        };
    }
    if (is_number(left.value_type) and is_number(right.value_type)) {
        // a float with an integer or a float, computed in f64 and rounded to the result type
        const float_type = if (is_float(result_type))
            result_type
        else if (is_float(left.value_type))
            left.value_type
        else
            right.value_type;
        return switch (operator) {
            .add => float(float_type, left.as_float() + right.as_float()),
            .subtract => float(float_type, left.as_float() - right.as_float()),
            .multiply => float(float_type, left.as_float() * right.as_float()),
            .divide => float(float_type, left.as_float() / right.as_float()),
            .equal, .not_equal, .less, .greater => compare(operator, left, right),
            .less_equal, .greater_equal => compare(operator, left, right),
            .remainder, .shift_left, .shift_right, .bit_or, .bit_xor, .bit_and => error.NotStatic,
            .logic_and, .logic_or, .logic_xor => error.NotStatic,
        };
    }
    if (left.value_type == .bool_type and right.value_type == .bool_type) {
        return switch (operator) {
            .logic_and, .bit_and => boolean(left.bits & right.bits != 0),
            .logic_or, .bit_or => boolean(left.bits | right.bits != 0),
            .logic_xor, .bit_xor, .not_equal => boolean(left.bits != right.bits),
            .equal => boolean(left.bits == right.bits),
            .add, .subtract, .multiply, .divide, .remainder => error.NotStatic,
            .shift_left, .shift_right => error.NotStatic,
            .less, .greater, .less_equal, .greater_equal => error.NotStatic,
        };
    }
    return switch (operator) {
        .equal => boolean(eql(left, right)),
        .not_equal => boolean(!eql(left, right)),
        .add, .subtract, .multiply, .divide, .remainder => error.NotStatic,
        .shift_left, .shift_right, .bit_or, .bit_xor, .bit_and => error.NotStatic,
        .less, .greater, .less_equal, .greater_equal => error.NotStatic,
        .logic_and, .logic_or, .logic_xor => error.NotStatic,
    };
}

fn is_number(value_type: Index) bool {
    return is_int(value_type) or is_float(value_type);
}

inline fn shift_amount(exact_amount: i128, int_type: Index) EvaluationError!u6 {
    const bit_width = integer_widths[@intFromEnum(int_type)];
    if (exact_amount < 0 or exact_amount >= bit_width) return error.Invalid;
    return @intCast(exact_amount);
}

// a signed integer shifts copies of its sign bit in
inline fn shift_right(left: Value, amount: u6, int_type: Index) Value {
    if (!is_signed(left.value_type)) return int(int_type, left.bits >> amount);
    const shifted: i64 = @as(i64, @bitCast(left.bits)) >> amount;
    return int(int_type, @bitCast(shifted));
}

inline fn compare(operator: BinaryOperator, left: Value, right: Value) EvaluationError!Value {
    return switch (operator) {
        .equal => boolean(eql(left, right)),
        .not_equal => boolean(!eql(left, right)),
        .less => boolean(less(left, right)),
        .greater => boolean(less(right, left)),
        .less_equal => boolean(!less(right, left)),
        .greater_equal => boolean(!less(left, right)),
        .add, .subtract, .multiply, .divide, .remainder => error.NotStatic,
        .shift_left, .shift_right, .bit_or, .bit_xor, .bit_and => error.NotStatic,
        .logic_and, .logic_or, .logic_xor => error.NotStatic,
    };
}
