const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const Kind = ParseTree.Node.Kind;
const constructs = @import("constructs.zig");

// the binary operators of the language, by what they compute rather than how they are written
// phases switch over them without `else`, a new operator is a member plus a row per table below
pub const BinaryOperator = enum {
    add,
    subtract,
    multiply,
    divide,
    remainder,
    shift_left,
    shift_right,
    bit_or,
    bit_xor,
    bit_and,
    equal,
    not_equal,
    less,
    greater,
    less_equal,
    greater_equal,
    logic_and,
    logic_or,
    logic_xor,
};

pub const UnaryOperator = enum {
    // `-x`
    negate,
    // `!x`: logical on booleans, bitwise on integers
    not,
};

// which operand types an operator accepts
pub const Operands = enum {
    // integers and floats, pointers for `+` and `-`
    numbers,
    integers,
    // any two values of joinable types
    comparable,
    booleans,
};

// the node kind writing each operator and what it takes
const binary_table = .{
    .{ .binary_add, .add, .numbers },
    .{ .binary_sub, .subtract, .numbers },
    .{ .binary_mul, .multiply, .numbers },
    .{ .binary_div, .divide, .numbers },
    .{ .binary_mod, .remainder, .integers },
    .{ .binary_shift_left, .shift_left, .integers },
    .{ .binary_shift_right, .shift_right, .integers },
    .{ .binary_num_or, .bit_or, .integers },
    .{ .binary_num_xor, .bit_xor, .integers },
    .{ .binary_num_and, .bit_and, .integers },
    .{ .binary_eq, .equal, .comparable },
    .{ .binary_neq, .not_equal, .comparable },
    .{ .binary_less, .less, .comparable },
    .{ .binary_greater, .greater, .comparable },
    .{ .binary_less_eq, .less_equal, .comparable },
    .{ .binary_greater_eq, .greater_equal, .comparable },
    .{ .binary_logic_and, .logic_and, .booleans },
    .{ .binary_logic_or, .logic_or, .booleans },
    .{ .binary_logic_xor, .logic_xor, .booleans },
};

// statements that apply an operator to a place: `x += 1`, `x++`
// `returns_old`: the expression is the value before the update (`x++`)
const assigning_table = .{
    .{ .assign_add, .add, false },
    .{ .assign_sub, .subtract, false },
    .{ .assign_mul, .multiply, false },
    .{ .assign_div, .divide, false },
    .{ .assign_mod, .remainder, false },
    .{ .inc_prefix, .add, false },
    .{ .dec_prefix, .subtract, false },
    .{ .inc_postfix, .add, true },
    .{ .dec_postfix, .subtract, true },
};

const kind_count = @typeInfo(Kind).@"enum".field_names.len;

const BinaryRow = struct { operator: BinaryOperator, operands: Operands };
const AssigningRow = struct { operator: BinaryOperator, returns_old: bool };

const binary_of_kind: [kind_count]?BinaryRow = blk: {
    @setEvalBranchQuota(100_000);
    var table: [kind_count]?BinaryRow = @splat(null);
    var seen: [@typeInfo(BinaryOperator).@"enum".field_names.len]bool = @splat(false);
    for (binary_table) |row| {
        const kind: Kind = row[0];
        if (table[@backingInt(kind)] != null) {
            @compileError("operator row listed twice: " ++ @tagName(kind));
        }
        table[@backingInt(kind)] = .{ .operator = row[1], .operands = row[2] };
        seen[@backingInt(@as(BinaryOperator, row[1]))] = true;
    }
    for (seen, 0..) |was_seen, i| {
        const operator: BinaryOperator = @fromBackingInt(@intCast(i));
        if (!was_seen) @compileError("operator without a node kind: " ++ @tagName(operator));
    }
    break :blk table;
};

const assigning_of_kind: [kind_count]?AssigningRow = blk: {
    var table: [kind_count]?AssigningRow = @splat(null);
    for (assigning_table) |row| {
        const kind: Kind = row[0];
        if (table[@backingInt(kind)] != null) {
            @compileError("assigning row listed twice: " ++ @tagName(kind));
        }
        table[@backingInt(kind)] = .{ .operator = row[1], .returns_old = row[2] };
    }
    break :blk table;
};

// the tables above and `constructs.zig` describe the same kinds: every operator construct has a row
// here and nothing else has one, so a new operator kind cannot be half added
comptime {
    @setEvalBranchQuota(100_000);
    for (0..kind_count) |i| {
        const kind: Kind = @fromBackingInt(@intCast(i));
        const wants_binary_row = switch (constructs.construct_of(kind)) {
            .arithmetic, .comparison, .short_circuit_logic, .logical_xor => true,
            else => false,
        };
        const wants_assigning_row = switch (constructs.construct_of(kind)) {
            .compound_assignment, .increment => true,
            else => false,
        };
        if (wants_binary_row != (binary_of_kind[i] != null)) {
            @compileError("binary_table and constructs.zig disagree on " ++ @tagName(kind));
        }
        if (wants_assigning_row != (assigning_of_kind[i] != null)) {
            @compileError("assigning_table and constructs.zig disagree on " ++ @tagName(kind));
        }
    }
}

// the operator of an `arithmetic`, `comparison`, `short_circuit_logic` or `logical_xor` node
pub fn binary_operator_of(kind: Kind) BinaryOperator {
    return (binary_of_kind[@backingInt(kind)] orelse unreachable).operator;
}

pub fn operands_of(kind: Kind) Operands {
    return (binary_of_kind[@backingInt(kind)] orelse unreachable).operands;
}

// the operator a `compound_assignment` or `increment` node applies
pub fn assigned_operator_of(kind: Kind) BinaryOperator {
    return (assigning_of_kind[@backingInt(kind)] orelse unreachable).operator;
}

// what that operator takes, as its binary form says (`%=` integers, as `%`)
pub fn assigned_operands_of(kind: Kind) Operands {
    return operands_of_operator[@backingInt(assigned_operator_of(kind))];
}

const operands_of_operator = blk: {
    var table: [@typeInfo(BinaryOperator).@"enum".field_names.len]Operands = undefined;
    for (binary_table) |row| table[@backingInt(@as(BinaryOperator, row[1]))] = row[2];
    break :blk table;
};

pub fn returns_old_value(kind: Kind) bool {
    return (assigning_of_kind[@backingInt(kind)] orelse unreachable).returns_old;
}
