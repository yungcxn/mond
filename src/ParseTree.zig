const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    pub const Kind = enum(u8) {
        none,

        func_def,
        type_def,

        param_deftuple,
        param_defsingle,

        param_calltuple,

        stmt_mut_untyped_assign, // identifier, expr
        stmt_mut_typed_assign, // typeexpr, identifier, expr
        stmt_untyped_assign, // identifier, expr
        stmt_typed_assign, // typeexpr, identifier, expr

        stmt_funccall,
        stmt_exec_block,
        stmt_return,
        stmt_if,
        stmt_if_else,
        stmt_if_elseif,
        stmt_if_elseif_else,

        typeexpr_builtin_u8,
        typeexpr_builtin_u32,
        typeexpr_builtin_f32,
        typeexpr_builtin_bool,
        typeexpr_builtin_pointer,
        typeexpr_builtin_constpointer,
        typeexpr_builtin_array,

        typeexpr_type_custom,

        expr_funccall,
        expr_paren,
        expr_indexed,

        expr_unary_neg,
        expr_unary_logical_neg,

        expr_binary_logical_or,
        expr_binary_logical_xor,
        expr_binary_logical_and,
        expr_binary_bitwise_or,
        expr_binary_bitwise_xor,
        expr_binary_bitwise_and,
        expr_binary_eq,
        expr_binary_neq,
        expr_binary_less,
        expr_binary_greater,
        expr_binary_less_eq,
        expr_binary_greater_eq,
        expr_binary_add,
        expr_binary_sub,
        expr_binary_mul,
        expr_binary_div,
        expr_binary_mod,
        expr_binary_pow,

        // leave nodes with first arg pointing into respective data_* buf //

        expr_identifier,
        expr_string,
        expr_int,
        expr_float,
        expr_char,
        expr_bool,
    };

    pub const tok_to_typeexpr = blk: {
        var t: [256]Node.Kind = @splat(.none);
        t[@intFromEnum(Lexer.Token.Kind.kw_u8)] = .typeexpr_builtin_u8;
        t[@intFromEnum(Lexer.Token.Kind.kw_u32)] = .typeexpr_builtin_u32;
        t[@intFromEnum(Lexer.Token.Kind.kw_f32)] = .typeexpr_builtin_f32;
        t[@intFromEnum(Lexer.Token.Kind.kw_bool)] = .typeexpr_builtin_bool;
        break :blk t;
    };

    pub const tok_to_expr_unary = blk: {
        var t: [256]Node.Kind = @splat(.none);
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .expr_unary_neg;
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_!")] = .expr_unary_logical_neg;
        break :blk t;
    };

    pub const tok_to_tagged_expr_binary = blk: {
        var t: [256]packed struct { nt: Node.Kind, prec: u8 } = @splat(.{ .nt = .none, .prec = 0 });

        t[@intFromEnum(Lexer.Token.Kind.@"xpct_||")] = .{ .nt = .expr_binary_logical_or, .prec = 3 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_^^")] = .{ .nt = .expr_binary_logical_xor, .prec = 3 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_&&")] = .{ .nt = .expr_binary_logical_and, .prec = 4 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_|")] = .{ .nt = .expr_binary_bitwise_or, .prec = 5 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_^")] = .{ .nt = .expr_binary_bitwise_xor, .prec = 6 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_&")] = .{ .nt = .expr_binary_bitwise_and, .prec = 7 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_==")] = .{ .nt = .expr_binary_eq, .prec = 8 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_!=")] = .{ .nt = .expr_binary_neq, .prec = 8 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_<")] = .{ .nt = .expr_binary_less, .prec = 9 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_>")] = .{ .nt = .expr_binary_greater, .prec = 9 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_<=")] = .{ .nt = .expr_binary_less_eq, .prec = 9 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_>=")] = .{ .nt = .expr_binary_greater_eq, .prec = 9 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_+")] = .{ .nt = .expr_binary_add, .prec = 10 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .{ .nt = .expr_binary_sub, .prec = 10 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_*")] = .{ .nt = .expr_binary_mul, .prec = 11 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_/")] = .{ .nt = .expr_binary_div, .prec = 11 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_%")] = .{ .nt = .expr_binary_mod, .prec = 11 };
        t[@intFromEnum(Lexer.Token.Kind.@"xpct_**")] = .{ .nt = .expr_binary_pow, .prec = 12 };

        break :blk t;
    };

    pub const tok_to_expr_data = blk: {
        var t: [256]Node.Kind = @splat(.none);
        t[@intFromEnum(Lexer.Token.Kind.identifier)] = .expr_identifier;
        t[@intFromEnum(Lexer.Token.Kind.val_string)] = .expr_string;
        t[@intFromEnum(Lexer.Token.Kind.val_int)] = .expr_int;
        t[@intFromEnum(Lexer.Token.Kind.val_float)] = .expr_float;
        t[@intFromEnum(Lexer.Token.Kind.val_char)] = .expr_char;
        t[@intFromEnum(Lexer.Token.Kind.kw_true)] = .expr_bool;
        t[@intFromEnum(Lexer.Token.Kind.kw_false)] = .expr_bool;
        break :blk t;
    };
};

ast_nodes: SoD(Node),
extra_childrefs: DynBuf(u32), // children of node i must be contiguous here
data_store: DataStore,

pub const DataStore = struct {
    alloc: std.mem.Allocator,
    data_identifiers: DynBuf([]const u8),
    data_strings: DynBuf([]const u8),
    data_ints: DynBuf(u64),
    data_floats: DynBuf(f64),
    data_chars: DynBuf(u8),
    data_bools: DynBuf(bool),

    pub fn init(alloc: std.mem.Allocator) @This() {
        return @This(){
            .alloc = alloc,
            .data_identifiers = .init(alloc, 10000),
            .data_strings = .init(alloc, 10000),
            .data_ints = .init(alloc, 10000),
            .data_floats = .init(alloc, 10000),
            .data_chars = .init(alloc, 10000),
            .data_bools = .init(alloc, 10000),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.data_identifiers.deinit();
        self.data_strings.deinit();
        self.data_ints.deinit();
        self.data_floats.deinit();
        self.data_chars.deinit();
        self.data_bools.deinit();
    }

    pub inline fn store(self: *@This(), store_for_nk: Node.Kind, data: anytype) u32 {
        var pushed_idx: u32 = undefined;
        switch (store_for_nk) {
            .expr_identifier => if (comptime @TypeOf(data) == []const u8) {
                self.data_identifiers.push(data);
                pushed_idx = self.data_identifiers.head - 1;
            },
            .expr_string => if (comptime @TypeOf(data) == []const u8) {
                self.data_strings.push(data);
                pushed_idx = self.data_strings.head - 1;
            },
            .expr_int => if (comptime @TypeOf(data) == []const u8) {
                const parsed_int = parse_u64(data);
                self.data_ints.push(parsed_int);
                pushed_idx = self.data_ints.head - 1;
            },
            .expr_float => if (comptime @TypeOf(data) == []const u8) {
                const parsed_float = parse_f64(data);
                self.data_floats.push(parsed_float);
                pushed_idx = self.data_floats.head - 1;
            },
            .expr_char => if (comptime @TypeOf(data) == []const u8) {
                const parsed_char = parse_char(data);
                self.data_chars.push(parsed_char);
                pushed_idx = self.data_chars.head - 1;
            },
            .expr_bool => if (comptime @TypeOf(data) == bool) {
                self.data_bools.push(data);
                pushed_idx = self.data_bools.head - 1;
            },
            else => unreachable,
        }

        return pushed_idx;
    }

    inline fn parse_u64(s: []const u8) u64 {
        var result: u64 = 0;
        for (s) |c| {
            result = result * 10 + (c - '0');
        }
        return result;
    }

    inline fn parse_f64(s: []const u8) f64 {
        var int_part: u64 = 0;
        var frac_part: u64 = 0;
        var frac_div: f64 = 1;
        var seen_dot = false;

        for (s) |c| {
            if (c == '.') {
                seen_dot = true;
                continue;
            }
            if (seen_dot) {
                frac_part = frac_part * 10 + (c - '0');
                frac_div *= 10;
            } else {
                int_part = int_part * 10 + (c - '0');
            }
        }

        return @as(f64, @floatFromInt(int_part)) + @as(f64, @floatFromInt(frac_part)) / frac_div;
    }

    fn parse_char(s: []const u8) u8 {
        if (s[0] == '\\') {
            return switch (s[1]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '\\' => '\\',
                '\'' => '\'',
                '"' => '"',
                '0' => 0,
                else => unreachable,
            };
        }
        return s[0];
    }
};

pub fn init(alloc: std.mem.Allocator) @This() {
    return @This(){
        .ast_nodes = .init(alloc, 10000),
        .extra_childrefs = .init(alloc, 10000),
        .data_store = .init(alloc),
    };
}

pub fn deinit(self: *@This()) void {
    self.ast_nodes.deinit();
    self.extra_childrefs.deinit();
    self.data_store.deinit();
}

pub inline fn set_node_arg0(self: *@This(), target_node: u32, val: u32) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, target_node) orelse unreachable;
    args_ptr.*[0] = val;
}

pub inline fn set_node_arg1(self: *@This(), target_node: u32, val: u32) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, target_node) orelse unreachable;
    args_ptr.*[1] = val;
}

// fully registers a new children to a parent node with "n" (>2) children
pub inline fn push_extra_childrefs(
    self: *@This(),
    parent_idx: u32,
    childrefs: []const u32,
) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, parent_idx) orelse unreachable;
    if (args_ptr.*[1] == 0) {
        args_ptr.*[0] = self.extra_childrefs.head;
    }

    self.extra_childrefs.append(childrefs);
    args_ptr.*[1] += @intCast(childrefs.len);
}

// -> `u32`: idx where node was pushed into
pub inline fn push_node(self: *@This(), nodekind: Node.Kind) u32 {
    self.ast_nodes.push(.{ .nk = nodekind, .args = .{ 0, 0 } });
    return self.ast_nodes.len() - 1;
}

pub inline fn push_data_node(self: *@This(), nodekind: Node.Kind, data: anytype) u32 {
    comptime {
        const T = @TypeOf(data);
        if (T != bool and T != []const u8) @compileError("wrong data: " ++ @typeName(T));
    }

    const new_node_idx = self.push_node(nodekind);
    const stored_idx = self.data_store.store(nodekind, data);
    self.set_node_arg0(new_node_idx, stored_idx);

    return new_node_idx;
}
