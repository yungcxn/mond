const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    pub const Kind = enum(u8) {
        //     none,

        //     func_def,
        //     type_def,
        //     enum_def, // TODO
        //     iface_def, // TODO

        //     tuple__type_identifier_optexpr,
        //     tupleelem__type_identifier,
        //     tupleelem__type_identifier_expr,

        //     tuple__identifier_optexpr,
        //     tupleelem__identifier_expr,
        //     // tupleelem_identifier => just an identifier

        //     tuple__expr, // for function calls and match cases

        //     match_case,

        //     match_block,
        //     methods_block,

        //     // statements
        //     stmt_exec_block,

        //     stmt_mut_untyped_assign,
        //     stmt_mut_typed_assign,
        //     stmt_untyped_assign,
        //     stmt_typed_assign,
        //     stmt_funccall,

        //     stmt_ret,
        //     stmt_if,
        //     stmt_if_else,
        //     stmt_match,
        //     stmt_for,
        //     stmt_for_ext,
        //     stmt_while,
        //     stmt_while_ext,
        //     stmt_loop,
        //     stmt_loop_ext,
        //     stmt_brk,
        //     stmt_cont,
        //     stmt_defer,
        //     stmt_deinit,

        //     // expressions that express a type

        //     expr_type_builtin_u8,
        //     expr_type_builtin_u16,
        //     expr_type_builtin_u32,
        //     expr_type_builtin_u64,
        //     expr_type_builtin_i8,
        //     expr_type_builtin_i16,
        //     expr_type_builtin_i32,
        //     expr_type_builtin_i64,
        //     expr_type_builtin_f8,
        //     expr_type_builtin_f16,
        //     expr_type_builtin_f32,
        //     expr_type_builtin_f64,
        //     expr_type_builtin_bool,
        //     expr_type_pointer,
        //     expr_type_constpointer,
        //     expr_type_varref, // TODO ^
        //     expr_type_array,

        //     // real expressions with (possible) value
        //     expr_funccall,
        //     expr_paren,
        //     expr_indexed,
        //     expr_member,
        //     expr_dereference,
        //     expr_genseq_inc,
        //     expr_genseq_exc,
        //     expr_genseq_from,
        //     expr_aliasarrow,
        //     expr_errarrow,
        //     expr_optarrow,
        //     expr_errunwrap,
        //     expr_optunwrap,
        //     expr_subinterfaces, // TODO <<<
        //     expr_if_else,
        //     expr_match,
        //     expr_for,
        //     expr_for_ext,
        //     expr_while,
        //     expr_while_ext,
        //     expr_loop,
        //     expr_loop_ext,

        //     expr_defer,
        //     expr_deinit,
        //     expr_return,
        //     expr_brk,
        //     expr_cont,

        //     // these accept any valued expression on both sides, unlike those above, that still
        //     //   logically be "unary/binary"

        //     expr_unary_neg,
        //     expr_unary_logical_neg,

        //     expr_binary_logical_or,
        //     expr_binary_logical_xor,
        //     expr_binary_logical_and,
        //     expr_binary_bitwise_or,
        //     expr_binary_bitwise_xor,
        //     expr_binary_bitwise_and,
        //     expr_binary_eq,
        //     expr_binary_neq,
        //     expr_binary_less,
        //     expr_binary_greater,
        //     expr_binary_less_eq,
        //     expr_binary_greater_eq,
        //     expr_binary_add,
        //     expr_binary_sub,
        //     expr_binary_mul,
        //     expr_binary_div,
        //     expr_binary_mod,
        //     expr_binary_pow,

        //     // leave nodes with first arg pointing into respective data_* buf //

        //     expr_identifier,
        //     expr_string,
        //     expr_int,
        //     expr_float,
        //     expr_char,
        //     expr_bool,
    };

    // pub const assignable_expressions = blk: { // TODO
    //     var t: [256]bool = @splat(false);
    //     t[@intFromEnum(Node.Kind.expr_identifier)] = true;
    //     t[@intFromEnum(Node.Kind.expr_member)] = true;
    //     t[@intFromEnum(Node.Kind.expr_dereference)] = true;
    //     break :blk t;
    // };

    // pub const statementable_expressions = blk: { // TODO
    //     var t: [256]bool = @splat(false);
    //     t[@intFromEnum(Node.Kind.expr_funccall)] = true;
    //     t[@intFromEnum(Node.Kind.expr_defer)] = true;
    //     t[@intFromEnum(Node.Kind.expr_errunwrap)] = true;
    //     t[@intFromEnum(Node.Kind.expr_optunwrap)] = true;
    //     break :blk t;
    // };

    // pub const extrachilded_nodekinds = blk: { // TODO
    //     var t: [256]bool = @splat(false);
    //     t[@intFromEnum(Node.Kind.func_def)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_exec_block)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_if_else)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_mut_typed_assign)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_typed_assign)] = true;
    //     t[@intFromEnum(Node.Kind.match_block)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_for_ext)] = true;
    //     t[@intFromEnum(Node.Kind.stmt_while_ext)] = true;
    //     break :blk t;
    // };

    // pub const nonchilded_nodekinds = blk: {
    //     var t: [256]bool = @splat(false);
    //     t[@intFromEnum(Node.Kind.expr_identifier)] = true;
    //     t[@intFromEnum(Node.Kind.expr_string)] = true;
    //     t[@intFromEnum(Node.Kind.expr_int)] = true;
    //     t[@intFromEnum(Node.Kind.expr_float)] = true;
    //     t[@intFromEnum(Node.Kind.expr_char)] = true;
    //     t[@intFromEnum(Node.Kind.expr_bool)] = true;
    //     break :blk t;
    // };

    // pub const tok_to_typeexpr_start = blk: { // TODO
    //     var t: [256]bool = @splat(false);
    //     t[@intFromEnum(Lexer.Token.Kind.kw_u8)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_u16)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_u32)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_u64)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_i8)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_i16)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_i32)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_i64)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_f8)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_f16)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_f32)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_f64)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_bool)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_*")] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_&")] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.@"pct_[")] = true;
    //     break :blk t;
    // };

    // pub const tok_to_expr_start = blk: { // TODO
    //     var t: [256]bool = undefined;
    //     for (0..256) |i| {
    //         t[i] = tok_to_typeexpr_start[i] or (tok_to_expr_unary[i] != .none) or (tok_to_expr_data[i] != .none);
    //     }

    //     t[@intFromEnum(Lexer.Token.Kind.@"pct_(")] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_if)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_match)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_for)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_while)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_loop)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_deinit)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_ret)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_brk)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_cont)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_..=")] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_..<")] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_true)] = true;
    //     t[@intFromEnum(Lexer.Token.Kind.kw_false)] = true;
    //     break :blk t;
    // };

    // pub const tok_to_expr_unary = blk: {
    //     var t: [256]Node.Kind = @splat(.none);
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .expr_unary_neg;
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_!")] = .expr_unary_logical_neg;
    //     break :blk t;
    // };

    // pub const tok_to_tagged_expr_binary = blk: {
    //     var t: [256]packed struct { nt: Node.Kind, prec: u8 } = @splat(.{ .nt = .none, .prec = 0 });
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_||")] = .{ .nt = .expr_binary_logical_or, .prec = 3 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_^^")] = .{ .nt = .expr_binary_logical_xor, .prec = 3 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_&&")] = .{ .nt = .expr_binary_logical_and, .prec = 4 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_|")] = .{ .nt = .expr_binary_bitwise_or, .prec = 5 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_^")] = .{ .nt = .expr_binary_bitwise_xor, .prec = 6 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_&")] = .{ .nt = .expr_binary_bitwise_and, .prec = 7 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_==")] = .{ .nt = .expr_binary_eq, .prec = 8 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_!=")] = .{ .nt = .expr_binary_neq, .prec = 8 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_<")] = .{ .nt = .expr_binary_less, .prec = 9 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_>")] = .{ .nt = .expr_binary_greater, .prec = 9 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_<=")] = .{ .nt = .expr_binary_less_eq, .prec = 9 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_>=")] = .{ .nt = .expr_binary_greater_eq, .prec = 9 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_+")] = .{ .nt = .expr_binary_add, .prec = 10 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .{ .nt = .expr_binary_sub, .prec = 10 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_*")] = .{ .nt = .expr_binary_mul, .prec = 11 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_/")] = .{ .nt = .expr_binary_div, .prec = 11 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_%")] = .{ .nt = .expr_binary_mod, .prec = 11 };
    //     t[@intFromEnum(Lexer.Token.Kind.@"xpct_**")] = .{ .nt = .expr_binary_pow, .prec = 12 };

    //     break :blk t;
    // };

    pub const tok_to_expr_data = blk: {
        var t: [256]Node.Kind = @splat(.none);
        t[@intFromEnum(Lexer.Token.Kind.identifier)] = .expr_identifier;
        t[@intFromEnum(Lexer.Token.Kind.val_string)] = .expr_string;
        t[@intFromEnum(Lexer.Token.Kind.val_int)] = .expr_int;
        t[@intFromEnum(Lexer.Token.Kind.val_float)] = .expr_float;
        t[@intFromEnum(Lexer.Token.Kind.val_char)] = .expr_char;
        break :blk t;
    };
};

ast_nodes: SoD(Node),
extra_childrefs: DynBuf(u32), // children of node i must be contiguous here
span_store: []const Lexer.TextSpan,

pub fn init(alloc: std.mem.Allocator, span_store: []const Lexer.TextSpan) @This() {
    return @This(){
        .ast_nodes = .init(alloc, 10000),
        .extra_childrefs = .init(alloc, 10000),
        .span_store = span_store,
    };
}

pub fn deinit(self: *@This()) void {
    self.ast_nodes.deinit();
    self.extra_childrefs.deinit();
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

pub inline fn push_data_node(self: *@This(), nodekind: Node.Kind, span_idx: u32) u32 {
    const new_node_idx = self.push_node(nodekind);
    self.set_node_arg0(new_node_idx, span_idx);

    return new_node_idx;
}

const COL_RESET = "\x1b[0m";
const COL_DIM = "\x1b[90m";
const COL_KIND = "\x1b[36m";
const COL_LEAF = "\x1b[32m";
const COL_FUNC = "\x1b[1;35m";
const COL_ERR = "\x1b[31m";
const COL_NONE = "\x1b[2;37m";

fn wr(io: std.Io, s: []const u8) void {
    std.Io.File.stdout().writeStreamingAll(io, s) catch @panic("print failed");
}

fn leaf_label(self: *@This(), src_bytes: []const u8, node: Node) []const u8 {
    const idx = node.args[0];
    const span = self.span_store[idx];
    return src_bytes[span[0]..span[1]];
}

fn print_placeholder(io: std.Io, prefix: []const u8, is_last: bool) void {
    wr(io, prefix);
    wr(io, if (is_last) "└── " else "├── ");
    wr(io, COL_NONE ++ "∅ (none)" ++ COL_RESET ++ "\n");
}

fn print_node(self: *@This(), io: std.Io, src_bytes: []const u8, idx: u32, prefix: []const u8, is_first: bool, is_last: bool) anyerror!void {
    wr(io, prefix);
    wr(io, if (is_first) "" else if (is_last) "└── " else "├── ");

    const node = self.ast_nodes.get(idx) orelse {
        wr(io, COL_ERR);
        wr(io, "<missing node #");
        var idx_buf: [16]u8 = undefined;
        wr(io, std.fmt.bufPrint(&idx_buf, "{d}", .{idx}) catch "?");
        wr(io, ">");
        wr(io, COL_RESET);
        wr(io, "\n");
        return;
    };

    const is_leaf = Node.nonchilded_nodekinds[@intFromEnum(node.nk)];

    if (!is_first) {
        wr(io, if (is_leaf) COL_LEAF else COL_KIND);
        wr(io, @tagName(node.nk));
        wr(io, COL_RESET);
    }

    if (is_leaf) {
        const label = self.leaf_label(src_bytes, node);
        if (label.len != 0) {
            wr(io, COL_DIM);
            wr(io, "  \"");
            wr(io, label);
            wr(io, "\"");
            wr(io, COL_RESET);
        }
    }

    if (!is_first) wr(io, "\n");

    if (is_leaf) return;

    var prefix_buf: [1024]u8 = undefined;
    const ext = if (is_first) "" else if (is_last) "    " else "\xe2\x94\x82   "; // "│   "
    const new_prefix = std.fmt.bufPrint(&prefix_buf, "{s}{s}", .{ prefix, ext }) catch prefix;

    if (Node.extrachilded_nodekinds[@intFromEnum(node.nk)]) {
        const start = node.args[0];
        const count = node.args[1];

        var i: u32 = 0;
        while (i < count) : (i += 1) {
            const childref = self.extra_childrefs.buf[start + i];
            const child_is_last = i == count - 1;
            if (childref == 0xFFFFFFFF) {
                print_placeholder(io, new_prefix, child_is_last);
            } else {
                try self.print_node(io, src_bytes, childref, new_prefix, false, child_is_last);
            }
        }
        return;
    }

    var children: [2]u32 = undefined;
    var childc: usize = 0;
    const a = node.args[0];
    const b = node.args[1];
    if (a != 0 and a != 0xFFFFFFFF) {
        children[childc] = a;
        childc += 1;
    }
    if (b != 0 and b != 0xFFFFFFFF) {
        children[childc] = b;
        childc += 1;
    }

    for (children[0..childc], 0..) |child_idx, i| {
        try self.print_node(io, src_bytes, child_idx, new_prefix, false, i == childc - 1);
    }
}

pub fn debug_print_tree(self: *@This(), io: std.Io, src_bytes: []const u8, func_ids: []const u32) !void {
    wr(io, COL_DIM);
    wr(io, "[DEBUG PARSER AST DUMP]\n");
    wr(io, COL_RESET);

    for (func_ids, 0..) |funcid, i| {
        const node = self.ast_nodes.get(funcid) orelse {
            wr(io, COL_ERR);
            wr(io, "func: <missing>\n\n");
            wr(io, COL_RESET);
            continue;
        };

        var num_buf: [16]u8 = undefined;
        const num_str = std.fmt.bufPrint(&num_buf, "{d}", .{i}) catch "?";

        wr(io, COL_FUNC);
        wr(io, @tagName(node.nk));
        wr(io, " (#");
        wr(io, num_str);
        wr(io, ")");
        wr(io, COL_RESET);
        wr(io, "\n");

        try self.print_node(io, src_bytes, funcid, "", true, true);
        wr(io, "\n");
    }

    var stats_buf: [64]u8 = undefined;
    const stats = std.fmt.bufPrint(&stats_buf, "{d} functions, {d} nodes total", .{ func_ids.len, self.ast_nodes.len() }) catch "";
    wr(io, COL_DIM);
    wr(io, stats);
    wr(io, "\n" ++ COL_RESET);
}
