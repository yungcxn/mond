const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    pub const Kind = enum(u8) {
        none,

        stmt_assign_fun,
        stmt_assign_fun_pub,

        expr_fun_def,

        subexpr_fun_def_header,
        subexpr_fun_def_param_tuple,
        subexpr_fun_def_param,

        expr_capture,

        expr_array,
        expr_array_empty,

        expr_typeof,
        expr_sizeof,

        expr_type_array,

        expr_neg_num,
        expr_neg_logic,

        expr_inc_prefix,
        expr_dec_prefix,

        expr_gen_upperbound_incl,
        expr_gen_upperbound_excl,

        expr_none,
        expr_err,
        expr_deinit,
        expr_cont,
        expr_brk,
        expr_ret,

        expr_if, // lhs: expr (condition), rhs: expr (body)
        expr_if_else, // lhs: expr_if, rhs: expr (body)
        expr_while, // lhs: expr (condition), rhs: expr (body)
        expr_while_with_repeat_stmt, // lhs: expr_while, rhs: stmt (repeat statement)
        expr_for, // lhs: expr (seq), rhs: expr (body)
        expr_for_in, // lhs: expr_for, rhs: expr (iterator var)
        expr_loop, // lhs: expr (optional repeat statement), rhs: expr (body)
        expr_match, // lhs: expr (match value), rhs: subexpr_match_body (match body)

        subexpr_match_body,
        subexpr_match_case,

        expr_ampersand,

        expr_typeptr,
        expr_typeu8,
        expr_typeu16,
        expr_typeu32,
        expr_typeu64,
        expr_typei8,
        expr_typei16,
        expr_typei32,
        expr_typei64,
        expr_typef16,
        expr_typef32,
        expr_typef64,
        expr_typebool,
        expr_typetype,
        expr_typetrait,
        expr_typevariant,
        expr_typeinlfun,
        expr_typefun,
        expr_typestcfun,

        expr_type_def,
        expr_type_def_packed,
        expr_variant_def,
        expr_variant_def_packed,
        expr_variant_def_unionsized,
        expr_trait_def,

        subexpr_type_param_tuple,
        subexpr_type_param,
        subexpr_type_param_mut,

        subexpr_variant_param_tuple,
        subexpr_variant_param,

        subexpr_trait_implof_tuple,
        subexpr_trait_body,

        expr_unify_variants, // lhs: expr (type/variant), rhs: expr (type/variant)

        expr_fun_call, // lhs: expr (function), rhs: subexpr_fun_call_param_tuple (params)
        subexpr_fun_call_param_tuple, // array of expr

        expr_array_index, // lhs: expr (array), rhs: expr (index)
        expr_member, // lhs: expr (struct), rhs: expr (member)
        expr_dereference, // lhs: expr (pointer)
        expr_inc_postfix, // lhs: expr (variable)
        expr_dec_postfix, // lhs: expr (variable)

        expr_gen_lowerbound,
        expr_gen_incl,
        expr_gen_excl,

        expr_oftype, // lhs: expr (value), rhs: expr (type)
        expr_as, // lhs: expr (value), rhs: expr (type)
        expr_labelarrow, // lhs: expr (what-to-label), rhs: expr OR subexpr_destructure (label)
        expr_optarrow, // see above
        expr_errarrow, // see above

        subexpr_destructure, // expr_identifier[] (used by arrows and assignment)

        expr_errhandle,
        expr_opthandle,

        expr_defer,
        expr_defer_with_deinit,

        expr_binary_logic_or,
        expr_binary_logic_xor,
        expr_binary_logic_and,
        expr_binary_num_or,
        expr_binary_num_xor,
        expr_binary_num_and,
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
        expr_binary_shift_left,
        expr_binary_shift_right,
        expr_binary_pow,

        expr_identifier,
        expr_string,
        expr_int,
        expr_float,
        expr_char,
        expr_bool,
    };

    const nk_childc = blk: {
        var t: [256]enum(u8) { none, oneortwo, many } = @splat(.oneortwo);
        t[@intFromEnum(Node.Kind.none)] = .none;
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
    childrefs: anytype,
) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, parent_idx) orelse unreachable;
    args_ptr.*[0] = self.extra_childrefs.head;

    const child_t = @typeInfo(@TypeOf(childrefs)).pointer.child;
    const child_ti = @typeInfo(child_t);
    if (child_ti == .@"struct") {
        const n = child_ti.@"struct".fields.len;
        comptime if (@sizeOf(child_t) != n * @sizeOf(u32)) @compileError("unexpected size for " ++ @typeName(child_t));
        const arr_ptr: *const [n]u32 = @ptrCast(childrefs);
        self.extra_childrefs.append(arr_ptr);
        args_ptr.*[1] += @intCast(n);
    } else {
        self.extra_childrefs.append(childrefs);
        args_ptr.*[1] += @intCast(childrefs.len);
    }
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

    const is_leaf = Node.nk_childc[@intFromEnum(node.nk)] == .none;

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

    if (Node.nk_childc[@intFromEnum(node.nk)] == .many) {
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
