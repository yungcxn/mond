const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    pub const Kind = enum(u8) {

        // This just builds a rule based on the names of `Kind` but makes sure that this rule
        //   can be realised. It could be that between two partially matching names could have non-
        //   matching enum values inbetween. Therefore this is checked at comptime.
        pub fn seg_table_by_prefix(comptime prefix: []const u8) [2]u32 {
            return comptime blk: {
                var scan_start: u32 = 0xFFFFFFFF;
                var scan_end: u32 = 0xFFFFFFFF;
                for (@typeInfo(Kind).@"enum".fields, 0..) |f, i| {
                    if (std.mem.startsWith(u8, f.name, prefix)) {
                        if (scan_start == null) scan_start = i;
                        scan_end = i;

                        if (i - scan_start > 1) {
                            @compileError("kinds must be contiguous in the enum");
                        } else {}
                    }
                }
                break :blk .{ scan_start, scan_end };
            };
        }

        pub fn is_assign(self: Kind) bool {
            const scan_region: [2]u32 = seg_table_by_prefix("assign");
            return @intFromEnum(self) >= scan_region[0] and @intFromEnum(self) <= scan_region[1];
        }

        NO_KIND,

        block,
        def_fun,

        partial__fun_header,
        partial__fun_param_tuple,
        partial__fun_param,

        capture,

        array,
        array_empty,

        typeof,
        sizeof,

        type_array,

        neg_num,
        neg_logic,

        inc_prefix,
        dec_prefix,

        gen_upperbound_incl,
        gen_upperbound_excl,

        none,
        err,
        deinit,
        cont,
        brk,
        ret,

        if_then, // lhs: expr (condition), rhs: expr (body)
        if_else, // lhs: expr_if, rhs: expr (body)
        @"while", // lhs: expr (condition), rhs: expr (body)
        while_with_repeat_stmt, // lhs: expr_while, rhs: stmt (repeat statement)
        for_seq, // lhs: expr (seq), rhs: expr (body)
        for_in_seq, // lhs: expr_for, rhs: expr (iterator var)
        loop, // lhs: expr (optional repeat statement), rhs: expr (body)
        match, // lhs: expr (match value), rhs: subexpr_match_body (match body)

        partial__match_body,
        partial__match_case,

        // note: can be type
        type_ptrmut,

        type_ptr,
        type_u8,
        type_u16,
        type_u32,
        type_u64,
        type_i8,
        type_i16,
        type_i32,
        type_i64,
        type_f16,
        type_f32,
        type_f64,
        type_bool,
        type_type,
        type_trait,
        type_variant,
        type_inlfun,
        type_fun,
        type_stcfun,

        def_type,
        def_type_packed,
        def_variant,
        def_variant_packed,
        def_variant_unionsized,
        def_trait,

        partial__type_param_tuple,
        partial__type_param,
        partial__type_param_mut,

        partial__variant_param_tuple,
        partial__variant_param,

        partial__trait_implof_tuple,
        partial__trait_body,

        unify_variants, // lhs: expr (type/variant), rhs: expr (type/variant)

        fun_call, // lhs: expr (function), rhs: subexpr_fun_call_param_tuple (params)
        partial__fun_call_param_tuple, // array of expr

        array_index, // lhs: expr (array), rhs: expr (index)
        member, // lhs: expr (struct), rhs: expr (member)
        dereference, // lhs: expr (pointer)
        address_of, // lhs: expr
        inc_postfix, // lhs: expr (variable)
        dec_postfix, // lhs: expr (variable)

        gen_lowerbound,
        gen_incl,
        gen_excl,

        oftype, // lhs: expr (value), rhs: expr (type)
        as, // lhs: expr (value), rhs: expr (type)
        labelarrow, // lhs: expr (what-to-label), rhs: expr OR subexpr_destructure (label)
        optarrow, // see above
        errarrow, // see above

        partial__destructure, // expr_identifier[] (used by arrows and assignment)

        // note: these are !! and ??
        errhandle,
        opthandle,

        @"defer",
        defer_with_deinit,

        binary_logic_or,
        binary_logic_xor,
        binary_logic_and,
        binary_num_or,
        binary_num_xor,
        binary_num_and,
        binary_eq,
        binary_neq,
        binary_less,
        binary_greater,
        binary_less_eq,
        binary_greater_eq,
        binary_add,
        binary_sub,
        binary_mul,
        binary_div,
        binary_mod,
        binary_shift_left,
        binary_shift_right,
        binary_pow,

        identifier,
        string,
        int,
        float,
        char,
        boolean,
    };

    const nk_childc = blk: { // TODO
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
