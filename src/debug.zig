const std = @import("std");
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Res = @import("Resolver.zig");
const Doctor = @import("resolver/Doctor.zig");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Node = ParseTree.Node;
const NodeId = ParseTree.NodeId;

const reset = "\x1b[0m";
const dim = "\x1b[90m";
const bold = "\x1b[1m";
const kind_col = "\x1b[36m";
const leaf_col = "\x1b[32m";
const func_col = "\x1b[1;35m";
const var_col = "\x1b[32m";
const field_col = "\x1b[33m";
const err_col = "\x1b[1;31m";
const warn_col = "\x1b[1;33m";
const type_col = "\x1b[34m";
const spaces = "                                ";

pub const Parser = struct {
    pub fn print_tree(io: std.Io, tree: *ParseTree, src: []const u8, roots: []const NodeId) !void {
        return Tree.print(io, tree, src, roots, null);
    }
};

pub const Resolver = struct {
    pub fn print_tree(io: std.Io, r: *Res) !void {
        return Tree.print(io, r.tree, r.src_bytes, r.roots, r);
    }

    pub fn print(io: std.Io, r: *Res) !void {
        var buf: [1 << 16]u8 = undefined;
        var fw = std.Io.File.stdout().writerStreaming(io, &buf);
        const w = &fw.interface;
        const sp = &r.static_pool;
        var line_starts: DynBuf(u32) = .init(r.alloc, 1024);
        defer line_starts.deinit();
        line_starts.push(0);
        for (r.src_bytes, 0..) |c, i| if (c == '\n') line_starts.push(@intCast(i + 1));
        const starts = line_starts.sliced();

        try w.writeAll(dim ++ "[DEBUG RESOLVER DUMP]\n" ++ reset ++ func_col ++ "declarations\n" ++ reset);
        const d = r.decls.sliced();
        var globals: usize = 0;
        for (0..d.name.len) |i| {
            const kind = d.kind[i];
            const flags = d.flags[i];
            globals += @intFromBool(flags.is_global);
            const col = if (flags.is_global) func_col else switch (kind) {
                .function, .static_function, .inlined_function, .trait_member, .type_alias, .record, .variant, .trait => kind_col,
                .field => field_col,
                else => var_col,
            };
            const line = if (node_span(r.tree, r.src_bytes, d.node[i])) |s| line_of(starts, s[0]) + 1 else 0;
            const name = decl_name(r, @enumFromInt(i));
            const mods = 4 * (@as(usize, @intFromBool(flags.is_pub)) + @intFromBool(flags.is_mut) + @intFromBool(flags.is_stc));
            try w.print(dim ++ "  #{d:<5}" ++ reset ++ " " ++ field_col ++ "{s}{s}{s}{s}{s}" ++ reset ++ "{s}", .{ i, if (flags.is_pub) "pub " else "", if (flags.is_mut) "mut " else "", if (flags.is_stc) "stc " else "", col, name, spaces[0 .. 24 -| (name.len + mods)] });
            try w.print(dim ++ "{s:<16} :{d:<5}" ++ reset ++ " ", .{ @tagName(kind), line });
            if (d.state[i] == .failed) try w.writeAll(err_col ++ "failed " ++ reset);
            try w.writeAll(type_col);
            try sp.format(&r.name_pool, &r.abstract_pool, d.ty[i], w);
            try w.writeAll(reset);
            const v = d.value[i];
            const own_fn = v != .none and sp.tag(v) == .function_value and @intFromEnum(sp.get(v).function) == i;
            if (v != .none and !own_fn and kind != .trait and sp.tag(v) != .generic) {
                try w.writeAll(dim ++ " = " ++ reset);
                try sp.format(&r.name_pool, &r.abstract_pool, v, w);
            }
            if (d.next_overload[i] != .none) try w.print(dim ++ "  next overload #{d}" ++ reset, .{@intFromEnum(d.next_overload[i])});
            try w.writeAll("\n");
        }

        const diags = r.doc.diagnostics.sliced();
        var errors: usize = 0;
        if (diags.code.len > 0) try w.writeAll(func_col ++ "\ndiagnostics\n" ++ reset);
        for (diags.code, diags.severity, diags.node, diags.a, diags.b) |code, severity, node, a, b| {
            errors += @intFromBool(severity == .@"error");
            try w.print("{s}{s}" ++ reset ++ " " ++ bold ++ "{s}" ++ reset, .{ if (severity == .@"error") err_col else warn_col, @tagName(severity), @tagName(code) });
            const span = node_span(r.tree, r.src_bytes, node);
            const line = if (span) |s| line_of(starts, s[0]) else 0;
            if (span) |s| try w.print(dim ++ ", :{d}:{d}" ++ reset, .{ line + 1, s[0] - starts[line] + 1 });
            try print_operands(w, r, code, a, b);
            try w.writeAll("\n");
            if (span) |s| {
                const end = if (line + 1 < starts.len) starts[line + 1] - 1 else @as(u32, @intCast(r.src_bytes.len));
                try w.print("    {s}\n    " ++ kind_col ++ "{s}", .{ r.src_bytes[starts[line]..end], spaces[0..@min(spaces.len, s[0] - starts[line])] });
                for (0..@max(1, @min(s[1], end) -| s[0])) |_| try w.writeAll("~");
                try w.writeAll(reset ++ "\n");
            }
        }
        try w.print(dim ++ "\n{d} declarations ({d} global), {d} pool entries, {d} type vars, {d} diagnostics ({d} errors, {d} warnings)\n" ++ reset, .{ d.name.len, globals, sp.items.len(), r.abstract_pool.count(), diags.code.len, errors, diags.code.len - errors });
        try w.flush();
    }
};

const Tree = struct {
    w: *std.Io.Writer,
    t: *ParseTree,
    src: []const u8,
    r: ?*Res,
    marked: []bool,

    fn print(io: std.Io, t: *ParseTree, src: []const u8, roots: []const NodeId, r: ?*Res) !void {
        var buf: [1 << 16]u8 = undefined;
        var fw = std.Io.File.stdout().writerStreaming(io, &buf);
        const marked = try std.heap.smp_allocator.alloc(bool, if (r == null) 0 else t.ast_nodes.len());
        defer std.heap.smp_allocator.free(marked);
        @memset(marked, false);
        if (r) |res| for (res.doc.diagnostics.sliced_field(.node)) |n| {
            marked[n] = true;
        };
        const s = Tree{ .w = &fw.interface, .t = t, .src = src, .r = r, .marked = marked };
        try s.w.writeAll(if (r == null) dim ++ "[DEBUG PARSER AST DUMP]\n" ++ reset else dim ++ "[DEBUG RESOLVER TREE]\n" ++ reset);
        for (roots, 0..) |root, i| {
            try s.w.print(func_col ++ "{s} (#{d})" ++ reset, .{ @tagName(t.ast_nodes.pool.nk.buf[root]), i });
            try s.annotate(root);
            try s.w.writeAll("\n");
            try s.node(root, "", true, true, "", 0);
            try s.w.writeAll("\n");
        }
        try s.w.print(dim ++ "{d} functions, {d} nodes total" ++ reset, .{ roots.len, t.ast_nodes.len() });
        if (r) |res| try s.w.print(dim ++ ", {d} declarations, {d} diagnostics" ++ reset, .{ res.decls.len(), res.doc.diagnostics.len() });
        try s.w.writeAll("\n");
        try s.w.flush();
    }

    fn node(s: Tree, idx: NodeId, prefix: []const u8, first: bool, last: bool, label: []const u8, lw: usize) !void {
        if (idx >= s.t.ast_nodes.len()) return s.w.print("{s}" ++ err_col ++ "<missing node #{d}>\n" ++ reset, .{ prefix, idx });
        const nk = s.t.ast_nodes.pool.nk.buf[idx];
        const args: [2]NodeId = s.t.ast_nodes.pool.args.buf[idx];
        const cc = Node.nk_childc[@intFromEnum(nk)];
        const leaf = cc == .none or cc == .data;
        if (!first) {
            try s.w.print("{s}{s}", .{ prefix, if (last) "└── " else "├── " });
            if (label.len > 0) try s.w.print(field_col ++ "{s}" ++ dim ++ ":" ++ reset ++ "{s}", .{ label, spaces[0 .. @min(spaces.len - 1, lw -| label.len) + 1] });
            try s.w.print("{s}{s}" ++ reset, .{ if (leaf) leaf_col else kind_col, @tagName(nk) });
            if (cc == .data) {
                const sp = s.t.span_store[args[0]];
                if (sp[1] > sp[0]) try s.w.print(dim ++ "  \"{s}\"" ++ reset, .{s.src[sp[0]..sp[1]]});
            }
            try s.annotate(idx);
            try s.w.writeAll("\n");
        }
        if (leaf) return;
        var buf: [1024]u8 = undefined;
        const next = std.fmt.bufPrint(&buf, "{s}{s}", .{ prefix, if (first) "" else if (last) "    " else "│   " }) catch prefix;
        if (cc == .many) {
            const kids = s.t.extra_childrefs.buf[args[0]..][0..args[1]];
            var lb: [16]u8 = undefined;
            const width = (std.fmt.bufPrint(&lb, "[{d}]", .{args[1] -| 1}) catch unreachable).len;
            for (kids, 0..) |k, i| try s.node(k, next, false, i + 1 == kids.len, std.fmt.bufPrint(&lb, "[{d}]", .{i}) catch unreachable, width);
            return;
        }
        const names = Node.nk_field_names[@intFromEnum(nk)];
        const n: usize = if (cc == .two) 2 else 1;
        for (0..n) |i| try s.node(args[i], next, false, i + 1 == n, names[i], @max(names[0].len, if (n == 2) names[1].len else 0));
    }

    fn annotate(s: Tree, idx: NodeId) !void {
        const r = s.r orelse return;
        const ty = r.node_type[idx];
        if (ty != .none) {
            try s.w.writeAll(if (ty == .poison_type) err_col ++ "  : " else type_col ++ "  : ");
            try r.static_pool.format(&r.name_pool, &r.abstract_pool, ty, s.w);
            try s.w.writeAll(reset);
        }
        const d = r.node_decl[idx];
        if (d != .none) try s.w.print(dim ++ "  → " ++ reset ++ bold ++ "#{d} {s}" ++ reset ++ dim ++ " {s}" ++ reset, .{ @intFromEnum(d), decl_name(r, d), @tagName(r.decls.pool.kind.buf[@intFromEnum(d)]) });
        if (!s.marked[idx]) return;
        const diags = r.doc.diagnostics.sliced();
        for (diags.node, diags.code, diags.severity, diags.a, diags.b) |n, code, sev, a, b| if (n == idx) {
            try s.w.print("{s}  ✗ {s}" ++ reset, .{ if (sev == .@"error") err_col else warn_col, @tagName(code) });
            try print_operands(s.w, r, code, a, b);
        };
    }
};

fn decl_name(r: *Res, d: Res.Decl.Index) []const u8 {
    const n = r.decls.pool.name.buf[@intFromEnum(d)];
    return if (n == .empty or n == .none) "<anon>" else r.name_pool.get(n);
}

const Operand = enum { none, name, type, int, decl };

pub fn print_operands(w: *std.Io.Writer, r: *Res, code: Doctor.Disorder, a: u32, b: u32) !void {
    const f: struct { []const u8, Operand, []const u8, Operand } = switch (code) {
        .undefined_name, .declaration_cycle => .{ "name", .name, "", .none },
        .duplicate_declaration => .{ "name", .name, "first declared as", .decl },
        .unknown_member => .{ "member", .name, "of", .type },
        .type_mismatch, .ret_type_mismatch, .invalid_cast, .runit_mixing, .destructure_type_conflict => .{ "found", .type, "expected", .type },
        .unknown_named_argument => .{ "name", .name, "of", .type },
        .infinite_type, .uninferable_type, .not_a_type, .not_callable, .recursive_by_value_type, .no_deinit, .non_exhaustive_match => .{ "type", .type, "", .none },
        .wrong_arity => .{ "arguments", .int, "parameters", .int },
        .no_matching_overload => .{ "arguments", .int, "", .none },
        .ambiguous_overload => .{ "picked", .decl, "", .none },
        .assertsize_failed => .{ "size", .int, "asserted", .int },
        .tag_overflow => .{ "tag", .type, "tag type", .type },
        .self_tag_without_niche => .{ "payload cases", .int, "", .none },
        .trait_member_missing, .trait_signature_mismatch => .{ "member", .name, "of trait", .type },
        .stcwhere_violated => .{ "in", .decl, "arguments", .type },
        else => .{ "", .none, "", .none },
    };
    inline for (.{ .{ f[0], f[1], a }, .{ f[2], f[3], b } }) |op| if (op[1] != .none and (op[1] == .int or op[2] != std.math.maxInt(u32))) {
        try w.print("  " ++ dim ++ "{s}" ++ reset ++ " ", .{op[0]});
        switch (op[1]) {
            .name => try w.print(bold ++ "`{s}`" ++ reset, .{if (op[2] < r.name_pool.map.count()) r.name_pool.get(@enumFromInt(op[2])) else "?"}),
            .type => {
                try w.writeAll(type_col);
                if (op[2] < r.static_pool.items.len()) try r.static_pool.format(&r.name_pool, &r.abstract_pool, @enumFromInt(op[2]), w) else try w.writeAll("?");
                try w.writeAll(reset);
            },
            .int => try w.print(bold ++ "{d}" ++ reset, .{op[2]}),
            .decl => try w.print(bold ++ "#{d}" ++ reset, .{op[2]}),
            .none => {},
        }
    };
}

fn line_of(starts: []const u32, at: u32) usize {
    var lo: usize = 0;
    var hi: usize = starts.len;
    while (hi - lo > 1) {
        const mid = (lo + hi) / 2;
        if (starts[mid] <= at) lo = mid else hi = mid;
    }
    return lo;
}

pub fn node_span(t: *const ParseTree, src: []const u8, node: NodeId) ?Lexer.TextSpan {
    const nk = t.ast_nodes.pool.nk.buf;
    const args = t.ast_nodes.pool.args.buf;
    const spans = t.span_store;
    var n = node;
    while (Node.nk_childc[@intFromEnum(nk[n])] != .data) {
        const a: [2]NodeId = args[n];
        const next = if (Node.nk_childc[@intFromEnum(nk[n])] == .many) (if (a[1] == 0) 0 else t.extra_childrefs.buf[a[0]]) else a[0];
        if (next == 0 or next >= t.ast_nodes.len()) break;
        n = next;
    } else return spans[args[n][0]];
    var tok: u32 = 0;
    var p = n;
    while (p > 0) : (p -= 1) if (Node.nk_childc[@intFromEnum(nk[p])] == .data) {
        tok = args[p][0];
        break;
    };
    const k = nk[n];
    const keyword: []const u8 = switch (k) {
        .brk => "brk",
        .cont => "cont",
        .ret_void => "ret",
        .boolean_true => "true",
        .boolean_false => "false",
        .identifier_self, .identifier_init, .identifier_deinit, .identifier_main => @tagName(k)["identifier_".len..],
        else => if (@intFromEnum(k) >= @intFromEnum(Node.Kind.type_u8) and @intFromEnum(k) <= @intFromEnum(Node.Kind.type_stcfun)) @tagName(k)["type_".len..] else return if (spans.len > 0) spans[tok] else null,
    };
    var rank: usize = 0;
    for (p + 1..n + 1) |q| rank += @intFromBool(nk[q] == k);
    for (spans[tok..@min(spans.len, tok + 256)]) |sp| if (std.mem.eql(u8, src[sp[0]..sp[1]], keyword)) {
        rank -= 1;
        if (rank == 0) return sp;
    };
    return if (spans.len > 0) spans[tok] else null;
}
