const std = @import("std");
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Res = @import("Resolver.zig");
const Doctor = @import("resolver/Doctor.zig");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const DeclPool = @import("resolver/DeclPool.zig");
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
        var line_starts = lines(r);
        defer line_starts.deinit();
        const starts = line_starts.sliced();

        try w.writeAll(dim ++ "[DEBUG RESOLVER DUMP]\n" ++ reset ++ func_col ++ "declarations\n" ++ reset);
        const d = r.decl_pool.entries.sliced();
        var globals: usize = 0;
        for (0..d.name.len) |i| {
            globals += @intFromBool(d.flags[i].is_global);
            try decl_row(w, r, starts, i);
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

    fn lines(r: *Res) DynBuf(u32) {
        var line_starts: DynBuf(u32) = .init(r.alloc, 1024);
        line_starts.push(0);
        for (r.src_bytes, 0..) |c, i| if (c == '\n') line_starts.push(@intCast(i + 1));
        return line_starts;
    }

    fn decl_row(w: *std.Io.Writer, r: *Res, starts: []const u32, i: usize) !void {
        const d = r.decl_pool.entries.sliced();
        const sp = &r.static_pool;
        const kind = d.kind[i];
        const flags = d.flags[i];
        const col = if (flags.is_global) func_col else switch (kind) {
            .function, .static_function, .inlined_function, .trait_member, .type_alias, .record, .variant, .trait => kind_col,
            .field => field_col,
            else => var_col,
        };
        const line = if (node_span(r.tree, r.src_bytes, d.node[i])) |s| line_of(starts, s[0]) + 1 else 0;
        const name = decl_name(r, @enumFromInt(i));
        const mods = 4 * (@as(usize, @intFromBool(flags.is_pub)) + @intFromBool(flags.is_mut) + @intFromBool(flags.is_stc));
        try w.print(dim ++ "  #{d:<5}" ++ reset ++ " " ++ field_col ++ "{s}{s}{s}{s}{s}" ++ reset ++ "{s}", .{ i, if (flags.is_pub) "pub " else "", if (flags.is_mut) "mut " else "", if (flags.is_stc) "stc " else "", col, name, spaces[0..24 -| (name.len + mods)] });
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
        const marked = try marks(t, r);
        defer std.heap.smp_allocator.free(marked);
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
        if (r) |res| try s.w.print(dim ++ ", {d} declarations, {d} diagnostics" ++ reset, .{ res.decl_pool.entries.len(), res.doc.diagnostics.len() });
        try s.w.writeAll("\n");
        try s.w.flush();
    }

    fn marks(t: *ParseTree, r: ?*Res) ![]bool {
        const marked = try std.heap.smp_allocator.alloc(bool, if (r == null) 0 else t.ast_nodes.len());
        @memset(marked, false);
        if (r) |res| for (res.doc.diagnostics.sliced_field(.node)) |n| {
            marked[n] = true;
        };
        return marked;
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
        if (d != .none) try s.w.print(dim ++ "  → " ++ reset ++ bold ++ "#{d} {s}" ++ reset ++ dim ++ " {s}" ++ reset, .{ @intFromEnum(d), decl_name(r, d), @tagName(r.decl_pool.kinds()[@intFromEnum(d)]) });
        if (!s.marked[idx]) return;
        const diags = r.doc.diagnostics.sliced();
        for (diags.node, diags.code, diags.severity, diags.a, diags.b) |n, code, sev, a, b| if (n == idx) {
            try s.w.print("{s}  ✗ {s}" ++ reset, .{ if (sev == .@"error") err_col else warn_col, @tagName(code) });
            try print_operands(s.w, r, code, a, b);
        };
    }
};

fn decl_name(r: *Res, d: DeclPool.Index) []const u8 {
    const n = r.decl_pool.names()[@intFromEnum(d)];
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

    inline for (.{ .{ f[0], f[1], a }, .{
        f[2],
        f[3],
        b,
    } }) |op| if (op[1] != .none and (op[1] == .int or op[2] != std.math.maxInt(u32))) {
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
        .identifier_self => @tagName(k)["identifier_".len..],
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

pub const HighLowerer = struct {
    const Low = @import("HighLowerer.zig");
    const Ir = @import("high_lowerer/HighIr.zig");
    const Pool = @import("resolver/StaticPool.zig");

    pub fn print(io: std.Io, l: *Low) !void {
        var buf: [1 << 16]u8 = undefined;
        var fw = std.Io.File.stdout().writerStreaming(io, &buf);
        const w = &fw.interface;
        const ir = &l.ir;
        try w.writeAll(dim ++ "[DEBUG HIGH IR]\n" ++ reset);
        const g = ir.globals.sliced();
        for (0..g.decl.len) |i| try global(w, l, i);
        const f = ir.functions.sliced();
        for (0..f.decl.len) |fi| try func(w, l, fi);
        try w.print(dim ++ "\n{d} functions, {d} blocks, {d} instructions, {d} globals\n" ++ reset, .{ f.decl.len, ir.blocks.len(), ir.insts.len(), g.decl.len });
        try w.flush();
    }

    fn global(w: *std.Io.Writer, l: *Low, i: usize) !void {
        const g = l.ir.globals.get(@intCast(i)).?;
        try w.writeAll(kind_col ++ "static " ++ reset);
        try ty(w, l, g.ty);
        try w.print(" " ++ bold ++ "{s}" ++ reset, .{decl_name(l.r, g.decl)});
        if (g.init != .none) {
            try w.writeAll(" = ");
            try value(w, l, g.init);
        }
        try w.print(";" ++ dim ++ "  @{d}\n" ++ reset, .{i});
    }

    fn func(w: *std.Io.Writer, l: *Low, fi: usize) !void {
        const ir = &l.ir;
        const f = ir.functions.sliced();
        const ft = l.sp.get(f.ty[fi]).function_type;
        try w.writeAll("\n");
        try ty(w, l, ft.ret);
        try w.print(" " ++ func_col ++ "{s}" ++ reset ++ "(", .{fn_name(l, fi)});
        if (f.blocks[fi] == 0) {
            for (0..ft.params.len) |i| {
                if (i > 0) try w.writeAll(", ");
                try ty(w, l, l.sp.get(f.ty[fi]).function_type.params[i]);
            }
            return w.print(");" ++ dim ++ "  extern #{d}\n" ++ reset, .{fi});
        }
        const entry = ir.blocks.get(f.first_block[fi]).?;
        var np: usize = 0;
        for (entry.start..entry.start + entry.len) |ii| {
            const in = ir.insts.get(f.first_inst[fi] + @as(u32, @intCast(ii))).?;
            if (in.op != .param) continue;
            if (np > 0) try w.writeAll(", ");
            try ty(w, l, in.ty);
            try w.print(" %{d}", .{ii});
            np += 1;
        }
        try w.print(") " ++ dim ++ "#{d}", .{fi});
        if (f.captures[fi] > 0) try w.print(", first {d} capture{s}", .{ f.captures[fi], if (f.captures[fi] == 1) "" else "s" });
        try w.writeAll(reset ++ " {\n");
        for (0..f.blocks[fi]) |bi| {
            const b = ir.blocks.get(f.first_block[fi] + @as(u32, @intCast(bi))).?;
            try w.print(leaf_col ++ "b{d}:" ++ reset, .{bi});
            const preds = ir.list(b.preds);
            if (preds.len > 0) {
                try w.writeAll(dim ++ "  // from");
                for (preds) |p| try w.print(" b{d}", .{p});
                try w.writeAll(reset);
            }
            try w.writeAll("\n");
            for (b.start..b.start + b.len) |ii| try inst(w, l, fi, @intCast(ii), preds);
        }
        try w.writeAll("}\n");
    }

    fn typedef(w: *std.Io.Writer, l: *Low, t: Pool.Index) !void {
        const sp = l.sp;
        switch (sp.get(t)) {
            .custom_type => |c| {
                try w.writeAll(kind_col ++ "struct " ++ reset);
                try ty(w, l, t);
                try w.writeAll(" {");
                for (c.field_types, c.field_names) |ft, n| {
                    try w.writeAll("\n    ");
                    try ty(w, l, ft);
                    try w.print(" " ++ field_col ++ "{s}" ++ reset ++ ";", .{l.r.name_pool.get(n)});
                }
                try w.writeAll("\n}");
            },
            .variant_type => |v| {
                try w.writeAll(kind_col ++ "variant " ++ reset);
                try ty(w, l, t);
                if (v.tag_type != .none) {
                    try w.writeAll(" : ");
                    try ty(w, l, v.tag_type);
                }
                try w.writeAll(" {");
                for (v.cases) |cs| {
                    const c = sp.get(cs).variant_case_type;
                    try w.print("\n    " ++ field_col ++ "{s}" ++ reset, .{l.r.name_pool.get(c.name)});
                    if (c.tag != .none) {
                        try w.writeAll(" = ");
                        try value(w, l, c.tag);
                    }
                    if (c.payload != .none) {
                        try w.writeAll(" (");
                        try ty(w, l, c.payload);
                        try w.writeAll(")");
                    }
                    try w.writeAll(";");
                }
                try w.writeAll("\n}");
            },
            else => {
                try w.writeAll(kind_col ++ "typedef " ++ reset);
                try ty(w, l, t);
            },
        }
        const lay = sp.layout(t);
        try w.print(";" ++ dim ++ "  // size {d}, align {d}\n" ++ reset, .{ lay.size, @as(u64, 1) << @intCast(lay.align_log2) });
    }

    fn fn_name(l: *Low, fi: usize) []const u8 {
        const d = l.ir.functions.pool.decl.buf[fi];
        return if (d == .none) "$init" else decl_name(l.r, d);
    }

    fn ty(w: *std.Io.Writer, l: *Low, t: Pool.Index) std.Io.Writer.Error!void {
        const sp = l.sp;
        if (t == .none) return w.writeAll(type_col ++ "?" ++ reset);
        try w.writeAll(type_col);
        defer w.writeAll(reset) catch {};
        switch (sp.get(t)) {
            .simple_type => |s| try w.writeAll(switch (s) {
                .unit, .runit => "void",
                .never => "noreturn",
                .bool => "bool",
                .poison => "poison",
            }),
            .meta_type => |m| try w.writeAll(@tagName(m)),
            .ptr_type => |p| {
                const dyn = sp.get(p.child) == .array_type and sp.get(p.child).array_type.len == Pool.dyn_len;
                if (!p.mutable) try w.writeAll("const ");
                try ty(w, l, p.child);
                if (!dyn) try w.writeAll(type_col ++ "*");
            },
            .array_type => |a| {
                try ty(w, l, a.elem);
                try w.writeAll(type_col ++ "[");
                if (a.len != Pool.dyn_len) try sp.format(&l.r.name_pool, &l.r.abstract_pool, a.len, w);
                try w.writeAll("]");
            },
            .function_type => |f| {
                try w.writeAll("fn(");
                for (0..f.params.len) |i| {
                    if (i > 0) try w.writeAll(type_col ++ ", ");
                    try ty(w, l, sp.get(t).function_type.params[i]);
                }
                try w.writeAll(type_col ++ ") -> ");
                try ty(w, l, sp.get(t).function_type.ret);
            },
            .custom_type => |c| if (!try nominal(w, l, c.decl)) {
                try w.writeAll("struct {");
                for (c.field_types, c.field_names, 0..) |ft, n, i| {
                    try w.writeAll(if (i > 0) type_col ++ "; " else " ");
                    try ty(w, l, ft);
                    try w.print(type_col ++ " {s}", .{l.r.name_pool.get(n)});
                }
                try w.writeAll(type_col ++ " }");
            },
            .variant_type => |v| if (!try nominal(w, l, v.decl)) try w.writeAll("variant"),
            .trait_type => |tr| if (!try nominal(w, l, tr.decl)) try w.writeAll("trait"),
            .variant_case_type => |c| {
                try ty(w, l, c.variant);
                try w.print(type_col ++ ".{s}", .{l.r.name_pool.get(c.name)});
            },
            .variant_union_type => |u| {
                try w.writeAll("union(");
                for (u, 0..) |m, i| {
                    if (i > 0) try w.writeAll(type_col ++ ", ");
                    try ty(w, l, m);
                }
                try w.writeAll(type_col ++ ")");
            },
            else => try sp.format(&l.r.name_pool, &l.r.abstract_pool, t, w),
        }
    }

    fn nominal(w: *std.Io.Writer, l: *Low, d: DeclPool.Index) !bool {
        const n = l.r.decl_pool.names()[@intFromEnum(d)];
        if (n == .empty or n == .none) return false;
        try w.writeAll(l.r.name_pool.get(n));
        const args = l.r.decl_pool.realized_args.get(d) orelse return true;
        try w.writeAll("(");
        for (0..l.sp.get(args).aggregate.elems.len) |i| {
            if (i > 0) try w.writeAll(type_col ++ ", ");
            try value(w, l, l.sp.get(args).aggregate.elems[i]);
        }
        try w.writeAll(type_col ++ ")");
        return true;
    }

    fn value(w: *std.Io.Writer, l: *Low, v: Pool.Index) std.Io.Writer.Error!void {
        const sp = l.sp;
        switch (sp.tag(v)) {
            .function_value => try w.print(func_col ++ "{s}" ++ reset, .{decl_name(l.r, sp.get(v).function)}),
            .simple_value => try w.print(leaf_col ++ "{s}" ++ reset, .{if (v == .unit_value) "void" else if (v == .bool_true) "true" else "false"}),
            .int_value, .float_value, .string_value, .aggregate_value, .variant_value => {
                try w.writeAll(leaf_col);
                try sp.format(&l.r.name_pool, &l.r.abstract_pool, v, w);
                try w.writeAll(reset);
            },
            else => try ty(w, l, v),
        }
    }

    fn ref(w: *std.Io.Writer, l: *Low, x: u32) !void {
        const rr: Ir.Ref = @enumFromInt(x);
        if (rr == .none) return w.writeAll(dim ++ "void" ++ reset);
        if (rr.is_global()) return w.print("&" ++ bold ++ "{s}" ++ reset, .{decl_name(l.r, l.ir.globals.pool.decl.buf[rr.index()])});
        if (!rr.is_const()) return w.print("%{d}", .{x});
        try value(w, l, rr.value());
    }

    fn place(w: *std.Io.Writer, l: *Low, x: u32) !void {
        const rr: Ir.Ref = @enumFromInt(x);
        if (rr.is_global()) return w.print(bold ++ "{s}" ++ reset, .{decl_name(l.r, l.ir.globals.pool.decl.buf[rr.index()])});
        try w.writeAll("*");
        try ref(w, l, x);
    }

    fn refs(w: *std.Io.Writer, l: *Low, at: u32) !void {
        for (l.ir.list(at), 0..) |x, i| {
            if (i > 0) try w.writeAll(", ");
            try ref(w, l, x);
        }
    }

    fn op_ty(l: *Low, fi: usize, x: u32) Pool.Index {
        const rr: Ir.Ref = @enumFromInt(x);
        if (rr == .none) return .none;
        if (rr.is_const()) return l.sp.type_of(rr.value());
        if (rr.is_global()) return l.sp.intern(.{ .ptr_type = .{ .child = l.ir.globals.pool.ty.buf[rr.index()], .mutable = true } });
        return l.ir.insts.pool.ty.buf[l.ir.functions.pool.first_inst.buf[fi] + x];
    }

    fn deref(l: *Low, t: Pool.Index) Pool.Index {
        if (t == .none) return t;
        if (l.sp.get(t) == .ptr_type) return l.sp.get(t).ptr_type.child;
        return if (l.sp.tag(t) == .variant_case_type) l.sp.get(t).variant_case_type.variant else t;
    }

    fn field_name(l: *Low, rec0: Pool.Index, idx: u32) []const u8 {
        const rec = deref(l, rec0);
        if (rec == .none or l.sp.tag(rec) != .record_type) return "?";
        const names = l.sp.get(rec).custom_type.field_names;
        return if (idx < names.len) l.r.name_pool.get(names[idx]) else "?";
    }

    fn case_name(l: *Low, variant: Pool.Index, idx: u32) []const u8 {
        const v = deref(l, variant);
        if (v == .none or l.sp.tag(v) != .variant_type) return "?";
        const cases = l.sp.get(v).variant_type.cases;
        return if (idx < cases.len) l.r.name_pool.get(l.sp.get(cases[idx]).variant_case_type.name) else "?";
    }

    fn inst(w: *std.Io.Writer, l: *Low, fi: usize, local: u32, preds: []const u32) !void {
        const i = l.ir.insts.get(l.ir.functions.pool.first_inst.buf[fi] + local).?;
        if (i.op == .param) return;
        try w.writeAll("    ");
        if (i.ty != .unit_type and !i.op.is_terminator() and i.op != .store) {
            try ty(w, l, i.ty);
            try w.print(" %{d} = ", .{local});
        }
        const sym: ?[]const u8 = switch (i.op) {
            .add => "+",
            .sub => "-",
            .mul => "*",
            .div => "/",
            .rem => "%",
            .shl => "<<",
            .shr => ">>",
            .bit_and => "&",
            .bit_or => "|",
            .bit_xor => "^",
            .eq => "==",
            .ne => "!=",
            .lt => "<",
            .gt => ">",
            .le => "<=",
            .ge => ">=",
            else => null,
        };
        if (sym) |s| {
            try ref(w, l, i.a);
            try w.print(" {s} ", .{s});
            try ref(w, l, i.b);
            return w.writeAll(";\n");
        }
        switch (i.op) {
            .undef => try w.writeAll(kind_col ++ "undefined" ++ reset),
            .zeroed => try w.writeAll("{0}"),
            .phi => {
                try w.writeAll(kind_col ++ "phi" ++ reset ++ "(");
                for (l.ir.list(i.b), 0..) |x, k| {
                    if (k > 0) try w.writeAll(", ");
                    try w.print(dim ++ "b{d}: " ++ reset, .{if (k < preds.len) preds[k] else 0});
                    try ref(w, l, x);
                }
                try w.writeAll(")");
            },
            .bytes_eq => {
                try w.writeAll(kind_col ++ "memeq" ++ reset ++ "(");
                try ref(w, l, i.a);
                try w.writeAll(", ");
                try ref(w, l, i.b);
                try w.writeAll(")");
            },
            .type_test => {
                try ref(w, l, i.a);
                try w.writeAll(" " ++ kind_col ++ "oftype" ++ reset ++ " ");
                try ty(w, l, @enumFromInt(i.b));
            },
            .neg, .not => {
                try w.writeAll(if (i.op == .neg) "-" else if (i.ty == .bool_type) "!" else "~");
                try ref(w, l, i.a);
            },
            .convert, .cast => {
                try w.writeAll("(");
                try ty(w, l, i.ty);
                try w.writeAll(") ");
                try ref(w, l, i.a);
                try w.print(dim ++ "  /* {s} */" ++ reset, .{if (i.op == .convert) @tagName(@as(Pool.CoercionKind, @enumFromInt(i.b))) else @tagName(@as(Pool.CastKind, @enumFromInt(i.b)))});
            },
            .alloca => {
                try w.writeAll(kind_col ++ "alloca" ++ reset ++ "(");
                try ty(w, l, l.sp.get(i.ty).ptr_type.child);
                if (@as(Ir.Ref, @enumFromInt(i.a)) != .none) {
                    try w.writeAll("[");
                    try ref(w, l, i.a);
                    try w.writeAll("]");
                }
                try w.writeAll(")");
            },
            .load => try place(w, l, i.a),
            .store => {
                try place(w, l, i.a);
                try w.writeAll(" = ");
                try ref(w, l, i.b);
            },
            .field_ptr => {
                try w.writeAll("&");
                try ref(w, l, i.a);
                try w.print("->{s}", .{field_name(l, op_ty(l, fi, i.a), i.b)});
            },
            .index_ptr => {
                try w.writeAll("&");
                try ref(w, l, i.a);
                try w.writeAll("[");
                try ref(w, l, i.b);
                try w.writeAll("]");
            },
            .dyn => {
                try ref(w, l, i.a);
                try w.writeAll("[");
                try ref(w, l, l.ir.list(i.b)[0]);
                try w.writeAll("..");
                try ref(w, l, l.ir.list(i.b)[1]);
                try w.writeAll("]");
            },
            .len => {
                try ref(w, l, i.a);
                try w.writeAll(".len");
            },
            .aggregate => {
                const rec = l.sp.tag(i.ty) == .record_type;
                try w.writeAll("(");
                try ty(w, l, i.ty);
                try w.writeAll("){");
                for (l.ir.list(i.b), 0..) |x, k| {
                    if (k > 0) try w.writeAll(", ");
                    if (rec) try w.print(".{s} = ", .{field_name(l, i.ty, @intCast(k))});
                    try ref(w, l, x);
                }
                try w.writeAll("}");
            },
            .extract => {
                try ref(w, l, i.a);
                const at = op_ty(l, fi, i.a);
                if (at != .none and l.sp.tag(at) == .record_type) try w.print(".{s}", .{field_name(l, at, i.b)}) else try w.print(".{d}", .{i.b});
            },
            .variant_make => {
                try w.writeAll("(");
                try ty(w, l, i.ty);
                try w.print(") " ++ kind_col ++ "{s}" ++ reset, .{case_name(l, i.ty, i.a)});
                try w.writeAll("(");
                if (@as(Ir.Ref, @enumFromInt(i.b)) != .none) try ref(w, l, i.b);
                try w.writeAll(")");
            },
            .variant_tag => {
                try ref(w, l, i.a);
                try w.writeAll(".tag");
            },
            .variant_payload => {
                try ref(w, l, i.a);
                try w.print(".{s}", .{case_name(l, op_ty(l, fi, i.a), i.b)});
            },
            .call, .call_dyn => {
                try ref(w, l, i.a);
                try w.writeAll("(");
                try refs(w, l, i.b);
                try w.writeAll(")");
                if (i.op == .call_dyn) try w.writeAll(dim ++ "  /* dynamic */" ++ reset);
            },
            .closure => {
                try w.print(kind_col ++ "closure" ++ reset ++ "(" ++ func_col ++ "{s}" ++ reset, .{fn_name(l, i.a)});
                if (l.ir.list(i.b).len > 0) try w.writeAll(", ");
                try refs(w, l, i.b);
                try w.writeAll(")");
            },
            .select => {
                try ref(w, l, i.a);
                try w.writeAll(" ? ");
                try ref(w, l, l.ir.list(i.b)[0]);
                try w.writeAll(" : ");
                try ref(w, l, l.ir.list(i.b)[1]);
            },
            .@"switch" => {
                const cs = l.ir.list(i.b);
                try w.writeAll(kind_col ++ "switch" ++ reset ++ " (");
                try ref(w, l, i.a);
                try w.writeAll(") {\n");
                for (0..cs.len / 2) |k| {
                    const grouped = k > 0 and cs[2 * k] == cs[2 + 2 * k];
                    try w.writeAll(if (grouped) kind_col ++ " case " ++ reset else kind_col ++ "        case " ++ reset);
                    try ref(w, l, cs[1 + 2 * k]);
                    try w.writeAll(":");
                    if (k + 1 < cs.len / 2 and cs[4 + 2 * k] == cs[2 + 2 * k]) continue;
                    try w.print(kind_col ++ " goto" ++ reset ++ " b{d};\n", .{cs[2 + 2 * k]});
                }
                try w.print(kind_col ++ "        default: goto" ++ reset ++ " b{d};\n    }}\n", .{cs[0]});
                return;
            },
            .br => try w.print(kind_col ++ "goto" ++ reset ++ " b{d}", .{i.a}),
            .cond_br => {
                try w.writeAll(kind_col ++ "if" ++ reset ++ " (");
                try ref(w, l, i.a);
                try w.print(") " ++ kind_col ++ "goto" ++ reset ++ " b{d}; " ++ kind_col ++ "else goto" ++ reset ++ " b{d}", .{ l.ir.list(i.b)[0], l.ir.list(i.b)[1] });
            },
            .ret => {
                try w.writeAll(kind_col ++ "return" ++ reset);
                if (@as(Ir.Ref, @enumFromInt(i.a)) != .none) {
                    try w.writeAll(" ");
                    try ref(w, l, i.a);
                }
            },
            .@"unreachable" => try w.writeAll(kind_col ++ "unreachable" ++ reset),
            else => {},
        }
        try w.writeAll(";\n");
    }
};

pub const Inspector = struct {
    const Low = HighLowerer.Low;
    const none = std.math.maxInt(NodeId);

    w: *std.Io.Writer,
    r: *Res,
    l: ?*Low,
    tree: Tree,
    starts: []const u32,
    parent: []NodeId,
    owner: []DeclPool.Index,

    pub fn run(io: std.Io, r: *Res, l: ?*Low) !void {
        const a = std.heap.smp_allocator;
        var ob: [1 << 16]u8 = undefined;
        var fw = std.Io.File.stdout().writerStreaming(io, &ob);
        var ib: [4096]u8 = undefined;
        var fr = std.Io.File.stdin().readerStreaming(io, &ib);
        var line_starts = Resolver.lines(r);
        defer line_starts.deinit();
        const n = r.tree.ast_nodes.len();
        const marked = try Tree.marks(r.tree, r);
        defer a.free(marked);
        const parent = try a.alloc(NodeId, n);
        defer a.free(parent);
        const owner = try a.alloc(DeclPool.Index, n);
        defer a.free(owner);
        @memset(parent, none);
        @memset(owner, .none);
        for (0..n) |p| for (children(r.tree, @intCast(p))) |c| if (c < n) {
            parent[c] = @intCast(p);
        };
        const d = r.decl_pool.entries.sliced();
        for (d.node, d.kind, 0..) |dn, k, i| if ((k.is_fn() or is_type(k)) and dn < n) {
            owner[dn] = @enumFromInt(i);
        };
        const s = Inspector{ .w = &fw.interface, .r = r, .l = l, .tree = .{ .w = &fw.interface, .t = r.tree, .src = r.src_bytes, .r = r, .marked = marked }, .starts = line_starts.sliced(), .parent = parent, .owner = owner };
        try s.w.writeAll(dim ++ "[DEBUG INSPECTOR] name | #decl | :line\n" ++ reset);
        try s.w.flush();
        while (try fr.interface.takeDelimiter('\n')) |raw| {
            const q = std.mem.trim(u8, raw, " \t\r");
            if (q.len == 0) continue;
            try s.w.print(bold ++ "\n▸ {s}\n" ++ reset, .{q});
            if (!(if (q[0] == ':') try s.line(q[1..]) else try s.decls(q))) try s.w.writeAll(err_col ++ "  no match\n" ++ reset);
            try s.w.flush();
        }
    }

    fn children(t: *ParseTree, p: NodeId) []const NodeId {
        const args: *const [2]NodeId = @ptrCast(&t.ast_nodes.pool.args.buf[p]);
        return switch (Node.nk_childc[@intFromEnum(t.ast_nodes.pool.nk.buf[p])]) {
            .many => t.extra_childrefs.buf[args[0]..][0..args[1]],
            .one => args[0..1],
            .two => args[0..2],
            else => &.{},
        };
    }

    fn line_at(s: Inspector, n: NodeId) ?usize {
        return if (node_span(s.r.tree, s.r.src_bytes, n)) |sp| line_of(s.starts, sp[0]) else null;
    }

    fn decls(s: Inspector, q: []const u8) !bool {
        const id = if (q[0] == '#') std.fmt.parseInt(usize, q[1..], 10) catch return false else null;
        var hit = false;
        for (0..s.r.decl_pool.entries.len()) |i| if (if (id) |x| x == i else std.mem.eql(u8, decl_name(s.r, @enumFromInt(i)), q)) {
            hit = true;
            try s.w.writeAll(func_col ++ "resolved\n" ++ reset);
            try Resolver.decl_row(s.w, s.r, s.starts, i);
            try s.subtree(s.r.decl_pool.nodes()[i]);
            if (id != null or s.l == null or !s.l.?.next_of.contains(@enumFromInt(i))) try s.lowered(@enumFromInt(i));
        };
        return hit or std.mem.eql(u8, q, "$init") and try s.funcs(.none) > 0;
    }

    fn line(s: Inspector, q: []const u8) !bool {
        const want = (std.fmt.parseInt(usize, q, 10) catch return false) -| 1;
        var last: ?DeclPool.Index = null;
        for (1..s.parent.len) |i| {
            const n: NodeId = @intCast(i);
            const p = s.parent[n];
            if (s.line_at(n) != want or s.open(n, want) or p != none and s.line_at(p) == want and !s.open(p, want)) continue;
            try s.w.writeAll(func_col ++ "resolved\n" ++ reset);
            try s.subtree(n);
            const d = s.enclosing(n);
            if (d != last) try s.lowered(d);
            last = d;
            for (s.owner, 0..) |o, m| if (o != .none and o != d and s.enclosing(@intCast(m)) == o and s.within(@intCast(m), n)) {
                _ = try s.funcs(o);
            };
        }
        return last != null;
    }

    fn subtree(s: Inspector, n: NodeId) !void {
        if (n == 0 or n >= s.parent.len) return;
        if (s.line_at(n)) |ln| {
            const end = if (ln + 1 < s.starts.len) s.starts[ln + 1] - 1 else @as(u32, @intCast(s.r.src_bytes.len));
            try s.w.print(dim ++ "  {d:>5} │ " ++ reset ++ "{s}\n", .{ ln + 1, s.r.src_bytes[s.starts[ln]..end] });
        }
        try s.w.print(kind_col ++ "{s}" ++ reset, .{@tagName(s.r.tree.ast_nodes.pool.nk.buf[n])});
        try s.tree.annotate(n);
        try s.w.writeAll("\n");
        try s.tree.node(n, "", true, true, "", 0);
    }

    fn enclosing(s: Inspector, n0: NodeId) DeclPool.Index {
        var n = n0;
        while (n != none and s.owner[n] == .none) n = s.parent[n];
        return if (n == none) .none else s.owner[n];
    }

    fn lowered(s: Inspector, d: DeclPool.Index) !void {
        const l = s.l orelse return s.w.writeAll(err_col ++ "lowered\n  not lowered, resolution failed\n" ++ reset);
        try s.w.writeAll(func_col ++ "lowered\n" ++ reset);
        var cur = d;
        while (cur != .none) : (cur = s.up(cur)) {
            if (l.global_of.get(cur)) |g| {
                try HighLowerer.global(s.w, l, g);
                if (l.ir.globals.pool.init.buf[g] != .none) return;
            }
            if (try s.types(cur) or try s.funcs(cur) > 0) return;
            if (s.r.decl_pool.kinds()[@intFromEnum(cur)].is_fn()) return s.w.writeAll(dim ++ "  no code: unused or static only\n" ++ reset);
        }
        _ = try s.funcs(.none);
    }

    fn open(s: Inspector, n0: NodeId, want: usize) bool {
        if (Node.nk_childc[@intFromEnum(s.r.tree.ast_nodes.pool.nk.buf[n0])] != .many) return false;
        var n = n0;
        while (children(s.r.tree, n).len > 0) {
            const k = children(s.r.tree, n);
            if (k[k.len - 1] == 0 or k[k.len - 1] >= s.parent.len) break;
            n = k[k.len - 1];
        }
        return s.line_at(n) != want;
    }

    fn within(s: Inspector, m0: NodeId, n: NodeId) bool {
        var m = m0;
        while (m != none and m != n) m = s.parent[m];
        return m == n;
    }

    fn up(s: Inspector, d: DeclPool.Index) DeclPool.Index {
        const n = s.r.decl_pool.nodes()[@intFromEnum(d)];
        return if (n < s.parent.len and s.parent[n] != none) s.enclosing(s.parent[n]) else .none;
    }

    fn is_type(k: DeclPool.Entry.Kind) bool {
        return k == .record or k == .variant or k == .type_alias;
    }

    fn funcs(s: Inspector, d: DeclPool.Index) !usize {
        const l = s.l.?;
        const h = l.head_of.get(d) orelse d;
        var count: usize = 0;
        for (l.ir.functions.sliced_field(.decl), 0..) |fd, fi| if (fd == h or fd != .none and s.r.decl_pool.template_of.get(fd) == h) {
            try HighLowerer.func(s.w, l, fi);
            count += 1;
        };
        return count;
    }

    fn types(s: Inspector, d: DeclPool.Index) !bool {
        if (!is_type(s.r.decl_pool.kinds()[@intFromEnum(d)])) return false;
        for (s.r.decl_pool.entries.sliced_field(.value), 0..) |v, i| {
            const di: DeclPool.Index = @enumFromInt(i);
            if (v != .none and (di == d or s.r.decl_pool.template_of.get(di) == d)) try HighLowerer.typedef(s.w, s.l.?, v);
        }
        return true;
    }
};
