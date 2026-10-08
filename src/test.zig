const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const Resolver = @import("Resolver.zig");
const HighLowerer = @import("HighLowerer.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const Ref = @import("high_lowerer/HighIr.zig").Ref;
const debug = @import("debug.zig");

const reset = "\x1b[0m";
const dim = "\x1b[90m";
const green = "\x1b[32m";
const red = "\x1b[1;31m";
const bold = "\x1b[1m";

const Finding = struct {
    line: usize,
    code: []const u8,
    msg: []const u8 = "",

    fn lt(_: void, x: Finding, y: Finding) bool {
        return x.line < y.line or (x.line == y.line and std.mem.order(u8, x.code, y.code) == .lt);
    }
};

const Result = struct { found: []Finding, r: ?*Resolver = null };

const Check = struct { line: usize, value: bool, name: []const u8, want: []const u8 };

fn line_at(src: []const u8, at: usize) usize {
    return std.mem.count(u8, src[0..@min(at, src.len)], "\n") + 1;
}

fn run(a: std.mem.Allocator, src: []u8) !Result {
    var out: std.ArrayList(Finding) = .empty;
    var res: ?*Resolver = null;
    var lexer = Lexer{ .src_bytes = src, .tokens = .init(a, 1024) };
    if (lexer.gen_tokens()) |_| {
        const parser = try a.create(Parser);
        parser.* = Parser.init(a, lexer.tokens, src, lexer.tokens.sliced_field(.span));
        if (parser.build_ast()) |_| {
            const r = try a.create(Resolver);
            r.* = Resolver.init(a, &parser.tree, src, parser.global_store.sliced());
            const resolved = if (r.resolve()) |_| true else |_| false;
            res = r;
            if (resolved) {
                const l = try a.create(HighLowerer);
                l.* = HighLowerer.init(a, r);
                l.lower();
                if (try verify(a, l)) |v| try out.append(a, .{ .line = if (v.d == .none) 1 else if (debug.node_span(&parser.tree, src, r.decl_pool.get_node(v.d))) |s| line_at(src, s[0]) else 1, .code = "invalid_ir", .msg = v.msg });
            }
            const d = r.doc.diagnostics.sliced();
            for (d.code, d.node, d.a, d.b) |code, node, x, y| {
                var msg: std.Io.Writer.Allocating = .init(a);
                try debug.print_operands(&msg.writer, r, code, x, y, true);
                try out.append(a, .{ .line = if (debug.node_span(&parser.tree, src, node)) |s| line_at(src, s[0]) else 1, .code = @tagName(code), .msg = msg.written() });
            }
        } else |e| try out.append(a, .{ .line = line_at(src, lexer.tokens.pool.span.buf[parser.tok_cursor -| 1][0]), .code = @errorName(e) });
    } else |e| try out.append(a, .{ .line = line_at(src, lexer.cursor -| 1), .code = @errorName(e) });
    std.mem.sort(Finding, out.items, {}, Finding.lt);
    return .{ .found = out.items, .r = res };
}

const Bad = struct { d: DeclPool.Index, msg: []const u8 };

fn bad(a: std.mem.Allocator, d: DeclPool.Index, comptime fmt: []const u8, args: anytype) !?Bad {
    return .{ .d = d, .msg = try std.fmt.allocPrint(a, fmt, args) };
}

fn verify(a: std.mem.Allocator, l: *HighLowerer) !?Bad {
    const ir = &l.ir;
    const f = ir.functions.sliced();
    const bs = ir.blocks.sliced();
    const is = ir.insts.sliced();
    for (0..f.decl.len) |fi| {
        const nb = f.blocks[fi];
        if (nb == 0) continue;
        const b0 = f.first_block[fi];
        const base = f.first_inst[fi];
        const owner = try a.alloc(u32, f.insts[fi]);
        const succs = try a.alloc(std.ArrayList(u32), nb);
        const dom = try a.alloc(std.DynamicBitSetUnmanaged, nb);
        const d = f.decl[fi];
        var next: u32 = 0;
        for (0..nb) |b| {
            const blk = bs.start[b0 + b];
            if (blk != next) return try bad(a, d, "fn #{d} b{d} not contiguous", .{ fi, b });
            next += bs.len[b0 + b];
            if (bs.len[b0 + b] == 0) return try bad(a, d, "fn #{d} b{d} empty", .{ fi, b });
            succs[b] = .empty;
            for (blk..blk + bs.len[b0 + b]) |i| {
                owner[i] = @intCast(b);
                const op = is.op[base + i];
                if (op.is_terminator() != (i + 1 == blk + bs.len[b0 + b])) return try bad(a, d, "fn #{d} b{d} terminator misplaced at %{d}", .{ fi, b, i });
                const ib = is.b[base + i];
                switch (op) {
                    .br => try succs[b].append(a, is.a[base + i]),
                    .cond_br => try succs[b].appendSlice(a, ir.list(ib)),
                    .@"switch" => for (ir.list(ib), 0..) |x, k| if (k % 2 == 0) try succs[b].append(a, x),
                    else => {},
                }
            }
            for (succs[b].items) |x| if (x >= nb) return try bad(a, d, "fn #{d} b{d} jumps out of range", .{ fi, b });
        }
        if (next != f.insts[fi]) return try bad(a, d, "fn #{d} instruction count mismatch", .{fi});
        for (0..nb) |b| for (0..nb) |t| {
            var n: usize = 0;
            for (succs[t].items) |x| n += @intFromBool(x == b);
            var m: usize = 0;
            for (ir.list(bs.preds[b0 + b])) |p| m += @intFromBool(p == t);
            if (n != m) return try bad(a, d, "fn #{d} b{d} preds disagree with b{d}", .{ fi, b, t });
        };
        for (dom, 0..) |*x, b| {
            x.* = try .initFull(a, nb);
            if (b == 0) {
                x.unsetAll();
                x.set(0);
            }
        }
        var changed = true;
        while (changed) {
            changed = false;
            for (1..nb) |b| {
                var nd = try dom[b].clone(a);
                for (ir.list(bs.preds[b0 + b])) |p| nd.setIntersection(dom[p]);
                nd.set(b);
                if (!nd.eql(dom[b])) {
                    dom[b] = nd;
                    changed = true;
                }
            }
        }
        for (0..f.insts[fi]) |i| {
            const op = is.op[base + i];
            const u = owner[i];
            const sh = op.shape();
            const preds = ir.list(bs.preds[b0 + u]);
            if (op == .phi and ir.list(is.b[base + i]).len != preds.len) return try bad(a, d, "fn #{d} phi %{d} has {d} operands for {d} preds", .{ fi, i, ir.list(is.b[base + i]).len, preds.len });
            inline for (.{ .{ sh[0], is.a[base + i] }, .{ sh[1], is.b[base + i] } }) |o| {
                const items: []const u32 = switch (o[0]) {
                    .ref => &.{o[1]},
                    .refs, .cases => ir.list(o[1]),
                    else => &.{},
                };
                for (items, 0..) |x, k| {
                    const r: Ref = @enumFromInt(x);
                    if (o[0] == .cases and k % 2 == 0 or r == .none) continue;
                    if (r.is_const()) continue;
                    if (r.is_global()) {
                        if (r.index() >= ir.globals.len()) return try bad(a, d, "fn #{d} %{d} bad global", .{ fi, i });
                        continue;
                    }
                    if (o[0] == .cases) return try bad(a, d, "fn #{d} %{d} non-constant case", .{ fi, i });
                    if (x >= f.insts[fi]) return try bad(a, d, "fn #{d} %{d} uses out of range %{d}", .{ fi, i, x });
                    const def = owner[x];
                    const ok = if (op == .phi) dom[preds[k]].isSet(def) else if (def == u) x < i else dom[u].isSet(def);
                    if (!ok) return try bad(a, d, "fn #{d} %{d} uses %{d} not dominating", .{ fi, i, x });
                }
            }
        }
    }
    return null;
}

fn marker(l: []const u8, m: []const u8) ?[]const u8 {
    const at = std.mem.indexOf(u8, l, m) orelse return null;
    const rest = l[at + m.len ..];
    return std.mem.trim(u8, rest[0 .. std.mem.indexOfScalar(u8, rest, '#') orelse rest.len], " \t");
}

fn checks(a: std.mem.Allocator, src: []const u8) ![]Check {
    var out: std.ArrayList(Check) = .empty;
    var lines = std.mem.splitScalar(u8, src, '\n');
    var n: usize = 0;
    while (lines.next()) |l| {
        n += 1;
        for ([_][]const u8{ "#:", "#=" }) |m| if (marker(l, m)) |c| {
            const sp = std.mem.indexOfScalar(u8, c, ' ') orelse c.len;
            try out.append(a, .{ .line = n, .value = m[1] == '=', .name = c[0..sp], .want = std.mem.trim(u8, c[sp..], " ") });
        };
    }
    return out.items;
}

fn actual(a: std.mem.Allocator, r: *Resolver, c: Check) ![]const u8 {
    const d = r.decl_pool.entries.sliced();
    for (0..d.name.len) |i| {
        if (d.name[i] == .empty or d.name[i] == .none or !std.mem.eql(u8, r.name_pool.get(d.name[i]), c.name)) continue;
        const span = debug.node_span(r.tree, r.src_bytes, d.node[i]) orelse continue;
        if (line_at(r.src_bytes, span[0]) != c.line) continue;
        var w: std.Io.Writer.Allocating = .init(a);
        const v = if (c.value) d.value[i] else r.static_pool.apply_vars(&r.abstract_pool, d.ty[i]);
        try r.static_pool.format(&r.name_pool, &r.abstract_pool, v, &w.writer);
        return w.written();
    }
    return "<no such declaration on this line>";
}

fn expectations(a: std.mem.Allocator, src: []const u8) ![]Finding {
    var out: std.ArrayList(Finding) = .empty;
    var lines = std.mem.splitScalar(u8, src, '\n');
    var n: usize = 0;
    while (lines.next()) |l| {
        n += 1;
        var codes = std.mem.tokenizeScalar(u8, marker(l, "#!") orelse continue, ' ');
        while (codes.next()) |c| try out.append(a, .{ .line = n, .code = c });
    }
    std.mem.sort(Finding, out.items, {}, Finding.lt);
    return out.items;
}

fn source_line(src: []const u8, line: usize) []const u8 {
    var lines = std.mem.splitScalar(u8, src, '\n');
    for (1..line) |_| _ = lines.next();
    const l = lines.next() orelse "";
    return std.mem.trim(u8, l[0 .. std.mem.indexOfScalar(u8, l, '#') orelse l.len], " \t");
}

fn report(w: *std.Io.Writer, src: []const u8, mark: []const u8, f: Finding) !void {
    try w.print("      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++ "{s}  " ++ dim ++ "{s}" ++ reset ++ "\n", .{ mark, dim, f.line, bold, f.code, f.msg, source_line(src, f.line) });
}

fn check(w: *std.Io.Writer, io: std.Io, path: []const u8, negative: bool, filters: []const [:0]const u8) ![2]usize {
    var arena = std.heap.ArenaAllocator.init(std.heap.smp_allocator);
    defer arena.deinit();
    var dir = try std.Io.Dir.cwd().openDir(io, path, .{ .iterate = true });
    defer dir.close(io);
    var names: std.ArrayList([]const u8) = .empty;
    var it = dir.iterate();
    while (try it.next(io)) |e| if (e.kind == .file and std.mem.endsWith(u8, e.name, ".mn")) try names.append(arena.allocator(), try arena.allocator().dupe(u8, e.name));
    std.mem.sort([]const u8, names.items, {}, struct {
        fn lt(_: void, x: []const u8, y: []const u8) bool {
            return std.mem.order(u8, x, y) == .lt;
        }
    }.lt);
    try w.print(bold ++ "\n{s} ({s})\n" ++ reset, .{ path, if (negative) "must report exactly the `#!` diagnostics" else "must resolve without diagnostics" });
    var counts: [2]usize = .{ 0, 0 };
    for (names.items) |name| {
        if (filters.len > 0) for (filters) |f| {
            if (std.mem.indexOf(u8, name, f) != null) break;
        } else continue;
        const a = arena.allocator();
        const src = try dir.readFileAlloc(io, name, a, .limited(50 << 20));
        const want = try expectations(a, src);
        const got = try run(a, src);
        var lines: std.Io.Writer.Allocating = .init(a);
        var i: usize = 0;
        var j: usize = 0;
        var ok = !negative or want.len > 0;
        while (i < want.len or j < got.found.len) {
            const match = i < want.len and j < got.found.len and want[i].line == got.found[j].line and std.mem.eql(u8, want[i].code, got.found[j].code);
            if (match) {
                try report(&lines.writer, src, green ++ "✓         ", got.found[j]);
                i += 1;
                j += 1;
            } else if (j >= got.found.len or (i < want.len and Finding.lt({}, want[i], got.found[j]))) {
                try report(&lines.writer, src, red ++ "missing   ", want[i]);
                i += 1;
                ok = false;
            } else {
                try report(&lines.writer, src, red ++ "unexpected", got.found[j]);
                j += 1;
                ok = false;
            }
        }
        const cs = try checks(a, src);
        for (cs) |c| {
            const have = if (got.r) |r| try actual(a, r, c) else "<not resolved>";
            const same = std.mem.eql(u8, have, c.want);
            ok = ok and same;
            try lines.writer.print("      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++ "{s}", .{ if (same) green ++ "✓         " else red ++ "wrong     ", dim, c.line, bold, c.name, have });
            if (!same) try lines.writer.print(red ++ "  expected " ++ reset ++ "{s}", .{c.want});
            try lines.writer.print("  " ++ dim ++ "{s}" ++ reset ++ "\n", .{source_line(src, c.line)});
        }
        counts[@intFromBool(!ok)] += 1;
        try w.print("  {s}{s}" ++ reset ++ " {s}/{s}  " ++ dim ++ "{d} expected, {d} found, {d} checks, {d} declarations" ++ reset ++ "\n{s}", .{ if (ok) green else red, if (ok) "✓" else "✗", path, name, want.len, got.found.len, cs.len, if (got.r) |r| r.decl_pool.entries.len() else 0, lines.written() });
    }
    return counts;
}

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    var buf: [1 << 16]u8 = undefined;
    var fw = std.Io.File.stdout().writerStreaming(io, &buf);
    const w = &fw.interface;
    const p1 = try check(w, io, "examples", false, args[1..]);
    const p2 = try check(w, io, "examples/positive", false, args[1..]);
    const p3 = try check(w, io, "examples/general-purpose", false, args[1..]);
    const pos = .{ p1[0] + p2[0] + p3[0], p1[1] + p2[1] + p3[1] };
    const neg = try check(w, io, "examples/negative", true, args[1..]);
    const failed = pos[1] + neg[1];
    try w.print(bold ++ "\n{s}{d} passed, {d} failed" ++ reset ++ dim ++ "  ({d} positive, {d} negative files)\n" ++ reset, .{ if (failed == 0) green else red, pos[0] + neg[0], failed, pos[0] + pos[1], neg[0] + neg[1] });
    try w.flush();
    if (failed > 0) std.process.exit(1);
}
