const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const Resolver = @import("Resolver.zig");
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
            r.resolve() catch {};
            res = r;
            const d = r.doc.diagnostics.sliced();
            for (d.code, d.node, d.a, d.b) |code, node, x, y| {
                var msg: std.Io.Writer.Allocating = .init(a);
                try debug.print_operands(&msg.writer, r, code, x, y);
                try out.append(a, .{ .line = if (debug.node_span(&parser.tree, src, node)) |s| line_at(src, s[0]) else 1, .code = @tagName(code), .msg = msg.written() });
            }
        } else |e| try out.append(a, .{ .line = line_at(src, lexer.tokens.pool.span.buf[parser.tok_cursor -| 1][0]), .code = @errorName(e) });
    } else |e| try out.append(a, .{ .line = line_at(src, lexer.cursor -| 1), .code = @errorName(e) });
    std.mem.sort(Finding, out.items, {}, Finding.lt);
    return .{ .found = out.items, .r = res };
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
    const d = r.decls.sliced();
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
        try w.print("  {s}{s}" ++ reset ++ " {s}/{s}  " ++ dim ++ "{d} expected, {d} found, {d} checks, {d} declarations" ++ reset ++ "\n{s}", .{ if (ok) green else red, if (ok) "✓" else "✗", path, name, want.len, got.found.len, cs.len, if (got.r) |r| r.decls.len() else 0, lines.written() });
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
    const pos = .{ p1[0] + p2[0], p1[1] + p2[1] };
    const neg = try check(w, io, "examples/negative", true, args[1..]);
    const failed = pos[1] + neg[1];
    try w.print(bold ++ "\n{s}{d} passed, {d} failed" ++ reset ++ dim ++ "  ({d} positive, {d} negative files)\n" ++ reset, .{ if (failed == 0) green else red, pos[0] + neg[0], failed, pos[0] + pos[1], neg[0] + neg[1] });
    try w.flush();
    if (failed > 0) std.process.exit(1);
}
