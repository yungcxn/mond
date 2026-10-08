const std = @import("std");
const Lexer = @import("src/Lexer.zig");
const Parser = @import("src/Parser.zig");
const Resolver = @import("src/Resolver.zig");
const DeclPool = @import("src/resolver/DeclPool.zig");
const Doctor = @import("src/resolver/Doctor.zig");
const DynBuf = @import("src/ds/dynbuf.zig").DynBuf;
const dbg = @import("src/debug.zig");
const Kind = Lexer.Token.Kind;

// the worker: runs the compiler on one source as far as it gets and turns what it found into
// semantic tokens (the highlighting) and diagnostics, the server passes both on to the editor

const Analysis = @This();

// the legend, tokens name their type and modifiers by index
pub const Type = enum(u8) { comment, keyword, operator, string, number, type, @"struct", @"enum", interface, enumMember, function, method, variable, parameter, property };
pub const Modifier = enum(u5) { readonly, static };

pub const Position = struct { line: u32, character: u32 };

pub const Diagnostic = struct {
    range: struct { start: Position, end: Position },
    severity: u8,
    source: []const u8 = "mond",
    message: []const u8,
};

pub const Result = struct { data: []const u32, diagnostics: []const Diagnostic };

// the class of a token kind by its name in the lexer, so new keywords and operators are colored too
const lexical = blk: {
    var t: [256]?Type = @splat(null);
    for (@typeInfo(Kind).@"enum".fields) |f| {
        if (std.mem.startsWith(u8, f.name, "kw_")) t[f.value] = .keyword;
        if (std.mem.startsWith(u8, f.name, "xpct_")) t[f.value] = .operator;
    }
    for (@intFromEnum(Kind.kw_u8)..@intFromEnum(Kind.kw_bool) + 1) |i| t[i] = .type;
    t[@intFromEnum(Kind.identifier)] = .variable;
    t[@intFromEnum(Kind.val_string)] = .string;
    t[@intFromEnum(Kind.val_char)] = .string;
    t[@intFromEnum(Kind.val_int)] = .number;
    t[@intFromEnum(Kind.val_float)] = .number;
    break :blk t;
};

a: std.mem.Allocator,
src: []u8,
// where every line starts
lines: DynBuf(u32),
data: DynBuf(u32),
diagnostics: DynBuf(Diagnostic),
// the start of the last token, tokens are encoded relative to it
last: Position = .{ .line = 0, .character = 0 },

// the source comes on stdin, the `Result` goes to stdout
pub fn run(io: std.Io, a: std.mem.Allocator) !void {
    var buf: [1 << 16]u8 = undefined;
    var in = std.Io.File.stdin().readerStreaming(io, &buf);
    const src = try in.interface.allocRemaining(a, .unlimited);
    var out = std.Io.File.stdout().writerStreaming(io, &buf);
    try std.json.Stringify.value(analyze(a, src), .{}, &out.interface);
    try out.interface.flush();
}

pub fn analyze(a: std.mem.Allocator, src: []u8) Result {
    var self = Analysis{ .a = a, .src = src, .lines = .init(a, 256), .data = .init(a, 4096), .diagnostics = .init(a, 16) };
    self.lines.push(0);
    for (src, 0..) |c, i| if (c == '\n') self.lines.push(@intCast(i + 1));
    var lexer = Lexer{ .src_bytes = src, .tokens = .init(a, 1024) };
    const r = self.resolve(&lexer);
    self.highlight(&lexer, r);
    return .{ .data = self.data.sliced(), .diagnostics = self.diagnostics.sliced() };
}

// every stage reports what stopped it, the resolver everything it found
fn resolve(self: *Analysis, lexer: *Lexer) ?*Resolver {
    lexer.gen_tokens() catch |e| return self.report(lexer.cursor -| 1, lexer.cursor, .@"error", @errorName(e), "");
    const p = self.a.create(Parser) catch @panic("OOM");
    p.* = Parser.init(self.a, lexer.tokens, self.src, lexer.tokens.sliced_field(.span));
    p.build_ast() catch |e| {
        const s = lexer.tokens.sliced_field(.span)[p.tok_cursor -| 1];
        return self.report(s[0], s[1], .@"error", @errorName(e), "");
    };
    const r = self.a.create(Resolver) catch @panic("OOM");
    r.* = Resolver.init(self.a, &p.tree, self.src, p.global_store.sliced());
    r.resolve() catch {};
    const d = r.doc.diagnostics.sliced();
    for (d.code, d.severity, d.node, d.a, d.b) |code, severity, n, x, y| {
        var operands: std.Io.Writer.Allocating = .init(self.a);
        dbg.print_operands(&operands.writer, r, code, x, y, false) catch @panic("OOM");
        const s = dbg.node_span(r.tree, self.src, n) orelse Lexer.TextSpan{ 0, 0 };
        _ = self.report(s[0], s[1], severity, @tagName(code), operands.written());
    }
    return r;
}

fn report(self: *Analysis, lo: u32, hi: u32, severity: Doctor.Disorder.Severity, what: []const u8, operands: []const u8) ?*Resolver {
    self.diagnostics.push(.{
        .range = .{ .start = self.pos(lo), .end = self.pos(@max(lo, hi)) },
        // lsp counts from error = 1 to hint = 4
        .severity = 3 - @intFromEnum(severity),
        .message = std.mem.concat(self.a, u8, &.{ what, operands }) catch @panic("OOM"),
    });
    return null;
}

// every token by its kind, identifiers by the declaration they mean once the resolver ran
fn highlight(self: *Analysis, lexer: *Lexer, r: ?*Resolver) void {
    const toks = lexer.tokens.sliced();
    const class = self.a.alloc(?Type, toks.tk.len) catch @panic("OOM");
    const mods = self.a.alloc(u32, toks.tk.len) catch @panic("OOM");
    for (class, toks.tk) |*c, tk| c.* = lexical[@intFromEnum(tk)];
    @memset(mods, 0);
    if (r) |res| resolved(res, class, mods);

    var end: u32 = 0;
    for (toks.span, toks.tk, class, mods) |s, tk, c, m| {
        // the span of a string or char leaves its quotes out
        const quoted: u32 = @intFromBool(tk == .val_string or tk == .val_char);
        self.comments(end, s[0] - quoted);
        end = s[1] + quoted;
        if (c) |t| self.push(s[0] - quoted, end, t, m);
    }
    self.comments(end, @intCast(self.src.len));
}

fn resolved(r: *Resolver, class: []?Type, mods: []u32) void {
    const t = r.tree;
    const d = r.decl_pool.entries.sliced();
    for (0..t.ast_nodes.len()) |i| {
        const n: u32 = @intCast(i);
        // names without a declaration: fields of a value and cases of a type
        const id, const undeclared: ?Type = switch (t.kind(n)) {
            .identifier => .{ n, null },
            .member => .{ t.arg(n, 1), if (is_type(r, t.arg(n, 0))) .enumMember else .property },
            .partial__variant_def_param => .{ t.laidout_children(.partial__variant_def_param, n).name, .enumMember },
            else => continue,
        };
        if (t.kind(id) != .identifier) continue;
        const tok = t.arg(id, 0);
        if (r.node_decl[n] == .none) {
            if (undeclared) |c| class[tok] = c;
            continue;
        }
        const decl = @intFromEnum(r.node_decl[n]);
        const c = of(d.kind[decl]);
        const value = c == .variable or c == .parameter or c == .property;
        class[tok] = c;
        mods[tok] = bit(.readonly, value and !d.flags[decl].is_mut) | bit(.static, d.flags[decl].is_stc);
    }
}

fn is_type(r: *Resolver, n: u32) bool {
    const ty = r.node_type[n];
    return ty != .none and r.static_pool.tag(ty) == .meta_type;
}

fn of(kind: DeclPool.Entry.Kind) Type {
    return switch (kind) {
        .parameter, .static_parameter => .parameter,
        .field => .property,
        .function, .static_function, .inlined_function => .function,
        .trait_member => .method,
        .type_alias => .type,
        .record => .@"struct",
        .variant => .@"enum",
        .variant_case => .enumMember,
        .trait => .interface,
        else => .variable,
    };
}

fn bit(m: Modifier, on: bool) u32 {
    return @as(u32, @intFromBool(on)) << @intFromEnum(m);
}

// whitespace and comments are all that is between tokens, a comment runs from `#` to the end of its line
fn comments(self: *Analysis, lo: u32, hi: u32) void {
    var at = lo;
    while (std.mem.indexOfScalarPos(u8, self.src[0..hi], at, '#')) |c| {
        at = @intCast(std.mem.indexOfScalarPos(u8, self.src[0..hi], c, '\n') orelse hi);
        self.push(@intCast(c), at, .comment, 0);
    }
}

// one token per line, editors draw none across lines
fn push(self: *Analysis, lo: u32, hi: u32, t: Type, mods: u32) void {
    var at = lo;
    var pieces = std.mem.splitScalar(u8, self.src[lo..hi], '\n');
    while (pieces.next()) |piece| : (at += @intCast(piece.len + 1)) if (piece.len > 0) {
        const p = self.pos(at);
        const delta = if (p.line == self.last.line) p.character - self.last.character else p.character;
        self.data.append(&.{ p.line - self.last.line, delta, utf16(piece), @intFromEnum(t), mods });
        self.last = p;
    };
}

fn pos(self: *Analysis, at: u32) Position {
    const lines = self.lines.sliced();
    const line = std.sort.partitionPoint(u32, lines, at, struct {
        fn before(x: u32, start: u32) bool {
            return start <= x;
        }
    }.before) - 1;
    return .{ .line = @intCast(line), .character = utf16(self.src[lines[line]..at]) };
}

// lsp counts columns in utf-16 code units
fn utf16(s: []const u8) u32 {
    var n: u32 = 0;
    for (s) |c| n += switch (c) {
        0x80...0xbf => 0,
        0xf0...0xff => 2,
        else => 1,
    };
    return n;
}
