const std = @import("std");
const builtin = @import("builtin");
const mond = @import("mond");
const Lexer = mond.Lexer;
const Parser = mond.Parser;
const ParseTree = mond.ParseTree;
const Resolver = mond.Resolver;
const DeclPool = mond.DeclPool;
const Doctor = mond.Doctor;
const DynBuf = mond.DynBuf;
const dbg = mond.dbg;
const Kind = Lexer.Token.Kind;

// the worker: runs the compiler on one source as far as it gets and turns what it found into
// semantic tokens (the highlighting), diagnostics and the declarations every name means, the server passes them on to the editor

const Analysis = @This();

// the legend, tokens name their type and modifiers by index
pub const Type = enum(u8) { comment, keyword, operator, string, number, type, @"struct", @"enum", interface, enumMember, function, method, variable, parameter, property };
pub const Modifier = enum(u5) { readonly, static };

pub const Position = struct { line: u32, character: u32 };
pub const Range = struct { start: Position, end: Position };

pub const Diagnostic = struct {
    range: Range,
    severity: u8,
    source: []const u8 = "mond",
    message: []const u8,
};

// a declaration, named at `selectionRange` (a builtin nowhere), the server gives it the `children` of its `Outline`
pub const Symbol = struct {
    name: []const u8,
    detail: []const u8,
    kind: u8,
    range: Range,
    selectionRange: ?Range,
    children: []const Symbol = &.{},
};

// a name: line, first and end character, the declaration in `decls` it means (its own for a declaration's name)
pub const Link = [4]u32;

// the declarations in the outline, each holding the ones within it
pub const Outline = struct { decl: u32, children: []const Outline };

pub const Result = struct {
    data: []const u32 = &.{},
    diagnostics: []const Diagnostic = &.{},
    decls: []const Symbol = &.{},
    // sorted by position
    links: []const Link = &.{},
    outline: []const Outline = &.{},
};

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
decls: DynBuf(Symbol),
links: DynBuf(Link),
// token -> its declaration in `decls`, declaration of the resolver -> the token naming it
meant: []u32 = &.{},
def: []u32 = &.{},
// per declaration in `decls`: the token naming it and whether it is global
sites: DynBuf(struct { tok: u32, global: bool }),
// per node: its parent, its first token and the declaration it makes, per token: its leaf
parent: []u32 = &.{},
first: []u32 = &.{},
declared: []u32 = &.{},
leaf: []u32 = &.{},
// the start of the last token, tokens are encoded relative to it
last: Position = .{ .line = 0, .character = 0 },

// the source comes on stdin, the `Result` goes to stdout
pub fn run(io: std.Io, a: std.mem.Allocator) !void {
    // a runaway compiler stops itself, even when the server is gone: memory and cpu time are capped, a crash dumps no core
    if (builtin.os.tag != .windows) for ([_]struct { std.posix.rlimit_resource, u64 }{ .{ .AS, 4 << 30 }, .{ .CPU, 10 }, .{ .CORE, 0 } }) |l| {
        std.posix.setrlimit(l[0], .{ .cur = l[1], .max = l[1] }) catch {};
    };
    var buf: [1 << 16]u8 = undefined;
    var in = std.Io.File.stdin().readerStreaming(io, &buf);
    const src = try in.interface.allocRemaining(a, .unlimited);
    var out = std.Io.File.stdout().writerStreaming(io, &buf);
    try std.json.Stringify.value(analyze(a, src), .{}, &out.interface);
    try out.interface.flush();
}

pub fn analyze(a: std.mem.Allocator, src: []u8) Result {
    var self = Analysis{ .a = a, .src = src, .lines = .init(a, 256), .data = .init(a, 4096), .diagnostics = .init(a, 16), .decls = .init(a, 256), .links = .init(a, 1024), .sites = .init(a, 256) };
    self.lines.push(0);
    for (src, 0..) |c, i| if (c == '\n') self.lines.push(@intCast(i + 1));
    var lexer = Lexer{ .src_bytes = src, .tokens = .init(a, 1024) };
    const r = self.resolve(&lexer);
    self.highlight(&lexer, r);
    if (r) |res| self.link(&lexer, res);
    return .{ .data = self.data.sliced(), .diagnostics = self.diagnostics.sliced(), .decls = self.decls.sliced(), .links = self.links.sliced(), .outline = self.outline() };
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
        const s = r.tree.extent(n) orelse dbg.node_span(r.tree, self.src, n) orelse Lexer.TextSpan{ 0, 0 };
        _ = self.report(s[0], s[1], severity, @tagName(code), operands.written());
    }
    return r;
}

// a diagnostic marks its node up to the end of the node's first line, a whole body would be too much
fn report(self: *Analysis, lo: u32, hi: u32, severity: Doctor.Disorder.Severity, what: []const u8, operands: []const u8) ?*Resolver {
    const eol = std.mem.indexOfScalarPos(u8, self.src, lo, '\n') orelse self.src.len;
    self.diagnostics.push(.{
        .range = self.range(lo, @intCast(@max(lo, @min(hi, eol)))),
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
    // `_` is no name
    for (class, toks.tk, toks.span) |*c, tk, s| c.* = if (tk == .identifier and std.mem.eql(u8, self.src[s[0]..s[1]], "_")) .keyword else lexical[@intFromEnum(tk)];
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

const none = std.math.maxInt(u32);
const undefined_name = none - 1;

// every declaration by the token naming it and every name by the declaration it means
fn link(self: *Analysis, lexer: *Lexer, r: *Resolver) void {
    const t = r.tree;
    const spans = lexer.tokens.sliced_field(.span);
    const d = r.decl_pool.entries.sliced();
    const nodes = t.ast_nodes.len();
    self.meant = self.alloc(spans.len);
    self.def = self.alloc(d.kind.len);
    self.parent = self.alloc(nodes);
    self.first = self.alloc(nodes);
    self.declared = self.alloc(nodes);
    self.leaf = self.alloc(spans.len);
    for (r.roots) |n| self.descend(t, n);
    for (self.def, 0..) |*x, i| {
        // a realization is named where its template is
        const at = r.generics.template_of.get(@enumFromInt(i)) orelse @as(DeclPool.Index, @enumFromInt(i));
        const node = d.node[@intFromEnum(at)];
        x.* = named(r, node, d.name[i]) orelse continue;
        if (self.meant[x.*] != none) continue;
        const c = of(d.kind[i]);
        // a type shows what it is
        const ty = if (d.kind[i].is_type_decl()) d.value[i] else d.ty[i];
        self.declare(x.*, r.name_pool.get(d.name[i]), self.type_text(r, ty), c, c != .variable and c != .parameter or d.flags[i].is_global, d.flags[i].is_global, t.extent(node), spans[x.*]);
        self.declared[node] = self.meant[x.*];
    }
    // the resolver declares no cases and no parameters of signatures it does not check (`fun print = (&u8 fmt);`)
    for (1..nodes) |i| {
        const n: u32 = @intCast(i);
        const id, const class: Type = switch (t.kind(n)) {
            .partial__variant_def_param => .{ t.laidout_children(.partial__variant_def_param, n).name, .enumMember },
            .partial__fun_def_param_named => .{ t.arg(n, 1), .parameter },
            .partial__type_def_param_named => .{ t.arg(n, 1), .property },
            else => continue,
        };
        if (t.kind(id) != .identifier or self.meant[t.arg(id, 0)] != none) continue;
        // a case spans its payload and tag (`Circle(f32 r)`)
        var outer = n;
        while (self.parent[outer] != none and (t.kind(self.parent[outer]) == .partial__variant_def_param_typed or t.kind(self.parent[outer]) == .partial__variant_def_param_tagged)) outer = self.parent[outer];
        self.declare(t.arg(id, 0), r.name_pool.get(r.name_pool.name_of(id)), if (class == .enumMember) "" else self.written(r, lexer, ParseTree.Param.from_node(t, n).ty, t.arg(id, 0)), class, class != .parameter, false, t.extent(outer), t.span(id));
        self.declared[outer] = self.meant[t.arg(id, 0)];
    }
    for (0..nodes) |i| {
        const n: u32 = @intCast(i);
        const tok = name_token(r, n) orelse continue;
        if (r.node_decl[n] == .none) continue;
        const at = self.def[@intFromEnum(r.node_decl[n])];
        const o = r.generics.template_of.get(r.node_decl[n]) orelse r.node_decl[n];
        // a positional parameter has no name of its own (`(i32, i32)`), its function declares it
        self.meant[tok] = if (at != none) self.meant[at] else if (positional(r.name_pool.get(d.name[@intFromEnum(o)]))) self.enclosing(d.node[@intFromEnum(o)]) else none;
    }
    // a named argument means the parameter or field of its name within what is called (`Point(x = 1)`, `p with (x = 1)`)
    for (0..nodes) |i| {
        const n: u32 = @intCast(i);
        if ((t.kind(n) != .fun_call and t.kind(n) != .with) or t.kind(t.arg(n, 1)) != .partial__fun_call_param_tuple) continue;
        const in = self.base(r, t.arg(n, 0));
        const f = if (t.kind(n) == .fun_call) if (name_token(r, t.arg(n, 0))) |x| self.meant[x] else none else none;
        for (t.laidout_children(.partial__fun_call_param_tuple, t.arg(n, 1))) |arg| {
            const id = t.arg_name(arg);
            if (id == 0 or t.kind(id) != .identifier) continue;
            const name = r.name_pool.get(r.name_pool.name_of(id));
            self.meant[t.arg(id, 0)] = if (in) |x| self.within(x, name) else if (f != none) self.overloaded(f, name) else none;
        }
    }
    // the other names in source order: a field or case lies within the declaration of its base's type, a positional field
    // (`A.$1`) is declared by it, else members and named arguments go by their unique name and the others by scope,
    // code the resolver did not check declares a name where it first appears once it appears again (`Res.Ok(v) => v` never matched)
    // a name the resolver reported undefined stays so
    const diags = r.doc.diagnostics.sliced();
    for (diags.code, diags.node) |code, n| if (code == .undefined_name and t.token(n) != null) {
        self.meant[t.token(n).?] = undefined_name;
    };
    var unmet: DynBuf(u32) = .init(self.a, 16);
    for (self.leaf, 0..) |n, tok| if (n != none and t.kind(n) == .identifier and self.meant[tok] == none) {
        const name = r.name_pool.get(r.name_pool.name_of(n));
        const p = self.parent[n];
        const member = p != none and t.kind(p) == .member and t.arg(p, 1) == n;
        const by_parent = member or p != none and t.kind(p) == .partial__fun_call_assigned_param and t.arg(p, 0) == n;
        if (if (member) self.base(r, t.arg(p, 0)) else null) |in| {
            self.meant[tok] = self.within(in, name);
            if (self.meant[tok] == none and positional(name)) self.meant[tok] = self.spanning(in);
        }
        if (self.meant[tok] == none) self.meant[tok] = if (by_parent) self.unique(name) else self.scoped(n, name);
        if (self.meant[tok] == none and name[0] == '$') self.meant[tok] = self.intrinsic(name, spans[tok]);
        if (self.meant[tok] != none or by_parent) continue;
        var same: DynBuf(u32) = .init(self.a, 4);
        for (unmet.sliced()) |u| if (r.name_pool.name_of(self.leaf[u]) == r.name_pool.name_of(n)) same.push(u);
        const i = self.nearest(n, same.sliced()) orelse {
            unmet.push(@intCast(tok));
            continue;
        };
        const u = same.sliced()[i];
        if (self.meant[u] == none) self.declare(u, name, "", .variable, false, false, null, spans[u]);
        self.meant[tok] = self.meant[u];
    };
    for (self.meant, spans) |m, s| if (m != none and m != undefined_name) {
        const at = self.range(s[0], s[1]);
        self.links.push(.{ at.start.line, at.start.character, at.end.character, m });
    };
}

// the parent and first token of every node below `n`
fn descend(self: *Analysis, t: *ParseTree, n: u32) void {
    if (t.token(n)) |tk| {
        self.first[n] = tk;
        self.leaf[tk] = n;
    }
    for (t.children(n)) |c| if (c != 0) {
        self.parent[c] = n;
        self.descend(t, c);
        self.first[n] = @min(self.first[n], self.first[c]);
    };
}

fn alloc(self: *Analysis, len: usize) []u32 {
    const x = self.a.alloc(u32, len) catch @panic("OOM");
    @memset(x, none);
    return x;
}

fn declare(self: *Analysis, tok: u32, name: []const u8, detail: []const u8, c: Type, outlined: bool, global: bool, extent: ?Lexer.TextSpan, at: Lexer.TextSpan) void {
    self.meant[tok] = @intCast(self.decls.sliced().len);
    self.sites.push(.{ .tok = tok, .global = global });
    const e = extent orelse at;
    // outside the outline a declaration has no kind
    self.decls.push(.{ .name = name, .detail = detail, .kind = if (outlined) symbol(c) else 0, .range = self.range(@min(e[0], at[0]), @max(e[1], at[1])), .selectionRange = self.range(at[0], at[1]) });
}

// the declaration made by `n` or by a node enclosing it
fn enclosing(self: *Analysis, n: u32) u32 {
    var a = n;
    while (a != none and self.declared[a] == none) a = self.parent[a];
    return if (a == none) none else self.declared[a];
}

// a positional name: `$0`, `$1`
fn positional(name: []const u8) bool {
    return name.len > 1 and name[0] == '$' and std.ascii.isDigit(name[1]);
}

// a builtin (`$len`) is declared nowhere, its uses share one declaration
fn intrinsic(self: *Analysis, name: []const u8, use: Lexer.TextSpan) u32 {
    for (self.decls.sliced(), 0..) |x, i| if (x.selectionRange == null and std.mem.eql(u8, x.name, name)) return @intCast(i);
    self.sites.push(.{ .tok = none, .global = false });
    self.decls.push(.{ .name = name, .detail = "builtin", .kind = 0, .range = self.range(use[0], use[1]), .selectionRange = null });
    return @intCast(self.decls.sliced().len - 1);
}

// the token of the name a node mentions: `x` or the `x` of `p.x`
fn name_token(r: *Resolver, n: u32) ?u32 {
    const id = switch (r.tree.kind(n)) {
        .identifier => n,
        .member => r.tree.arg(n, 1),
        else => return null,
    };
    return if (r.tree.kind(id) == .identifier) r.tree.arg(id, 0) else null;
}

// the token of the first identifier called `name` in the subtree of `n`
fn named(r: *Resolver, n: u32, name: anytype) ?u32 {
    const s = r.tree.subtree(n);
    for (s[0]..s[1]) |i| if (r.tree.kind(@intCast(i)) == .identifier and r.name_pool.name_of(@intCast(i)) == name) return r.tree.arg(@intCast(i), 0);
    return null;
}

// the first declaration called `name` within `in`, but not the one spanning `in`
fn within(self: *Analysis, in: Range, name: []const u8) u32 {
    for (self.decls.sliced(), 0..) |x, i| if (x.selectionRange) |at| if (std.mem.eql(u8, x.name, name) and !std.meta.eql(x.range, in) and !before(at.start, in.start) and !before(in.end, at.end)) return @intCast(i);
    return none;
}

// the declaration spanning `in`
fn spanning(self: *Analysis, in: Range) u32 {
    for (self.decls.sliced(), 0..) |x, i| if (std.meta.eql(x.range, in)) return @intCast(i);
    return none;
}

// within `f` or within another overload of it (`mixed(1, b = 2)`)
fn overloaded(self: *Analysis, f: u32, name: []const u8) u32 {
    const decls = self.decls.sliced();
    var w = self.within(decls[f].range, name);
    for (decls) |x| if (w == none and x.selectionRange != null and std.mem.eql(u8, x.name, decls[f].name)) {
        w = self.within(x.range, name);
    };
    return w;
}

// the only member, field, case or function called `name`
fn unique(self: *Analysis, name: []const u8) u32 {
    var found: u32 = none;
    for (self.decls.sliced(), 0..) |x, i| if ((x.kind == symbol(.method) or x.kind == symbol(.property) or x.kind == symbol(.function) or x.kind == symbol(.enumMember)) and std.mem.eql(u8, x.name, name)) {
        if (found != none) return none;
        found = @intCast(i);
    };
    return found;
}

// the nearest declaration of `name` before `n` within a node enclosing `n`, else a global one
fn scoped(self: *Analysis, n: u32, name: []const u8) u32 {
    var candidates: DynBuf(u32) = .init(self.a, 8);
    var at: DynBuf(u32) = .init(self.a, 8);
    for (self.decls.sliced(), self.sites.sliced(), 0..) |x, s, i| if (x.selectionRange != null and std.mem.eql(u8, x.name, name)) {
        candidates.push(@intCast(i));
        at.push(s.tok);
    };
    if (self.nearest(n, at.sliced())) |i| return candidates.sliced()[i];
    for (candidates.sliced()) |c| if (self.sites.sliced()[c].global) return c;
    return none;
}

// of the tokens `at`, the nearest one before `n` within a node enclosing `n`
fn nearest(self: *Analysis, n: u32, at: []const u32) ?usize {
    var a = self.parent[n];
    while (a != none) : (a = self.parent[a]) {
        var best: ?usize = null;
        for (at, 0..) |tk, i| if (tk >= self.first[a] and tk < self.first[n] and (best == null or tk > at[best.?])) {
            best = i;
        };
        if (best != null) return best;
    }
    return null;
}

// where the type of `n` is declared, a type stands for itself
fn base(self: *Analysis, r: *Resolver, n: u32) ?Range {
    const d = r.node_decl[n];
    // a static value can be a type (`Q = Opt(u8)`)
    for ([_]@TypeOf(r.node_type[0]){ if (d == .none) .none else r.decl_pool.get_value(d), if (is_type(r, n)) r.node_value[n] else .none, r.node_type[n] }) |ty| {
        if (self.owner(r, ty)) |in| return in;
    }
    // a value made by a call is made within what it calls (`Q = Opt(wide)` evaluated only by the interpreter)
    if (d != .none) for (r.tree.children(r.decl_pool.get_node(d))) |c| if (c != 0 and r.tree.kind(c) == .fun_call) {
        const x = name_token(r, r.tree.arg(c, 0)) orelse continue;
        if (self.meant[x] != none) return self.decls.sliced()[self.meant[x]].range;
    };
    return null;
}

// where a type is declared, an anonymous one too (`ret ++(Some(t), None)`), a case lies within its variant
fn owner(self: *Analysis, r: *Resolver, ty: anytype) ?Range {
    if (ty == .none) return null;
    const d = switch (r.static_pool.get(ty)) {
        .ptr_type => |p| return self.owner(r, p.child),
        .custom_type => |c| c.decl,
        .variant_type => |v| v.decl,
        .variant_case_type => |c| {
            const c_at = self.within(self.owner(r, c.variant) orelse return null, r.name_pool.get(c.name));
            return if (c_at == none) null else self.decls.sliced()[c_at].range;
        },
        else => return null,
    };
    if (d == .none) return null;
    const o = r.generics.template_of.get(d) orelse d;
    if (self.def[@intFromEnum(o)] != none) return self.decls.sliced()[self.meant[self.def[@intFromEnum(o)]]].range;
    const e = r.tree.extent(r.decl_pool.get_node(o)) orelse return null;
    return self.range(e[0], e[1]);
}

// the type of a parameter, as written before its name (`&u8 fmt`) when the resolver did not evaluate it
fn written(self: *Analysis, r: *Resolver, lexer: *Lexer, ty: u32, name: u32) []const u8 {
    if (r.node_value[ty] != .none) return self.type_text(r, r.node_value[ty]);
    const toks = lexer.tokens.sliced();
    var i = name;
    var depth: u32 = 0;
    while (i > 0) : (i -= 1) switch (toks.tk[i - 1]) {
        .@"pct_)", .@"pct_]" => depth += 1,
        .@"pct_(", .@"pct_[" => if (depth == 0) break else {
            depth -= 1;
        },
        .@"pct_," => if (depth == 0) break,
        else => {},
    };
    return if (i == name) "" else self.src[toks.span[i][0]..toks.span[name - 1][1]];
}

fn type_text(self: *Analysis, r: *Resolver, ty: anytype) []const u8 {
    var w: std.Io.Writer.Allocating = .init(self.a);
    if (ty != .none and ty != .poison_type) r.static_pool.format(&r.name_pool, &r.abstract_pool, ty, &w.writer) catch @panic("OOM");
    return w.written();
}

// the declarations with a kind, each holding the ones within it
fn outline(self: *Analysis) []const Outline {
    const decls = self.decls.sliced();
    var list: DynBuf(u32) = .init(self.a, 64);
    for (decls, 0..) |s, i| if (s.kind != 0) list.push(@intCast(i));
    std.mem.sort(u32, list.sliced(), decls, struct {
        fn first(ds: []const Symbol, x: u32, y: u32) bool {
            const p, const q = .{ ds[x].range, ds[y].range };
            return before(p.start, q.start) or std.meta.eql(p.start, q.start) and before(q.end, p.end);
        }
    }.first);
    var i: usize = 0;
    return self.nest(list.sliced(), &i, null);
}

fn nest(self: *Analysis, list: []const u32, i: *usize, end: ?Position) []const Outline {
    var out: DynBuf(Outline) = .init(self.a, 8);
    while (i.* < list.len and (end == null or !before(end.?, self.decls.sliced()[list[i.*]].range.end))) {
        const d = list[i.*];
        i.* += 1;
        out.push(.{ .decl = d, .children = self.nest(list, i, self.decls.sliced()[d].range.end) });
    }
    return out.sliced();
}

pub fn before(x: Position, y: Position) bool {
    return x.line < y.line or x.line == y.line and x.character < y.character;
}

// lsp numbers the kinds of symbols
fn symbol(c: Type) u8 {
    return switch (c) {
        .method => 6,
        .property => 8,
        .@"enum" => 10,
        .interface => 11,
        .function => 12,
        .enumMember => 22,
        .@"struct" => 23,
        .type => 26,
        else => 13,
    };
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

fn range(self: *Analysis, lo: u32, hi: u32) Range {
    return .{ .start = self.pos(lo), .end = self.pos(hi) };
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

test "tokens and diagnostics" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const src = try arena.allocator().dupe(u8, "fun f = (i32 x) -> i32: ret x; # é\n$main = () { s = \"𝄞\"; f(1, 2); }\n");
    const r = analyze(arena.allocator(), src);
    // line and column relative to the token before, length, type, modifiers
    const want = [_]struct { u32, u32, u32, Type, u32 }{
        .{ 0, 0, 3, .keyword, 0 },   .{ 0, 4, 1, .function, 0 }, .{ 0, 2, 1, .operator, 0 }, .{ 0, 3, 3, .type, 0 },
        .{ 0, 4, 1, .parameter, 1 }, .{ 0, 3, 2, .operator, 0 }, .{ 0, 3, 3, .type, 0 },     .{ 0, 5, 3, .keyword, 0 },
        .{ 0, 4, 1, .parameter, 1 }, .{ 0, 3, 3, .comment, 0 },  .{ 1, 0, 5, .function, 0 }, .{ 0, 6, 1, .operator, 0 },
        .{ 0, 7, 1, .variable, 1 },  .{ 0, 2, 1, .operator, 0 }, .{ 0, 2, 4, .string, 0 },   .{ 0, 6, 1, .function, 0 },
        .{ 0, 2, 1, .number, 0 },    .{ 0, 3, 1, .number, 0 },
    };
    try std.testing.expectEqual(want.len * 5, r.data.len);
    for (want, 0..) |w, i| try std.testing.expectEqualSlices(u32, &.{ w[0], w[1], w[2], @intFromEnum(w[3]), w[4] }, r.data[i * 5 ..][0..5]);
    try std.testing.expectEqual(1, r.diagnostics.len);
    try std.testing.expectEqualStrings("wrong_arity  arguments 2  parameters 1", r.diagnostics[0].message);
    try std.testing.expectEqual(Position{ .line = 1, .character = 23 }, r.diagnostics[0].range.start);
}

test "links and outline" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const src = try arena.allocator().dupe(u8,
        \\type Point = *(mut i32 x, i32 y);
        \\variant Shape = +(Circle(f32 r), Rect);
        \\fun f = (Point p) -> i32: ret p.x;
        \\$main = () { Point q = Point(x = 1, y = 2); s = Shape.Circle(r = 1.0); f(q); }
    );
    const r = analyze(arena.allocator(), src);
    try std.testing.expectEqual(0, r.diagnostics.len);
    // a name at line and character, the name it means, where that is declared
    const want = [_]struct { u32, u32, []const u8, u32, u32 }{
        .{ 0, 23, "x", 0, 23 }, .{ 2, 15, "p", 2, 15 }, .{ 2, 30, "p", 2, 15 },    .{ 2, 32, "x", 0, 23 },
        .{ 3, 29, "x", 0, 23 }, .{ 3, 36, "y", 0, 30 }, .{ 3, 48, "Shape", 1, 8 }, .{ 3, 54, "Circle", 1, 18 },
        .{ 3, 61, "r", 1, 29 }, .{ 3, 71, "f", 2, 4 },  .{ 3, 73, "q", 3, 19 },
    };
    for (want) |w| {
        const l = for (r.links) |l| {
            if (l[0] == w[0] and l[1] == w[1]) break l;
        } else return error.TestUnexpectedResult;
        const d = r.decls[l[3]];
        try std.testing.expectEqualStrings(w[2], d.name);
        try std.testing.expectEqual(Position{ .line = w[3], .character = w[4] }, d.selectionRange.?.start);
    }
    try std.testing.expectEqualStrings("i32", r.decls[r.links[1][3]].detail);
    // types hold their fields and cases, cases their payload
    const tree = struct {
        fn write(w: *std.Io.Writer, res: Result, o: []const Outline) !void {
            for (o) |x| {
                try w.print("{s}(", .{res.decls[x.decl].name});
                try write(w, res, x.children);
                try w.writeByte(')');
            }
        }
    };
    var buf: [64]u8 = undefined;
    var w: std.Io.Writer = .fixed(&buf);
    try tree.write(&w, r, r.outline);
    try std.testing.expectEqualStrings("Point(x()y())Shape(Circle(r())Rect())f()$main()", w.buffered());
}

test "names the resolver never met" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const src = try arena.allocator().dupe(u8,
        \\fun print = (&u8 fmt);
        \\type Pair = *(i32, i32);
        \\variant Res = +(Ok(u32), Err(u8 code));
        \\fun first = (Pair p) -> i32: ret p.$0;
        \\fun add = (i32, i32) -> i32: ret $0 + $1;
        \\fun mixed = (u32 a) -> u32: ret a;
        \\fun mixed = (u32 a, u32 b = 5) -> u32: ret a + b;
        \\stcfun code = (Res r) -> u32: ret match r { Res.Ok(v) => v, _ => 0 };
        \\$main = () { print("x"); u32 m = mixed(1, b = 2); u64 l = "ab".$len; }
    );
    const r = analyze(arena.allocator(), src);
    try std.testing.expectEqual(0, r.diagnostics.len);
    // a name at line and character, the name it means and where that is declared, a builtin nowhere
    const want = [_]struct { u32, u32, []const u8, ?Position }{
        .{ 0, 17, "fmt", .{ .line = 0, .character = 17 } }, // a signature without body
        .{ 3, 35, "Pair", .{ .line = 1, .character = 5 } }, // a positional field
        .{ 4, 33, "add", .{ .line = 4, .character = 4 } }, // a positional parameter
        .{ 7, 57, "v", .{ .line = 7, .character = 51 } }, // an arm never matched
        .{ 8, 42, "b", .{ .line = 6, .character = 24 } }, // in another overload
        .{ 8, 63, "$len", null },
    };
    for (want) |w| {
        const l = for (r.links) |l| {
            if (l[0] == w[0] and l[1] == w[1]) break l;
        } else return error.TestUnexpectedResult;
        const d = r.decls[l[3]];
        try std.testing.expectEqualStrings(w[2], d.name);
        try std.testing.expectEqual(w[3], if (d.selectionRange) |at| at.start else null);
    }
    try std.testing.expectEqualStrings("&u8", r.decls[r.links[1][3]].detail);
}

test "a name reported undefined stays unlinked" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const src = try arena.allocator().dupe(u8, "$main = () { { i32 inner = 1; } i32 b = inner; }");
    const r = analyze(arena.allocator(), src);
    try std.testing.expectEqualStrings("undefined_name  name `inner`", r.diagnostics[0].message);
    for (r.links) |l| try std.testing.expect(l[1] != 40);
}
