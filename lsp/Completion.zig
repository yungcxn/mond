const std = @import("std");
const mond = @import("mond");
const Analysis = @import("Analysis.zig");
const Node = mond.ParseTree.Node;
const Macros = mond.Resolver.Macros;

// completion: what the editor offers at the cursor, the api of trees. after `x.` the views of a tree and the children
// of its kind, after `xs.` the length of a list of trees, after `ast.` the kinds, the builtins after `$`. it goes by the
// text before the cursor and the types of the names the last analysis that knew them found, the text being typed
// rarely parses

pub const Item = struct {
    label: []const u8,
    kind: u8,
    detail: []const u8,
    documentation: []const u8,
    textEdit: struct { range: Analysis.Range, newText: []const u8 },
};

// lsp numbers the kinds of completions
const Class = enum(u8) { function = 3, field = 5, property = 10, enum_member = 20 };

// what is offered: its text, its type and what it is
pub const Entry = struct { label: []const u8, ty: []const u8, doc: []const u8 = "", class: Class };

const views = blk: {
    var t: [Macros.views.len]Entry = undefined;
    for (Macros.views, &t) |v, *e| e.* = .{ .label = "$" ++ @tagName(v.name), .ty = switch (v.gives) {
        .tree => "ast",
        .list => "[]ast",
        .text => "[]u8",
        .flag => "bool",
    }, .doc = v.doc, .class = .property };
    break :blk t;
};

const len: Entry = .{ .label = "$len", .ty = "u64", .doc = "its length", .class = .property };

const builtins = [_]Entry{
    .{ .label = "$fresh", .ty = "([]u8 name) -> ast.Identifier", .doc = "a name like no other", .class = .function },
    .{ .label = "$error", .ty = "(ast at, []u8 message)", .doc = "ends the expansion with an error at the tree", .class = .function },
};

const file: Entry = .{ .label = "$file", .ty = "*ast", .doc = "the program: `refl $file` reads and writes its declarations", .class = .property };

// `ast.Kind` with the children it is made of
const kinds = blk: {
    @setEvalBranchQuota(100_000);
    var t: [Node.case_names.len]Entry = undefined;
    for (&t, Node.case_names, Node.nk_field_names[0..t.len], Node.nk_childc[0..t.len]) |*e, name, f, c| e.* = .{ .label = name, .ty = switch (c) {
        .none => "()",
        .data => "([]u8 text)",
        .one => "(" ++ f[0] ++ ")",
        .two => "(" ++ f[0] ++ ", " ++ f[1] ++ ")",
        .many => "(..)",
    }, .class = .enum_member };
    break :blk t;
};

// a view of trees or `$file`: code, not a value of the program
pub fn of_trees(name: []const u8) bool {
    for (views ++ [_]Entry{file}) |e| if (std.mem.eql(u8, e.label, name)) return true;
    return false;
}

// a view or builtin by its name, for hovers
pub fn described(name: []const u8) ?Entry {
    for (views ++ builtins ++ [_]Entry{ len, file }) |e| if (std.mem.eql(u8, e.label, name)) return e;
    return null;
}

// what a chain of members makes: a tree (of a kind when known), a list of trees or nothing to complete
const Shape = struct { of: enum { none, tree, list, kinds } = .none, kind: ?Node.Kind = null };

pub fn offer(a: std.mem.Allocator, src: []const u8, p: Analysis.Position, names: []const Analysis.Symbol) ![]const Item {
    const cur = offset(src, p);
    var start = cur;
    while (start > 0 and word(src[start - 1])) start -= 1;
    const typed = src[start..cur];
    // the word being typed is replaced
    const range: Analysis.Range = .{ .start = .{ .line = p.line, .character = p.character - utf16(typed) }, .end = p };
    var out: std.ArrayList(Item) = .empty;
    if (start > 0 and src[start - 1] == '.') {
        const s = shape(src, start - 1, p, names);
        switch (s.of) {
            .none => {},
            .kinds => for (kinds) |e| try out.append(a, item(e, range)),
            .list => try out.append(a, item(len, range)),
            .tree => {
                for (views) |e| try out.append(a, item(e, range));
                const k = s.kind orelse return out.items;
                const c = Node.nk_childc[@intFromEnum(k)];
                for (Node.nk_field_names[@intFromEnum(k)][0..@as(usize, if (c == .one) 1 else if (c == .two) 2 else 0)]) |f| try out.append(a, item(.{ .label = f, .ty = "ast", .class = .field }, range));
            },
        }
    } else if (typed.len > 0 and typed[0] == '$') {
        for (builtins) |e| try out.append(a, item(e, range));
        if (std.mem.endsWith(u8, std.mem.trimEnd(u8, src[0..start], " "), "refl")) try out.append(a, item(file, range));
    }
    return out.items;
}

fn item(e: Entry, range: Analysis.Range) Item {
    return .{ .label = e.label, .kind = @intFromEnum(e.class), .detail = e.ty, .documentation = e.doc, .textEdit = .{ .range = range, .newText = e.label } };
}

// the chain before the `.` at `dot` from its root on: a name, `ast`, a call, `(refl f)`, then members and indexes
fn shape(src: []const u8, dot: usize, p: Analysis.Position, names: []const Analysis.Symbol) Shape {
    // its parts back to front: names, `[` for an index, `(` for a call
    var parts: [16][]const u8 = undefined;
    var n: usize = 0;
    var i = dot;
    const root = while (n < parts.len) {
        if (i > 0 and (src[i - 1] == ']' or src[i - 1] == ')')) {
            const open = opening(src, i - 1) orelse return .{};
            const group = open == 0 or !word(src[open - 1]);
            if (src[i - 1] == ')' and group) break src[open + 1 .. i - 1];
            parts[n] = src[open .. open + 1];
            n += 1;
            i = open;
            continue;
        }
        var s = i;
        while (s > 0 and word(src[s - 1])) s -= 1;
        if (s == i) return .{};
        if (s == 0 or src[s - 1] != '.') break src[s..i];
        parts[n] = src[s..i];
        n += 1;
        i = s - 1;
    } else return .{};
    std.mem.reverse([]const u8, parts[0..n]);
    var steps = parts[0..n];
    var at: Shape = if (std.mem.eql(u8, root, "ast")) blk: {
        if (steps.len == 0) break :blk .{ .of = .kinds };
        // `ast.Kind(..)` makes a tree of that kind
        if (steps.len < 2 or steps[1][0] != '(') return .{};
        const k = Node.named.get(steps[0]) orelse return .{};
        steps = steps[2..];
        break :blk .{ .of = .tree, .kind = k };
    } else if (std.mem.eql(u8, root, "$fresh")) blk: {
        if (steps.len == 0 or steps[0][0] != '(') return .{};
        steps = steps[1..];
        break :blk .{ .of = .tree, .kind = .identifier };
    } else if (std.mem.startsWith(u8, root, "refl") or std.mem.startsWith(u8, root, "quote") or std.mem.startsWith(u8, root, "include"))
        .{ .of = .tree }
    else
        parse(type_of(src, root, p, names));
    for (steps) |step| at = after(at, step);
    return at;
}

// what a member (`$params`, `lhs`), an index or a call of `at` makes
fn after(at: Shape, step: []const u8) Shape {
    switch (at.of) {
        .list => return if (step[0] == '[') .{ .of = .tree, .kind = at.kind } else .{},
        .tree => {
            if (step[0] == '[' or step[0] == '(') return .{};
            // a child by its field name
            if (step[0] != '$') return .{ .of = .tree };
            for (Macros.views) |v| if (std.mem.eql(u8, step[1..], @tagName(v.name))) return switch (v.gives) {
                .tree => .{ .of = .tree },
                .list => .{ .of = .list },
                .text, .flag => .{},
            };
            return .{};
        },
        else => return .{},
    }
}

// the type of a tree or list of trees as the analysis wrote it (`*ast(fun)`, `[]ast.Identifier`) or as it is written (`mut ast`)
fn parse(written: []const u8) Shape {
    var t = std.mem.trim(u8, written, " ");
    for ([_][]const u8{ "pub ", "mut ", "stc " }) |m| if (std.mem.startsWith(u8, t, m)) {
        t = std.mem.trimStart(u8, t[m.len..], " ");
    };
    if (t.len > 0 and (t[0] == '*' or t[0] == '&')) t = t[1..];
    var list = false;
    if (t.len > 0 and t[0] == '[') {
        list = true;
        t = t[(std.mem.indexOfScalar(u8, t, ']') orelse return .{}) + 1 ..];
        if (t.len > 0 and (t[0] == '*' or t[0] == '&')) t = t[1..];
    }
    if (!std.mem.startsWith(u8, t, "ast") or t.len > 3 and t[3] != '.' and t[3] != '(' and t[3] != ' ') return .{};
    var kind: ?Node.Kind = null;
    if (t.len > 3 and t[3] == '.') {
        var e: usize = 4;
        while (e < t.len and word(t[e])) e += 1;
        kind = Node.named.get(t[4..e]) orelse return .{};
    }
    return .{ .of = if (list) .list else .tree, .kind = kind };
}

// the type of the nearest declaration of `name` before the cursor, a name the resolver never typed by what is written before it
fn type_of(src: []const u8, name: []const u8, p: Analysis.Position, names: []const Analysis.Symbol) []const u8 {
    var best: ?Analysis.Symbol = null;
    for (names) |d| if (d.selectionRange) |sel| if (std.mem.eql(u8, d.name, name) and !Analysis.before(p, sel.start)) {
        if (best == null or Analysis.before(best.?.selectionRange.?.start, sel.start)) best = d;
    };
    const d = best orelse return "";
    if (d.detail.len > 0) return d.detail;
    const at = @min(offset(src, d.selectionRange.?.start), src.len);
    var s = at;
    while (s > 0 and std.mem.indexOfScalar(u8, "\n;{(,:", src[s - 1]) == null) s -= 1;
    return src[s..at];
}

// the `(` or `[` opening the bracket at `close`
fn opening(src: []const u8, close: usize) ?usize {
    var depth: usize = 0;
    var i = close + 1;
    while (i > 0) {
        i -= 1;
        switch (src[i]) {
            ')', ']' => depth += 1,
            '(', '[' => {
                depth -= 1;
                if (depth == 0) return i;
            },
            '\n', ';', '{', '}' => return null,
            else => {},
        }
    }
    return null;
}

fn word(c: u8) bool {
    return std.ascii.isAlphanumeric(c) or c == '_' or c == '$';
}

// the byte at a position, lsp counts columns in utf-16 code units
fn offset(src: []const u8, p: Analysis.Position) usize {
    var i: usize = 0;
    for (0..p.line) |_| i = (std.mem.indexOfScalarPos(u8, src, i, '\n') orelse return src.len) + 1;
    var units: u32 = 0;
    while (i < src.len and src[i] != '\n' and units < p.character) : (i += 1) units += utf16(src[i .. i + 1]);
    while (i < src.len and src[i] >= 0x80 and src[i] <= 0xbf) i += 1;
    return i;
}

fn utf16(s: []const u8) u32 {
    var n: u32 = 0;
    for (s) |c| n += switch (c) {
        0x80...0xbf => 0,
        0xf0...0xff => 2,
        else => 1,
    };
    return n;
}

fn labels(a: std.mem.Allocator, src: []const u8, line: u32, character: u32) ![]const u8 {
    const r = Analysis.analyze(a, try a.dupe(u8, src));
    // the analysis of a text that does not parse knows no names, the server keeps the last one that did
    var cut = try a.dupe(u8, src);
    const at = offset(src, .{ .line = line, .character = character });
    @memset(cut[at..], ' ');
    var out: std.ArrayList(u8) = .empty;
    for (try offer(a, cut, .{ .line = line, .character = character }, r.decls)) |x| try out.print(a, "{s} ", .{x.label});
    return out.items;
}

test "the api of trees by the type of what is before the dot" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const src =
        \\stcfun f = (*ast(fun) g, ast.BinaryAdd e, []ast xs) -> u64 {
        \\    mut ast out = g.$body;
        \\    ret out.$src.$len + g.$params[0].$name.$src.$len + e.lhs.$src.$len + xs.$len + (refl f).$params.$len + ast.Identifier("x").$src.$len;
        \\}
        \\$main = () {}
    ;
    const all = "$src $children $name $type $value $params $ret $body $fields $cases $methods $implof $default $where $mut $decls ";
    // a local only written, a parameter, an element of a list view, a view, a child, a group, a made node
    for ([_]u32{ 12, 26, 37, 43, 61, 92, 127 }) |at| try std.testing.expectEqualStrings(all, try labels(a, src, 2, at));
    // a tree of a kind has its children, a list its length, text nothing
    try std.testing.expectEqualStrings(all ++ "lhs rhs ", try labels(a, src, 2, 57));
    try std.testing.expectEqualStrings("$len ", try labels(a, src, 2, 76));
    try std.testing.expectEqualStrings("$len ", try labels(a, src, 2, 100));
    try std.testing.expectEqualStrings("", try labels(a, src, 2, 48));
}

test "the kinds after `ast.`, the builtins after `$`" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const src = "stc ast x = ast.BinaryAdd(quote: 1, quote: 2);\nstc ast y = $fresh(\"t\");\nstc ast z = refl $file;\n";
    const r = Analysis.analyze(a, try a.dupe(u8, src));
    const k = try offer(a, src, .{ .line = 0, .character = 16 }, r.decls);
    try std.testing.expectEqual(Node.case_names.len, k.len);
    for (k) |x| if (std.mem.eql(u8, x.label, "BinaryAdd")) try std.testing.expectEqualStrings("(lhs, rhs)", x.detail);
    try std.testing.expectEqualStrings("$fresh $error ", try labels(a, src, 1, 14));
    try std.testing.expectEqualStrings("$fresh $error $file ", try labels(a, src, 2, 18));
    // the word typed is replaced, its `$` too
    const f = try offer(a, src, .{ .line = 2, .character = 18 }, r.decls);
    try std.testing.expectEqual(@as(u32, 17), f[0].textEdit.range.start.character);
    try std.testing.expectEqualStrings("a name like no other", described("$fresh").?.doc);
}
