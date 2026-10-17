const std = @import("std");
const mond = @import("mond");
const Analysis = @import("Analysis.zig");
const positions = @import("positions.zig");
const highlighting = @import("highlighting.zig");
const Node = mond.ParseTree.Node;
const Macros = mond.Resolver.Macros;
const NamePool = mond.NamePool;
const Kind = mond.Lexer.Token.Kind;
const lookahead = mond.Parser.lookahead;

// completion of the api of trees: views, children, the kinds after `ast.`, builtins
// it goes by the text before the cursor and the last names known, typed text rarely parses

pub const Item = struct {
    label: []const u8,
    kind: u8,
    detail: []const u8,
    documentation: []const u8,
    textEdit: struct { range: Analysis.Range, newText: []const u8 },
};

// lsp numbers the kinds of completions
const Class = enum(u8) { function = 3, field = 5, property = 10, enum_member = 20 };

// where a name is offered: while typing a name starting with `__`, after the `.` of a tree
const Offered = enum { compiler, tree };

// what is offered: its text, its type and what it is
pub const Entry = struct {
    label: []const u8,
    ty: []const u8,
    doc: []const u8 = "",
    class: Class,
    offered: Offered = .compiler,
};

const view_entries = blk: {
    var entries: [Macros.views.len]Entry = undefined;
    for (Macros.views, &entries) |view, *entry| {
        const view_type = switch (view.gives) {
            .tree => "ast",
            .list => "[]ast",
            .text => "[]u8",
            .flag => "bool",
        };
        entry.* = .{
            .label = NamePool.predefined_text(view.name),
            .ty = view_type,
            .doc = view.doc,
            .class = .property,
            .offered = .tree,
        };
    }
    break :blk entries;
};

// what the editor shows of a name the compiler predefines, one it adds compiles only once described
fn entry_of(comptime name: NamePool.Index) ?Entry {
    const label = NamePool.predefined_text(name);
    return switch (name) {
        .os => .{
            .label = label,
            .ty = "[]u8",
            .doc = "the system the program is built for: \"macos\", \"linux\"",
            .class = .property,
        },
        .arch => .{
            .label = label,
            .ty = "[]u8",
            .doc = "the machine the program is built for: \"aarch64\", \"x86_64\"",
            .class = .property,
        },
        .empty, .underscore, .it, .self, .init, .deinit, .main, .has_next, .next, .len => null,
        .fresh, .crash, .@"asm", .syscall, .wall => null,
        .none, _ => null,
        inline else => for (view_entries) |entry| {
            if (std.mem.eql(u8, entry.label, label)) break entry;
        } else @compileError("describe the predefined name " ++ label),
    };
}

// the described names in the order the compiler predefines them
const predefined_entries = blk: {
    var described_entries: []const Entry = &.{};
    for (@typeInfo(NamePool.Index).@"enum".fields) |field| {
        const entry = entry_of(@field(NamePool.Index, field.name)) orelse continue;
        described_entries = described_entries ++ .{entry};
    }
    break :blk described_entries;
};

// `ast.Kind` with the children it is made of
const kind_entries = blk: {
    @setEvalBranchQuota(100_000);
    var entries: [Node.case_names.len]Entry = undefined;
    for (
        &entries,
        Node.case_names,
        Node.nk_field_names[0..entries.len],
        Node.nk_childc[0..entries.len],
    ) |*entry, name, field_names, child_count| {
        const children = switch (child_count) {
            .none => "()",
            .data => "([]u8 text)",
            .one => "(" ++ field_names[0] ++ ")",
            .two => "(" ++ field_names[0] ++ ", " ++ field_names[1] ++ ")",
            .many => "(..)",
        };
        entry.* = .{ .label = name, .ty = children, .class = .enum_member };
    }
    break :blk entries;
};

// a view or builtin by its name, for hovers
pub fn described(name: []const u8) ?Entry {
    for (predefined_entries) |entry| {
        if (std.mem.eql(u8, entry.label, name)) return entry;
    }
    return null;
}

// what a chain of members makes: a tree (of a kind when known), a list of trees or nothing to offer
const Shape = struct {
    holds: enum { none, tree, list, kinds } = .none,
    kind: ?Node.Kind = null,
};

pub fn offer(
    allocator: std.mem.Allocator,
    source: []const u8,
    cursor: Analysis.Position,
    names: []const Analysis.Symbol,
) ![]const Item {
    const cursor_offset = byte_offset(source, cursor);
    var word_start = cursor_offset;
    while (word_start > 0 and is_word_byte(source[word_start - 1])) word_start -= 1;
    const typed = source[word_start..cursor_offset];
    // the word being typed is replaced
    const typed_start: Analysis.Position = .{
        .line = cursor.line,
        .character = cursor.character - positions.utf16_length(typed),
    };
    const replaced: Analysis.Range = .{ .start = typed_start, .end = cursor };

    var items: std.ArrayList(Item) = .empty;
    if (word_start > 0 and source[word_start - 1] == '.') {
        const shape = shape_before_dot(source, word_start - 1, cursor, names);
        switch (shape.holds) {
            .none, .list => {},
            .kinds => for (kind_entries) |entry| {
                try items.append(allocator, item_of(entry, replaced));
            },
            .tree => {
                for (view_entries) |entry| try items.append(allocator, item_of(entry, replaced));
                const kind = shape.kind orelse return items.items;
                const field_names = Node.nk_field_names[@intFromEnum(kind)];
                const named_children: usize = switch (Node.nk_childc[@intFromEnum(kind)]) {
                    .one => 1,
                    .two => 2,
                    .none, .data, .many => 0,
                };
                for (field_names[0..named_children]) |field_name| {
                    const child: Entry = .{ .label = field_name, .ty = "ast", .class = .field };
                    try items.append(allocator, item_of(child, replaced));
                }
            },
        }
        return items.items;
    }

    if (std.mem.startsWith(u8, typed, "__")) {
        for (predefined_entries) |entry| {
            if (entry.offered == .compiler) try items.append(allocator, item_of(entry, replaced));
        }
    }
    return items.items;
}

fn item_of(entry: Entry, replaced: Analysis.Range) Item {
    return .{
        .label = entry.label,
        .kind = @intFromEnum(entry.class),
        .detail = entry.ty,
        .documentation = entry.doc,
        .textEdit = .{ .range = replaced, .newText = entry.label },
    };
}

// the chain before the `.` at `dot`: a root (a name, `ast`, a call, `(refl f)`) then its steps
fn shape_before_dot(
    source: []const u8,
    dot: usize,
    cursor: Analysis.Position,
    names: []const Analysis.Symbol,
) Shape {
    // its parts back to front: names, `[` for an index, `(` for a call
    var parts: [16][]const u8 = undefined;
    var part_count: usize = 0;
    var end = dot;
    const root = while (part_count < parts.len) {
        if (end > 0 and (source[end - 1] == ']' or source[end - 1] == ')')) {
            // the bracket opening `end - 1`, each closer must meet its own kind of opener
            const open = blk: {
                var expected: [64]u8 = undefined;
                var depth: usize = 0;
                var i = end;
                while (i > 0) {
                    i -= 1;
                    switch (source[i]) {
                        ')', ']' => {
                            if (depth == expected.len) return .{};
                            expected[depth] = if (source[i] == ')') '(' else '[';
                            depth += 1;
                        },
                        '(', '[' => {
                            if (depth == 0 or expected[depth - 1] != source[i]) return .{};
                            depth -= 1;
                            if (depth == 0) break :blk i;
                        },
                        '\n', ';', '{', '}' => return .{},
                        else => {},
                    }
                }
                return .{};
            };
            const is_group = open == 0 or !is_word_byte(source[open - 1]);
            if (source[end - 1] == ')' and is_group) break source[open + 1 .. end - 1];
            parts[part_count] = source[open .. open + 1];
            part_count += 1;
            end = open;
            continue;
        }

        var start = end;
        while (start > 0 and is_word_byte(source[start - 1])) start -= 1;
        if (start == end) return .{};
        if (start == 0 or source[start - 1] != '.') break source[start..end];
        parts[part_count] = source[start..end];
        part_count += 1;
        end = start - 1;
    } else return .{};

    std.mem.reverse([]const u8, parts[0..part_count]);
    var steps = parts[0..part_count];
    var shape = shape_of_root(source, root, &steps, cursor, names) orelse return .{};
    for (steps) |step| shape = shape_after_step(shape, step);
    return shape;
}

// the shape `root` makes, the steps it takes itself are dropped from `steps`
fn shape_of_root(
    source: []const u8,
    root: []const u8,
    steps: *[][]const u8,
    cursor: Analysis.Position,
    names: []const Analysis.Symbol,
) ?Shape {
    var keyword_end: usize = 0;
    while (keyword_end < root.len and is_word_byte(root[keyword_end])) keyword_end += 1;
    const keyword = Kind.kw_from_str(root[0..keyword_end]);
    if (keyword == .kw_ast and keyword_end == root.len) {
        if (steps.len == 0) return .{ .holds = .kinds };
        // `ast.Kind(..)` makes a tree of that kind
        if (steps.len < 2 or steps.*[1][0] != '(') return null;
        const kind = Node.named.get(steps.*[0]) orelse return null;
        steps.* = steps.*[2..];
        return .{ .holds = .tree, .kind = kind };
    }

    // a builtin's call makes what its type says it returns
    if (described(root)) |entry| {
        const arrow = std.mem.indexOf(u8, entry.ty, "-> ") orelse return null;
        if (steps.len == 0 or steps.*[0][0] != '(') return null;
        steps.* = steps.*[1..];
        return shape_of_type(entry.ty[arrow + "-> ".len ..]);
    }

    // `quote: ..`, `(refl f)`, `include ".."`: macro syntax makes a tree
    if (keyword) |kind| if (lookahead.macro_syntax[@intFromEnum(kind)]) return .{ .holds = .tree };

    // the type of the nearest `root` before the cursor, of an untyped one what is written before it
    const written = blk: {
        var best: ?Analysis.Symbol = null;
        for (names) |declaration| {
            const name_range = declaration.selectionRange orelse continue;
            if (!std.mem.eql(u8, declaration.name, root)) continue;
            if (Analysis.before(cursor, name_range.start)) continue;
            if (best) |nearer| {
                if (!Analysis.before(nearer.selectionRange.?.start, name_range.start)) continue;
            }
            best = declaration;
        }

        const declaration = best orelse break :blk "";
        if (declaration.detail.len > 0) break :blk declaration.detail;
        const name_start =
            @min(byte_offset(source, declaration.selectionRange.?.start), source.len);
        var start = name_start;
        while (start > 0 and std.mem.indexOfScalar(u8, "\n;{(,:", source[start - 1]) == null) {
            start -= 1;
        }
        break :blk source[start..name_start];
    };
    return shape_of_type(written);
}

// a type as the analysis wrote it (`*ast(fun)`, `[]ast.Identifier`) or as written (`mut ast`)
fn shape_of_type(written: []const u8) Shape {
    var text = std.mem.trim(u8, written, " ");
    // the modifiers before it: keywords that are no type
    while (std.mem.indexOfScalar(u8, text, ' ')) |space| {
        const modifier = Kind.kw_from_str(text[0..space]) orelse break;
        if (highlighting.class_of_token_kind[@intFromEnum(modifier)] != .keyword) break;
        text = std.mem.trimStart(u8, text[space..], " ");
    }
    if (text.len > 0 and (text[0] == '*' or text[0] == '&')) text = text[1..];

    var is_list = false;
    if (text.len > 0 and text[0] == '[') {
        is_list = true;
        const close = std.mem.indexOfScalar(u8, text, ']') orelse return .{};
        text = text[close + 1 ..];
        if (text.len > 0 and (text[0] == '*' or text[0] == '&')) text = text[1..];
    }

    if (!std.mem.startsWith(u8, text, "ast")) return .{};
    const ends_after_ast = text.len == 3 or text[3] == '.' or text[3] == '(' or text[3] == ' ';
    if (!ends_after_ast) return .{};

    var kind: ?Node.Kind = null;
    if (text.len > 3 and text[3] == '.') {
        var kind_end: usize = 4;
        while (kind_end < text.len and is_word_byte(text[kind_end])) kind_end += 1;
        kind = Node.named.get(text[4..kind_end]) orelse return .{};
    }
    return .{ .holds = if (is_list) .list else .tree, .kind = kind };
}

// what a member (`params`, `lhs`), an index or a call of `shape` makes
fn shape_after_step(shape: Shape, step: []const u8) Shape {
    switch (shape.holds) {
        .list => {
            if (step[0] == '[') return .{ .holds = .tree, .kind = shape.kind };
            return .{};
        },
        .tree => {
            if (step[0] == '[' or step[0] == '(') return .{};
            for (Macros.views) |view| {
                if (!std.mem.eql(u8, step, @tagName(view.name))) continue;
                return switch (view.gives) {
                    .tree => .{ .holds = .tree },
                    .list => .{ .holds = .list },
                    .text, .flag => .{},
                };
            }
            // a child by its field name
            return .{ .holds = .tree };
        },
        .none, .kinds => return .{},
    }
}

fn is_word_byte(byte: u8) bool {
    return std.ascii.isAlphanumeric(byte) or byte == '_' or byte == '$';
}

// the byte at a position, lsp counts columns in utf-16 code units
fn byte_offset(source: []const u8, position: Analysis.Position) usize {
    var offset: usize = 0;
    for (0..position.line) |_| {
        const line_end = std.mem.indexOfScalarPos(u8, source, offset, '\n');
        offset = (line_end orelse return source.len) + 1;
    }

    var units: u32 = 0;
    while (offset < source.len and source[offset] != '\n' and units < position.character) {
        units += positions.utf16_length(source[offset .. offset + 1]);
        offset += 1;
    }
    // a column within a character stands for the whole character
    while (offset < source.len and source[offset] >= 0x80 and source[offset] <= 0xbf) offset += 1;
    return offset;
}

fn offered_labels(
    allocator: std.mem.Allocator,
    source: []const u8,
    line: u32,
    character: u32,
) ![]const u8 {
    const result = Analysis.analyze(allocator, try allocator.dupe(u8, source));
    // the analysis of a text that does not parse knows no names, the server keeps the last that did
    var cut = try allocator.dupe(u8, source);
    const cursor: Analysis.Position = .{ .line = line, .character = character };
    @memset(cut[byte_offset(source, cursor)..], ' ');

    var labels: std.ArrayList(u8) = .empty;
    for (try offer(allocator, cut, cursor, result.decls)) |offered| {
        try labels.print(allocator, "{s} ", .{offered.label});
    }
    return labels.items;
}

test "the api of trees by the type of what is before the dot" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const source = "" ++
        "stcfun f = (*ast(fun) g, ast.BinaryAdd e, []ast xs) -> u64 {\n" ++
        "    mut ast out = g.body;\n" ++
        "    ret lenof out.src + lenof g.params[0].name.src + lenof e.lhs.src + lenof xs + " ++
        "lenof (refl f).params + lenof ast.Identifier(\"x\").src;\n" ++
        "}\n" ++
        "main = () {}";
    const all_views = "src children name type assigned params rettype body fields cases " ++
        "methods traits defval guard ismut decls ";
    // a written local, a parameter, a list view element, a view, a child, a group, a made node
    for ([_]u32{ 18, 32, 42, 47, 65, 97, 132 }) |character| {
        const labels = try offered_labels(allocator, source, 2, character);
        try std.testing.expectEqualStrings(all_views, labels);
    }
    // a tree of a kind has its children
    const with_children = all_views ++ "lhs rhs ";
    try std.testing.expectEqualStrings(with_children, try offered_labels(allocator, source, 2, 61));
}

test "the kinds after `ast.`, the compiler's names after `__`" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const source = "stc ast x = ast.BinaryAdd(quote: 1, quote: 2);\n" ++
        "stc u64 n = lenof __os;\n";
    const result = Analysis.analyze(allocator, try allocator.dupe(u8, source));
    const kinds = try offer(allocator, source, .{ .line = 0, .character = 16 }, result.decls);
    try std.testing.expectEqual(Node.case_names.len, kinds.len);
    for (kinds) |kind| {
        if (!std.mem.eql(u8, kind.label, "BinaryAdd")) continue;
        try std.testing.expectEqualStrings("(lhs, rhs)", kind.detail);
    }
    const compiler_names = try offered_labels(allocator, source, 1, 20);
    try std.testing.expectEqualStrings("__os __arch ", compiler_names);
    // the word typed is replaced, its `__` too
    const builtins = try offer(allocator, source, .{ .line = 1, .character = 20 }, result.decls);
    try std.testing.expectEqual(@as(u32, 18), builtins[0].textEdit.range.start.character);
    const os_doc = "the system the program is built for: \"macos\", \"linux\"";
    try std.testing.expectEqualStrings(os_doc, described("__os").?.doc);
}
