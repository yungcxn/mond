const std = @import("std");
const builtin = @import("builtin");
const mond = @import("mond");
const Lexer = mond.Lexer;
const Parser = mond.Parser;
const Resolver = mond.Resolver;
const Doctor = mond.Doctor;
const DynamicBuffer = mond.DynamicBuffer;
const dbg = mond.dbg;
const highlighting = @import("highlighting.zig");
const linking = @import("linking.zig");
const outline = @import("outline.zig");
const positions = @import("positions.zig");
const includers = @import("includers.zig");

// the worker: runs the compiler on one source as far as it gets and turns what it found into
// semantic tokens, diagnostics, the declarations every name means and an outline for the server

const Analysis = @This();

// the legend, tokens name their type and modifiers by index
pub const Type = enum(u8) {
    comment,
    keyword,
    operator,
    string,
    number,
    type,
    @"struct",
    @"enum",
    interface,
    enumMember,
    function,
    method,
    variable,
    parameter,
    property,
    macro,
    namespace,
};
pub const Modifier = enum(u5) { readonly, static };

pub const Position = struct { line: u32, character: u32 };
pub const Range = struct { start: Position, end: Position };

pub const Diagnostic = struct {
    range: Range,
    severity: u8,
    source: []const u8 = "mond",
    message: []const u8,
};

// a declaration named at `selectionRange` (a builtin nowhere), `children` come from its `Outline`
pub const Symbol = struct {
    name: []const u8,
    detail: []const u8,
    kind: u8,
    range: Range,
    selectionRange: ?Range,
    children: []const Symbol = &.{},
};

// a name: line, first and end character, the declaration in `decls` it means (or names)
pub const Link = [4]u32;

// the declarations in the outline, each holding the ones within it
pub const Outline = struct { decl: u32, children: []const Outline };

// the static value of a `stc` variable, shown at the end of its line as a `#=` check would read
pub const Hint = struct { position: Position, label: []const u8, paddingLeft: bool = true };

// a declaration of `decls` made in another file (an included one), where it is there
pub const Elsewhere = struct { decl: u32, uri: []const u8, range: Range };

// the code a splice of the document put in its place in a macro pass, `range` from its `<` to its
// `>`. one a splice made is at the splice it is in
pub const Expansion = struct { range: Range, pass: u32, code: []const u8 };

pub const Result = struct {
    data: []const u32 = &.{},
    diagnostics: []const Diagnostic = &.{},
    decls: []const Symbol = &.{},
    // sorted by position
    links: []const Link = &.{},
    outline: []const Outline = &.{},
    hints: []const Hint = &.{},
    elsewhere: []const Elsewhere = &.{},
    // by pass, then position
    expansions: []const Expansion = &.{},
    // the program as code before the first macro pass and after each one: the steps of its
    // expansion, empty when nothing expands
    passes: []const []const u8 = &.{},
};

pub const before = positions.before;

// no token or declaration, and a name the resolver reported undefined
pub const none = std.math.maxInt(u32);
pub const undefined_name = none - 1;

const DeclarationSite = struct { token: u32, global: bool, class: Type, modifiers: u32 };

const PastDeclaration = struct {
    name: []const u8,
    detail: []const u8,
    class: Type,
    modifiers: u32,
    extent: ?Lexer.TextSpan,
};

allocator: std.mem.Allocator,
source: []u8,
// where `include` reads: the document's file
io: ?std.Io = null,
path: []const u8 = "",
line_starts: DynamicBuffer(u32),
// the semantic tokens, five numbers each
token_data: DynamicBuffer(u32),
diagnostics: DynamicBuffer(Diagnostic),
declarations: DynamicBuffer(Symbol),
links: DynamicBuffer(Link),
hints: DynamicBuffer(Hint),
elsewhere: DynamicBuffer(Elsewhere),
expansions: DynamicBuffer(Expansion),
passes: DynamicBuffer([]const u8),
// per token: its declaration in `declarations`
token_meaning: []u32 = &.{},
// per declaration of the resolver: the token naming it
declaration_token: []u32 = &.{},
// per declaration in `declarations`: how its names are highlighted and found
declaration_sites: DynamicBuffer(DeclarationSite),
token_kinds: []const Lexer.Token.Kind = &.{},
token_class: []?Type = &.{},
token_modifiers: []u32 = &.{},
// the last pass has no trace of the names splices spelled and of stcfuns it does not run again
// per token: the token naming the declaration an earlier pass found it to mean
// per such naming token: its declaration in `past_declarations`
earlier_naming_token: []u32 = &.{},
// per token: the name of a declaration without a naming token (an included one) an earlier pass
// found it to mean, empty for none
earlier_names: [][]const u8 = &.{},
past_declaration_index: []u32 = &.{},
past_declarations: DynamicBuffer(PastDeclaration),
// per node: the block or match arm it is in and the declaration it makes
node_parent: []u32 = &.{},
node_scope: []u32 = &.{},
node_first_token: []u32 = &.{},
node_declaration: []u32 = &.{},
// per token: the identifier node written at it
token_leaf: []u32 = &.{},
// semantic tokens are encoded relative to the start of the one before
last_token_start: Position = .{ .line = 0, .character = 0 },

// the source comes on stdin, the `Result` goes to stdout, `path` is the document's file or empty
pub fn run(io: std.Io, allocator: std.mem.Allocator, path: []const u8) !void {
    // a runaway compiler stops itself even when the server is gone, a crash dumps no core
    // macos does not enforce the address space limit, the cpu limit still ends a runaway there
    if (builtin.os.tag != .windows) {
        const limits = [_]struct { std.posix.rlimit_resource, u64 }{
            .{ .AS, 4 << 30 },
            .{ .CPU, 10 },
            .{ .CORE, 0 },
        };
        for (limits) |limit| {
            const resource, const maximum = limit;
            std.posix.setrlimit(resource, .{ .cur = maximum, .max = maximum }) catch {};
        }
    }

    var input_buffer: [1 << 16]u8 = undefined;
    var input = std.Io.File.stdin().readerStreaming(io, &input_buffer);
    const source = try input.interface.allocRemaining(allocator, .unlimited);

    var output_buffer: [1 << 16]u8 = undefined;
    var output = std.Io.File.stdout().writerStreaming(io, &output_buffer);
    const result = analyze_at(allocator, source, io, path);
    try std.json.Stringify.value(result, .{}, &output.interface);
    try output.interface.flush();
}

pub fn analyze(allocator: std.mem.Allocator, source: []u8) Result {
    return analyze_at(allocator, source, null, "");
}

pub fn analyze_at(
    allocator: std.mem.Allocator,
    source: []u8,
    io: ?std.Io,
    path: []const u8,
) Result {
    var self = Analysis{
        .allocator = allocator,
        .source = source,
        .io = io,
        .path = path,
        .line_starts = .init(allocator, 256),
        .token_data = .init(allocator, 4096),
        .diagnostics = .init(allocator, 16),
        .declarations = .init(allocator, 256),
        .links = .init(allocator, 1024),
        .hints = .init(allocator, 64),
        .elsewhere = .init(allocator, 8),
        .expansions = .init(allocator, 16),
        .passes = .init(allocator, 4),
        .declaration_sites = .init(allocator, 256),
        .past_declarations = .init(allocator, 64),
    };
    self.line_starts.push(0);
    for (source, 0..) |byte, i| {
        if (byte == '\n') self.line_starts.push(@intCast(i + 1));
    }

    var lexer = Lexer{ .src_bytes = source, .tokens = .init(allocator, 1024) };
    if (self.resolve(&lexer)) |resolver| {
        highlighting.classify_resolved(resolver, self.token_class, self.token_modifiers);
        highlighting.classify_namespaces(&self, &lexer, resolver);
        linking.link(&self, &lexer, resolver);

        // the value of every `stc` variable that has one, at the end of the line its name is on
        const declarations = resolver.decl_pool.entries.columns();
        const longest = 80;
        for (0..declarations.name.len) |i| {
            const value = declarations.static_value[i];
            const is_variable = declarations.kind[i] == .variable and declarations.flags[i].is_stc;
            if (!is_variable or value == .none or value == .poison_type) continue;
            // the compiler's own constants (`__os`) are written nowhere
            const node = declarations.node[i];
            if (node == 0) continue;
            const span = resolver.tree.extent(node) orelse
                dbg.node_span(resolver.tree, source, node) orelse continue;
            if (span[0] >= source.len) continue;

            var text: std.Io.Writer.Allocating = .init(allocator);
            text.writer.writeAll("= ") catch @panic("OOM");
            const pool = &resolver.static_pool;
            pool.format(&resolver.name_pool, value, &text.writer) catch @panic("OOM");
            var label = text.written();
            if (label.len > longest) {
                const shortened = .{ label[0 .. longest - 3], "..." };
                label = std.mem.concat(allocator, u8, &shortened) catch @panic("OOM");
            }
            const line_end = std.mem.indexOfScalarPos(u8, source, span[0], '\n') orelse source.len;
            const position = positions.position(&self, @intCast(line_end));
            self.hints.push(.{ .position = position, .label = label });
        }
        std.mem.sort(Hint, self.hints.items(), {}, struct {
            fn earlier(_: void, left: Hint, right: Hint) bool {
                return positions.before(left.position, right.position);
            }
        }.earlier);
    }
    highlighting.encode(&self, &lexer);

    return .{
        .data = self.token_data.items(),
        .diagnostics = self.diagnostics.items(),
        .decls = self.declarations.items(),
        .links = self.links.items(),
        .outline = outline.build(&self),
        .hints = self.hints.items(),
        .elsewhere = self.elsewhere.items(),
        .expansions = self.expansions.items(),
        // the source alone is no step
        .passes = if (self.passes.len > 1) self.passes.items() else &.{},
    };
}

// every stage reports what stopped it, the resolver everything it found
fn resolve(self: *Analysis, lexer: *Lexer) ?*Resolver {
    const lexed = lexer.gen_tokens();
    highlighting.classify_lexically(self, lexer);
    const token_count = lexer.tokens.columns().tk.len;
    self.earlier_naming_token = self.allocate_unset(token_count);
    self.earlier_names = self.allocator.alloc([]const u8, token_count) catch @panic("OOM");
    @memset(self.earlier_names, "");
    self.past_declaration_index = self.allocate_unset(token_count);
    lexed catch |err| {
        self.report(lexer.cursor -| 1, lexer.cursor, .@"error", @errorName(err), "");
        return null;
    };

    const parser = self.allocator.create(Parser) catch @panic("OOM");
    parser.* = Parser.init(self.allocator, lexer.tokens, self.source, lexer.tokens.column(.span));
    // a statement that doesn't parse is a hole: the rest is analyzed, each error reported
    parser.recover = true;
    parser.build_ast() catch |err| {
        const span = lexer.tokens.column(.span)[parser.tok_cursor -| 1];
        self.report(span[0], span[1], .@"error", @errorName(err), "");
        return null;
    };
    for (parser.errors.items) |found| {
        const span = lexer.tokens.column(.span)[found.token];
        self.report(span[0], span[1], .@"error", @errorName(found.err), "");
    }

    const resolver = self.allocator.create(Resolver) catch @panic("OOM");
    const globals = parser.global_store.items();
    resolver.* = Resolver.init(self.allocator, &parser.tree, self.source, globals);
    highlighting.classify_written(self, resolver);
    resolver.session = .{
        .io = self.io,
        .path = self.path,
        .watch = .{ .observer = self, .pass = observe_pass },
    };
    // a pass writes into the tree, the program it starts from is kept before
    if (parser.tree.macros) self.passes.push(self.printed(resolver, resolver.roots, null));
    resolver.resolve() catch {};
    const found = resolver.doctor.diagnostics.columns();
    for (
        found.code,
        found.node,
        found.first_operand,
        found.second_operand,
    ) |code, node, first_operand, second_operand| {
        // a file other files include needs no `main` of its own
        // the editor shows no `missing_main` for it
        if (code == .missing_main and self.io != null) {
            if (includers.is_included(self.io.?, self.allocator, self.path)) continue;
        }
        var operands: std.Io.Writer.Allocating = .init(self.allocator);
        dbg.print_operands(
            &operands.writer,
            resolver,
            code,
            first_operand,
            second_operand,
            false,
        ) catch @panic("OOM");
        const span = resolver.tree.extent(node) orelse
            dbg.node_span(resolver.tree, self.source, node) orelse
            Lexer.TextSpan{ 0, 0 };
        self.report(span[0], span[1], Doctor.severity_of(code), @tagName(code), operands.written());
    }
    return resolver;
}

// a diagnostic marks its node up to the end of the node's first line, a whole body is too much
fn report(
    self: *Analysis,
    start: u32,
    end: u32,
    severity: Doctor.Severity,
    what: []const u8,
    operands: []const u8,
) void {
    const line_end = std.mem.indexOfScalarPos(u8, self.source, start, '\n') orelse self.source.len;
    const marked_end: u32 = @intCast(@max(start, @min(end, line_end)));
    self.diagnostics.push(.{
        .range = positions.range(self, start, marked_end),
        // lsp counts from error = 1 to hint = 4
        .severity = 3 - @backingInt(severity),
        .message = std.mem.concat(self.allocator, u8, &.{ what, operands }) catch @panic("OOM"),
    });
}

// a pass the next one starts over from, on a rebuilt tree: what it resolved and declared
fn observe_pass(context: *anyopaque, resolver: *Resolver) void {
    const self: *Analysis = @ptrCast(@alignCast(context));
    highlighting.classify_resolved(resolver, self.token_class, self.token_modifiers);
    linking.remember_pass(self, resolver);

    // the program the pass leaves and the code of each splice of the document it evaluated
    const tree = resolver.tree;
    const file = resolver.macros.file;
    const roots = if (file != 0) tree.manychildren(file) else resolver.roots;
    self.passes.push(self.printed(resolver, roots, null));
    const pass: u32 = @intCast(self.passes.len - 1);
    const first = self.expansions.len;
    const kinds = self.token_kinds;
    for (0..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        if (tree.kind(node) != .splice or tree.arg(node, 1) == 0) continue;
        const range: Range = (found: {
            // from the `<` a few tokens before its first one (`<quote: x>`) to its `>`
            const token = tree.first_token(node);
            if (tree.extent(node) == null or token == 0 or token >= kinds.len) break :found null;
            var open = token - 1;
            while (kinds[open] != .@"xpct_<") : (open -= 1) {
                if (open == 0 or token - open >= 4) break :found null;
            }
            const spans = tree.span_store;
            var depth: u32 = 0;
            for (open + 1..kinds.len) |at| switch (kinds[at]) {
                .@"pct_(", .@"pct_[", .@"pct_{", .@"xpct_!{" => depth += 1,
                .@"xpct_*(", .@"xpct_**(", .@"xpct_+(", .@"xpct_++(" => depth += 1,
                .@"pct_)", .@"pct_]", .@"pct_}" => {
                    if (depth == 0) break :found null;
                    depth -= 1;
                },
                .@"xpct_>" => if (depth == 0) {
                    break :found positions.range(self, spans[open][0], spans[at][1]);
                },
                else => {},
            };
            break :found null;
        }) orelse continue;

        const expansion = tree.arg(node, 1) - 1;
        var code = if (tree.kind(expansion) == .block)
            self.printed(resolver, tree.manychildren(expansion), null)
        else
            self.printed(resolver, &.{}, expansion);
        // a whole file included shows how it starts
        const longest = 40;
        var lines: u32 = 0;
        for (code, 0..) |byte, at| {
            if (byte != '\n') continue;
            lines += 1;
            if (lines < longest) continue;
            const more = std.mem.count(u8, code[at + 1 ..], "\n");
            if (more == 0) break;
            const shown = .{ code[0..at], more };
            code = std.fmt.allocPrint(self.allocator, "{s}\n# .. {d} more lines", shown) catch {
                @panic("OOM");
            };
            break;
        }
        const trimmed = std.mem.trimEnd(u8, code, "\n");
        self.expansions.push(.{ .range = range, .pass = pass, .code = trimmed });
    }
    std.mem.sort(Expansion, self.expansions.items()[first..], {}, struct {
        fn earlier(_: void, left: Expansion, right: Expansion) bool {
            return positions.before(left.range.start, right.range.start);
        }
    }.earlier);
}

// statements, or an expression, as code: a splice evaluated in this pass as what it expanded to
fn printed(self: *Analysis, resolver: *Resolver, statements: []const u32, expression: ?u32) []u8 {
    var written: std.ArrayList(u8) = .empty;
    var printer: dbg.CodePrinter = .{
        .out = &written,
        .allocator = self.allocator,
        .tree = resolver.tree,
        .source = resolver.src_bytes,
        .expand = true,
    };
    // names hygiene made are written as they were where that is unambiguous
    if (expression) |node| {
        printer.note_names(node) catch @panic("OOM");
        printer.expression(node) catch @panic("OOM");
    } else {
        for (statements) |statement| printer.note_names(statement) catch @panic("OOM");
        printer.statements(statements) catch @panic("OOM");
    }
    return written.items;
}

// `length` entries, all `none`
pub fn allocate_unset(self: *Analysis, length: usize) []u32 {
    const entries = self.allocator.alloc(u32, length) catch @panic("OOM");
    @memset(entries, none);
    return entries;
}

// the link of the name at `line` and `character`
fn link_at(result: Result, line: u32, character: u32) !Link {
    for (result.links) |found| {
        if (found[0] == line and found[1] == character) return found;
    }
    return error.TestUnexpectedResult;
}

test {
    _ = includers;
}

test "tokens and diagnostics" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(
        u8,
        "fun f = (i32 x) -> i32: ret x; # é\nmain = () { s = \"𝄞\"; f(1, 2); }\n",
    );
    const result = analyze(arena.allocator(), source);
    // line and column relative to the token before, length, type, modifiers
    const expected = [_]struct { u32, u32, u32, Type, u32 }{
        .{ 0, 0, 3, .type, 0 },     .{ 0, 4, 1, .function, 0 },  .{ 0, 2, 1, .operator, 0 },
        .{ 0, 3, 3, .type, 0 },     .{ 0, 4, 1, .parameter, 1 }, .{ 0, 3, 2, .operator, 0 },
        .{ 0, 3, 3, .type, 0 },     .{ 0, 5, 3, .keyword, 0 },   .{ 0, 4, 1, .parameter, 1 },
        .{ 0, 3, 3, .comment, 0 },  .{ 1, 0, 4, .keyword, 0 },   .{ 0, 5, 1, .operator, 0 },
        .{ 0, 7, 1, .variable, 1 }, .{ 0, 2, 1, .operator, 0 },  .{ 0, 2, 4, .string, 0 },
        .{ 0, 6, 1, .function, 0 }, .{ 0, 2, 1, .number, 0 },    .{ 0, 3, 1, .number, 0 },
    };
    try std.testing.expectEqual(expected.len * 5, result.data.len);
    for (expected, 0..) |token, i| {
        const encoded = [_]u32{ token[0], token[1], token[2], @backingInt(token[3]), token[4] };
        try std.testing.expectEqualSlices(u32, &encoded, result.data[i * 5 ..][0..5]);
    }
    try std.testing.expectEqual(1, result.diagnostics.len);
    const diagnostic = result.diagnostics[0];
    const expected_message = "wrong_arity  arguments 2  parameters 1";
    try std.testing.expectEqualStrings(expected_message, diagnostic.message);
    try std.testing.expectEqual(Position{ .line = 1, .character = 22 }, diagnostic.range.start);
}

test "links and outline" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\type Point = *(mut i32 x, i32 y);
        \\variant Shape = +(Circle(f32 r), Rect);
        \\fun f = (Point p) -> i32: ret p.x;
        \\main = () { Point q = Point(x = 1, y = 2); s = Shape.Circle(r = 1.0); f(q); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a name at line and character, the name it means, where that is declared
    const expected = [_]struct { u32, u32, []const u8, u32, u32 }{
        .{ 0, 23, "x", 0, 23 },    .{ 2, 15, "p", 2, 15 },      .{ 2, 30, "p", 2, 15 },
        .{ 2, 32, "x", 0, 23 },    .{ 3, 28, "x", 0, 23 },      .{ 3, 35, "y", 0, 30 },
        .{ 3, 47, "Shape", 1, 8 }, .{ 3, 53, "Circle", 1, 18 }, .{ 3, 60, "r", 1, 29 },
        .{ 3, 70, "f", 2, 4 },     .{ 3, 72, "q", 3, 18 },
    };
    for (expected) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
        const declared_at = Position{ .line = name[3], .character = name[4] };
        try std.testing.expectEqual(declared_at, declaration.selectionRange.?.start);
    }
    try std.testing.expectEqualStrings("i32", result.decls[result.links[1][3]].detail);

    // types hold their fields and cases, cases their payload
    const tree = struct {
        fn write(writer: *std.Io.Writer, analyzed: Result, outlines: []const Outline) !void {
            for (outlines) |entry| {
                try writer.print("{s}(", .{analyzed.decls[entry.decl].name});
                try write(writer, analyzed, entry.children);
                try writer.writeByte(')');
            }
        }
    };
    var buffer: [64]u8 = undefined;
    var writer: std.Io.Writer = .fixed(&buffer);
    try tree.write(&writer, result, result.outline);
    const written = writer.buffered();
    try std.testing.expectEqualStrings("Point(x()y())Shape(Circle(r())Rect())f()main()", written);
}

test "guard binders, parts of `with` and narrowed binders link" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\type Pos = *(i32 x, i32 y);
        \\type W = *(Pos pos, u8 hp);
        \\variant E = +(A, B(u8 n), C);
        \\fun f = (W w, E e) -> u8: ret match e {
        \\    E.B(k) where k > (w with (pos.x = 1)).hp => k, E.A => 0, rest => tagof rest
        \\};
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    const expected = [_]struct { u32, u32, []const u8, u32, u32 }{
        .{ 4, 17, "k", 4, 8 },     .{ 4, 48, "k", 4, 8 },  .{ 4, 22, "w", 3, 11 },
        .{ 4, 30, "pos", 1, 15 },  .{ 4, 34, "x", 0, 17 }, .{ 4, 42, "hp", 1, 23 },
        .{ 4, 75, "rest", 4, 61 },
    };
    for (expected) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
        const declared_at = Position{ .line = name[3], .character = name[4] };
        try std.testing.expectEqual(declared_at, declaration.selectionRange.?.start);
    }
    // the binder after `E.A` is of `E` without it
    const rest = result.decls[(try link_at(result, 4, 75))[3]];
    try std.testing.expect(std.mem.indexOf(u8, rest.detail, " -- ") != null);
}

test "names the resolver never met" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\fun print = (&u8 fmt);
        \\type Pair = *(i32, i32);
        \\variant Res = +(Ok(u32), Err(u8 code));
        \\fun first = (Pair p) -> i32: ret p.$0;
        \\fun add = (i32, i32) -> i32: ret $0 + $1;
        \\fun mixed = (u32 a) -> u32: ret a;
        \\fun mixed = (u32 a, u32 b = 5) -> u32: ret a + b;
        \\stcfun code = (Res r) -> u32: ret match r { Res.Ok(v) => v, _ => 0 };
        \\main = () { print("x"); u32 m = mixed(1, b = 2); u64 l = lenof "ab"; }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a name at line and character, the name it means and where that is declared
    const expected = [_]struct { u32, u32, []const u8, ?Position }{
        // a signature without body
        .{ 0, 17, "fmt", .{ .line = 0, .character = 17 } },
        // a positional field
        .{ 3, 35, "Pair", .{ .line = 1, .character = 5 } },
        // a positional parameter
        .{ 4, 33, "add", .{ .line = 4, .character = 4 } },
        // an arm never matched
        .{ 7, 57, "v", .{ .line = 7, .character = 51 } },
        // in another overload
        .{ 8, 41, "b", .{ .line = 6, .character = 24 } },
    };
    for (expected) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
        const declared_at = if (declaration.selectionRange) |name_range| name_range.start else null;
        try std.testing.expectEqual(name[3], declared_at);
    }
    try std.testing.expectEqualStrings("&u8", result.decls[result.links[1][3]].detail);
}

test "a bare unwrap shows the fallback it returns" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\variant Opt = +(Some(i32), None);
        \\variant Res = +(Ok(i32), Err(u8));
        \\type Span = *(u32 from, u32 to = 10);
        \\variant Many = +(Ok(u32), Short(u8), Long(Span));
        \\variant Err8 = +(Err = 0xFF, Fine(u8)) tagtype self;
        \\variant Either = u64 || Opt;
        \\fun stamp = (u32 n) -> u32: ret n;
        \\type P = *(i32 x = 1, i32 y, &u8 name = "hi", u32 at = stamp(2));
        \\type Pair = *(u8, i16);
        \\fun int = (Opt o) -> i32: ret o?? + 1;
        \\fun float = (Opt o) -> f64: ret o?? as f64;
        \\fun truth = (Opt o) -> bool: ret o?? > 0;
        \\fun unit = (Opt o) { i32 v = o??; }
        \\fun bytes = (Opt o) -> [3]u8 { i32 v = o??; ret [1, 2, 3]; }
        \\fun long = (Opt o) -> [8]u8 { i32 v = o??; ret [1, 2, 3, 4, 5, 6, 7, 8]; }
        \\fun record = (Opt o) -> P { i32 v = o??; ret P(y = v); }
        \\fun pair = (Opt o) -> Pair { i32 v = o??; ret Pair(1, 1); }
        \\fun option = (Res r) -> Opt { i32 v = r??; ret Opt.Some(v); }
        \\fun err8 = (Opt o) -> Err8 { i32 v = o??; ret Err8.Fine(1); }
        \\fun again = (Res r) -> Res { i32 v = r??; ret r; }
        \\fun many = (Many m) -> Many { u32 v = m??; ret m; }
        \\fun foreign = (Opt o) -> Res { i32 v = o??; ret Res.Ok(v); }
        \\fun either = (Opt o) -> Either { i32 v = o??; ret 1 as u64; }
        \\fun pointer = (Opt o) -> &u8 { i32 v = o??; ret "x"; }
        \\stcfun pick = (type T): (Opt o, T other) -> T { i32 v = o??; ret other; }
        \\fun lambda = (Opt o) -> u8 { fun f = (Opt p) -> bool: ret p?? > 0; ret 1; }
        \\fun nested = (Opt o) -> i32: ret Opt.Some(o??)??;
        \\fun call = () -> i32: ret option(Res.Ok(1))??;
        \\fun deref = (&Opt p) -> u8: ret p.*?? as u8;
        \\fun fallback = (Opt o) -> i32: ret o ?? 3;
        \\fun case_typed = () -> &u8 { i32 v = Opt.Some(1)??; ret "x"; }
        \\stc Opt SOME = Opt.Some(2);
        \\stc i32 TOP = SOME??;
        \\main = () { a = pick(u8)(Opt.None, 1); b = pick(Opt)(Opt.None, Opt.None); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(1, result.diagnostics.len);
    try std.testing.expectEqualStrings("no_fallback  type &u8", result.diagnostics[0].message);
    // the `??` at line and character, what hovering it shows
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 9, 31, "ret 0  # i32" },
        .{ 10, 33, "ret 0.0  # f64" },
        .{ 11, 34, "ret false  # bool" },
        .{ 12, 30, "ret" },
        .{ 13, 40, "ret [0, 0, 0]  # [3]u8" },
        .{ 14, 39, "ret [0, 0, 0, 0, ..]  # [8]u8" },
        // defaults as written
        .{ 15, 37, "ret P(x = 1, y = 0, name = \"hi\", at = stamp(2))  # P" },
        .{ 16, 38, "ret Pair(0, 0)  # Pair" },
        // a case without payload, the self tag's one, the case held, else the case tagged 0
        .{ 17, 39, "ret Opt.None  # Opt" },
        .{ 18, 38, "ret Err8.Err  # Err8" },
        .{ 19, 38, "ret Res.Err(0)  # Res" },
        .{ 20, 39, "ret Many.Short(0) or Many.Long(Span(from = 0, to = 10))  # Many" },
        .{ 21, 40, "ret Res.Ok(0)  # Res" },
        .{ 22, 42, "ret Opt.None  # u64 || +(Some, None)" },
        .{ 23, 40, "no fallback: &u8" },
        // each realization, the innermost function
        .{ 24, 57, "ret 0  # u8 | ret Opt.None  # Opt" },
        .{ 25, 59, "ret false  # bool" },
        // after brackets, a call and a dereference; an operand typed as a case
        .{ 26, 43, "ret 0  # i32" },
        .{ 26, 46, "never fails" },
        .{ 27, 43, "ret 0  # i32" },
        .{ 28, 35, "ret 0  # u8" },
        .{ 30, 48, "never fails" },
        .{ 32, 18, "outside a function: static_eval_failed" },
    };
    for (expected) |unwrap| {
        const found = try link_at(result, unwrap[0], unwrap[1]);
        try std.testing.expectEqual(unwrap[1] + 2, found[2]);
        const declaration = result.decls[found[3]];
        try std.testing.expectEqualStrings("??", declaration.name);
        try std.testing.expectEqualStrings(unwrap[2], declaration.detail);
        try std.testing.expectEqual(null, declaration.selectionRange);
    }
    // an unwrap with a fallback shows nothing
    try std.testing.expectError(error.TestUnexpectedResult, link_at(result, 29, 37));
}

test "a label shows whether it writes the place it names" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\variant Opt = +(Some(i32), None);
        \\fun f = (Opt o, *Opt p) -> i32 {
        \\    mut i32 x = 1;
        \\    if (x <- a) > 0 and o ?<- b and p ?<- c { a = 2; c = 3; }
        \\    ret (x + 1 <- d) + d;
        \\}
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a mutable local and a `*` pointer's payload may be written, an immutable parameter's
    // payload and a value of its own not
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 3, 13, "i32 (writable)" },
        .{ 3, 30, "i32" },
        .{ 3, 42, "i32 (writable)" },
        .{ 4, 18, "i32" },
    };
    for (expected) |label| {
        const declaration = result.decls[(try link_at(result, label[0], label[1]))[3]];
        try std.testing.expectEqualStrings(label[2], declaration.detail);
    }
}

test "a bare unwrap in a default, a guard and a quote" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\variant Opt = +(Some(i32), None);
        \\type IntFn = (Opt) -> i32;
        \\fun apply = (IntFn f, Opt o) -> i32: ret f(o);
        \\fun defaulted = (Opt o, i32 k = Opt.Some(1)??) -> i32: ret k;
        \\fun guarded = (Opt o, i32 k where k > 0 else o??) -> u8: ret 1;
        \\fun inside = (Opt o, i32 k = apply((Opt p) -> i32: ret p?? + 1, o)) -> i32: ret k;
        \\fun quoted = (Opt o) -> &u8 { stc q = quote: o??; ret "x"; }
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a default runs where the function is called, a guard's `else` and a lambda return
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 3, 43, "outside a function: static_eval_failed" },
        .{ 4, 46, "ret 0  # u8" },
        .{ 5, 56, "ret 0  # i32" },
    };
    for (expected) |unwrap| {
        const declaration = result.decls[(try link_at(result, unwrap[0], unwrap[1]))[3]];
        try std.testing.expectEqualStrings(unwrap[2], declaration.detail);
    }
    // quoted code returns from where it lands
    try std.testing.expectError(error.TestUnexpectedResult, link_at(result, 6, 46));
}

test "the target, machine code and alignment" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\stc u64 KNOWN = (stcmatch __os { "macos" => 1, _ => 2 }) + lenof __arch;
        \\fun relax = () { asm "nop"; }
        \\stc u64 A = alignof u64;
        \\main = () { relax(); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // `__os` and `__arch` are declared by the compiler, nowhere in the source
    for ([_]struct { u32, []const u8 }{ .{ 26, "__os" }, .{ 65, "__arch" } }) |name| {
        const declaration = result.decls[(try link_at(result, 0, name[0]))[3]];
        try std.testing.expectEqualStrings(name[1], declaration.name);
        try std.testing.expectEqual(null, declaration.selectionRange);
    }
}

test "a crash reports its text where it is, of every static text" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\stc &u8 POINTER = "pointer";
        \\type Holder = *([5]u8 text);
        \\stc Holder HOLDER = Holder(text = "field");
        \\stcfun checked = (u32 n) -> u32: ret if n > 3: crash "too big" else: n;
        \\stc u32 BIG = checked(9);
        \\crash POINTER;
        \\crash HOLDER.text;
        \\stcif false: crash "pruned";
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 3, 47, "crash   `too big`" },
        .{ 5, 0, "crash   `pointer`" },
        .{ 6, 0, "crash   `field`" },
    };
    try std.testing.expectEqual(expected.len, result.diagnostics.len);
    for (expected) |crash| {
        const found = for (result.diagnostics) |diagnostic| {
            if (diagnostic.range.start.line == crash[0]) break diagnostic;
        } else return error.TestExpectedEqual;
        try std.testing.expectEqual(crash[1], found.range.start.character);
        try std.testing.expectEqualStrings(crash[2], found.message);
    }
}

test "a name reported undefined stays unlinked" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const text = "main = () { { i32 inner = 1; } i32 b = inner; }";
    const source = try arena.allocator().dupe(u8, text);
    const result = analyze(arena.allocator(), source);
    const message = result.diagnostics[0].message;
    try std.testing.expectEqualStrings("undefined_name  name `inner`", message);
    for (result.links) |found| try std.testing.expect(found[1] != 40);
}

test "macros expand before anything is linked, made names link nowhere" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(
        u8,
        "stcfun twice = (ast e) -> ast: ret quote { tmp = @e; ret tmp + tmp; };\n" ++
            "fun f = () -> u32: <twice(quote: 21)>;\nmain = () {}",
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // the `tmp` of the expansion is renamed where it lands and written at no token
    for (result.decls) |declaration| {
        try std.testing.expect(std.mem.indexOfScalar(u8, declaration.name, '`') == null);
    }

    const failing = try arena.allocator().dupe(u8, "<include \"nope.mn\">;\nmain = () {}");
    const message = analyze(arena.allocator(), failing).diagnostics[0].message;
    try std.testing.expectEqualStrings("include_failed  file `nope.mn`  because `NoIo`", message);
}

test "macros: the meta syntax is a macro, code by its role, splices and stcfuns by what they mean" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8, "" ++
        "stcfun twice = (ast(u32) e) -> ast(u32): ret quote: @e + @e;\n" ++
        "fun f = (u32 a) -> bool: ret <twice(quote: a)> < a;\n" ++
        "stcfun unused = (ast e) -> ast: ret match e { " ++
        "quote: @x + 0 => x, quote: 0 + @x => fresh \"t\", _ => e };\n" ++
        "stcfun kids = (ast e) -> ast: ret match e { " ++
        "ast.BinaryAdd(l, r) | ast.BinaryMultiply(l, r) => e with (lhs = r), _ => e.src };\n" ++
        "fun g = () -> u32: ret <kids(quote: 1 * 2)>;\n" ++
        "main = () {}");
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    var classes: [4][128]?struct { Type, u32 } = @splat(@splat(null));
    var line: u32, var character: u32 = .{ 0, 0 };
    for (0..result.data.len / 5) |i| {
        const encoded = result.data[i * 5 ..][0..5];
        line += encoded[0];
        character = if (encoded[0] == 0) character + encoded[1] else encoded[1];
        const class: Type = @fromBackingInt(@intCast(encoded[3]));
        if (line < 4) classes[line][character] = .{ class, encoded[4] };
    }
    // line, character, what it is
    // `twice` ran in the pass that expanded it, `unused` never ran
    // `kids` matched only the second alternative, the splice is gone from the last pass
    // a `<` after a splice compares
    const expected = [_]struct { u32, u32, Type }{
        .{ 0, 7, .function },   .{ 0, 25, .parameter },  .{ 0, 45, .macro },
        .{ 0, 52, .macro },     .{ 0, 53, .parameter },  .{ 1, 29, .macro },
        .{ 1, 30, .function },  .{ 1, 43, .parameter },  .{ 1, 45, .macro },
        .{ 1, 47, .operator },  .{ 2, 42, .parameter },  .{ 2, 54, .variable },
        .{ 2, 63, .variable },  .{ 2, 78, .variable },   .{ 2, 83, .macro },
        .{ 2, 99, .parameter }, .{ 3, 48, .enumMember }, .{ 3, 58, .variable },
        .{ 3, 61, .variable },  .{ 3, 102, .property },  .{ 3, 108, .variable },
        .{ 3, 119, .property },
    };
    for (expected) |token| try std.testing.expectEqual(token[2], classes[token[0]][token[1]].?[0]);

    // the splice's name means the stcfun
    // a binder of a quote pattern is seen in its arm only, alternatives share their binders
    const expected_links = [_]struct { u32, u32, u32, u32 }{
        .{ 1, 30, 0, 7 },  .{ 2, 63, 2, 54 },  .{ 0, 53, 0, 25 },
        .{ 3, 58, 3, 85 }, .{ 3, 108, 3, 88 },
    };
    for (expected_links) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        const declared_at = Position{ .line = name[2], .character = name[3] };
        try std.testing.expectEqual(declared_at, declaration.selectionRange.?.start);
    }
    for (result.links) |found| {
        const is_fresh_call = found[0] == 2 and found[1] == 78;
        if (!is_fresh_call) continue;
        try std.testing.expect(result.decls[found[3]].selectionRange.?.start.character == 78);
    }
}

test "a namespace is a namespace where it is declared and reached, a `pub` one of it too" {
    const io = std.testing.io;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var workspace = std.testing.tmpDir(.{});
    defer workspace.cleanup();
    const inner_source = "pub fun deep = () -> u32: ret 3;\n";
    const library_source = "pub inner = <include \"inner.mn\">;\npub fun f = () -> u32: ret 1;\n";
    try workspace.dir.writeFile(io, .{ .sub_path = "inner.mn", .data = inner_source });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib.mn", .data = library_source });
    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root_buffer[0..try workspace.dir.realPath(io, &root_buffer)];
    const path = try std.fs.path.join(allocator, &.{ root, "main.mn" });

    const source = try allocator.dupe(u8,
        \\m = <include "lib.mn">;
        \\main = () -> u32: ret m.f() + m.inner.deep();
    );
    const result = analyze_at(allocator, source, io, path);
    try std.testing.expectEqual(0, result.diagnostics.len);
    var classes: [2][64]?Type = @splat(@splat(null));
    var line: u32, var character: u32 = .{ 0, 0 };
    for (0..result.data.len / 5) |i| {
        const encoded = result.data[i * 5 ..][0..5];
        line += encoded[0];
        character = if (encoded[0] == 0) character + encoded[1] else encoded[1];
        classes[line][character] = @fromBackingInt(@intCast(encoded[3]));
    }
    const expected = [_]struct { u32, u32, Type }{
        .{ 0, 0, .namespace },  .{ 1, 22, .namespace }, .{ 1, 24, .function },
        .{ 1, 30, .namespace }, .{ 1, 32, .namespace }, .{ 1, 38, .function },
    };
    for (expected) |token| try std.testing.expectEqual(token[2], classes[token[0]][token[1]].?);
}

test "main and the protocol methods are keywords, a free function of the same name is not" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\type R = *(mut u32 n) !{ init = () -> R: ret R(0); next = () -> u32: ret self.n; };
        \\type P = *(u32 a);
        \\fun next = () -> u32: ret 1;
        \\main = () { mut R r = R.init(); u32 v = r.next() + next(); P p = P.init(); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    var classes: [4][128]?Type = @splat(@splat(null));
    var line: u32, var character: u32 = .{ 0, 0 };
    for (0..result.data.len / 5) |i| {
        const encoded = result.data[i * 5 ..][0..5];
        line += encoded[0];
        character = if (encoded[0] == 0) character + encoded[1] else encoded[1];
        classes[line][character] = @fromBackingInt(@intCast(encoded[3]));
    }
    const expected = [_]struct { u32, u32, Type }{
        .{ 0, 25, .keyword }, .{ 0, 51, .keyword }, .{ 2, 4, .function },  .{ 3, 0, .keyword },
        .{ 3, 24, .keyword }, .{ 3, 42, .keyword }, .{ 3, 51, .function }, .{ 3, 67, .keyword },
    };
    for (expected) |token| try std.testing.expectEqual(token[2], classes[token[0]][token[1]].?);
}

test "the values of `stc` variables, as `#=` reads them" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\stc u32 A = 2 + 3;
        \\stc []u8 TEXT = "ab" ~ "c"; # a comment
        \\fun f = () -> u32 {
        \\    stc u32 LOCAL = A * 2;
        \\    ret LOCAL;
        \\}
        \\u32 runtime = 4;
        \\stc [40]u32 MANY = for 0..<40: 123456;
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // the line, the character after its end and the label, a long one shortened
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 0, 18, "= 5" },
        .{ 1, 39, "= \"abc\"" },
        .{ 3, 26, "= 10" },
        .{ 7, 38, "= [123456, 123456, 123456, 123456, 123456, 123456, 123456, 123456, 1234" ++
            "56, 12..." },
    };
    try std.testing.expectEqual(expected.len, result.hints.len);
    for (expected, result.hints) |hint, found| {
        const position = Position{ .line = hint[0], .character = hint[1] };
        try std.testing.expectEqual(position, found.position);
        try std.testing.expectEqualStrings(hint[2], found.label);
    }
}

test "a statement that doesn't parse is a hole, the rest is analyzed" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\fun f = (u32 x) -> u32 {
        \\    u32 a = x +;
        \\    u32 b = x * 2;
        \\    ret b;
        \\}
        \\fun g = ( -> u32: ret 1;
        \\fun h = () -> u32: ret f(1) + missing;
        \\main = () { u32 c = (1 +; h(); }
    );
    const result = analyze(arena.allocator(), source);
    // each error where it is, the declarations after them still known and linked
    const expected = [_]struct { u32, u32, []const u8 }{
        .{ 1, 15, "NoRuleFound" },
        .{ 5, 10, "NoRuleFound" },
        .{ 7, 24, "NoRuleFound" },
        .{ 6, 30, "undefined_name  name `missing`" },
    };
    try std.testing.expectEqual(expected.len, result.diagnostics.len);
    for (expected, result.diagnostics) |want, found| {
        const start = Position{ .line = want[0], .character = want[1] };
        try std.testing.expectEqual(start, found.range.start);
        try std.testing.expectEqualStrings(want[2], found.message);
    }
    const names = [_]struct { u32, u32, []const u8 }{
        .{ 3, 8, "b" }, .{ 6, 23, "f" }, .{ 7, 26, "h" },
    };
    for (names) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
    }
}

test "what each macro pass expanded a splice to, and the program after it" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\stcfun twice = (ast e) -> ast: ret quote: @e + @e;
        \\stcfun make = () -> ast: ret quote: <twice(quote: 3)>;
        \\stc u32 A = <twice(quote: 1 * 2)>;
        \\stc u32 B = <make()>;
        \\<quote { u32 c = 1; u32 d = 2; }>;
        \\stcfun nothing = () {};
        \\<nothing()>;
        \\main = () {}
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // the top splices first, then the ones of declarations, then the one a splice made, which is
    // at the splice that made it
    const expected = [_]struct { u32, u32, u32, u32, []const u8 }{
        .{ 1, 4, 0, 33, "u32 c = 1;\nu32 d = 2;" },
        .{ 1, 6, 0, 11, "" },
        .{ 2, 2, 12, 33, "1 * 2 + 1 * 2" },
        .{ 2, 3, 12, 20, "<twice(quote: 3)>" },
        .{ 3, 3, 12, 20, "3 + 3" },
    };
    try std.testing.expectEqual(expected.len, result.expansions.len);
    for (expected, result.expansions) |expansion, found| {
        const pass, const line, const start, const end, const code = expansion;
        try std.testing.expectEqual(pass, found.pass);
        const starts = Position{ .line = line, .character = start };
        try std.testing.expectEqual(starts, found.range.start);
        try std.testing.expectEqual(Position{ .line = line, .character = end }, found.range.end);
        try std.testing.expectEqualStrings(code, found.code);
    }
    try std.testing.expectEqual(4, result.passes.len);
    try std.testing.expectEqualStrings(
        \\stcfun twice = (ast e) -> ast: ret quote: @e + @e;
        \\stcfun make = () -> ast: ret quote: <twice(quote: 3)>;
        \\stc u32 A = 1 * 2 + 1 * 2;
        \\stc u32 B = 3 + 3;
        \\u32 c = 1;
        \\u32 d = 2;
        \\stcfun nothing = () {};
        \\main = () {};
        \\
    , result.passes[3]);

    // a pass that only writes into a declaration
    const written = try arena.allocator().dupe(u8,
        \\fun early = () -> u32: ret 1;
        \\stcfun rewrite = (*ast(fun) f) { f.body = quote: ret 2; };
        \\<rewrite(refl early)>;
        \\main = () {}
    );
    const rewritten = analyze(arena.allocator(), written);
    try std.testing.expectEqual(0, rewritten.diagnostics.len);
    try std.testing.expectEqual(2, rewritten.passes.len);
    try std.testing.expectEqualStrings(
        \\fun early = () -> u32: ret 2;
        \\stcfun rewrite = (*ast(fun) f) {
        \\    f.body = quote: ret 2;
        \\};
        \\main = () {};
        \\
    , rewritten.passes[1]);

    // a name hygiene made is written as it was where no other name is written that way
    const hygienic = try arena.allocator().dupe(u8,
        \\stcfun body = () -> ast: ret quote { u32 t = 2; ret t * 3; };
        \\fun f = () -> u32 { <body()>; }
        \\stcfun two = () -> ast: ret quote { u32 t = 1; u32 u = t; };
        \\fun g = () -> u32 { <two()>; <two()>; ret 0; }
        \\main = () {}
    );
    const renamed = analyze(arena.allocator(), hygienic);
    try std.testing.expectEqual(0, renamed.diagnostics.len);
    try std.testing.expectEqual(3, renamed.expansions.len);
    try std.testing.expectEqualStrings("u32 t = 2;\nret t * 3;", renamed.expansions[0].code);
    try std.testing.expectEqualStrings("u32 t = 1;\nu32 u = t;", renamed.expansions[2].code);
    // in the whole program the quotes write `t` too, and `g` has two of each
    const program = renamed.passes[1];
    const in_f = "    u32 t`0 = 2;\n    ret t`0 * 3;";
    try std.testing.expect(std.mem.indexOf(u8, program, in_f) != null);
    const in_g = "    u32 u`2 = t`1;\n    u32 t`3 = 1;";
    try std.testing.expect(std.mem.indexOf(u8, program, in_g) != null);

    // nothing to step through without macros
    const plain = try arena.allocator().dupe(u8, "main = () {}");
    const unexpanded = analyze(arena.allocator(), plain);
    try std.testing.expectEqual(0, unexpanded.passes.len);
    try std.testing.expectEqual(0, unexpanded.expansions.len);
}

test "names of an included file link to their declarations there" {
    const io = std.testing.io;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var workspace = std.testing.tmpDir(.{});
    defer workspace.cleanup();
    try workspace.dir.createDirPath(io, "lib");
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/util.mn", .data =
        \\# a library
        \\pub stcfun twice = (ast e) -> ast: ret quote: @e + @e;
        \\pub fun add = (u32 a, u32 b) -> u32: ret a + b;
        \\pub stc u32 LIMIT = 9;
        \\
    });
    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root_buffer[0..try workspace.dir.realPath(io, &root_buffer)];
    const path = try std.fs.path.join(allocator, &.{ root, "main.mn" });
    const source = try allocator.dupe(u8,
        \\<include "lib/util.mn">;
        \\stc u32 A = <twice(quote: 2)>;
        \\fun f = () -> u32: ret add(LIMIT, 1);
        \\main = () {}
    );
    const result = analyze_at(allocator, source, io, path);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // the name in the document, then the declaration: its type and where it is in the library
    const expected = [_]struct { u32, u32, []const u8, []const u8, u32, u32, u32 }{
        // only an earlier pass met the name a splice calls
        .{ 1, 13, "twice", "(ast) -> ast", 1, 11, 16 },
        .{ 2, 23, "add", "(u32, u32) -> u32", 2, 8, 11 },
        .{ 2, 27, "LIMIT", "u32", 3, 12, 17 },
    };
    for (expected) |name| {
        const link = try link_at(result, name[0], name[1]);
        const declaration = result.decls[link[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
        try std.testing.expectEqualStrings(name[3], declaration.detail);
        const elsewhere = for (result.elsewhere) |found| {
            if (found.decl == link[3]) break found;
        } else return error.TestUnexpectedResult;
        try std.testing.expect(std.mem.endsWith(u8, elsewhere.uri, "/lib/util.mn"));
        try std.testing.expect(std.mem.startsWith(u8, elsewhere.uri, "file:///"));
        const starts = Position{ .line = name[4], .character = name[5] };
        try std.testing.expectEqual(starts, elsewhere.range.start);
        try std.testing.expectEqual(name[6], elsewhere.range.end.character);
    }
    // one declaration for every use of a name
    var adds: u32 = 0;
    for (result.decls) |declaration| adds += @intFromBool(std.mem.eql(u8, declaration.name, "add"));
    try std.testing.expectEqual(1, adds);
}
