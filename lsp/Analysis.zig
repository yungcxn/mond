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

pub const Result = struct {
    data: []const u32 = &.{},
    diagnostics: []const Diagnostic = &.{},
    decls: []const Symbol = &.{},
    // sorted by position
    links: []const Link = &.{},
    outline: []const Outline = &.{},
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
// per token: its declaration in `declarations`
token_meaning: []u32 = &.{},
// per declaration of the resolver: the token naming it
declaration_token: []u32 = &.{},
// per declaration in `declarations`: how its names are highlighted and found
declaration_sites: DynamicBuffer(DeclarationSite),
token_class: []?Type = &.{},
token_modifiers: []u32 = &.{},
// the last pass has no trace of the names splices spelled and of stcfuns it does not run again
// per token: the token naming the declaration an earlier pass found it to mean
// per such naming token: its declaration in `past_declarations`
earlier_naming_token: []u32 = &.{},
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
        linking.link(&self, &lexer, resolver);
    }
    highlighting.encode(&self, &lexer);

    return .{
        .data = self.token_data.items(),
        .diagnostics = self.diagnostics.items(),
        .decls = self.declarations.items(),
        .links = self.links.items(),
        .outline = outline.build(&self),
    };
}

// every stage reports what stopped it, the resolver everything it found
fn resolve(self: *Analysis, lexer: *Lexer) ?*Resolver {
    const lexed = lexer.gen_tokens();
    highlighting.classify_lexically(self, lexer);
    const token_count = lexer.tokens.columns().tk.len;
    self.earlier_naming_token = self.allocate_unset(token_count);
    self.past_declaration_index = self.allocate_unset(token_count);
    lexed catch |err| {
        self.report(lexer.cursor -| 1, lexer.cursor, .@"error", @errorName(err), "");
        return null;
    };

    const parser = self.allocator.create(Parser) catch @panic("OOM");
    parser.* = Parser.init(self.allocator, lexer.tokens, self.source, lexer.tokens.column(.span));
    parser.build_ast() catch |err| {
        const span = lexer.tokens.column(.span)[parser.tok_cursor -| 1];
        self.report(span[0], span[1], .@"error", @errorName(err), "");
        return null;
    };

    const resolver = self.allocator.create(Resolver) catch @panic("OOM");
    const globals = parser.global_store.items();
    resolver.* = Resolver.init(self.allocator, &parser.tree, self.source, globals);
    resolver.session = .{
        .io = self.io,
        .path = self.path,
        .watch = .{ .observer = self, .pass = observe_pass },
    };
    resolver.resolve() catch {};
    const found = resolver.doctor.diagnostics.columns();
    for (
        found.code,
        found.node,
        found.first_operand,
        found.second_operand,
    ) |code, node, first_operand, second_operand| {
        // a file other files include needs no `$main` of its own
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
        .severity = 3 - @intFromEnum(severity),
        .message = std.mem.concat(self.allocator, u8, &.{ what, operands }) catch @panic("OOM"),
    });
}

// a pass the next one starts over from, on a rebuilt tree: what it resolved and declared
fn observe_pass(context: *anyopaque, resolver: *Resolver) void {
    const self: *Analysis = @ptrCast(@alignCast(context));
    highlighting.classify_resolved(resolver, self.token_class, self.token_modifiers);
    linking.remember_pass(self, resolver);
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
        "fun f = (i32 x) -> i32: ret x; # é\n$main = () { s = \"𝄞\"; f(1, 2); }\n",
    );
    const result = analyze(arena.allocator(), source);
    // line and column relative to the token before, length, type, modifiers
    const expected = [_]struct { u32, u32, u32, Type, u32 }{
        .{ 0, 0, 3, .keyword, 0 },  .{ 0, 4, 1, .function, 0 },  .{ 0, 2, 1, .operator, 0 },
        .{ 0, 3, 3, .type, 0 },     .{ 0, 4, 1, .parameter, 1 }, .{ 0, 3, 2, .operator, 0 },
        .{ 0, 3, 3, .type, 0 },     .{ 0, 5, 3, .keyword, 0 },   .{ 0, 4, 1, .parameter, 1 },
        .{ 0, 3, 3, .comment, 0 },  .{ 1, 0, 5, .function, 0 },  .{ 0, 6, 1, .operator, 0 },
        .{ 0, 7, 1, .variable, 1 }, .{ 0, 2, 1, .operator, 0 },  .{ 0, 2, 4, .string, 0 },
        .{ 0, 6, 1, .function, 0 }, .{ 0, 2, 1, .number, 0 },    .{ 0, 3, 1, .number, 0 },
    };
    try std.testing.expectEqual(expected.len * 5, result.data.len);
    for (expected, 0..) |token, i| {
        const encoded = [_]u32{ token[0], token[1], token[2], @intFromEnum(token[3]), token[4] };
        try std.testing.expectEqualSlices(u32, &encoded, result.data[i * 5 ..][0..5]);
    }
    try std.testing.expectEqual(1, result.diagnostics.len);
    const diagnostic = result.diagnostics[0];
    const expected_message = "wrong_arity  arguments 2  parameters 1";
    try std.testing.expectEqualStrings(expected_message, diagnostic.message);
    try std.testing.expectEqual(Position{ .line = 1, .character = 23 }, diagnostic.range.start);
}

test "links and outline" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\type Point = *(mut i32 x, i32 y);
        \\variant Shape = +(Circle(f32 r), Rect);
        \\fun f = (Point p) -> i32: ret p.x;
        \\$main = () { Point q = Point(x = 1, y = 2); s = Shape.Circle(r = 1.0); f(q); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a name at line and character, the name it means, where that is declared
    const expected = [_]struct { u32, u32, []const u8, u32, u32 }{
        .{ 0, 23, "x", 0, 23 },    .{ 2, 15, "p", 2, 15 },      .{ 2, 30, "p", 2, 15 },
        .{ 2, 32, "x", 0, 23 },    .{ 3, 29, "x", 0, 23 },      .{ 3, 36, "y", 0, 30 },
        .{ 3, 48, "Shape", 1, 8 }, .{ 3, 54, "Circle", 1, 18 }, .{ 3, 61, "r", 1, 29 },
        .{ 3, 71, "f", 2, 4 },     .{ 3, 73, "q", 3, 19 },
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
    try std.testing.expectEqualStrings("Point(x()y())Shape(Circle(r())Rect())f()$main()", written);
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
        \\$main = () { print("x"); u32 m = mixed(1, b = 2); u64 l = "ab".$len; }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // a name at line and character, the name it means and where that is declared, a builtin nowhere
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
        .{ 8, 42, "b", .{ .line = 6, .character = 24 } },
        .{ 8, 63, "$len", null },
    };
    for (expected) |name| {
        const declaration = result.decls[(try link_at(result, name[0], name[1]))[3]];
        try std.testing.expectEqualStrings(name[2], declaration.name);
        const declared_at = if (declaration.selectionRange) |name_range| name_range.start else null;
        try std.testing.expectEqual(name[3], declared_at);
    }
    try std.testing.expectEqualStrings("&u8", result.decls[result.links[1][3]].detail);
}

test "the target, machine code and alignment" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8,
        \\stc u64 KNOWN = (stcmatch $os { "macos" => 1, _ => 2 }) + $arch.$len;
        \\fun relax = () { $asm("nop"); }
        \\stc u64 A = alignof u64;
        \\$main = () { relax(); }
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // `$os` and `$arch` are declared by the compiler, nowhere in the source
    for ([_]struct { u32, []const u8 }{ .{ 26, "$os" }, .{ 58, "$arch" } }) |name| {
        const declaration = result.decls[(try link_at(result, 0, name[0]))[3]];
        try std.testing.expectEqualStrings(name[1], declaration.name);
        try std.testing.expectEqual(null, declaration.selectionRange);
    }
}

test "a name reported undefined stays unlinked" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const text = "$main = () { { i32 inner = 1; } i32 b = inner; }";
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
            "fun f = () -> u32: <twice(quote: 21)>;\n$main = () {}",
    );
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    // the `tmp` of the expansion is renamed where it lands and written at no token
    for (result.decls) |declaration| {
        try std.testing.expect(std.mem.indexOfScalar(u8, declaration.name, '`') == null);
    }

    const failing = try arena.allocator().dupe(u8, "<include \"nope.mn\">;\n$main = () {}");
    const message = analyze(arena.allocator(), failing).diagnostics[0].message;
    try std.testing.expectEqualStrings("include_failed   `nope.mn`", message);
}

test "macros: the meta syntax is a macro, code by its role, splices and stcfuns by what they mean" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const source = try arena.allocator().dupe(u8, "" ++
        "stcfun twice = (ast(u32) e) -> ast(u32): ret quote: @e + @e;\n" ++
        "fun f = (u32 a) -> bool: ret <twice(quote: a)> < a;\n" ++
        "stcfun unused = (ast e) -> ast: ret match e { " ++
        "quote: @x + 0 => x, quote: 0 + @x => $fresh(\"t\"), _ => e };\n" ++
        "stcfun kids = (ast e) -> ast: ret match e { " ++
        "ast.BinaryAdd(l, r) | ast.BinaryMultiply(l, r) => e with (lhs = r), _ => e.$src };\n" ++
        "fun g = () -> u32: ret <kids(quote: 1 * 2)>;\n" ++
        "$main = () {}");
    const result = analyze(arena.allocator(), source);
    try std.testing.expectEqual(0, result.diagnostics.len);
    var classes: [4][128]?struct { Type, u32 } = @splat(@splat(null));
    var line: u32, var character: u32 = .{ 0, 0 };
    for (0..result.data.len / 5) |i| {
        const encoded = result.data[i * 5 ..][0..5];
        line += encoded[0];
        character = if (encoded[0] == 0) character + encoded[1] else encoded[1];
        if (line < 4) classes[line][character] = .{ @enumFromInt(encoded[3]), encoded[4] };
    }
    // line, character, what it is
    // `twice` ran in the pass that expanded it, `unused` never ran
    // `kids` matched only the second alternative, the splice is gone from the last pass
    // a `<` after a splice compares
    const expected = [_]struct { u32, u32, Type }{
        .{ 0, 7, .function },    .{ 0, 25, .parameter },  .{ 0, 45, .macro },
        .{ 0, 52, .macro },      .{ 0, 53, .parameter },  .{ 1, 29, .macro },
        .{ 1, 30, .function },   .{ 1, 43, .parameter },  .{ 1, 45, .macro },
        .{ 1, 47, .operator },   .{ 2, 42, .parameter },  .{ 2, 54, .variable },
        .{ 2, 63, .variable },   .{ 2, 78, .variable },   .{ 2, 83, .function },
        .{ 2, 101, .parameter }, .{ 3, 48, .enumMember }, .{ 3, 58, .variable },
        .{ 3, 61, .variable },   .{ 3, 102, .property },  .{ 3, 108, .variable },
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
