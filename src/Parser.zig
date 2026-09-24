const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Parser = @This();
const lookahead = @import("parser/lookahead.zig");
const NodeId = ParseTree.NodeId;

tokens: SoD(Lexer.Token),
src_bytes: []const u8,
alloc: std.mem.Allocator,
tok_cursor: u32 = 0,
global_store: DynBuf(NodeId),
tree: ParseTree,

pub fn init(
    alloc: std.mem.Allocator,
    tokens: SoD(Lexer.Token),
    src_bytes: []const u8,
    span_store: []const Lexer.TextSpan,
) @This() {
    return @This(){
        .alloc = alloc,
        .tokens = tokens,
        .src_bytes = src_bytes,
        .tree = .init(alloc, span_store),
        .global_store = .init(alloc, 1000),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
    self.global_store.deinit();
}

pub inline fn peek_tok(self: *@This()) !Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor) orelse return error.EOF;
}

pub inline fn pop_tok(self: *@This()) !Lexer.Token.Kind {
    defer self.tok_cursor += 1;
    return self.tokens.get_field(.tk, self.tok_cursor) orelse return error.EOF;
}

pub inline fn eat_assert_tok(self: *@This(), comptime tok: Lexer.Token.Kind) !void {
    const chosen_error: anyerror = comptime switch (tok) {
        .@"pct_(" => error.ExpectedOpeningParen,
        .@"pct_)" => error.ExpectedClosingParen,
        .@"pct_]" => error.ExpectedClosingBracket,
        .@"pct_{" => error.ExpectedOpeningBrace,
        .@"pct_}" => error.ExpectedClosingBrace,
        .@"pct_," => error.ExpectedComma,
        .@"pct_;" => error.ExpectedSemicolon,
        .@"xpct_=" => error.ExpectedAssign,
        .@"xpct_=>" => error.ExpectedMatchArrow,
        .@"xpct_!{" => error.ExpectedTraitBody,
        .identifier => error.ExpectedIdentifier,
        .kw_deinit => error.ExpectedDeinit,
        else => error.UnexpectedToken,
    };

    if ((try self.pop_tok()) != tok) return chosen_error;
}

pub inline fn peek_eq_tok(self: *@This(), comptime tok: Lexer.Token.Kind) !bool {
    return (try self.peek_tok()) == tok;
}

pub inline fn prev_eq_tok(self: *@This(), comptime tok: Lexer.Token.Kind) bool {
    if (self.tok_cursor == 0) return false;
    return (self.tokens.get_field(.tk, self.tok_cursor - 1) orelse return false) == tok;
}

pub inline fn eat_stmt_end(self: *@This()) !void {
    if (self.tok_cursor < self.tokens.len() and (try self.peek_tok()) == .@"pct_;") {
        self.tok_cursor += 1;
        return;
    }

    if (!self.prev_eq_tok(.@"pct_}")) return error.ExpectedSemicolon;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none);

    while (self.tok_cursor < self.tokens.len()) {
        const node_parent = try @import("parser/eval.zig").any(self, .allow_assign, 0);
        self.global_store.push(node_parent);
        try self.eat_stmt_end();
    }
}

pub fn handle_err(self: *@This(), io: std.Io, e: anyerror) noreturn {
    // get text line where error occured:
    const problem_tok_id: u32 = if (self.tok_cursor == 0) 0 else self.tok_cursor - 1;
    const problem_span: Lexer.TextSpan = self.tokens.get_field(.span, problem_tok_id) orelse unreachable;

    const src_len: u32 = @intCast(self.src_bytes.len);

    var lstart_cur: u32 = @min(problem_span[0], src_len);
    while (lstart_cur != 0) {
        if (self.src_bytes[lstart_cur - 1] == '\n') break;

        lstart_cur -= 1;
    }

    var rend_cur: u32 = @min(@max(problem_span[1], lstart_cur), src_len);
    while (rend_cur != src_len) {
        if (self.src_bytes[rend_cur] == '\n') break;

        rend_cur += 1;
    }

    var lc: u32 = 1;
    for (self.src_bytes[0..lstart_cur]) |b| {
        if (b == '\n') lc += 1;
    }

    var buf: [4096]u8 = undefined;
    var linebuf: [1024]u8 = undefined;
    const mark_start = @min(problem_span[0] -| lstart_cur, @as(u32, linebuf.len));
    const mark_end = @min(@max(problem_span[1] -| lstart_cur, mark_start + 1), @as(u32, linebuf.len));
    @memset(linebuf[0..mark_start], ' ');
    @memset(linebuf[mark_start..mark_end], '~');

    const hint: []const u8 = "TODO";

    const err_msg = std.fmt.bufPrint(
        &buf,
        "\x1b[31m{s}\x1b[90m, :{d}, {s}:\x1b[0m\n{s}\n\x1b[36m{s}\x1b[0m\n",
        .{ @errorName(e), lc, hint, self.src_bytes[lstart_cur..rend_cur], linebuf[0..mark_end] },
    ) catch @panic("OOM, could not print error");

    std.Io.File.stdout().writeStreamingAll(io, err_msg) catch @panic("print failed");

    return std.process.exit(1);
}
