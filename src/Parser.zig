const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Parser = @This();
const lookahead = @import("parser/lookahead.zig");

tokens: SoD(Lexer.Token),
src_bytes: []const u8,
alloc: std.mem.Allocator,
tok_cursor: u32 = 0,
global_store: DynBuf(u32),
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
        else => error.EOF, // TODO detailed errors wrt `tok`
    };

    if ((try self.pop_tok()) != tok) return chosen_error;
}

pub inline fn peek_eq_tok(self: *@This(), comptime tok: Lexer.Token.Kind) !bool {
    return (try self.peek_tok()) == tok;
}

// used for the lookahead tables
pub inline fn invalid_token(_: *@This()) anyerror!u32 {
    return error.InvalidToken;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none);

    while (self.tok_cursor < self.tokens.len()) {
        const is_pub = try self.peek_eq_tok(.kw_pub);
        if (is_pub) self.tok_cursor += 1;
        self.global_store.push(try lookahead.assignment[@intFromEnum(try self.pop_tok())](self, is_pub));
    }
}

pub fn handle_err(self: *@This(), io: std.Io, e: anyerror) noreturn {
    // get text line where error occured:
    const problem_tok_id: u32 = if (self.tok_cursor == 0) 0 else self.tok_cursor - 1;
    const problem_span: Lexer.TextSpan = self.tokens.get_field(.span, problem_tok_id) orelse unreachable;

    var lstart_cur: u32 = problem_span[0];
    while (lstart_cur != 0) {
        if (self.src_bytes[lstart_cur] == '\n') break;

        lstart_cur -= 1;
    }
    lstart_cur += 1;

    var rend_cur: u32 = problem_span[1];
    while (rend_cur != self.src_bytes.len - 1) {
        if (self.src_bytes[rend_cur] == '\n') break;

        rend_cur += 1;
    }

    var lc: u32 = 0;
    for (0..lstart_cur) |i| {
        if (self.src_bytes[i] == '\n') lc += 1;
    }

    var buf: [1024]u8 = undefined;
    var linebuf: [1024]u8 = undefined;
    @memset(linebuf[0 .. problem_span[0] - lstart_cur], ' ');
    @memset(linebuf[problem_span[0] - lstart_cur .. problem_span[1] - lstart_cur], '~');

    const hint: []const u8 = "TODO";

    const err_msg = std.fmt.bufPrint(
        &buf,
        "\x1b[31m{s}\x1b[90m, :{d}, {s}:\x1b[0m\n{s}\n\x1b[36m{s}\x1b[0m\n",
        .{ @errorName(e), lc, hint, self.src_bytes[lstart_cur..rend_cur], linebuf[0 .. problem_span[1] - lstart_cur] },
    ) catch @panic("OOM, could not print error");

    std.Io.File.stdout().writeStreamingAll(io, err_msg) catch @panic("print failed");

    return std.process.exit(1);
}
