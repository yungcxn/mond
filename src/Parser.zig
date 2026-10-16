const std = @import("std");
const StructOfArrays = @import("containers.zig").StructOfArrays;
const DynamicBuffer = @import("containers.zig").DynamicBuffer;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Parser = @This();
const lookahead = @import("parser/lookahead.zig");
const NodeId = ParseTree.NodeId;

tokens: StructOfArrays(Lexer.Token),
src_bytes: []const u8,
alloc: std.mem.Allocator,
tok_cursor: u32 = 0,
// in the head of an if / while / for / match a group right before `{` or `:` is no lambda
head: bool = false,
// in the arguments of a call a comma ends the value, it starts no destructuring assignment
list: bool = false,
// in the pattern of a match arm a quote is no arm itself (`quote: @x + 0 => x`)
pattern: bool = false,
// in a splice `<..>` a `>` closes it, a comparison needs parentheses
angle: bool = false,
global_store: DynamicBuffer(NodeId),
// children of the lists being parsed, nested lists stack above their parents
scratch: DynamicBuffer(NodeId),
tree: ParseTree,

pub fn init(
    alloc: std.mem.Allocator,
    tokens: StructOfArrays(Lexer.Token),
    src_bytes: []const u8,
    span_store: []const Lexer.TextSpan,
) @This() {
    return @This(){
        .alloc = alloc,
        .tokens = tokens,
        .src_bytes = src_bytes,
        .tree = .init(alloc, span_store),
        .global_store = .init(alloc, 1000),
        .scratch = .init(alloc, 256),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
    self.global_store.deinit();
    self.scratch.deinit();
}

// the children of `parent` pushed onto `scratch` since `mark`, they leave the scratch
pub inline fn close(self: *@This(), parent: NodeId, mark: u32) void {
    self.tree.set_children(parent, self.scratch.buffer[mark..self.scratch.len]);
    self.scratch.len = mark;
}

pub inline fn peek_tok(self: *@This()) !Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor) orelse return error.EOF;
}

pub inline fn pop_tok(self: *@This()) !Lexer.Token.Kind {
    const tk = self.tokens.get_field(.tk, self.tok_cursor) orelse return error.EOF;
    self.tok_cursor += 1;
    return tk;
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

pub fn handle_err(self: *@This(), io: std.Io, path: []const u8, e: anyerror) noreturn {
    // get text line where error occured:
    const problem_tok_id: u32 = if (self.tok_cursor == 0) 0 else self.tok_cursor - 1;
    const problem_span: Lexer.TextSpan = self.tokens.get_field(.span, problem_tok_id) orelse unreachable;
    Lexer.print_error(io, path, self.src_bytes, problem_span, @errorName(e));
    return std.process.exit(1);
}
