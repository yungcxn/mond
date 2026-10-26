const std = @import("std");
const StructOfArrays = @import("containers.zig").StructOfArrays;
const DynamicBuffer = @import("containers.zig").DynamicBuffer;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const Parser = @This();
pub const lookahead = @import("parser/lookahead.zig");
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
// in the right side of `A -- B` the next `--` belongs to the left: `A -- A.x -- A.y`
difference: bool = false,
// in the editor a statement that doesn't parse becomes a `hole` and parsing goes on after it, its
// error kept here
recover: bool = false,
errors: std.ArrayList(struct { token: u32, err: anyerror }) = .empty,
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
        self.global_store.push(try self.statement(false));
    }
}

// a statement of the file or of a block, when recovering a `hole` where it doesn't parse
pub fn statement(self: *@This(), in_block: bool) !NodeId {
    const eval = @import("parser/eval.zig");
    if (!self.recover) {
        const node = try eval.any(self, .allow_assign, 0);
        try self.eat_stmt_end();
        return node;
    }
    const mark = self.scratch.len;
    const start = self.tok_cursor;
    const parsed: anyerror!NodeId = blk: {
        const node = eval.any(self, .allow_assign, 0) catch |err| break :blk err;
        self.eat_stmt_end() catch |err| break :blk err;
        break :blk node;
    };
    const err = if (parsed) |node| return node else |err| err;
    self.scratch.len = mark;
    const last_token: u32 = @intCast(self.tokens.len() -| 1);
    const token = @min(self.tok_cursor -| 1, last_token);
    self.errors.append(self.alloc, .{ .token = token, .err = err }) catch @panic("OOM");

    // on past its `;` outside the braces it opens, or up to the `}` of the block it is in, or to
    // a line starting no further in than it did (a bracket may be what is broken)
    const kinds = self.tokens.column(.tk);
    const spans = self.tokens.column(.span);
    var start_column: ?u32 = null;
    var braces: u32 = 0;
    var at = start;
    while (at < kinds.len) : (at += 1) {
        // the column of a token starting its line, null for one after others on its line
        const offset = spans[at][0];
        const column: ?u32 = column: {
            var line_start = offset;
            while (line_start > 0) : (line_start -= 1) switch (self.src_bytes[line_start - 1]) {
                '\n' => break,
                ' ', '\t' => {},
                else => break :column null,
            };
            break :column offset - line_start;
        };
        if (at == start) start_column = column;
        const outdents = start_column != null and column != null and column.? <= start_column.?;
        if (at > start and outdents) break;
        switch (kinds[at]) {
            .@"pct_{", .@"xpct_!{" => braces += 1,
            .@"pct_}" => if (braces > 0) {
                braces -= 1;
            } else if (in_block) break,
            .@"pct_;" => if (braces == 0) {
                at += 1;
                break;
            },
            else => {},
        }
    }
    self.tok_cursor = @max(at, start + 1);
    if (in_block and at < kinds.len and kinds[at] == .@"pct_}") self.tok_cursor = at;
    return self.tree.push_node(.hole);
}

pub fn handle_err(self: *@This(), io: std.Io, path: []const u8, e: anyerror) noreturn {
    // get text line where error occured:
    const problem_tok_id: u32 = if (self.tok_cursor == 0) 0 else self.tok_cursor - 1;
    const problem_span: Lexer.TextSpan = self.tokens.get_field(.span, problem_tok_id) orelse unreachable;
    Lexer.print_error(io, path, self.src_bytes, problem_span, @errorName(e));
    return std.process.exit(1);
}
