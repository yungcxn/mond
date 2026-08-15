const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");

tokens: SoD(Lexer.Token), // in
src_bytes: []const u8, //    in
alloc: std.mem.Allocator, // internal
tok_cursor: u32 = 0, //      internal
func_cache: DynBuf(u32), //  out
tree: ParseTree, //          out

pub fn init(
    alloc: std.mem.Allocator,
    tokens: SoD(Lexer.Token),
    src_bytes: []const u8,
) @This() {
    return @This(){
        .alloc = alloc,
        .tokens = tokens,
        .src_bytes = src_bytes,
        .tree = .init(alloc),
        .func_cache = .init(alloc, 1000),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
    self.func_cache.deinit();
}

inline fn peek_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn peek_tok(self: *@This()) ?Lexer.Token {
    return self.tokens.get(self.tok_cursor);
}

inline fn peek_n_tok_kind(self: *@This(), n: comptime_int) ?[n]Lexer.Token.Kind {
    var ret: [n]Lexer.Token.Kind = undefined;
    inline for (0..n) |i| {
        ret[i] = self.tokens.get_field(.tk, self.tok_cursor + @as(u32, i)) orelse return null;
    }

    return ret;
}

inline fn peek_n_tok(self: *@This(), n: comptime_int) ?[n]Lexer.Token {
    var ret: [n]Lexer.Token = undefined;
    inline for (0..n) |i| {
        ret[i] = self.tokens.get(self.tok_cursor + @as(u32, i)) orelse return null;
    }

    return ret;
}

inline fn pop_tok(self: *@This()) ?Lexer.Token {
    defer self.tok_cursor += 1;
    return self.tokens.get(self.tok_cursor);
}

inline fn pop_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    defer self.tok_cursor += 1;
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn realize_span(self: *@This(), span: Lexer.TextSpan) []const u8 {
    return self.src_bytes[span[0]..span[1]];
}

fn eval_stmt(self: *@This()) !u32 {
    const tok = self.pop_tok() orelse return error.EOF;

    var parent_idx: u32 = undefined;

    switch (tok.tk) {
        .@"pct_{" => {
            var staged_children: DynBuf(u32) = .init(self.alloc, 50);
            defer staged_children.deinit();

            parent_idx = self.tree.push_node(.stmt_exec_block);
            while ((self.peek_tok_kind() orelse return error.EOF) != .@"pct_}") {
                staged_children.push(try self.eval_expr(0));
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(parent_idx, staged_children.sliced());
        },
        .kw_if => {
            const ch_expr_idx = try self.eval_expr(0);
            const ch_stmt_idx = try self.eval_stmt();

            if ((self.peek_tok_kind() orelse return error.EOF) == .kw_else) {
                _ = self.pop_tok();
                const alt_ch_stmt_idx = try self.eval_stmt();
                const parent_if_else_idx = self.tree.push_node(.stmt_if_else);
                self.tree.push_extra_childrefs(parent_if_else_idx, &.{ ch_expr_idx, ch_stmt_idx, alt_ch_stmt_idx });
            } else {
                const parent_if_idx = self.tree.push_node(.stmt_if);
                self.tree.set_node_arg0(parent_if_idx, ch_expr_idx);
                self.tree.set_node_arg1(parent_if_idx, ch_stmt_idx);
            }
        },
        .kw_return => {
            parent_idx = self.tree.push_node(.stmt_return);
            const opt_ch_expr_idx = if (try self.could_be_at_expr()) try self.eval_expr(0) else null;
            self.tree.set_node_arg0(parent_idx, if (opt_ch_expr_idx) |idx| idx else 0xFFFFFFFF);
        },
        .kw_mut => parent_idx = try self.eval_expr_or_assign(true, true), // `stmt_mut_untyped_assign` or `stmt_mut_typed_assign`
        else => parent_idx = try self.eval_expr_or_assign(false, false),
    }

    return error.EOF;
}

fn eval_expr_or_assign(self: *@This(), comptime assign_is_mut: bool, comptime exclude_expr_eval: bool) !u32 {
    const tokinfo = try self.eval_identifier_or_typeexpr_or_expr();
    const tok_next = self.peek_tok() orelse return error.EOF;

    var parent_idx: u32 = undefined;

    var ch_identifier_idx: u32 = undefined;
    var ch_expr_idx: u32 = undefined;

    if (tokinfo[1] == 1 or tok_next.tk == .identifier) { // typeexpr or "identifier identifier"
        var ch_typeexpr_idx: u32 = undefined;
        if (tokinfo[1] == 1) {
            ch_typeexpr_idx = tokinfo[0];
        } else if (tokinfo[1] == 0) {
            ch_typeexpr_idx = self.tree.push_node(.typeexpr_type_custom);
            self.tree.set_node_arg0(ch_typeexpr_idx, try self.eval_identifier());
        } else unreachable;

        ch_identifier_idx = try self.eval_identifier();
        if ((self.pop_tok_kind() orelse return error.EOF) != .@"xpct_=") return error.AssignSignAssumed;
        ch_expr_idx = try self.eval_expr(0);

        parent_idx = self.tree.push_node(if (assign_is_mut) .stmt_mut_typed_assign else .stmt_typed_assign);
        self.tree.push_extra_childrefs(parent_idx, &.{ ch_typeexpr_idx, ch_identifier_idx, ch_expr_idx });
    } else if (tokinfo[1] == 0 and tok_next.tk == .@"xpct_=") { // "identifier ="
        self.tok_cursor += 1;
        ch_identifier_idx = tokinfo[0];
        ch_expr_idx = try self.eval_expr(0);

        parent_idx = self.tree.push_node(if (assign_is_mut) .stmt_mut_untyped_assign else .stmt_untyped_assign);
        self.tree.set_node_arg0(parent_idx, ch_identifier_idx);
        self.tree.set_node_arg1(parent_idx, ch_expr_idx);
    } else if (!exclude_expr_eval and tokinfo[1] == 2) {
        return tokinfo[0]; // expr was already evaluated
    } else if (!exclude_expr_eval and tokinfo[1] == 0 and tok_next.tk == .@"pct_(") { // "identifier("
        self.tok_cursor -= 1; // cursor is now back at "identifier" where next is guaranteed "("
        return self.eval_expr(0);
    } else return error.InvalidSyntax;

    return parent_idx;
}

// pushes either
// A): if its just an identifier -> identifier, and that could be possibly a typeexpr
// B): if it starts with type-specific characters -> typeexpr
// C): if it starts with expr-specific characters -> expr
inline fn eval_identifier_or_typeexpr_or_expr(self: *@This()) !struct { u32, u8 } {
    const tok = self.peek_tok_kind() orelse return error.EOF;
    if (tok == .identifier) {
        return .{ try self.eval_identifier(), 0 };
    } else if (try self.could_be_at_typeexpr()) {
        return .{ try self.eval_typeexpr(), 1 };
    } else if (try self.could_be_at_expr()) {
        return .{ try self.eval_expr(0), 2 };
    } else return error.InvalidSyntax;
}

// pushes either
// A): if its just an identifier -> identifier, and that could be possibly a typeexpr
// B): if it starts with type-specific characters -> typeexpr
// inline fn eval_identifier_or_typeexpr(self: *@This()) !struct { u32, bool } {
//     const tok = self.peek_tok_kind() orelse return error.EOF;
//     return if (tok == .identifier) .{ try self.eval_identifier(), false } else .{ try self.eval_typeexpr(), true };
// }

// - tries always to push a full expr or nothing
// - just checking if tok0 is an identifier is not enough as there may come postfix/binary ops after
inline fn could_be_at_expr(self: *@This()) !bool {
    const tok = self.peek_tok_kind() orelse return error.EOF;

    return tok == .@"pct_(" or
        (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] == .none) or
        (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] == .none);
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_expr(self: *@This(), depth: u32) anyerror!u32 {
    const tok = self.pop_tok() orelse return error.EOF;

    var left_idx: u32 = undefined;

    if (tok.tk == .@"pct_(") {
        // nested () just recurses into ourselves at min_prec 0
        left_idx = self.tree.push_node(.expr_paren);
        self.tree.set_node_arg0(left_idx, try eval_expr(self, 0));
        if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_)") return error.MissingEnclosingParen;
    } else if (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)] != .none) {
        left_idx = self.tree.push_node(ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)]);
        self.tree.set_node_arg0(left_idx, try eval_expr(self, 0));
    } else if (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok.tk)] != .none) {
        left_idx = self.tree.push_data_node(ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)], self.realize_span(tok.span));
    } else return error.SyntaxError;

    while (true) {
        const next_tok = self.peek_tok_kind() orelse break;

        if (next_tok == .@"pct_[") { // postfix indexing: expr[expr]
            self.tok_cursor += 1;

            const index_node_idx = self.tree.push_node(.expr_indexed);
            const right_idx = try eval_expr(self, 0); // inner expr, fresh precedence

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_]") return error.ClosingBracketAssumed;

            self.tree.set_node_arg0(index_node_idx, left_idx);
            self.tree.set_node_arg1(index_node_idx, right_idx);

            left_idx = index_node_idx;
            continue;
        } else if (next_tok == .@"pct_(") { // postfix funccall: expr[expr]
            self.tok_cursor += 1;

            const index_node_idx = self.tree.push_node(.expr_funccall);
            const right_idx = if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_)") 0xFFFFFFFF else try self.eval_param_calltuple();

            self.tree.set_node_arg0(index_node_idx, left_idx);
            self.tree.set_node_arg1(index_node_idx, right_idx);

            left_idx = index_node_idx;
            continue;
        }

        const bin_lookup = ParseTree.Node.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
        if (bin_lookup.nt == .none) break;
        if (bin_lookup.prec < depth) break;

        // op consumption
        self.tok_cursor += 1;

        const op_node_idx = self.tree.push_node(bin_lookup.nt);
        const right_idx = try eval_expr(self, bin_lookup.prec + 1);

        self.tree.set_node_arg0(op_node_idx, left_idx);
        self.tree.set_node_arg1(op_node_idx, right_idx);

        left_idx = op_node_idx;
    }

    return left_idx;
}

inline fn could_be_at_typeexpr(self: *@This()) !bool {
    const tok = self.peek_tok_kind() orelse return error.EOF;

    return tok == .identifier or
        tok == .@"xpct_*" or
        tok == .@"xpct_&" or
        tok == .@"pct_[" or
        ParseTree.Node.tok_to_typeexpr[@intFromEnum(tok)] != .none;
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// also assumed: this func is not used if the token cursor is on a optionally given type
fn eval_typeexpr(self: *@This()) !u32 {
    const tok_a = self.pop_tok() orelse return error.EOF;

    if (tok_a.tk == .identifier) {
        const id = self.tree.push_node(.typeexpr_type_custom);
        self.tree.set_node_arg0(id, try self.eval_identifier());
        return id;
    }

    const typeexpr_lookup = ParseTree.Node.tok_to_typeexpr[@intFromEnum(tok_a.tk)];
    if (typeexpr_lookup != .none) return self.tree.push_node(typeexpr_lookup);

    var parent_idx: u32 = 0;
    switch (tok_a.tk) {
        .@"xpct_*" => parent_idx = self.tree.push_node(.typeexpr_builtin_pointer),
        .@"xpct_&" => parent_idx = self.tree.push_node(.typeexpr_builtin_constpointer),
        .@"pct_[" => {
            parent_idx = self.tree.push_node(.typeexpr_builtin_array);
            const next_tok = self.peek_tok_kind() orelse return error.EOF;
            self.tree.set_node_arg1(parent_idx, if (next_tok == .@"pct_]") 0xFFFFFFFF else try self.eval_expr(0));
        },
        else => return error.InvalidTypeTok,
    }

    self.tree.set_node_arg0(parent_idx, try self.eval_typeexpr());
    return parent_idx;
}

inline fn eval_param_calltuple(self: *@This()) anyerror!u32 {
    const deftuple_node_idx = self.tree.push_node(.param_calltuple);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyParameters;

        children_idxs[paramc] = try self.eval_expr(0);
        paramc += 1;

        switch (self.pop_tok_kind() orelse return error.EOF) {
            .@"pct_)" => break,
            .@"pct_," => {
                if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_)") {
                    break;
                } else {
                    continue;
                }
            },
            else => return error.ArgumentDefSepAssumed,
        }
    }

    self.tree.push_extra_childrefs(deftuple_node_idx, &children_idxs);

    return deftuple_node_idx;
}

// assumed: `tok_cursor` is at first relevant token of a `param_deftuple`, which is '('+1
inline fn eval_param_deftuple(self: *@This()) !u32 {
    const deftuple_node_idx = self.tree.push_node(.param_deftuple);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyArguments;

        const defsingle_node_idx = self.tree.push_node(.param_defsingle);
        children_idxs[paramc] = defsingle_node_idx;
        paramc += 1;

        const child_type_idx = try self.eval_typeexpr();
        const child_identifier_idx = try self.eval_identifier();
        self.tree.set_node_arg0(defsingle_node_idx, child_type_idx);
        self.tree.set_node_arg1(defsingle_node_idx, child_identifier_idx);

        switch (self.pop_tok_kind() orelse return error.EOF) {
            .@"pct_)" => break,
            .@"pct_," => {
                if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_)") {
                    break;
                } else {
                    continue;
                }
            },
            else => return error.ArgumentDefSepAssumed,
        }
    }

    self.tree.push_extra_childrefs(deftuple_node_idx, &children_idxs);

    return deftuple_node_idx;
}

inline fn eval_identifier(self: *@This()) !u32 {
    const next_tok = self.pop_tok() orelse return error.EOF;
    if (next_tok.tk != .identifier) return error.IdentifierAssumed;
    return self.tree.push_data_node(.expr_identifier, self.realize_span(next_tok.span));
}

// assumed: `tok_cursor` is at first relevant token of a `func_def`
//   and must exit on cursor being on first token outside of func `exec_block`
// -> `false`: no new func generated
fn eval_func(self: *@This()) !u32 {
    // func "header":
    const cursor_before = self.tok_cursor;
    const tok_a = self.pop_tok() orelse return error.EOF;
    const tok_b = self.pop_tok() orelse return error.EOF;

    const func_node_idx = self.tree.push_node(.func_def);

    // type, identifier, param_deftuple, stmt
    var children_idxs: [4]u32 = undefined;

    if (tok_a.tk == .identifier and tok_b.tk == .@"pct_(") {
        // func def without type
        children_idxs[0] = self.tree.push_node(.none);
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, self.realize_span(tok_a.span));
    } else {
        self.tok_cursor = cursor_before;
        children_idxs[0] = try self.eval_typeexpr();
        children_idxs[1] = try self.eval_identifier();
    }

    // cursor should be on '(' token
    const tok_c = self.pop_tok_kind() orelse return error.EOF;
    const tok_d = self.pop_tok_kind() orelse return error.EOF;

    if (tok_c != .@"pct_(") return error.OpenParenAssumed;

    if (tok_d == .@"pct_)") {
        children_idxs[2] = 0xFFFFFFFF;
    } else {
        // needs cursor to be +1 after '(', so we -1 since we were on '('+1
        self.tok_cursor -= 1;
        children_idxs[2] = try self.eval_param_deftuple();
    }
    children_idxs[3] = try self.eval_stmt();

    self.tree.push_extra_childrefs(func_node_idx, &children_idxs);

    return func_node_idx;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none); // sentinel to correctly understand argi=0

    // first token guaranteed to be "func_def-relevant"
    while (self.tok_cursor < self.tokens.len()) {
        self.func_cache.push(try self.eval_func());
    }
}
