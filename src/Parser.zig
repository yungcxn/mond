const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");

tokens: SoD(Lexer.Token), // in
src_bytes: []const u8, //    in
tok_cursor: u32 = 0, //      internal
tree: ParseTree, //          out

pub fn init(
    alloc: std.mem.Allocator,
    tokens: SoD(Lexer.Token),
    src_bytes: []const u8,
) @This() {
    return @This(){
        .tokens = tokens,
        .src_bytes = src_bytes,
        .tree = .init(alloc),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
}

inline fn peek_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor);
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

    switch (tok.tk) {
        // .@"pct_{" => {
        //     const parent_exec_block_idx = self.tree.push_node(.stmt_exec_block);
        //     while (true) {
        //         const child_stmt_idx = try self.eval_expr();
        //         self.tree.new_extra_childref(parent_exec_block_idx, child_stmt_idx);

        //         const peeked = self.peek_tok_kind() orelse return error.EOF;
        //         if (peeked == .@"pct_}") break;
        //     }
        // },
        .kw_if => {
            const child_expr_idx = try self.eval_expr();
            const child_stmt_idx = try self.eval_stmt();

            const peeked = self.peek_tok_kind() orelse return error.EOF;
            if (peeked == .kw_else) {
                _ = self.pop_tok();
                const alt_child_stmt_idx = try self.eval_stmt();
                const parent_if_else_idx = self.tree.push_node(.stmt_if_else);
                self.tree.push_extra_childrefs(parent_if_else_idx, 3, .{ child_expr_idx, child_stmt_idx, alt_child_stmt_idx });
            } else {
                const parent_if_idx = self.tree.push_node(.stmt_if);
                self.tree.set_node_arg0(parent_if_idx, child_expr_idx);
                self.tree.set_node_arg1(parent_if_idx, child_stmt_idx);
            }
        },
        else => { // assign or call statement
            if (tok.tk == .kw_mut) {}
            // TODO
        },
    }

    return error.EOF;
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_expr(self: *@This()) !u32 {
    const P = @TypeOf(self);

    const prec_parse = struct {
        pub fn prec_parse(self_: P, min_prec: u32) !u32 {
            const tok = self_.pop_tok() orelse return error.EOF;

            var left_idx: u32 = undefined;

            if (tok.tk == .@"pct_(") {
                // nested () just recurses into ourselves at min_prec 0
                const paren_node_idx = self_.tree.push_node(.expr_paren);
                left_idx = try prec_parse(self_, 0);

                self_.tree.set_node_arg0(paren_node_idx, left_idx);
                left_idx = paren_node_idx;

                const tok_close = self_.pop_tok_kind() orelse return error.EOF;
                if (tok_close != .@"pct_)") return error.MissingEnclosingParen;
            } else if (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)] != .none) {
                const unary_nt = ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)];
                const unary_node_idx = self_.tree.push_node(unary_nt);
                const child_idx = try prec_parse(self_, 0);

                self_.tree.set_node_arg0(unary_node_idx, child_idx);
                left_idx = unary_node_idx;
            } else {
                const data_nt = ParseTree.Node.tok_to_expr_data[@intFromEnum(tok.tk)];
                if (data_nt == .none) return error.SyntaxError;
                left_idx = self_.tree.push_data_node(data_nt, self_.realize_span(tok.span));
            }

            while (true) {
                const next_tok = self_.peek_tok_kind() orelse break;
                const bin_lookup = ParseTree.Node.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
                if (bin_lookup.nt == .none) break;
                if (bin_lookup.prec < min_prec) break;

                // op consumption
                self_.tok_cursor += 1;

                const op_node_idx = self_.tree.push_node(bin_lookup.nt);
                const right_idx = try prec_parse(self_, bin_lookup.prec + 1);

                self_.tree.set_node_arg0(op_node_idx, left_idx);
                self_.tree.set_node_arg1(op_node_idx, right_idx);

                left_idx = op_node_idx;
            }

            return left_idx;
        }
    }.prec_parse;

    return prec_parse(self, 0);
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// also assumed: this func is not used if the token cursor is on a optionally given type
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_type(self: *@This()) !u32 {
    var first_node_idx: ?u32 = null;
    var last_parent_idx: ?u32 = null;
    var done: bool = false;

    while (true) {
        const tok = self.pop_tok() orelse return error.SyntaxError;
        var new_child_idx: u32 = undefined;
        switch (tok.tk) {
            .@"xpct_*" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_pointer);
            },
            .@"xpct_&" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_constpointer);
            },
            .@"pct_[" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_array);
                const next_tok = self.peek_tok_kind() orelse return error.EOF;
                if (next_tok == .@"pct_]") {
                    self.tree.set_node_arg1(new_child_idx, 0xFFFFFFFF);
                } else {
                    const expr_node_idx = try self.eval_expr();
                    self.tree.set_node_arg1(new_child_idx, expr_node_idx);
                }
            },
            .kw_u32 => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_u32);
                done = true;
            },
            .identifier => {
                new_child_idx = self.tree.push_node(.typeexpr_type_custom);

                const child_child_idx = self.tree.push_data_node(.expr_identifier, self.realize_span(tok.span));

                self.tree.set_node_arg0(new_child_idx, child_child_idx);
                self.tree.set_node_arg0(new_child_idx, 0xFFFFFFFF);
                done = true;
            },
            else => return error.SyntaxError,
        }
        if (first_node_idx == null) first_node_idx = new_child_idx;
        if (last_parent_idx != null) self.tree.set_node_arg0(last_parent_idx.?, new_child_idx);
        if (done) return first_node_idx.?;

        last_parent_idx = new_child_idx;
    }
}

// assumed: `tok_cursor` is at first relevant token of a `param_deftuple`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_param_deftuple(self: *@This()) !u32 {
    const tok0 = self.pop_tok() orelse return error.EOF;

    if (tok0.tk != .@"pct_(") return error.ParenAssumed;

    const deftuple_node_idx = self.tree.push_node(.param_deftuple);
    self.tree.set_node_arg0(deftuple_node_idx, 0xFFFFFFFF);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (self.peek_tok_kind() == .@"pct_)") break;

        const defsingle_node_idx = self.tree.push_node(.param_defsingle);
        children_idxs[paramc] = defsingle_node_idx;
        paramc += 1;

        const child_type_idx = try self.eval_type();

        const next_tok = self.pop_tok() orelse return error.EOF;
        if (next_tok.tk != .identifier) return error.IdentifierAssumed;
        const child_identifier_idx = self.tree.push_data_node(.expr_identifier, self.realize_span(next_tok.span));

        self.tree.set_node_arg0(defsingle_node_idx, child_type_idx);
        self.tree.set_node_arg1(defsingle_node_idx, child_identifier_idx);
    }

    return deftuple_node_idx;
}

// assumed: `tok_cursor` is at first relevant token of a `func_def`
//   and must exit on cursor being on first token outside of func `exec_block`
// -> `false`: no new func generated
fn eval_func(self: *@This()) !bool {
    // func "header":
    const tok_cursor_save = self.tok_cursor;
    const peeked_tok0 = self.pop_tok() orelse return false;
    const peeked_tok1 = self.pop_tok() orelse return error.EOF; // "func name" or "("
    self.tok_cursor = tok_cursor_save;

    const func_node_idx = self.tree.push_node(.func_def);

    // type, identifier, param_deftuple, stmt
    var children_idxs: [4]u32 = undefined;

    if (peeked_tok0.tk == .identifier and peeked_tok1.tk == .@"pct_(") {
        // untyped, funcxxx(...)
        children_idxs[0] = self.tree.push_node(.none);
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, self.realize_span(peeked_tok0.span));
    } else {
        // typed, typexxx funcxxx(...)
        children_idxs[0] = try self.eval_type();

        const next_tok = self.pop_tok() orelse return error.EOF;
        if (next_tok.tk != .identifier) return error.IdentifierAssumed;
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, self.realize_span(next_tok.span));
    }

    // cursor should be on '(' token
    children_idxs[2] = try self.eval_param_deftuple();
    children_idxs[3] = try self.eval_stmt();

    self.tree.push_extra_childrefs(func_node_idx, 4, children_idxs);

    return true;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none); // sentinel to correctly understand argi=0

    // first token guaranteed to be "func_def-relevant"
    while (try self.eval_func()) {}
}
