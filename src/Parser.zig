const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");

tokens: SoD(Lexer.Token),
src_bytes: []const u8,
alloc: std.mem.Allocator,
tok_cursor: u32 = 0,
func_cache: DynBuf(u32),
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
        .func_cache = .init(alloc, 1000),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
    self.func_cache.deinit();
}

inline fn peek_tok(self: *@This()) ?Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn pop_tok(self: *@This()) ?Lexer.Token.Kind {
    defer self.tok_cursor += 1;
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn eat_assert_tok(self: *@This(), comptime tok: Lexer.Token.Kind) !void {
    const chosen_error: anyerror = comptime switch (tok) {
        else => error.EOF, // TODO detailed errors wrt `tok`
    };

    if ((self.pop_tok() orelse return error.EOF) != tok) return chosen_error;
}

inline fn peek_eq_tok(self: *@This(), comptime tok: Lexer.Token.Kind) !bool {
    return (self.peek_tok() orelse return error.EOF) == tok;
}

inline fn eval_helper_loop(self: *@This(), comptime statemented: bool) anyerror!u32 {
    var parent_idx: u32 = 0;

    var ch_expr_b_idx: ?u32 = null;

    if (try self.peek_eq_tok(.@"pct_(")) {
        self.tok_cursor += 1;

        ch_expr_b_idx = try self.eval_expr(0);

        try self.eat_assert_tok(.@"pct_)");
    }

    const nk: ParseTree.Node.Kind = if (ch_expr_b_idx != null)
        (if (statemented) .stmt_loop_ext else .expr_loop_ext)
    else
        (if (statemented) .stmt_loop else .expr_loop);

    parent_idx = self.tree.push_node(nk);
    self.tree.set_node_arg0(parent_idx, if (ch_expr_b_idx) |b_idx| b_idx else 0xFFFFFFFF);
    self.tree.set_node_arg1(parent_idx, if (statemented) try self.eval_stmt() else try self.eval_expr(0));

    return parent_idx;
}

inline fn eval_helper_for_while(self: *@This(), comptime for_for: bool, comptime statemented: bool) anyerror!u32 {
    var parent_idx: u32 = 0;

    try self.eat_assert_tok(.@"pct_(");
    const ch_expr_a_idx = try self.eval_expr(0);
    var ch_expr_b_idx: ?u32 = null;
    if (try self.peek_eq_tok(.@"pct_:")) {
        self.tok_cursor += 1;

        ch_expr_b_idx = try self.eval_expr(0);
    }
    try self.eat_assert_tok(.@"pct_)");

    const ch_to_exec_idx = if (statemented) try self.eval_stmt() else try self.eval_expr(0);

    if (ch_expr_b_idx) |b_idx| {
        const nk: ParseTree.Node.Kind = if (for_for)
            (if (statemented) .stmt_for_ext else .expr_for_ext)
        else
            (if (statemented) .stmt_while_ext else .expr_while_ext);

        parent_idx = self.tree.push_node(nk);
        self.tree.push_extra_childrefs(parent_idx, &.{ ch_expr_a_idx, b_idx, ch_to_exec_idx });
    } else {
        const nk: ParseTree.Node.Kind = if (for_for)
            (if (statemented) .stmt_for else .expr_for)
        else
            (if (statemented) .stmt_while else .expr_while);

        parent_idx = self.tree.push_node(nk);
        self.tree.set_node_arg0(parent_idx, ch_expr_a_idx);
        self.tree.set_node_arg1(parent_idx, ch_to_exec_idx);
    }
    return parent_idx;
}

inline fn eval_helper_match(self: *@This(), comptime statemented: bool) !u32 {
    const parent_idx = self.tree.push_node(if (statemented) .stmt_match else .expr_match);

    try self.eat_assert_tok(.@"pct_(");
    self.tree.set_node_arg0(parent_idx, try self.eval_expr(0));
    try self.eat_assert_tok(.@"pct_)");

    const ch_block_idx = self.tree.push_node(.match_block);
    self.tree.set_node_arg1(parent_idx, ch_block_idx);

    try self.eat_assert_tok(.@"pct_{");

    var children_idxs: [512]u32 = undefined;
    var childc: u32 = 0;

    while (true) {
        if (childc >= children_idxs.len) return error.TooManyMatchCases;

        children_idxs[childc] = self.tree.push_node(.match_case);

        var case_ch_idx = try self.eval_expr(0);
        if (try self.peek_eq_tok(.@"pct_,")) {
            case_ch_idx = try self.eval_tuple_exprs(case_ch_idx, .@"xpct_=>");
            self.tok_cursor += 1;
        } else {
            try self.eat_assert_tok(.@"xpct_=>");
        }
        self.tree.set_node_arg0(children_idxs[childc], case_ch_idx);

        self.tree.set_node_arg1(children_idxs[childc], if (statemented) try self.eval_stmt() else try self.eval_expr(0));
        childc += 1;

        const tok_after_matchcase = self.peek_tok() orelse return error.EOF;
        switch (tok_after_matchcase) {
            .@"pct_," => {
                self.tok_cursor += 1;

                if (try self.peek_eq_tok(.@"pct_}")) break;
            },
            .@"pct_}" => break,
            else => return error.CommaOrBlockEndAssumed,
        }
    }

    self.tok_cursor += 1;
    self.tree.push_extra_childrefs(ch_block_idx, children_idxs[0..childc]);
    return parent_idx;
}

fn eval_stmt(self: *@This()) anyerror!u32 {
    var parent_idx: u32 = undefined;

    switch (self.pop_tok() orelse return error.EOF) {
        .@"pct_{" => {
            var children_idxs: [512]u32 = undefined;
            var childc: u32 = 0;

            parent_idx = self.tree.push_node(.stmt_exec_block);
            while (!try self.peek_eq_tok(.@"pct_}")) {
                if (childc >= children_idxs.len) return error.TooManySubstatements;
                children_idxs[childc] = try self.eval_stmt();
                childc += 1;
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(parent_idx, children_idxs[0..childc]);
        },
        .kw_if => {
            try self.eat_assert_tok(.@"pct_(");
            const ch_expr_idx = try self.eval_expr(0);
            try self.eat_assert_tok(.@"pct_)");
            const ch_stmt_idx = try self.eval_stmt();

            if (try self.peek_eq_tok(.kw_else)) {
                self.tok_cursor += 1;
                const alt_ch_stmt_idx = try self.eval_stmt();
                parent_idx = self.tree.push_node(.stmt_if_else);
                self.tree.push_extra_childrefs(parent_idx, &.{ ch_expr_idx, ch_stmt_idx, alt_ch_stmt_idx });
            } else {
                parent_idx = self.tree.push_node(.stmt_if);
                self.tree.set_node_arg0(parent_idx, ch_expr_idx);
                self.tree.set_node_arg1(parent_idx, ch_stmt_idx);
            }
        },
        .kw_match => parent_idx = try self.eval_helper_match(true),
        .kw_for => parent_idx = try self.eval_helper_for_while(true, true),
        .kw_while => parent_idx = try self.eval_helper_for_while(false, true),
        .kw_loop => parent_idx = try self.eval_helper_loop(true),
        .kw_cont => parent_idx = self.tree.push_node(.stmt_cont),
        .kw_brk => parent_idx = self.tree.push_node(.stmt_brk),
        .kw_defer => {
            parent_idx = self.tree.push_node(.stmt_defer);
            self.tree.set_node_arg0(parent_idx, try self.eval_stmt());
        },
        .kw_deinit => {
            parent_idx = self.tree.push_node(.stmt_deinit);
            self.tree.set_node_arg0(parent_idx, try self.eval_expr(0));
        },
        .kw_return => {
            parent_idx = self.tree.push_node(.stmt_return);
            self.tree.set_node_arg0(parent_idx, if (try self.could_be_at_expr()) try self.eval_expr(0) else 0xFFFFFFFF);
        },
        .kw_mut => parent_idx = try self.eval_helper_expr_or_assign(true, true),
        else => {
            self.tok_cursor -= 1;
            parent_idx = try self.eval_helper_expr_or_assign(false, false);
        },
    }

    return parent_idx;
}

fn eval_helper_expr_or_assign(self: *@This(), comptime assign_is_mut: bool, comptime exclude_expr_eval: bool) !u32 {
    const cursor_start = self.tok_cursor;
    const tokinfo = try self.eval_identifier_or_typeexpr_or_expr();
    const tok_next = self.peek_tok() orelse return error.EOF;

    var parent_idx: u32 = undefined;
    var ch_identifier_idx: u32 = undefined;
    var ch_expr_idx: u32 = undefined;

    if (tokinfo[1] == 1 or (tokinfo[1] == 0 and tok_next == .identifier)) {
        var ch_typeexpr_idx: u32 = undefined;
        if (tokinfo[1] == 1) {
            ch_typeexpr_idx = tokinfo[0];
        } else {
            ch_typeexpr_idx = self.tree.push_node(.typeexpr_type_custom);
            self.tree.set_node_arg0(ch_typeexpr_idx, tokinfo[0]);
        }

        ch_identifier_idx = try self.eval_identifier();

        try self.eat_assert_tok(.@"xpct_=");

        ch_expr_idx = try self.eval_expr(0);

        parent_idx = self.tree.push_node(if (assign_is_mut) .stmt_mut_typed_assign else .stmt_typed_assign);
        self.tree.push_extra_childrefs(parent_idx, &.{ ch_typeexpr_idx, ch_identifier_idx, ch_expr_idx });
    } else if (tokinfo[1] == 0) {
        ch_identifier_idx = tokinfo[0];

        while (true) ch_identifier_idx = (try self.eval_helper_postfix_step(ch_identifier_idx, false)) orelse break;

        const after_target = self.peek_tok() orelse return error.EOF;

        if (after_target == .@"xpct_=") {
            self.tok_cursor += 1;
            ch_expr_idx = try self.eval_expr(0);

            parent_idx = self.tree.push_node(if (assign_is_mut) .stmt_mut_untyped_assign else .stmt_untyped_assign);
            self.tree.set_node_arg0(parent_idx, ch_identifier_idx);
            self.tree.set_node_arg1(parent_idx, ch_expr_idx);
        } else if (!exclude_expr_eval) {
            self.tok_cursor = cursor_start;
            return self.eval_expr(0);
        } else return error.InvalidSyntax;
    } else if (!exclude_expr_eval and tokinfo[1] == 2) {
        return tokinfo[0];
    } else return error.InvalidSyntax;

    return parent_idx;
}

inline fn eval_identifier_or_typeexpr_or_expr(self: *@This()) !struct { u32, u8 } {
    const tok = self.peek_tok() orelse return error.EOF;
    if (tok == .identifier) {
        return .{ try self.eval_identifier(), 0 };
    } else if (try self.could_be_at_typeexpr()) {
        return .{ try self.eval_typeexpr(), 1 };
    } else if (try self.could_be_at_expr()) {
        return .{ try self.eval_expr(0), 2 };
    } else return error.InvalidSyntax;
}

inline fn could_be_at_expr(self: *@This()) !bool {
    const tok = self.peek_tok() orelse return error.EOF;

    return tok == .@"pct_(" or
        tok == .kw_true or
        tok == .kw_false or
        (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] != .none) or
        (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] != .none);
}

inline fn could_be_at_typeexpr(self: *@This()) !bool {
    const tok = self.peek_tok() orelse return error.EOF;

    return tok == .identifier or
        tok == .@"xpct_*" or
        tok == .@"xpct_&" or
        tok == .@"pct_[" or
        ParseTree.Node.tok_to_typeexpr[@intFromEnum(tok)] != .none;
}

inline fn eval_helper_postfix_step(self: *@This(), left_idx: u32, comptime allow_call: bool) !?u32 {
    var node_idx: u32 = 0;
    var right_idx: u32 = 0;

    switch (self.pop_tok() orelse return null) {
        .@"xpct_.*" => node_idx = self.tree.push_node(.expr_dereference),
        .kw_defer => {
            node_idx = self.tree.push_node(.expr_defer);
            right_idx = try self.eval_expr(0);
        },
        .@"pct_[" => {
            node_idx = self.tree.push_node(.expr_indexed);
            right_idx = try self.eval_expr(0);
            try self.eat_assert_tok(.@"pct_]");
        },
        .@"xpct_." => {
            node_idx = self.tree.push_node(.expr_member);
            right_idx = try self.eval_identifier();
        },
        .@"xpct_<-" => {
            node_idx = self.tree.push_node(.expr_aliasarrow);
            right_idx = try self.eval_identifier();
            // TODO hint the user should enclose in () by peeking if (
        },
        .@"xpct_!<-" => {
            node_idx = self.tree.push_node(.expr_errarrow);
            right_idx = try self.eval_identifier();
        },
        .@"xpct_?<-" => {
            node_idx = self.tree.push_node(.expr_errunwrap);
            right_idx = try self.eval_identifier();
        },
        .@"xpct_??" => {
            node_idx = self.tree.push_node(.expr_optunwrap);
            right_idx = if (try self.could_be_at_expr()) try self.eval_expr(0) else 0xFFFFFFFF;
        },
        .@"xpct_!!" => {
            node_idx = self.tree.push_node(.expr_optarrow);
            right_idx = if (try self.could_be_at_expr()) try self.eval_expr(0) else 0xFFFFFFFF;
        },
        .@"xpct_..=" => {
            node_idx = self.tree.push_node(.expr_genseq_inc);
            right_idx = try self.eval_expr(0);
        },
        .@"xpct_..<" => {
            node_idx = self.tree.push_node(.expr_genseq_exc);
            right_idx = try self.eval_expr(0);
        },
        .@"xpct_.." => {
            node_idx = self.tree.push_node(.expr_genseq_from);
            right_idx = 0xFFFFFFFF;
        },
        .@"pct_(" => if (comptime allow_call) {
            node_idx = self.tree.push_node(.expr_funccall);
            if ((self.peek_tok() orelse return error.EOF) == .@"pct_)") {
                self.tok_cursor += 1;
                right_idx = 0xFFFFFFFF;
            } else {
                right_idx = try self.eval_tuple_exprs(null, .@"pct_)");
            }
        },
        else => {
            // a helper func is not to consume anything if doing nothing
            self.tok_cursor += 1;
            return null;
        },
    }

    self.tree.set_node_arg0(node_idx, left_idx);
    self.tree.set_node_arg1(node_idx, right_idx);
    return node_idx;
}

fn eval_expr(self: *@This(), depth: u32) anyerror!u32 {
    const tok_a_at = self.tok_cursor;

    var left_idx: u32 = undefined;

    switch (self.pop_tok() orelse return error.EOF) {
        .@"pct_(" => {
            left_idx = self.tree.push_node(.expr_paren);
            self.tree.set_node_arg0(left_idx, try eval_expr(self, 0));
            try self.eat_assert_tok(.@"pct_)");
        },
        .@"pct_[" => {
            left_idx = self.tree.push_node(.expr_array);

            var children_idxs: [512]u32 = undefined;
            var childc: u32 = 0;

            while (true) {
                if (childc >= children_idxs.len) return error.TooManyElements;

                children_idxs[childc] = try self.eval_expr(0);
                childc += 1;

                switch (self.peek_tok() orelse return error.EOF) {
                    .@"pct_," => {
                        self.tok_cursor += 1;

                        if (try self.peek_eq_tok(.@"pct_]")) break;
                    },
                    .@"pct_]" => break,
                    else => return error.CommaOrArrayEndAssumed,
                }
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(left_idx, children_idxs[0..childc]);
        },
        .kw_if => {
            left_idx = self.tree.push_node(.expr_if_else);

            try self.eat_assert_tok(.@"pct_(");
            const ch_cond_expr_idx = try self.eval_expr(0);
            try self.eat_assert_tok(.@"pct_)");
            const ch_lhs_expr_idx = try self.eval_expr(0);
            try self.eat_assert_tok(.kw_else);
            const ch_rhs_expr_idx = try self.eval_expr(0);

            self.tree.push_extra_childrefs(left_idx, &.{ ch_cond_expr_idx, ch_lhs_expr_idx, ch_rhs_expr_idx });
        },
        .kw_match => left_idx = try self.eval_helper_match(false),
        .kw_for => left_idx = try self.eval_helper_for_while(true, false),
        .kw_while => left_idx = try self.eval_helper_for_while(false, false),
        .kw_loop => left_idx = try self.eval_helper_loop(false),
        .kw_deinit => {
            left_idx = self.tree.push_node(.expr_deinit);
            self.tree.set_node_arg0(left_idx, if (try self.could_be_at_expr()) try self.eval_expr(0) else 0xFFFFFFFF);
        },
        .kw_return => {
            left_idx = self.tree.push_node(.expr_return);
            self.tree.set_node_arg0(left_idx, if (try self.could_be_at_expr()) try self.eval_expr(0) else 0xFFFFFFFF);
        },
        .kw_brk => left_idx = self.tree.push_node(.expr_brk),
        .kw_cont => left_idx = self.tree.push_node(.expr_cont),
        .@"xpct_..=" => {
            left_idx = self.tree.push_node(.expr_genseq_inc);
            self.tree.set_node_arg0(left_idx, 0xFFFFFFFF);
            self.tree.set_node_arg1(left_idx, try self.eval_expr(0));
        },
        .@"xpct_..<" => {
            left_idx = self.tree.push_node(.expr_genseq_exc);
            self.tree.set_node_arg0(left_idx, 0xFFFFFFFF);
            self.tree.set_node_arg1(left_idx, try self.eval_expr(0));
        },
        .kw_true, .kw_false => |tok| {
            left_idx = self.tree.push_node(.expr_bool);
            if (tok == .kw_true) self.tree.set_node_arg0(left_idx, 1);
        },
        else => |tok| {
            if (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] != .none) {
                left_idx = self.tree.push_node(ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)]);
                self.tree.set_node_arg0(left_idx, try self.eval_expr(0));
            } else if (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] != .none) {
                left_idx = self.tree.push_data_node(ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)], tok_a_at);
            } else return error.SyntaxError;
        },
    }

    while (true) {
        if (try self.eval_helper_postfix_step(left_idx, true)) |stepped| {
            left_idx = stepped;
            continue;
        }

        const next_tok = self.peek_tok() orelse break;
        const bin_lookup = ParseTree.Node.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
        if (bin_lookup.nt == .none) break;
        if (bin_lookup.prec < depth) break;

        self.tok_cursor += 1;

        const op_node_idx = self.tree.push_node(bin_lookup.nt);
        const right_idx = try eval_expr(self, bin_lookup.prec + 1);

        self.tree.set_node_arg0(op_node_idx, left_idx);
        self.tree.set_node_arg1(op_node_idx, right_idx);

        left_idx = op_node_idx;
    }

    return left_idx;
}

fn eval_typeexpr(self: *@This()) !u32 {
    const tok_a_at = self.tok_cursor;
    const tok_a = self.pop_tok() orelse return error.EOF;

    if (tok_a == .identifier) {
        const id = self.tree.push_node(.typeexpr_type_custom);
        self.tree.set_node_arg0(id, self.tree.push_data_node(.expr_identifier, tok_a_at));
        return id;
    }

    const typeexpr_lookup = ParseTree.Node.tok_to_typeexpr[@intFromEnum(tok_a)];
    if (typeexpr_lookup != .none) return self.tree.push_node(typeexpr_lookup);

    var parent_idx: u32 = 0;
    switch (tok_a) {
        .@"xpct_*" => parent_idx = self.tree.push_node(.typeexpr_builtin_pointer),
        .@"xpct_&" => parent_idx = self.tree.push_node(.typeexpr_builtin_constpointer),
        .@"pct_[" => {
            parent_idx = self.tree.push_node(.typeexpr_builtin_array);
            const next_tok = self.peek_tok() orelse return error.EOF;
            self.tree.set_node_arg1(parent_idx, if (next_tok == .@"pct_]") 0xFFFFFFFF else try self.eval_expr(0));
            try self.eat_assert_tok(.@"pct_]");
        },
        else => return error.InvalidTypeTok,
    }

    self.tree.set_node_arg0(parent_idx, try self.eval_typeexpr());
    return parent_idx;
}

inline fn eval_tuple_exprs(self: *@This(), early_evald_expr: ?u32, comptime end_tok: Lexer.Token.Kind) anyerror!u32 {
    const deftuple_node_idx = self.tree.push_node(.tuple_exprs);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    if (early_evald_expr) |evald_expr| {
        children_idxs[0] = evald_expr;
        paramc += 1;
    }

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyParameters;

        children_idxs[paramc] = try self.eval_expr(0);
        paramc += 1;

        switch (self.pop_tok() orelse return error.EOF) {
            end_tok => break,
            .@"pct_," => {
                if (try self.peek_eq_tok(.@"pct_)")) {
                    break;
                } else {
                    continue;
                }
            },
            else => return error.ArgumentDefSepAssumed,
        }
    }

    self.tree.push_extra_childrefs(deftuple_node_idx, children_idxs[0..paramc]);

    return deftuple_node_idx;
}

inline fn eval_tuple_typed_identifiers(self: *@This()) !u32 {
    const deftuple_node_idx = self.tree.push_node(.tuple_typed_identifiers);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyArguments;

        const defsingle_node_idx = self.tree.push_node(.tuple_elem_typed_identifier);
        children_idxs[paramc] = defsingle_node_idx;
        paramc += 1;

        const child_type_idx = try self.eval_typeexpr();
        const child_identifier_idx = try self.eval_identifier();
        self.tree.set_node_arg0(defsingle_node_idx, child_type_idx);
        self.tree.set_node_arg1(defsingle_node_idx, child_identifier_idx);

        switch (self.pop_tok() orelse return error.EOF) {
            .@"pct_)" => break,
            .@"pct_," => {
                if (try self.peek_eq_tok(.@"pct_)")) {
                    break;
                } else {
                    continue;
                }
            },
            else => return error.ArgumentDefSepAssumed,
        }
    }

    self.tree.push_extra_childrefs(deftuple_node_idx, children_idxs[0..paramc]);

    return deftuple_node_idx;
}

inline fn eval_identifier(self: *@This()) !u32 {
    const next_tok_at = self.tok_cursor;
    const next_tok = self.pop_tok() orelse return error.EOF;
    if (next_tok != .identifier) return error.IdentifierAssumed;
    return self.tree.push_data_node(.expr_identifier, next_tok_at);
}

fn eval_func(self: *@This()) !u32 {
    const cursor_before = self.tok_cursor;
    const tok_a_at = self.tok_cursor;
    const tok_a = self.pop_tok() orelse return error.EOF;
    const tok_b = self.pop_tok() orelse return error.EOF;

    const func_node_idx = self.tree.push_node(.func_def);

    var children_idxs: [4]u32 = undefined;

    if (tok_a == .identifier and tok_b == .@"pct_(") {
        children_idxs[0] = 0xFFFFFFFF;
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, tok_a_at);
        self.tok_cursor -= 1;
    } else {
        self.tok_cursor = cursor_before;
        children_idxs[0] = try self.eval_typeexpr();
        children_idxs[1] = try self.eval_identifier();
    }

    try self.eat_assert_tok(.@"pct_(");

    children_idxs[2] = if (try self.peek_eq_tok(.@"pct_)")) 0xFFFFFFFF else try self.eval_tuple_typed_identifiers();
    children_idxs[3] = try self.eval_stmt();

    self.tree.push_extra_childrefs(func_node_idx, &children_idxs);
    return func_node_idx;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none);

    while (self.tok_cursor < self.tokens.len()) {
        self.func_cache.push(try self.eval_func());
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
        if (i == '\n') lc += 1;
    }

    var buf: [1024]u8 = undefined;
    var linebuf: [512]u8 = undefined;
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
