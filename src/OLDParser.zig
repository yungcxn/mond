const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");

tokens: SoD(Lexer.Token),
src_bytes: []const u8,
alloc: std.mem.Allocator,
tok_cursor: u32 = 0,
func_store: DynBuf(u32),
type_store: DynBuf(u32),
globals_store: DynBuf(u32),
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
        .func_store = .init(alloc, 1000),
        .type_store = .init(alloc, 1000),
        .globals_store = .init(alloc, 1000),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
    self.func_store.deinit();
    self.type_store.deinit();
    self.globals_store.deinit();
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
    const tok = self.peek_tok() orelse return error.EOF;
    const has_loop_expr: bool = (tok != .@"pct_:" and tok != .@"pct_{");

    const nk: ParseTree.Node.Kind = if (has_loop_expr)
        (if (statemented) .stmt_loop_ext else .expr_loop_ext)
    else
        (if (statemented) .stmt_loop else .expr_loop);

    parent_idx = self.tree.push_node(nk);
    self.tree.set_node_arg0(parent_idx, if (has_loop_expr) try self.eval_expr(0, false) else 0xFFFFFFFF);
    self.tree.set_node_arg1(parent_idx, if (statemented) try self.eval_stmt(!has_loop_expr) else blk: {
        if (has_loop_expr) try self.eat_assert_tok(.@"pct_:");
        break :blk try self.eval_expr(0, false);
    });

    return parent_idx;
}

inline fn eval_helper_for_while(self: *@This(), comptime for_for: bool, comptime statemented: bool) anyerror!u32 {
    var parent_idx: u32 = 0;

    const ch_expr_a_idx = try self.eval_expr(0, false);
    var ch_expr_b_idx: ?u32 = null;

    const ext_tok = if (for_for) .kw_in else .@"pct_,";

    if (try self.peek_eq_tok(ext_tok)) {
        self.tok_cursor += 1;
        ch_expr_b_idx = try self.eval_expr(0, false);
    }

    const ch_to_exec_idx = if (statemented) try self.eval_stmt(false) else blk: {
        try self.eat_assert_tok(.@"pct_:");
        break :blk try self.eval_expr(0, false);
    };

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

    self.tree.set_node_arg0(parent_idx, try self.eval_expr(0, false));

    const ch_block_idx = self.tree.push_node(.match_block);
    self.tree.set_node_arg1(parent_idx, ch_block_idx);

    try self.eat_assert_tok(.@"pct_{");

    var children_idxs: [512]u32 = undefined;
    var childc: u32 = 0;

    while (true) {
        if (childc >= children_idxs.len) return error.TooManyMatchCases;

        children_idxs[childc] = self.tree.push_node(.match_case);

        var case_ch_idx = try self.eval_expr(0, true);
        if (try self.peek_eq_tok(.@"pct_,")) {
            case_ch_idx = try self.eval_expression_tuple(case_ch_idx, .@"xpct_=>");
        } else {
            try self.eat_assert_tok(.@"xpct_=>");
        }
        self.tree.set_node_arg0(children_idxs[childc], case_ch_idx);

        self.tree.set_node_arg1(children_idxs[childc], if (statemented) try self.eval_stmt(true) else try self.eval_expr(0, true));
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

fn eval_stmt(self: *@This(), colonless: bool) anyerror!u32 {
    var parent_idx: u32 = undefined;

    var at_colon: bool = false;

    if (!colonless) {
        at_colon = (self.peek_tok() orelse return error.EOF) == .@"pct_:";
        if (at_colon) self.tok_cursor += 1;
    }

    switch (self.pop_tok() orelse return error.EOF) {
        .@"pct_{" => {
            if (at_colon) return error.BlockAfterColon;

            var children_idxs: [512]u32 = undefined;
            var childc: u32 = 0;

            parent_idx = self.tree.push_node(.stmt_exec_block);
            while (!try self.peek_eq_tok(.@"pct_}")) {
                if (childc >= children_idxs.len) return error.TooManySubstatements;
                children_idxs[childc] = try self.eval_stmt(true);
                childc += 1;
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(parent_idx, children_idxs[0..childc]);
        },
        .kw_if => {
            const ch_expr_idx = try self.eval_expr(0, false);
            const ch_stmt_idx = try self.eval_stmt(false);

            if (try self.peek_eq_tok(.kw_else)) {
                self.tok_cursor += 1;
                const alt_ch_stmt_idx = try self.eval_stmt(true);
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
            self.tree.set_node_arg0(parent_idx, try self.eval_stmt(true));
        },
        .kw_deinit => {
            parent_idx = self.tree.push_node(.stmt_deinit);
            self.tree.set_node_arg0(parent_idx, try self.eval_expr(0, false));
        },
        .kw_ret => {
            parent_idx = self.tree.push_node(.stmt_ret);
            self.tree.set_node_arg0(parent_idx, if (try self.peek_eq_tok(.@"pct_;")) 0xFFFFFFFF else try self.eval_expr(0, true));
        },
        else => {
            self.tok_cursor -= 1;
            parent_idx = try self.eval_helper_stmt_expr_or_assign();
        },
    }

    return parent_idx;
}

inline fn eval_helper_stmt_expr_or_assign(self: *@This()) !u32 {
    const is_mut: bool = try self.peek_eq_tok(.kw_mut);
    const expr0 = try self.eval_expr(0, true);

    switch (self.peek_tok() orelse return error.EOF) {
        .@"pct_;" => { // [mut] expr  ->  [mut] expr;
            if (is_mut) return error.MutBeforeExpr;

            const expr_kind = self.tree.ast_nodes.get_field(.nk, expr0) orelse unreachable;
            if (!ParseTree.Node.statementable_expressions[@intFromEnum(expr_kind)]) return error.UnstatementableExpr;
            return expr0;
        },
        .@"xpct_=" => { // [mut] expr =   ->  [mut] expr expr
            const expr_kind = self.tree.ast_nodes.get_field(.nk, expr0) orelse unreachable;
            if (!ParseTree.Node.assignable_expressions[@intFromEnum(expr_kind)]) return error.UnassignableExpr;

            self.tok_cursor += 1;
            const expr1 = try self.eval_expr(0, true);

            const parent_idx = self.tree.push_node(if (is_mut) .stmt_mut_untyped_assign else .stmt_untyped_assign);
            self.tree.set_node_arg0(parent_idx, expr0);
            self.tree.set_node_arg0(parent_idx, expr1);
            try self.eat_assert_tok(.@"pct_;");

            return parent_idx;
        },
        else => { // [mut] expr ?   ->   [mut] expr expr = expr;
            const expr1 = try self.eval_expr(0, false);
            try self.eat_assert_tok(.@"xpct_=");
            const expr2 = try self.eval_expr(0, true);

            const parent_idx = self.tree.push_node(if (is_mut) .stmt_mut_typed_assign else .stmt_typed_assign);
            self.tree.push_extra_childrefs(parent_idx, &.{ expr0, expr1, expr2 });

            return parent_idx;
        },
    }
}

fn eval_expr(self: *@This(), depth: u32, comptime allow_type_expr: bool) anyerror!u32 {
    const tok_a_at = self.tok_cursor;

    var left_idx: u32 = undefined;

    switch (self.pop_tok() orelse return error.EOF) { // TODO add `type` and `fun` and function types
        .kw_u8 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_u8) else return error.TypeExprForbidden,
        .kw_u16 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_u16) else return error.TypeExprForbidden,
        .kw_u32 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_u32) else return error.TypeExprForbidden,
        .kw_u64 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_u64) else return error.TypeExprForbidden,
        .kw_i8 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_i8) else return error.TypeExprForbidden,
        .kw_i16 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_i16) else return error.TypeExprForbidden,
        .kw_i32 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_i32) else return error.TypeExprForbidden,
        .kw_i64 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_i64) else return error.TypeExprForbidden,
        .kw_f8 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_f8) else return error.TypeExprForbidden,
        .kw_f16 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_f16) else return error.TypeExprForbidden,
        .kw_f32 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_f32) else return error.TypeExprForbidden,
        .kw_f64 => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_f64) else return error.TypeExprForbidden,
        .kw_bool => if (comptime allow_type_expr) return self.tree.push_node(.expr_type_builtin_bool) else return error.TypeExprForbidden,
        .@"xpct_*" => if (comptime allow_type_expr) return {
            const parent_idx = self.tree.push_node(.expr_type_pointer);
            self.tree.set_node_arg0(parent_idx, try self.eval_expr(0, true));
            return parent_idx;
        } else return error.TypeExprForbidden,
        .@"xpct_&" => if (comptime allow_type_expr) return {
            const parent_idx = self.tree.push_node(.expr_type_constpointer);
            self.tree.set_node_arg0(parent_idx, try self.eval_expr(0, true));
            return parent_idx;
        } else return error.TypeExprForbidden,
        // this is the last case of type expressions and simultaneously the first of nontype-expr.
        .@"pct_[" => {
            var typeexpr_impossible: bool = !allow_type_expr;

            const empty: bool = try self.peek_eq_tok(.@"pct_]");
            const ch_idx = if (empty) 0xFFFFFFFF else try self.eval_expr(0, true);

            if (comptime allow_type_expr) {
                // either [expr, expr, expr] ... or [expr]typexpr
                if (!empty) {
                    const has_comma: bool = try self.peek_eq_tok(.@"pct_,");

                    if (has_comma) {
                        typeexpr_impossible = true;
                    } else {
                        try self.eat_assert_tok(.@"pct_]");
                        if (ParseTree.Node.tok_to_typeexpr_start[@intFromEnum(self.peek_tok() orelse return error.EOF)]) {
                            left_idx = if (empty) ch_idx else try self.eval_expr(0, true);
                        }
                    }
                }
            }

            if (typeexpr_impossible) {
                left_idx = if (empty) ch_idx else try self.eval_expression_tuple(ch_idx, .@"pct_]");
            }
        },
        // here, the non-type-expression rules start
        .@"pct_(" => {
            left_idx = self.tree.push_node(.expr_paren);
            self.tree.set_node_arg0(left_idx, try self.eval_expr(0, allow_type_expr));
            try self.eat_assert_tok(.@"pct_)");
        },
        .kw_if => {
            left_idx = self.tree.push_node(.expr_if_else);

            const ch_cond_expr_idx = try self.eval_expr(0, true);
            try self.eat_assert_tok(.@"pct_:");
            const ch_lhs_expr_idx = try self.eval_expr(0, true);
            try self.eat_assert_tok(.kw_else);
            const ch_rhs_expr_idx = try self.eval_expr(0, true);

            self.tree.push_extra_childrefs(left_idx, &.{ ch_cond_expr_idx, ch_lhs_expr_idx, ch_rhs_expr_idx });
        },
        .kw_match => left_idx = try self.eval_helper_match(false),
        .kw_for => left_idx = try self.eval_helper_for_while(true, false),
        .kw_while => left_idx = try self.eval_helper_for_while(false, false),
        .kw_loop => left_idx = try self.eval_helper_loop(false),
        .kw_deinit => {
            left_idx = self.tree.push_node(.expr_deinit);
            const expr_after = ParseTree.Node.tok_to_expr_start[@intFromEnum(self.peek_tok() orelse return error.EOF)];
            self.tree.set_node_arg0(left_idx, if (expr_after) try self.eval_expr(0, false) else 0xFFFFFFFF);
        },
        .kw_ret => {
            left_idx = self.tree.push_node(.expr_return);
            const expr_after = ParseTree.Node.tok_to_expr_start[@intFromEnum(self.peek_tok() orelse return error.EOF)];
            self.tree.set_node_arg0(left_idx, if (expr_after) try self.eval_expr(0, true) else 0xFFFFFFFF);
        },
        .kw_brk => left_idx = self.tree.push_node(.expr_brk),
        .kw_cont => left_idx = self.tree.push_node(.expr_cont),
        .@"xpct_..=" => {
            left_idx = self.tree.push_node(.expr_genseq_inc);
            self.tree.set_node_arg0(left_idx, 0xFFFFFFFF);
            self.tree.set_node_arg1(left_idx, try self.eval_expr(0, false));
        },
        .@"xpct_..<" => {
            left_idx = self.tree.push_node(.expr_genseq_exc);
            self.tree.set_node_arg0(left_idx, 0xFFFFFFFF);
            self.tree.set_node_arg1(left_idx, try self.eval_expr(0, false));
        },
        .kw_true, .kw_false => |tok| {
            left_idx = self.tree.push_node(.expr_bool);
            if (tok == .kw_true) self.tree.set_node_arg0(left_idx, 1);
        },
        else => |tok| {
            if (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] != .none) {
                left_idx = self.tree.push_node(ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)]);
                self.tree.set_node_arg0(left_idx, try self.eval_expr(0, false));
            } else if (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] != .none) {
                left_idx = self.tree.push_data_node(ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)], tok_a_at);
            } else return error.SyntaxError;
        },
    }

    while (true) {
        var possible_parent: ?u32 = null;
        var possible_parents_rhs: u32 = 0;

        switch (self.pop_tok() orelse break) {
            .@"xpct_.*" => possible_parent = self.tree.push_node(.expr_dereference),
            .kw_defer => {
                possible_parent = self.tree.push_node(.expr_defer);
                possible_parents_rhs = try self.eval_expr(0, false);
            },
            .@"pct_[" => {
                possible_parent = self.tree.push_node(.expr_indexed);
                possible_parents_rhs = try self.eval_expr(0, false);
                try self.eat_assert_tok(.@"pct_]");
            },
            .@"xpct_." => {
                possible_parent = self.tree.push_node(.expr_member);
                possible_parents_rhs = try self.eval_identifier();
            },
            .@"xpct_<-" => {
                possible_parent = self.tree.push_node(.expr_aliasarrow);
                possible_parents_rhs = try self.eval_identifier();
                // TODO hint the user should enclose in () by peeking if (
            },
            .@"xpct_!<-" => {
                possible_parent = self.tree.push_node(.expr_errarrow);
                possible_parents_rhs = try self.eval_identifier();
            },
            .@"xpct_?<-" => {
                possible_parent = self.tree.push_node(.expr_errunwrap);
                possible_parents_rhs = try self.eval_identifier();
            },
            .@"xpct_??" => {
                possible_parent = self.tree.push_node(.expr_optunwrap);
                const expr_after = ParseTree.Node.tok_to_expr_start[@intFromEnum(self.peek_tok() orelse return error.EOF)];
                possible_parents_rhs = if (expr_after) try self.eval_expr(0, false) else 0xFFFFFFFF;
            },
            .@"xpct_!!" => {
                possible_parent = self.tree.push_node(.expr_optarrow);
                const expr_after = ParseTree.Node.tok_to_expr_start[@intFromEnum(self.peek_tok() orelse return error.EOF)];
                possible_parents_rhs = if (expr_after) try self.eval_expr(0, false) else 0xFFFFFFFF;
            },
            .@"xpct_..=" => {
                possible_parent = self.tree.push_node(.expr_genseq_inc);
                possible_parents_rhs = try self.eval_expr(0, false);
            },
            .@"xpct_..<" => {
                possible_parent = self.tree.push_node(.expr_genseq_exc);
                possible_parents_rhs = try self.eval_expr(0, false);
            },
            .@"xpct_.." => {
                possible_parent = self.tree.push_node(.expr_genseq_from);
                possible_parents_rhs = 0xFFFFFFFF;
            },
            .@"pct_(" => {
                possible_parent = self.tree.push_node(.expr_funccall);
                if ((self.peek_tok() orelse return error.EOF) == .@"pct_)") {
                    self.tok_cursor += 1;
                    possible_parents_rhs = 0xFFFFFFFF;
                } else {
                    possible_parents_rhs = try self.eval_expression_tuple(null, .@"pct_)");
                }
            },
            else => {
                // a helper func is not to consume anything if doing nothing
                self.tok_cursor -= 1;
            },
        }

        if (possible_parent) |parent_idx| {
            self.tree.set_node_arg0(parent_idx, left_idx);
            self.tree.set_node_arg1(parent_idx, possible_parents_rhs);

            left_idx = parent_idx;
        }

        const next_tok = self.peek_tok() orelse break;
        const bin_lookup = ParseTree.Node.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
        if (bin_lookup.nt == .none) break;
        if (bin_lookup.prec < depth) break;

        self.tok_cursor += 1;

        const op_node_idx = self.tree.push_node(bin_lookup.nt);
        const right_idx = try eval_expr(self, bin_lookup.prec + 1, true);

        self.tree.set_node_arg0(op_node_idx, left_idx);
        self.tree.set_node_arg1(op_node_idx, right_idx);

        left_idx = op_node_idx;
    }

    return left_idx;
}

inline fn eval_expression_tuple(self: *@This(), early_evald_expr: ?u32, comptime end_tok: Lexer.Token.Kind) anyerror!u32 {
    const tuple_node_idx = self.tree.push_node(.tuple__expr);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    if (early_evald_expr) |evald_expr| {
        children_idxs[0] = evald_expr;
        paramc += 1;
    }

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyParameters;

        children_idxs[paramc] = try self.eval_expr(0, true);
        paramc += 1;

        switch (self.peek_tok() orelse return error.EOF) {
            end_tok => break,
            .@"pct_," => {
                self.tok_cursor += 1;
                if (try self.peek_eq_tok(end_tok)) {
                    break;
                } else {
                    continue;
                }
            },
            else => return error.ArgumentDefSepAssumed,
        }
    }

    self.tree.push_extra_childrefs(tuple_node_idx, children_idxs[0..paramc]);
    self.tok_cursor += 1;

    return tuple_node_idx;
}

inline fn eval_complex_tuple(self: *@This(), comptime typed: bool) !u32 {
    const deftuple_node_idx = if (typed) self.tree.push_node(.tuple__type_identifier_optexpr) else self.tree.push_node(.tuple__identifier_optexpr);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (paramc >= children_idxs.len) return error.TooManyArguments;

        const child_type_idx = if (comptime typed) try self.eval_expr(0, true) else null;
        const child_identifier_idx = try self.eval_identifier();

        var next = self.peek_tok() orelse return error.EOF;
        var subparent_idx: u32 = undefined;

        if (next == .@"xpct_=") {
            self.tok_cursor += 1;
            const child_expr_idx = try self.eval_expr(0, true);
            subparent_idx = self.tree.push_node(if (comptime typed) .tupleelem__type_identifier_expr else .tupleelem__identifier_expr);
            if (comptime typed) {
                self.tree.push_extra_childrefs(subparent_idx, &.{ child_type_idx, child_identifier_idx, child_expr_idx });
            } else {
                self.tree.set_node_arg0(subparent_idx, child_identifier_idx);
                self.tree.set_node_arg0(subparent_idx, child_expr_idx);
            }
            next = self.peek_tok() orelse return error.EOF;
        } else {
            if (comptime typed) {
                subparent_idx = self.tree.push_node(.tupleelem__type_identifier);
                self.tree.set_node_arg0(subparent_idx, child_type_idx);
                self.tree.set_node_arg1(subparent_idx, child_identifier_idx);
            } else {
                subparent_idx = child_identifier_idx;
            }
        }

        children_idxs[paramc] = subparent_idx;
        paramc += 1;

        switch (next) {
            .@"pct_)" => break,
            .@"pct_," => {
                self.tok_cursor += 1;
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
    self.tok_cursor += 1;

    return deftuple_node_idx;
}

inline fn eval_tuple_assigned_identifiers(self: *@This()) !u32 { // TODO
    const deftuple_node_idx = self.tree.push_node(.tuple_typed_identifiers);
    return deftuple_node_idx;
}

inline fn eval_identifier(self: *@This()) !u32 {
    const next_tok_at = self.tok_cursor;
    const next_tok = self.pop_tok() orelse return error.EOF;
    if (next_tok != .identifier) return error.IdentifierAssumed;
    return self.tree.push_data_node(.expr_identifier, next_tok_at);
}

fn eval_func(self: *@This(), allow_bodyless: bool) !u32 {
    const func_node_idx = self.tree.push_node(.func_def);

    // name, runtime args, [rettype], (if allow_bodyless optional:) stmt, [build args]
    var children_idxs: [5]u32 = undefined;
    children_idxs[2] = 0xFFFFFFFF;
    children_idxs[4] = 0xFFFFFFFF;

    children_idxs[0] = try self.eval_identifier();
    try self.eat_assert_tok(.@"xpct_=");
    try self.eat_assert_tok(.@"pct_(");

    children_idxs[1] = if (try self.peek_eq_tok(.@"pct_)")) 0xFFFFFFFF else try self.eval_complex_tuple(true);

    if (try self.peek_eq_tok(.@"pct_(")) {
        self.tok_cursor += 1;
        children_idxs[4] = children_idxs[1];
        children_idxs[1] = if (try self.peek_eq_tok(.@"pct_)")) 0xFFFFFFFF else try self.eval_complex_tuple(true);
    }

    const rettype_given: bool = try self.peek_eq_tok(.@"xpct_->");

    if (rettype_given) {
        self.tok_cursor += 1;
        children_idxs[2] = try self.eval_expr(0, true);
    }

    if (allow_bodyless and try self.peek_eq_tok(.@"pct_;")) {
        self.tok_cursor += 1;
        children_idxs[3] = 0xFFFFFFFF;
    } else {
        children_idxs[3] = try self.eval_stmt(rettype_given);
    }

    self.tree.push_extra_childrefs(func_node_idx, &children_idxs);
    return func_node_idx;
}

inline fn eval_subinterfaces(self: *@This()) !u32 {
    const parent_idx = self.tree.push_node(.expr_subinterfaces);

    var ch_subinterfaces: [100]u32 = undefined;
    ch_subinterfaces[0] = try self.eval_expr(0, true);
    var subinterfacec: u32 = 1;

    while (true) switch (self.peek_tok() orelse return error.EOF) {
        .@"pct_," => {
            self.tok_cursor += 1;
            const next = self.peek_tok() orelse return error.EOF;
            if (next == .@"pct_{" or next == .@"pct_;") break;
        },
        .@"pct_{", .@"pct_;" => break,
        else => {
            ch_subinterfaces[subinterfacec] = try self.eval_expr(0, true);
            subinterfacec += 1;
        },
    };
    self.tree.push_extra_childrefs(parent_idx, ch_subinterfaces[0..subinterfacec]);
    return parent_idx;
}

inline fn eval_methods_block(self: *@This(), allow_bodyless_fns: bool) !u32 {
    const parent_idx = self.tree.push_node(.expr_subinterfaces);

    var children_idxs: [1024]u32 = undefined;
    var childc: u32 = 0;

    var peeked = self.peek_tok() orelse return error.EOF;
    while (peeked != .@"pct_}") : (peeked = self.peek_tok() orelse return error.EOF) {
        if (peeked == .kw_fun) {
            self.tok_cursor += 1;
            children_idxs[childc] = try self.eval_func(allow_bodyless_fns);
            childc += 1;
        } else {
            return error.FunctionAssumed;
        }
    }

    self.tree.push_extra_childrefs(parent_idx, children_idxs[0..childc]);

    return parent_idx;
}

fn eval_type(self: *@This()) !u32 {
    // name, runtime args, [subinterfaces], [method_block], [build args]
    var children_idxs: [5]u32 = undefined;
    children_idxs[2] = 0xFFFFFFFF;
    children_idxs[3] = 0xFFFFFFFF;
    children_idxs[4] = 0xFFFFFFFF;

    children_idxs[0] = try self.eval_identifier();
    try self.eat_assert_tok(.@"xpct_=");
    try self.eat_assert_tok(.@"pct_(");
    children_idxs[1] = if (try self.peek_eq_tok(.@"pct_)")) return error.EmptyTypeDef else try self.eval_complex_tuple(true);

    if (try self.peek_eq_tok(.@"pct_(")) {
        self.tok_cursor += 1;
        children_idxs[4] = children_idxs[1];
        children_idxs[1] = if (try self.peek_eq_tok(.@"pct_)")) 0xFFFFFFFF else try self.eval_complex_tuple(true);
    }

    if (try self.peek_eq_tok(.@"xpct_<<<")) {
        self.tok_cursor += 1;
        children_idxs[2] = try self.eval_subinterfaces();
    }

    switch (self.peek_tok() orelse return error.EOF) {
        .@"pct_{" => {
            self.tok_cursor += 1;
            children_idxs[3] = try self.eval_methods_block(false);
        },
        .@"pct_;" => {
            self.tok_cursor += 1;
        },
        else => return error.InvalidSyntax,
    }

    const type_node_idx = self.tree.push_node(.type_def);
    self.tree.push_extra_childrefs(type_node_idx, &children_idxs);
    return type_node_idx;
}

fn eval_iface(self: *@This()) !u32 {
    // name, [subinterfaces], [method_block], [build args]
    var children_idxs: [4]u32 = undefined;
    children_idxs[1] = 0xFFFFFFFF;
    children_idxs[2] = 0xFFFFFFFF;
    children_idxs[3] = 0xFFFFFFFF;

    children_idxs[0] = try self.eval_identifier();
    try self.eat_assert_tok(.@"xpct_=");

    if (try self.peek_eq_tok(.@"pct_(")) {
        self.tok_cursor += 1;
        children_idxs[3] = if (try self.peek_eq_tok(.@"pct_)")) return error.EmptyStaticArgs else try self.eval_complex_tuple(true);
    }

    if (try self.peek_eq_tok(.@"xpct_<<<")) {
        self.tok_cursor += 1;
        children_idxs[1] = try self.eval_subinterfaces();
    }

    switch (self.peek_tok() orelse return error.EOF) {
        .@"pct_{" => {
            self.tok_cursor += 1;
            children_idxs[2] = try self.eval_methods_block(true);
        },
        else => return error.InvalidSyntax,
    }

    const iface_node_idx = self.tree.push_node(.iface_def);
    self.tree.push_extra_childrefs(iface_node_idx, &children_idxs);
    return iface_node_idx;
}

fn eval_enum(self: *@This()) !u32 {
    const enum_node_idx = self.tree.push_node(.enum_def);
    const ch_identifier_idx = try self.eval_identifier();
    const ch_def_idx = try self.eval_complex_tuple(false);
    self.tree.set_node_arg0(enum_node_idx, ch_identifier_idx);
    self.tree.set_node_arg1(enum_node_idx, ch_def_idx);
    try self.eat_assert_tok(.@"pct_;");
    return enum_node_idx;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none);

    while (self.tok_cursor < self.tokens.len()) switch (self.pop_tok() orelse return) {
        .kw_fun => self.func_store.push(try self.eval_func(false)),
        .kw_type => self.type_store.push(try self.eval_type()),
        .kw_iface => self.type_store.push(try self.eval_iface()),
        .kw_enum => self.type_store.push(try self.eval_enum()),
        else => self.globals_store.push(try self.eval_helper_stmt_expr_or_assign()),
    };
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
