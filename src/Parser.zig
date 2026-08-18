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

inline fn peek_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn peek_n_tok(self: *@This(), n: comptime_int) ?[n]Lexer.Token {
    var ret: [n]Lexer.Token = undefined;
    inline for (0..n) |i| {
        ret[i] = self.tokens.get(self.tok_cursor + @as(u32, i)) orelse return null;
    }

    return ret;
}

inline fn pop_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    defer self.tok_cursor += 1;
    return self.tokens.get_field(.tk, self.tok_cursor);
}

fn eval_stmt(self: *@This()) !u32 {
    const tok_kind = self.peek_tok_kind() orelse return error.EOF;
    var parent_idx: u32 = undefined;

    switch (tok_kind) {
        .@"pct_{" => {
            self.tok_cursor += 1;

            var children_idxs: [512]u32 = undefined;
            var childc: u32 = 0;

            parent_idx = self.tree.push_node(.stmt_exec_block);
            while ((self.peek_tok_kind() orelse return error.EOF) != .@"pct_}") {
                if (childc >= children_idxs.len) return error.TooManySubstatements;
                children_idxs[childc] = try self.eval_stmt();
                childc += 1;
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(parent_idx, children_idxs[0..childc]);
        },
        .kw_if => {
            self.tok_cursor += 1;

            const ch_expr_idx = try self.eval_expr(0);
            const ch_stmt_idx = try self.eval_stmt();

            if ((self.peek_tok_kind() orelse return error.EOF) == .kw_else) {
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
        .kw_match => {
            self.tok_cursor += 1;

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_(") return error.OpenParenAssumed;

            parent_idx = self.tree.push_node(.stmt_match);
            self.tree.set_node_arg0(parent_idx, try self.eval_expr(0));

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_)") return error.CloseParenAssumed;

            const ch_block_idx = self.tree.push_node(.match_block);
            self.tree.set_node_arg1(parent_idx, ch_block_idx);

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_{") return error.OpenCurlyBraceAssumed;

            var children_idxs: [512]u32 = undefined;
            var childc: u32 = 0;

            // TODO match cases sep'd with comma. USE tuple_exprs!
            while (true) {
                if (childc >= children_idxs.len) return error.TooManyMatchCases;

                children_idxs[childc] = self.tree.push_node(.match_case);
                self.tree.set_node_arg0(children_idxs[childc], self.eval_expr(0));

                if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_=>") return error.MatchCaseArrowAssumed;

                self.tree.set_node_arg1(children_idxs[childc], self.eval_stmt());
                childc += 1;

                const tok_after_matchcase = self.peek_tok_kind() orelse return error.EOF;
                switch (tok_after_matchcase) {
                    .@"pct_," => {
                        self.tok_cursor += 1;

                        if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_}") break;
                    },
                    .@"pct_}" => break,
                    else => return error.CommaOrBlockEndAssumed,
                }
            }

            self.tok_cursor += 1;
            self.tree.push_extra_childrefs(ch_block_idx, children_idxs[0..childc]);
        },
        .kw_for, .kw_while => |kw| {
            self.tok_cursor += 1;

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_(") return error.OpenParenAssumed;

            const ch_expr_a_idx = try .self.eval_expr(0);
            var ch_expr_b_idx: ?u32 = null;

            if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_:") {
                self.tok_cursor += 1;

                ch_expr_b_idx = self.eval_expr(0);
            }

            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_)") return error.CloseParenAssumed;

            const ch_stmt_idx = try self.eval_stmt();

            if (ch_expr_b_idx) |b_idx| {
                parent_idx = self.tree.push_node(if (kw == .kw_for) .stmt_for_ext else .stmt_while_ext);
                self.tree.push_extra_childrefs(parent_idx, &.{ ch_expr_a_idx, b_idx, ch_stmt_idx });
            } else {
                parent_idx = self.tree.push_node(if (kw == .kw_for) .stmt_for else .stmt_while);
                self.tree.set_node_arg0(parent_idx, ch_expr_a_idx);
                self.tree.set_node_arg1(parent_idx, ch_stmt_idx);
            }
        },
        .kw_loop => {
            self.tok_cursor += 1;

            var ch_expr_b_idx: ?u32 = null;

            if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_(") {
                self.tok_cursor += 1;

                ch_expr_b_idx = self.eval_expr(0);

                if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_)") return error.CloseParenAssumed;
            }

            parent_idx = self.tree.push_node(if (ch_expr_b_idx) |_| .stmt_loop_ext else .stmt_loop);
            self.tree.set_node_arg0(parent_idx, if (ch_expr_b_idx) |b_idx| b_idx else 0xFFFFFFFF);
            self.tree.set_node_arg1(parent_idx, try self.eval_stmt());
        },
        .kw_cont, .kw_brk => |kw| {
            self.tok_cursor += 1;
            parent_idx = self.tree.push_node(if (kw == .kw_cont) .stmt_cont else .stmt_brk);
        },
        .kw_defer => {
            self.tok_cursor += 1;
            parent_idx = self.tree.push_node(.stmt_defer);
            self.tree.set_node_arg0(parent_idx, try self.eval_stmt());
        },
        .kw_return => {
            self.tok_cursor += 1;

            parent_idx = self.tree.push_node(.stmt_return);
            const opt_ch_expr_idx = if (try self.could_be_at_expr()) try self.eval_expr(0) else null;
            self.tree.set_node_arg0(parent_idx, if (opt_ch_expr_idx) |idx| idx else 0xFFFFFFFF);
        },
        .kw_mut => {
            self.tok_cursor += 1;
            parent_idx = try self.eval_helper_expr_or_assign(true, true);
        },
        else => parent_idx = try self.eval_helper_expr_or_assign(false, false),
    }

    return parent_idx;
}

inline fn eval_helper_assign_target(self: *@This(), base_identifier_idx: u32) !u32 {
    var target_idx = base_identifier_idx;
    while (true) {
        target_idx = (try self.eval_helper_postfix_step(target_idx, false)) orelse break;
    }
    return target_idx;
}

fn eval_helper_expr_or_assign(self: *@This(), comptime assign_is_mut: bool, comptime exclude_expr_eval: bool) !u32 {
    const cursor_start = self.tok_cursor;
    const tokinfo = try self.eval_identifier_or_typeexpr_or_expr();
    const tok_next = self.peek_tok_kind() orelse return error.EOF;

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
        if ((self.pop_tok_kind() orelse return error.EOF) != .@"xpct_=") return error.AssignSignAssumed;
        ch_expr_idx = try self.eval_expr(0);

        parent_idx = self.tree.push_node(if (assign_is_mut) .stmt_mut_typed_assign else .stmt_typed_assign);
        self.tree.push_extra_childrefs(parent_idx, &.{ ch_typeexpr_idx, ch_identifier_idx, ch_expr_idx });
    } else if (tokinfo[1] == 0) {
        ch_identifier_idx = try self.eval_helper_assign_target(tokinfo[0]);
        const after_target = self.peek_tok_kind() orelse return error.EOF;

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
    const tok = self.peek_tok_kind() orelse return error.EOF;
    if (tok == .identifier) {
        return .{ try self.eval_identifier(), 0 };
    } else if (try self.could_be_at_typeexpr()) {
        return .{ try self.eval_typeexpr(), 1 };
    } else if (try self.could_be_at_expr()) {
        return .{ try self.eval_expr(0), 2 };
    } else return error.InvalidSyntax;
}

inline fn could_be_at_expr(self: *@This()) !bool {
    const tok = self.peek_tok_kind() orelse return error.EOF;

    return tok == .@"pct_(" or
        tok == .kw_true or
        tok == .kw_false or
        (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] != .none) or
        (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] != .none);
}

inline fn eval_helper_postfix_step(self: *@This(), left_idx: u32, comptime allow_call: bool) !?u32 {
    const next_tok = self.peek_tok_kind() orelse return null;

    var node_idx: u32 = 0;
    var right_idx: u32 = 0;

    if (next_tok == .@"pct_[") {
        self.tok_cursor += 1;
        node_idx = self.tree.push_node(.expr_indexed);
        right_idx = try self.eval_expr(0);
        if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_]") return error.ClosingBracketAssumed;
    } else if (next_tok == .@"xpct_.") {
        self.tok_cursor += 1;
        node_idx = self.tree.push_node(.expr_member);
        right_idx = try self.eval_identifier();
    } else if (allow_call and next_tok == .@"pct_(") {
        self.tok_cursor += 1;
        node_idx = self.tree.push_node(.expr_funccall);
        if ((self.peek_tok_kind() orelse return error.EOF) == .@"pct_)") {
            self.tok_cursor += 1;
            right_idx = 0xFFFFFFFF;
        } else {
            right_idx = try self.eval_tuple_exprs();
        }
    } else {
        return null;
    }

    self.tree.set_node_arg0(node_idx, left_idx);
    self.tree.set_node_arg1(node_idx, right_idx);
    return node_idx;
}

fn eval_expr(self: *@This(), depth: u32) anyerror!u32 {
    const tok_a_at = self.tok_cursor;
    const tok = self.pop_tok_kind() orelse return error.EOF;

    var left_idx: u32 = undefined;

    if (tok == .@"pct_(") {
        left_idx = self.tree.push_node(.expr_paren);
        self.tree.set_node_arg0(left_idx, try eval_expr(self, 0));
        if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_)") return error.MissingEnclosingParen;
    } else if (ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)] != .none) {
        left_idx = self.tree.push_node(ParseTree.Node.tok_to_expr_unary[@intFromEnum(tok)]);
        self.tree.set_node_arg0(left_idx, try eval_expr(self, 0));
    } else if (ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)] != .none) {
        left_idx = self.tree.push_data_node(ParseTree.Node.tok_to_expr_data[@intFromEnum(tok)], tok_a_at);
    } else if (tok == .kw_true or tok == .kw_false) {
        left_idx = self.tree.push_node(.expr_bool);
        if (tok == .kw_true) self.tree.set_node_arg0(left_idx, 1);
    } else return error.SyntaxError;

    while (true) {
        if (try self.eval_helper_postfix_step(left_idx, true)) |stepped| {
            left_idx = stepped;
            continue;
        }

        const next_tok = self.peek_tok_kind() orelse break;
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

inline fn could_be_at_typeexpr(self: *@This()) !bool {
    const tok = self.peek_tok_kind() orelse return error.EOF;

    return tok == .identifier or
        tok == .@"xpct_*" or
        tok == .@"xpct_&" or
        tok == .@"pct_[" or
        ParseTree.Node.tok_to_typeexpr[@intFromEnum(tok)] != .none;
}

fn eval_typeexpr(self: *@This()) !u32 {
    const tok_a_at = self.tok_cursor;
    const tok_a = self.pop_tok_kind() orelse return error.EOF;

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
            const next_tok = self.peek_tok_kind() orelse return error.EOF;
            self.tree.set_node_arg1(parent_idx, if (next_tok == .@"pct_]") 0xFFFFFFFF else try self.eval_expr(0));
            if ((self.pop_tok_kind() orelse return error.EOF) != .@"pct_]") return error.ClosingBracketAssumed;
        },
        else => return error.InvalidTypeTok,
    }

    self.tree.set_node_arg0(parent_idx, try self.eval_typeexpr());
    return parent_idx;
}

inline fn eval_tuple_exprs(self: *@This()) anyerror!u32 {
    const deftuple_node_idx = self.tree.push_node(.tuple_exprs);

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

    self.tree.push_extra_childrefs(deftuple_node_idx, children_idxs[0..paramc]);

    return deftuple_node_idx;
}

inline fn eval_identifier(self: *@This()) !u32 {
    const next_tok_at = self.tok_cursor;
    const next_tok = self.pop_tok_kind() orelse return error.EOF;
    if (next_tok != .identifier) return error.IdentifierAssumed;
    return self.tree.push_data_node(.expr_identifier, next_tok_at);
}

fn eval_func(self: *@This()) !u32 {
    const cursor_before = self.tok_cursor;
    const tok_a_at = self.tok_cursor;
    const tok_a = self.pop_tok_kind() orelse return error.EOF;
    const tok_b = self.pop_tok_kind() orelse return error.EOF;

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

    const tok_c = self.pop_tok_kind() orelse return error.EOF;
    const tok_d = self.pop_tok_kind() orelse return error.EOF;

    if (tok_c != .@"pct_(") return error.OpenParenAssumed;

    if (tok_d == .@"pct_)") {
        children_idxs[2] = 0xFFFFFFFF;
    } else {
        self.tok_cursor -= 1;
        children_idxs[2] = try self.eval_tuple_typed_identifiers();
    }
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
