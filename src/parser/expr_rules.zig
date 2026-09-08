const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const stmt_rules = @import("stmt_rules.zig");
const subexpr_rules = @import("subexpr_rules.zig");

pub const FunctionDefinition = struct {
    function_header: u32,
    substatement: u32,
};

pub fn eval_expr(p: *Parser, prec: u8) anyerror!u32 {
    const parent = try lookahead.pre_expression[@intFromEnum(try p.pop_tok())].?(p);
    return try known_eval_expr(p, prec, parent);
}

// lookahead was already evaluated and passed as `parent_in`
inline fn known_eval_expr(p: *Parser, prec: u8, parent_in: u32) anyerror!u32 {
    var parent = parent_in;
    while (lookahead.post_expression[@intFromEnum(try p.pop_tok())]) |post_expr_f| {
        const lhs = parent;
        parent = try post_expr_f(p, lhs);
    } else {
        p.tok_cursor -= 1;
    }

    while (lookahead.binary_compute_expression[@intFromEnum(try p.pop_tok())]) |precd_bin_expr| {
        if (precd_bin_expr.prec < prec) {
            p.tok_cursor -= 1;
            break;
        }

        const lhs = parent;
        parent = try precd_bin_expr.f(p, lhs);
        p.tree.set_node_arg0(parent, lhs);
    } else {
        p.tok_cursor -= 1;
    }

    return parent;
}

// function definition start OR some function's type start OR capture start
// `(` is already consumed
pub fn eval_expr_paren(p: *Parser) anyerror!u32 {
    var parent: u32 = 0xFFFFFFFF;
    if (!try p.peek_eq_tok(.@"pct_)")) {
        parent = try eval_expr(p, 0);
        // it was '(' behind, then expr, then ')', if after it's `->` or `:` or `{`, it's a func!
        try p.eat_assert_tok(.@"pct_)");
        switch (try p.peek_tok()) {
            .@"xpct_->", .@"pct_:", .@"pct_{" => {
                // `parent` was an expression in a "()", but it's actually a function parameter tuple
                parent = try subexpr_rules.ee_eval_subexpr_fun_def_header(p, parent);
                parent = try ee_eval_expr_fun_def(p, parent);
            },
            else => {
                // `parent` just needs to be in a capture expression
                const child_expr = parent;
                parent = p.tree.push_node(.expr_capture);
                p.tree.set_node_arg0(parent, child_expr);
            },
        }
    } else {
        // guaranteed to be a `subexpr_fun_param_def_tuple`, and paren_expr is early
        parent = try subexpr_rules.ee_eval_subexpr_fun_def_header(p, parent);
        parent = try ee_eval_expr_fun_def(p, parent);
    }
    return parent;
}

// `argument_tuple` was already parsed (either by ee_eval_subexpr_fun_param_def_tuple
// in eval_paren_expr's early-tuple path, or the closing ')' was already consumed there too)
fn ee_eval_expr_fun_def(p: *Parser, early_function_header: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_fun_def);
    var def: FunctionDefinition = undefined;
    def.function_header = early_function_header;

    if (try p.peek_eq_tok(.@"pct_;")) {
        p.tok_cursor += 1;
        def.substatement = 0xFFFFFFFF;
    } else {
        def.substatement = try stmt_rules.eval_sub_stmt(p);
    }

    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

// array with "[<expr>,]" or "[]", type with "[<expr>]<expr>" or "[]<expr>"
// already consumed "["
pub fn eval_expr_bracket(p: *Parser) anyerror!u32 {
    var parent: u32 = undefined;
    if (!try p.peek_eq_tok(.@"pct_]")) {
        parent = try eval_expr(p, 0);
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                var children: FixedStack(4096) = .{};
                try children.push(parent);
                while (true) {
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try children.push(try eval_expr(p, 0));
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try p.eat_assert_tok(.@"pct_,");
                }
                parent = p.tree.push_node(.expr_array);
                p.tree.push_extra_childrefs(parent, children.view());
            },
            .@"pct_]" => { // no comma -> type
                p.tok_cursor += 1;
                const lhs = parent;
                parent = p.tree.push_node(.expr_type_array);
                const rhs = try eval_expr(p, 0);
                p.tree.set_node_arg0(parent, lhs);
                p.tree.set_node_arg1(parent, rhs);
            },
            else => return error.IllegalArraySeparatorTerminator,
        }
    } else {
        // is after this an expression? (see lookahead) -> type, else array
        p.tok_cursor += 1;
        if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())]) |expr_f| {
            const lhs = parent;
            parent = p.tree.push_node(.expr_type_array);
            const rhs = try expr_f(p); // consume the expression
            p.tree.set_node_arg0(parent, lhs);
            p.tree.set_node_arg1(parent, rhs);
        } else {
            p.tok_cursor -= 1;
            parent = p.tree.push_node(.expr_array_empty);
            p.tree.set_node_arg0(parent, 0xFFFFFFFF);
        }
    }
    return parent;
}

pub fn eval_expr_typeof(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_typeof);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_sizeof(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_sizeof);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_neg_num(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_neg_num);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_neg_logic(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_neg_logic);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_inc_prefix(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_inc_prefix);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_dec_prefix(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_dec_prefix);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_gen_upperbound_incl(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_gen_upperbound_incl);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_gen_upperbound_excl(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_gen_upperbound_excl);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_true(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_bool);
}

pub fn eval_expr_false(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_bool);
}

pub fn eval_expr_none(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_none);
}

pub fn eval_expr_err(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_err);
}

pub fn eval_expr_deinit(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_deinit);
}

pub fn eval_expr_cont(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_cont);
}

pub fn eval_expr_brk(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_brk);
}

pub fn eval_expr_ret(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_ret);
    if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())]) |expr_f| {
        const child_expr = try expr_f(p);
        p.tree.set_node_arg0(parent, child_expr);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }
    return parent;
}

pub fn eval_expr_if(p: *Parser) anyerror!u32 {
    var parent = p.tree.push_node(.expr_if);

    const if_cond_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, if_cond_expr);
    try p.eat_assert_tok(.@"pct_:");
    const if_body_expr = try eval_expr(p, 0);
    p.tree.set_node_arg1(parent, if_body_expr);

    if (try p.peek_eq_tok(.kw_else)) {
        p.tok_cursor += 1;
        const else_body_expr = try eval_expr(p, 0);
        const if_parent = parent;

        parent = p.tree.push_node(.expr_if_else);
        p.tree.set_node_arg0(parent, if_parent);
        p.tree.set_node_arg1(parent, else_body_expr);
    }

    return parent;
}

pub fn eval_expr_while(p: *Parser) anyerror!u32 {
    const while_expr = p.tree.push_node(.expr_while);
    var parent = while_expr;

    const while_cond_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(while_expr, while_cond_expr);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        const while_repeat_stmt = try stmt_rules.eval_stmt(p);
        parent = p.tree.push_node(.expr_while_with_repeat_stmt);
        p.tree.set_node_arg0(parent, while_expr);
        p.tree.set_node_arg1(parent, while_repeat_stmt);
    }

    try p.eat_assert_tok(.@"pct_:");
    const while_body_expr = try eval_expr(p, 0);
    p.tree.set_node_arg1(while_expr, while_body_expr);

    return parent;
}

pub fn eval_expr_for(p: *Parser) anyerror!u32 {
    const for_expr = p.tree.push_node(.expr_for);
    var parent = for_expr;

    var for_seq_expr = try eval_expr(p, 0);

    if (try p.peek_eq_tok(.kw_in)) {
        p.tok_cursor += 1;
        const for_var = for_seq_expr;
        for_seq_expr = try eval_expr(p, 0);
        p.tree.set_node_arg0(for_expr, for_seq_expr);
        parent = p.tree.push_node(.expr_for_in);
        p.tree.set_node_arg0(parent, for_expr);
        p.tree.set_node_arg1(parent, for_var);
    } else {
        p.tree.set_node_arg0(for_expr, for_seq_expr);
    }

    try p.eat_assert_tok(.@"pct_:");
    const for_body_expr = try eval_expr(p, 0);
    p.tree.set_node_arg1(for_expr, for_body_expr);

    return parent;
}

pub fn eval_expr_loop(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_loop);
    const expr0 = try eval_expr(p, 0);
    if (try p.peek_eq_tok(.@"pct_:")) {
        p.tok_cursor += 1;
        const repeat_stmt = expr0;
        const body_expr = try eval_expr(p, 0);
        p.tree.set_node_arg0(parent, repeat_stmt);
        p.tree.set_node_arg1(parent, body_expr);
    } else {
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
        p.tree.set_node_arg1(parent, expr0);
    }
    return parent;
}

pub fn eval_expr_match(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_match);
    const match_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, match_expr);
    const match_body = try subexpr_rules.eval_subexpr_match_body(p);
    p.tree.set_node_arg1(parent, match_body);
    return parent;
}

pub fn eval_expr_typeptr(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_typeptr);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_ampersand(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.expr_ampersand);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_typeu8(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typeu8);
}

pub fn eval_expr_typeu16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typeu16);
}

pub fn eval_expr_typeu32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typeu32);
}

pub fn eval_expr_typeu64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typeu64);
}

pub fn eval_expr_typei8(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typei8);
}

pub fn eval_expr_typei16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typei16);
}

pub fn eval_expr_typei32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typei32);
}

pub fn eval_expr_typei64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typei64);
}

pub fn eval_expr_typef16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typef16);
}

pub fn eval_expr_typef32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typef32);
}

pub fn eval_expr_typef64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typef64);
}

pub fn eval_expr_typebool(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typebool);
}

pub fn eval_expr_typetype(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typetype);
}

pub fn eval_expr_typetrait(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typetrait);
}

pub fn eval_expr_typevariant(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typevariant);
}

pub fn eval_expr_typeinlfun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typeinlfun);
}

pub fn eval_expr_typefun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typefun);
}

pub fn eval_expr_typestcfun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.expr_typestcfun);
}

pub fn eval_expr_type_or_variant(p: *Parser) anyerror!u32 { // TODO
    p.tok_cursor -= 1; // go back to count how much of '@' are in the scanned token

    const parent = p.tree.push_node(.none);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_trait(p: *Parser) anyerror!u32 { // TODO
    p.tok_cursor -= 1; // to know if 'implof' or '@{' was scanned
    const parent = p.tree.push_node(.none);
    const child_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_expr_fun_call(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_fun_call);
    const param_tuple = try subexpr_rules.eval_subexpr_fun_call_param_tuple(p);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, param_tuple);
    return parent;
}

pub fn eval_expr_array_index(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_array_index);
    const index_expr = try eval_expr(p, 0);
    try p.eat_assert_tok(.@"pct_]");
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, index_expr);
    return parent;
}

pub fn eval_expr_member(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_member);
    const member_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, member_expr);
    return parent;
}

pub fn eval_expr_dereference(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_dereference);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn eval_expr_inc_postfix(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_inc_postfix);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn eval_expr_dec_postfix(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_dec_postfix);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn eval_expr_gen_lowerbound(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_gen_lowerbound);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn eval_expr_gen_incl(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_gen_incl);
    const upper_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, upper_expr);
    return parent;
}

pub fn eval_expr_gen_excl(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_gen_excl);
    const upper_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, upper_expr);
    return parent;
}

pub fn eval_expr_oftype(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_oftype);
    const type_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, type_expr);
    return parent;
}

pub fn eval_expr_as(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_as);
    const type_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, type_expr);
    return parent;
}

pub fn eval_expr_labelarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_labelarrow);
    var rhs = try safeeval_expr_identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        rhs = subexpr_rules.ee_eval_subexpr_destructure(p, rhs); // TODO NEXT
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn safeeval_expr_identifier(p: *Parser) anyerror!u32 {
    if (!try p.pop_tok(.identifier)) return error.IdentifierExpected;
    return p.tree.push_data_node(.expr_identifier, p.tok_cursor - 1);
}

pub fn eval_expr_identifier(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_identifier, p.tok_cursor);
}

pub fn eval_expr_int(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_identifier, p.tok_cursor);
}

pub fn eval_expr_float(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_float, p.tok_cursor);
}

pub fn eval_expr_string(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_string, p.tok_cursor);
}

pub fn eval_expr_char(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_char, p.tok_cursor);
}
