const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const expr_rules = @import("expr_rules.zig");
const lookahead = @import("lookahead.zig");

pub const Assignment = packed struct {
    name: u32,
    expr: u32,
};

pub fn eval_stmt(p: *Parser) anyerror!u32 {
    return try lookahead.pre_statement[@intFromEnum(try p.peek_tok())](p);
}

pub fn eval_assign_stmt(p: *Parser) anyerror!u32 {
    const parent = try eval_stmt(p);
    if (!p.tree.ast_nodes.get_field(.nk, parent).?.is_stmt_assign()) return error.AssignStatementExpected;
    return parent;
}

pub fn eval_sub_stmt(p: *Parser) anyerror!u32 {
    switch (try p.peek_tok()) {
        .@"pct_:" => {
            p.tok_cursor += 1;
            return try eval_stmt(p);
        },
        .@"pct_{" => {
            return try eval_stmt_block(p);
        },
        else => return error.SubStatementExpected,
    }
}

pub fn eval_stmt_block(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_block);
    var block_stmts: FixedStack(64) = .{};
    while (true) {
        if (try p.peek_eq_tok(.@"pct_}")) {
            p.tok_cursor += 1;
            p.tree.push_extra_childrefs(parent, block_stmts.view());
            return parent;
        }

        try block_stmts.push(try eval_stmt(p));
    }
}

pub fn eval_stmt_if(p: *Parser) anyerror!u32 {
    var parent = p.tree.push_node(.stmt_if);
    const cond_expr = try expr_rules.eval_expr(p, 0);
    p.tree.set_node_arg0(parent, cond_expr);
    const if_body_expr = try eval_sub_stmt(p);
    p.tree.set_node_arg1(parent, if_body_expr);

    if (try p.peek_eq_tok(.kw_else)) {
        p.tok_cursor += 1;
        const else_block = try eval_stmt(p);
        const if_parent = parent;

        parent = p.tree.push_node(.stmt_if_else);
        p.tree.set_node_arg0(parent, if_parent);
        p.tree.set_node_arg1(parent, else_block);
    }

    return parent;
}

pub fn eval_stmt_while(p: *Parser) anyerror!u32 {
    const while_stmt = p.tree.push_node(.stmt_while);
    var parent = while_stmt;

    const while_cond_expr = try expr_rules.eval_expr(p, 0);
    p.tree.set_node_arg0(while_stmt, while_cond_expr);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        const while_repeat_stmt = try eval_stmt(p);
        parent = p.tree.push_node(.stmt_while_with_repeat_stmt);
        p.tree.set_node_arg0(parent, while_stmt);
        p.tree.set_node_arg1(parent, while_repeat_stmt);
    }

    try p.eat_assert_tok(.@"pct_:");
    const while_body_stmt = try eval_sub_stmt(p);
    p.tree.set_node_arg1(while_stmt, while_body_stmt);

    return parent;
}

pub fn eval_stmt_for(p: *Parser) anyerror!u32 {
    const for_stmt = p.tree.push_node(.stmt_for);
    var parent = for_stmt;

    var for_seq_expr = try expr_rules.eval_expr(p, 0);

    if (try p.peek_eq_tok(.kw_in)) {
        p.tok_cursor += 1;
        const for_var = for_seq_expr;
        for_seq_expr = try expr_rules.eval_expr(p, 0);
        p.tree.set_node_arg0(for_stmt, for_seq_expr);
        parent = p.tree.push_node(.stmt_for_in);
        p.tree.set_node_arg0(parent, for_stmt);
        p.tree.set_node_arg1(parent, for_var);
    } else {
        p.tree.set_node_arg0(for_stmt, for_seq_expr);
    }
    const for_body_stmt = try eval_sub_stmt(p);
    p.tree.set_node_arg1(for_stmt, for_body_stmt);
    return parent;
}

pub fn eval_stmt_loop(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_loop);

    // this is "kinda" dirty as `sub_stmt` could change and this function would need a update too
    switch (try p.peek_tok()) {
        .@"pct_:", .@"pct_{" => {
            p.tree.set_node_arg0(parent, 0xFFFFFFFF);
            p.tree.set_node_arg1(parent, try eval_sub_stmt(p));
        },
        else => {
            const loop_expr = try expr_rules.eval_expr(p, 0);
            p.tree.set_node_arg0(parent, loop_expr);
            p.tree.set_node_arg1(parent, try eval_sub_stmt(p));
        },
    }
    return parent;
}

pub fn eval_stmt_match(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_match);
    const match_expr = try expr_rules.eval_expr(p, 0);
    p.tree.set_node_arg0(parent, match_expr);

    const body = p.tree.push_node(.substmt_match_body);
    try p.eat_assert_tok(.@"pct_{");
    var match_cases: FixedStack(64) = .{};
    while (true) {
        const case_node = p.tree.push_node(.subexpr_match_case);
        const pattern_expr = try expr_rules.eval_expr(p, 0);
        p.tree.set_node_arg0(case_node, pattern_expr);
        p.tree.set_node_arg1(case_node, 0xFFFFFFFF);
        if (try p.peek_eq_tok(.@"xpct_=>")) {
            p.tok_cursor += 1;
            const body_expr = try expr_rules.eval_expr(p, 0);
            p.tree.set_node_arg1(case_node, body_expr);
        }
        try match_cases.push(case_node);
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_}")) break;
            },
            .@"pct_}" => break,
            else => return error.IllegalMatchCase,
        }
    }
    p.tree.push_extra_childrefs(body, match_cases.view());

    p.tree.set_node_arg1(parent, body);
    return parent;
}

pub fn eval_stmt_cont(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.stmt_cont);
}

pub fn eval_stmt_brk(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.stmt_brk);
}

pub fn eval_stmt_ret(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_ret);
    if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())]) |expr_f| {
        const child_expr = try expr_f(p);
        p.tree.set_node_arg0(parent, child_expr);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }
    return parent;
}

pub fn eval_stmt_defer(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_defer);
    const child_stmt = try eval_sub_stmt(p);
    p.tree.set_node_arg0(parent, child_stmt);
    return parent;
}

pub fn eval_stmt_deinit(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.stmt_deinit);
    const child_expr = try expr_rules.eval_expr(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn eval_generic_stmt(p: *Parser) anyerror!u32 {
    // const parent = p.tree.push_node(.stmt_generic);
    // const child_expr = try expr_rules.eval_expr(p, 0);
    // p.tree.set_node_arg0(parent, child_expr);
    // return parent;
    _ = p; // TODO
    return error.TODO;
}
