const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const stmt_rules = @import("stmt_rules.zig");
const expr_rules = @import("expr_rules.zig");

pub const FunctionHeader = struct {
    argument_tuple: u32,
    return_type: u32,
};

pub const FunctionDefinitionParameter = struct {
    param_type: u32,
    name: u32,
    default_value: u32,
    where_predicate: u32,
    where_else_value: u32,
};

pub fn ee_eval_subexpr_fun_def_header(p: *Parser, early_expr0_in_tuple: u32) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_fun_def_header);
    var def: FunctionHeader = undefined;
    def.argument_tuple = try ee_eval_subexpr_fun_def_param_tuple(p, early_expr0_in_tuple);

    if (try p.peek_eq_tok(.@"xpct_->")) {
        p.tok_cursor += 1;
        def.return_type = try expr_rules.eval_expr(p, 0);
    } else {
        def.return_type = 0xFFFFFFFF;
    }

    p.tree.set_node_arg0(parent, def.argument_tuple);
    p.tree.set_node_arg1(parent, def.return_type);
    return parent;
}

pub fn ee_eval_subexpr_fun_def_param_tuple(p: *Parser, early_expr0: u32) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_fun_def_param_tuple);

    if (!try p.peek_eq_tok(.@"pct_)")) {
        var params: FixedStack(64) = .{};
        while (true) {
            if (params.cursor == 0) {
                try params.push(try ee_eval_subexpr_fun_def_param(p, early_expr0));
            } else {
                try params.push(try ee_eval_subexpr_fun_def_param(p, try expr_rules.eval_expr(p, 0)));
            }
            switch (try p.peek_tok()) {
                .@"pct_)" => break,
                .@"pct_," => {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"pct_)")) break;
                },
                else => return error.IllegalFunParamDef,
            }
        }
        p.tree.push_extra_childrefs(parent, params.view());
        return parent;
    } else {
        p.tok_cursor += 1;
        return parent;
    }
}

pub fn ee_eval_subexpr_fun_def_param(p: *Parser, early_expr0: u32) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_fun_def_param);
    var def: FunctionDefinitionParameter = undefined;
    // here, we could encounter <expr> <expr> or <expr>
    // + they are followed by , OR ) OR = OR where

    // first expr is safe:
    const a = early_expr0;
    const next_tok = try p.peek_tok();
    if (next_tok != .@"pct_," and next_tok != .@"pct_)" and next_tok != .@"xpct_=" and next_tok != .kw_where) {
        const b = try expr_rules.eval_expr_identifier(p);
        def.param_type = a;
        def.name = b;
    } else {
        def.param_type = a;
        def.name = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.default_value = try expr_rules.eval_expr(p, 0);
    } else {
        def.default_value = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_where)) {
        p.tok_cursor += 1;
        def.where_predicate = try expr_rules.eval_expr(p, 0);
        if (try p.peek_eq_tok(.kw_else)) {
            p.tok_cursor += 1;
            def.where_else_value = try expr_rules.eval_expr(p, 0);
        } else {
            def.where_else_value = 0xFFFFFFFF;
        }
    } else {
        def.where_predicate = 0xFFFFFFFF;
        def.where_else_value = 0xFFFFFFFF;
    }

    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

pub fn eval_subexpr_match_body(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_match_body);
    var match_cases: FixedStack(64) = .{};

    try p.eat_assert_tok(.@"pct_{");

    while (true) {
        try match_cases.push(try eval_subexpr_match_case(p));
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_}")) break;
            },
            .@"pct_}" => break,
            else => return error.IllegalMatchCase,
        }
    }
    p.tree.push_extra_childrefs(parent, match_cases.view());
    return parent;
}

pub fn eval_subexpr_match_case(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_match_case);
    const pattern_expr = try expr_rules.eval_expr(p, 0);
    p.tree.set_node_arg0(parent, pattern_expr);
    p.tree.set_node_arg1(parent, 0xFFFFFFFF);
    if (try p.peek_eq_tok(.@"xpct_=>")) {
        p.tok_cursor += 1;
        const body_expr = try expr_rules.eval_expr(p, 0);
        p.tree.set_node_arg1(parent, body_expr);
    }
    return parent;
}

pub fn eval_subexpr_fun_call_param_tuple(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.subexpr_fun_call_param_tuple);
    try p.eat_assert_tok(.@"xpct_(");

    if (!try p.peek_eq_tok(.@"pct_)")) {
        var params: FixedStack(64) = .{};
        while (true) {
            try params.push(try expr_rules.eval_expr(p, 0));
            switch (try p.peek_tok()) {
                .@"pct_)" => break,
                .@"pct_," => {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"pct_)")) break;
                },
                else => return error.IllegalFunCallParam,
            }
        }
        p.tree.push_extra_childrefs(parent, params.view());
        return parent;
    } else {
        p.tok_cursor += 1;
        return parent;
    }
}
