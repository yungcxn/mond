const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const expr_rules = @import("expr_rules.zig");

pub const Assignment = packed struct {
    name: u32,
    expr: u32,
};

pub fn eval_stmt(p: *Parser) anyerror!u32 {
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

fn eval_substmt(p: *Parser) anyerror!u32 {
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

fn opt_eval_substmt(p: *Parser) anyerror!u32 {
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_inlfun_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_fun_assign(p: *Parser, public: bool) anyerror!u32 { // TODO inline
    const parent = p.tree.push_node(if (public) .stmt_assign_fun_pub else .stmt_assign_fun);

    var def: Assignment = undefined;
    if (!try p.peek_eq_tok(.identifier)) return error.IdentifierExpected;
    def.name = try expr_rules.eval_expr_identifier(p);
    try p.eat_assert_tok(.@"xpct_=");
    def.expr = try expr_rules.eval_expr(p, 0);
    try p.eat_assert_tok(.@"pct_;");

    p.tree.set_node_arg0(parent, def.name);
    p.tree.set_node_arg1(parent, def.expr);
    return parent;
}

pub fn eval_sub_stmt(p: *Parser) anyerror!u32 {
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_type_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_trait_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_variant_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_stcfun_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}

pub fn eval_generic_assign(p: *Parser, public: bool) anyerror!u32 {
    _ = public;
    const node_idx = p.tree.push_node(.none);
    return node_idx;
}
