const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const stmt_rules = @import("stmt_rules.zig");
const subexpr_rules = @import("subexpr_rules.zig");

pub const FunctionDefinition = struct {
    function_header: u32,
    substatement: u32,
};

pub const TypeDefinition = struct {
    parameter_tuple: u32,
    sizeof_expr: u32,
    trait_def: u32,
};

pub const VariantDefinition = struct {
    parameter_tuple: u32,
    tagof_expr: u32,
    sizeof_expr: u32,
};

pub const TraitDefinition = struct {
    implof_tuple: u32,
    body: u32,
};

// *** rule templates *** //

pub fn templ_binary_expr(kind: ParseTree.Node.Kind) fn (parser: *Parser, lhs: u32) anyerror!u32 {
    return struct {
        pub fn eval(p: *Parser, lhs: u32) anyerror!u32 {
            const parent = p.tree.push_node(kind);
            p.tree.set_node_arg0(parent, lhs);
            const rhs = try eval_expr(p, 0);
            p.tree.set_node_arg1(parent, rhs);
            return parent;
        }
    }.eval;
}

// *** rule generators end *** //

pub fn eval_expr(p: *Parser, prec: u8) anyerror!u32 {
    var parent = try lookahead.pre_expression[@intFromEnum(try p.pop_tok())].?(p);
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

fn eval_type_def_tail(p: *Parser, kind: ParseTree.Node.Kind, parameter_tuple: u32) anyerror!u32 {
    var def: TypeDefinition = undefined;
    def.parameter_tuple = parameter_tuple;

    if (try p.peek_eq_tok(.kw_sizeof)) {
        p.tok_cursor += 1;
        def.sizeof_expr = try eval_expr(p, 0);
    } else {
        def.sizeof_expr = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_implof) or try p.peek_eq_tok(.@"xpct_@{")) {
        def.trait_def = try eval_expr_trait(p);
    } else {
        def.trait_def = 0xFFFFFFFF;
    }

    const parent = p.tree.push_node(kind);
    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

fn eval_variant_def_tail(p: *Parser, kind: ParseTree.Node.Kind, parameter_tuple: u32) anyerror!u32 {
    var def: VariantDefinition = undefined;
    def.parameter_tuple = parameter_tuple;

    if (try p.peek_eq_tok(.kw_tagof)) {
        p.tok_cursor += 1;
        def.tagof_expr = try eval_expr(p, 0);
    } else {
        def.tagof_expr = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_sizeof)) {
        p.tok_cursor += 1;
        def.sizeof_expr = try eval_expr(p, 0);
    } else {
        def.sizeof_expr = 0xFFFFFFFF;
    }

    const parent = p.tree.push_node(kind);
    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

pub fn eval_expr_type_or_variant(p: *Parser) anyerror!u32 {
    p.tok_cursor -= 1;
    const open_tok = try p.pop_tok();

    if (try p.peek_eq_tok(.@"pct_)")) return error.EmptyTypeOrVariantDef;

    const is_mut0 = try p.peek_eq_tok(.kw_mut);
    if (is_mut0) p.tok_cursor += 1;
    const early_expr0 = try eval_expr(p, 0);

    var name: u32 = 0xFFFFFFFF;
    var of_type: u32 = 0xFFFFFFFF;
    var default_value: u32 = 0xFFFFFFFF;
    var where_predicate: u32 = 0xFFFFFFFF;
    var where_else_value: u32 = 0xFFFFFFFF;

    var kind: ?enum { type_def, variant_def } = null;

    if (try p.peek_eq_tok(.kw_of)) {
        p.tok_cursor += 1;
        kind = .variant_def;
        of_type = try eval_expr(p, 0);
    } else {
        const t = try p.peek_tok();
        if (t != .@"pct_," and t != .@"xpct_|" and t != .@"pct_)" and
            t != .@"xpct_=" and t != .kw_where)
        {
            try p.eat_assert_tok(.identifier);
            name = try eval_expr_identifier(p);
            kind = .type_def;
        }
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        default_value = try eval_expr(p, 0);
    }

    if (kind != .variant_def) {
        // "where" only exists on the type side; if we already know we're
        // building a variant (saw "of"), skip this check entirely.
        if (try p.peek_eq_tok(.kw_where)) {
            p.tok_cursor += 1;
            kind = .type_def;
            where_predicate = try eval_expr(p, 0);
            if (try p.peek_eq_tok(.kw_else)) {
                p.tok_cursor += 1;
                where_else_value = try eval_expr(p, 0);
            }
        }
    }

    if (kind == null) {
        // bare `early_expr0` with no tail at all - only the separator can tell us
        kind = switch (try p.peek_tok()) {
            .@"pct_," => .type_def,
            .@"xpct_|" => .variant_def,
            // grammar requires a trailing "," or "|" even for a single element
            else => return error.IllegalTypeOrVariantDef,
        };
    }

    if (kind.? == .variant_def and is_mut0) return error.IllegalMutOnVariantParam;

    switch (kind.?) {
        .type_def => {
            const type_kind: ParseTree.Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .expr_type_def,
                .@"xpct_@@(" => .expr_type_def_packed,
                .@"xpct_@@@(" => return error.IllegalUnionsizedTypeDef,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const param = p.tree.push_node(if (is_mut0) .subexpr_type_param_mut else .subexpr_type_param);
                var def: subexpr_rules.TypeParameter = .{
                    .param_type = early_expr0,
                    .name = name,
                    .default_value = default_value,
                    .where_predicate = where_predicate,
                    .where_else_value = where_else_value,
                };
                p.tree.push_extra_childrefs(param, &def);
                try params.push(param);
            }
            while (try p.peek_eq_tok(.@"pct_,")) {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_)")) break;
                try params.push(try subexpr_rules.ee_eval_subexpr_type_param(p, null));
            }
            try p.eat_assert_tok(.@"pct_)");
            const param_tuple = p.tree.push_node(.subexpr_type_param_tuple);
            p.tree.push_extra_childrefs(param_tuple, params.view());
            return try eval_type_def_tail(p, type_kind, param_tuple);
        },
        .variant_def => {
            const variant_kind: ParseTree.Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .expr_variant_def,
                .@"xpct_@@(" => .expr_variant_def_packed,
                .@"xpct_@@@(" => .expr_variant_def_unionsized,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const first = p.tree.push_node(.subexpr_variant_param);
                var def: subexpr_rules.VariantParameter = .{
                    .name = early_expr0,
                    .of_type = of_type,
                    .tag_value = default_value,
                };
                p.tree.push_extra_childrefs(first, &def);
                try params.push(first);
            }
            while (try p.peek_eq_tok(.@"xpct_|")) {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_)")) break;
                try params.push(try subexpr_rules.ee_eval_subexpr_variant_param(p, null));
            }
            try p.eat_assert_tok(.@"pct_)");
            const param_tuple = p.tree.push_node(.subexpr_variant_param_tuple);
            p.tree.push_extra_childrefs(param_tuple, params.view());
            return try eval_variant_def_tail(p, variant_kind, param_tuple);
        },
    }
}

pub fn eval_expr_trait(p: *Parser) anyerror!u32 {
    p.tok_cursor -= 1; // to know if 'implof' or '@{' was scanned
    var def: TraitDefinition = undefined;

    if (try p.peek_eq_tok(.kw_implof)) {
        p.tok_cursor += 1;
        var impls: FixedStack(64) = .{};
        while (true) {
            try impls.push(try eval_expr(p, 0));
            switch (try p.peek_tok()) {
                .@"xpct_@{" => break,
                .@"pct_," => {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"xpct_@{")) break;
                },
                else => return error.IllegalImplofList,
            }
        }
        const implof_tuple = p.tree.push_node(.subexpr_trait_implof_tuple);
        p.tree.push_extra_childrefs(implof_tuple, impls.view());
        def.implof_tuple = implof_tuple;
    } else {
        def.implof_tuple = 0xFFFFFFFF;
    }

    try p.eat_assert_tok(.@"xpct_@{");
    var members: FixedStack(4096) = .{};
    while (!try p.peek_eq_tok(.@"pct_}")) {
        try members.push(try stmt_rules.eval_stmt_assign(p));
    }
    p.tok_cursor += 1; // consume "}"

    const body = p.tree.push_node(.subexpr_trait_body);
    p.tree.push_extra_childrefs(body, members.view());
    def.body = body;

    const parent = p.tree.push_node(.expr_trait_def);
    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

pub fn eval_expr_unify_variants(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_unify_variants);
    const type_expr = try eval_expr(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, type_expr);
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
    try p.eat_assert_tok(.identifier);
    var rhs = try eval_expr_identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try subexpr_rules.ee_eval_subexpr_destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn eval_expr_optarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_optarrow);
    try p.eat_assert_tok(.identifier);
    var rhs = try eval_expr_identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try subexpr_rules.ee_eval_subexpr_destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn eval_expr_errarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_errarrow);
    try p.eat_assert_tok(.identifier);
    var rhs = try eval_expr_identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try subexpr_rules.ee_eval_subexpr_destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn eval_expr_errhandle(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_errhandle);
    p.tree.set_node_arg0(parent, lhs);

    if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())]) |expr_f| {
        const child_expr = try expr_f(p);
        p.tree.set_node_arg1(parent, child_expr);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }

    return parent;
}

pub fn eval_expr_opthandle(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.expr_opthandle);
    p.tree.set_node_arg0(parent, lhs);

    if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())]) |expr_f| {
        const child_expr = try expr_f(p);
        p.tree.set_node_arg1(parent, child_expr);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }

    return parent;
}

pub fn eval_expr_defer(p: *Parser, lhs: u32) anyerror!u32 {
    if (try p.peek_eq_tok(.kw_deinit)) {
        p.tok_cursor += 1;
        if (lookahead.pre_expression[@intFromEnum(try p.pop_tok())] == null) {
            const parent = p.tree.push_node(.expr_defer_with_deinit);
            p.tree.set_node_arg0(parent, lhs);
            return parent;
        } else {
            p.tok_cursor -= 2;
        }
    }
    const parent = p.tree.push_node(.expr_defer);
    p.tree.set_node_arg0(parent, lhs);
    const rhs = try eval_expr(p, 0);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn eval_expr_identifier(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_identifier, p.tok_cursor - 1);
}

pub fn eval_expr_int(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_identifier, p.tok_cursor - 1);
}

pub fn eval_expr_float(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_float, p.tok_cursor - 1);
}

pub fn eval_expr_string(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_string, p.tok_cursor - 1);
}

pub fn eval_expr_char(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.expr_char, p.tok_cursor - 1);
}
