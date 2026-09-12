const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const partial = @import("partial.zig");

// might seem repetitive for now, but makes extensions easy (FOR NOW)

// TODO: bake these structs into a parse table with the node

pub const FunctionDefinition = struct {
    function_header: u32,
    body: u32,
};

pub const TypeDefinition = struct {
    parameter_tuple: u32,
    sizeof: u32,
    trait_def: u32,
};

pub const VariantDefinition = struct {
    parameter_tuple: u32,
    tagof: u32,
    sizeof: u32,
};

pub const TraitDefinition = struct {
    implof_tuple: u32,
    body: u32,
};

// *** rule templates *** //

pub fn templ_binary(kind: ParseTree.Node.Kind) fn (parser: *Parser, lhs: u32) anyerror!u32 {
    return struct {
        pub fn eval(p: *Parser, lhs: u32) anyerror!u32 {
            const parent = p.tree.push_node(kind);
            p.tree.set_node_arg0(parent, lhs);
            const rhs = try any(p, 0);
            p.tree.set_node_arg1(parent, rhs);
            return parent;
        }
    }.eval;
}

// *** rule generators end *** //

pub fn any(p: *Parser, prec: u8) anyerror!u32 {
    var parent = try lookahead.pre[@intFromEnum(try p.pop_tok())].?(p);
    while (lookahead.post[@intFromEnum(try p.pop_tok())]) |post_f| {
        const lhs = parent;
        parent = try post_f(p, lhs);
    } else {
        p.tok_cursor -= 1;
    }

    while (lookahead.binary_compute[@intFromEnum(try p.pop_tok())]) |precd_bin| {
        if (precd_bin.prec < prec) {
            p.tok_cursor -= 1;
            break;
        }

        const lhs = parent;
        parent = try precd_bin.f(p, lhs);
        p.tree.set_node_arg0(parent, lhs);
    } else {
        p.tok_cursor -= 1;
    }

    return parent;
}

// function definition start OR some function's type start OR capture start
// `(` is already consumed
pub fn paren(p: *Parser) anyerror!u32 {
    var parent: u32 = 0xFFFFFFFF;
    if (!try p.peek_eq_tok(.@"pct_)")) {
        parent = try any(p, 0);
        // it was '(' behind, then expr, then ')', if after it's `->` or `:` or `{`, it's a func!
        try p.eat_assert_tok(.@"pct_)");
        switch (try p.peek_tok()) {
            .@"xpct_->", .@"pct_:", .@"pct_{" => {
                // `parent` was an expression in a "()", but it's actually a function parameter tuple
                parent = try partial.ee_fun_header(p, parent);
                parent = try ee_def_fun(p, parent);
            },
            else => {
                // `parent` just needs to be in a capture expression
                const child = parent;
                parent = p.tree.push_node(.capture);
                p.tree.set_node_arg0(parent, child);
            },
        }
    } else {
        // guaranteed to be a `subexpr_fun_param_def_tuple`, and `paren` is early
        parent = try partial.ee_fun_header(p, parent);
        parent = try ee_def_fun(p, parent);
    }
    return parent;
}

// `argument_tuple` was already parsed (either by ee_eval_subexpr_fun_param_def_tuple
// in paren's early-tuple path, or the closing ')' was already consumed there too)
fn ee_def_fun(p: *Parser, early_function_header: u32) anyerror!u32 {
    const parent = p.tree.push_node(.def_fun);
    var def: FunctionDefinition = undefined;
    def.function_header = early_function_header;

    switch (try p.peek_tok()) {
        .@"pct_:" => {
            p.tok_cursor += 1;
            if (try p.peek_eq_tok(.@"pct_{")) return error.IllegalBlockAfterColon;
            def.body = try any(p, 0);
        },
        .@"pct_{" => {
            def.body = try any(p, 0);
        },
        else => {
            def.body = 0xFFFFFFFF;
        },
    }

    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

// array with "[<expr>,]" or "[]", type with "[<expr>]<expr>" or "[]<expr>"
// already consumed "["
pub fn bracket(p: *Parser) anyerror!u32 {
    var parent: u32 = undefined;
    if (!try p.peek_eq_tok(.@"pct_]")) {
        parent = try any(p, 0);
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                var children: FixedStack(4096) = .{};
                try children.push(parent);
                while (true) {
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try children.push(try any(p, 0));
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try p.eat_assert_tok(.@"pct_,");
                }
                parent = p.tree.push_node(.array);
                p.tree.push_extra_childrefs(parent, children.view());
            },
            .@"pct_]" => { // no comma -> type
                p.tok_cursor += 1;
                const lhs = parent;
                parent = p.tree.push_node(.type_array);
                const rhs = try any(p, 0);
                p.tree.set_node_arg0(parent, lhs);
                p.tree.set_node_arg1(parent, rhs);
            },
            else => return error.IllegalArraySeparatorTerminator,
        }
    } else {
        // is after this an expression? (see lookahead) -> type, else array
        p.tok_cursor += 1;
        if (lookahead.pre[@intFromEnum(try p.pop_tok())]) |f| {
            const lhs = parent;
            parent = p.tree.push_node(.type_array);
            const rhs = try f(p); // consume the expression
            p.tree.set_node_arg0(parent, lhs);
            p.tree.set_node_arg1(parent, rhs);
        } else {
            p.tok_cursor -= 1;
            parent = p.tree.push_node(.array);
            p.tree.set_node_arg0(parent, 0xFFFFFFFF);
        }
    }
    return parent;
}

pub fn typeof(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.typeof);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn sizeof(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.sizeof);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn neg_num(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.neg_num);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn neg_logic(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.neg_logic);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn inc_prefix(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.inc_prefix);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn dec_prefix(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.dec_prefix);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn gen_upperbound_incl(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.gen_upperbound_incl);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn gen_upperbound_excl(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.gen_upperbound_excl);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn true_(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.boolean);
    p.tree.set_node_arg0(parent, 1);
    return parent;
}

pub fn false_(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.boolean);
    p.tree.set_node_arg0(parent, 0);
    return parent;
}

pub fn none(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.none);
}

pub fn err(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.err);
}

pub fn deinit(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.deinit);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn cont(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.cont);
}

pub fn brk(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.brk);
}

pub fn ret(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.ret);
    if (lookahead.pre[@intFromEnum(try p.pop_tok())]) |f| {
        const child = try f(p);
        p.tree.set_node_arg0(parent, child);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }
    return parent;
}

pub fn if_(p: *Parser) anyerror!u32 {
    var parent = p.tree.push_node(.if_then);

    const if_cond = try any(p, 0);
    p.tree.set_node_arg0(parent, if_cond);
    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalIfFormat,
    }

    const if_body = try any(p, 0);
    p.tree.set_node_arg1(parent, if_body);

    if (try p.peek_eq_tok(.kw_else)) {
        p.tok_cursor += 1;
        const else_body = try any(p, 0);
        const if_parent = parent;

        parent = p.tree.push_node(.if_else);
        p.tree.set_node_arg0(parent, if_parent);
        p.tree.set_node_arg1(parent, else_body);
    }

    return parent;
}

pub fn while_(p: *Parser) anyerror!u32 {
    const while_node = p.tree.push_node(.@"while");
    var parent = while_node;

    const while_cond = try any(p, 0);
    p.tree.set_node_arg0(while_node, while_cond);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        const while_repeat = try any(p, 0);
        parent = p.tree.push_node(.while_with_repeat_stmt);
        p.tree.set_node_arg0(parent, while_node);
        p.tree.set_node_arg1(parent, while_repeat);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalWhileFormat,
    }

    const while_body = try any(p, 0);
    p.tree.set_node_arg1(while_node, while_body);

    return parent;
}

pub fn for_(p: *Parser) anyerror!u32 {
    const for_node = p.tree.push_node(.for_seq);
    var parent = for_node;

    var for_seq = try any(p, 0);

    if (try p.peek_eq_tok(.kw_in)) {
        p.tok_cursor += 1;
        const for_var = for_seq;
        for_seq = try any(p, 0);
        p.tree.set_node_arg0(for_node, for_seq);
        parent = p.tree.push_node(.for_in_seq);
        p.tree.set_node_arg0(parent, for_node);
        p.tree.set_node_arg1(parent, for_var);
    } else {
        p.tree.set_node_arg0(for_node, for_seq);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalForFormat,
    }

    const for_body = try any(p, 0);
    p.tree.set_node_arg1(for_node, for_body);

    return parent;
}

pub fn loop(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.loop);
    const node0 = try any(p, 0);

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => {
            p.tree.set_node_arg0(parent, 0xFFFFFFFF);
            p.tree.set_node_arg1(parent, node0);
            return parent;
        },
    }

    p.tok_cursor += 1;
    const node1 = try any(p, 0);
    p.tree.set_node_arg0(parent, node0);
    p.tree.set_node_arg1(parent, node1);

    return parent;
}

pub fn match(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.match);
    const to_match = try any(p, 0);
    p.tree.set_node_arg0(parent, to_match);
    const match_body = try partial.match_body(p);
    p.tree.set_node_arg1(parent, match_body);
    return parent;
}

pub fn type_ptr(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.type_ptr);
    const child_expr = try any(p, 0);
    p.tree.set_node_arg0(parent, child_expr);
    return parent;
}

pub fn type_ptrmut(p: *Parser) anyerror!u32 {
    const parent = p.tree.push_node(.type_ptrmut);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, child);
    return parent;
}

pub fn type_u8(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_u8);
}

pub fn type_u16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_u16);
}

pub fn type_u32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_u32);
}

pub fn type_u64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_u64);
}

pub fn type_i8(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_i8);
}

pub fn type_i16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_i16);
}

pub fn type_i32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_i32);
}

pub fn type_i64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_i64);
}

pub fn type_f16(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_f16);
}

pub fn type_f32(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_f32);
}

pub fn type_f64(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_f64);
}

pub fn type_bool(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_bool);
}

pub fn type_type(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_type);
}

pub fn type_trait(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_trait);
}

pub fn type_variant(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_variant);
}

pub fn type_inlfun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_inlfun);
}

pub fn type_fun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_fun);
}

pub fn type_stcfun(p: *Parser) anyerror!u32 {
    return p.tree.push_node(.type_stcfun);
}

pub fn type_or_variant(p: *Parser) anyerror!u32 {
    p.tok_cursor -= 1;
    const open_tok = try p.pop_tok();

    if (try p.peek_eq_tok(.@"pct_)")) return error.EmptyTypeOrVariantDef;

    const is_mut0 = try p.peek_eq_tok(.kw_mut);
    if (is_mut0) p.tok_cursor += 1;
    const early_node0 = try any(p, 0);

    var name: u32 = 0xFFFFFFFF;
    var of_type: u32 = 0xFFFFFFFF;
    var default_value: u32 = 0xFFFFFFFF;
    var where_predicate: u32 = 0xFFFFFFFF;
    var where_else_value: u32 = 0xFFFFFFFF;

    var kind: ?enum { type, variant } = null;

    if (try p.peek_eq_tok(.kw_of)) {
        p.tok_cursor += 1;
        kind = .variant;
        of_type = try any(p, 0);
    } else {
        const t = try p.peek_tok();
        if (t != .@"pct_," and t != .@"xpct_|" and t != .@"pct_)" and
            t != .@"xpct_=" and t != .kw_where)
        {
            try p.eat_assert_tok(.identifier);
            name = try identifier(p);
            kind = .type;
        }
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        default_value = try any(p, 0);
    }

    if (kind != .variant) {
        // "where" only exists on the type side; if we already know we're
        // building a variant (saw "of"), skip this check entirely.
        if (try p.peek_eq_tok(.kw_where)) {
            p.tok_cursor += 1;
            kind = .type;
            where_predicate = try any(p, 0);
            if (try p.peek_eq_tok(.kw_else)) {
                p.tok_cursor += 1;
                where_else_value = try any(p, 0);
            }
        }
    }

    if (kind == null) {
        // bare `early_node0` with no tail at all - only the separator can tell us
        kind = switch (try p.peek_tok()) {
            .@"pct_," => .type,
            .@"xpct_|" => .variant,
            // grammar requires a trailing "," or "|" even for a single element
            else => return error.IllegalTypeOrVariantDef,
        };
    }

    if (kind.? == .variant and is_mut0) return error.IllegalMutOnVariantParam;

    switch (kind.?) {
        .type => {
            const type_kind: ParseTree.Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .def_type,
                .@"xpct_@@(" => .def_type_packed,
                .@"xpct_@@@(" => return error.IllegalUnionsizedTypeDef,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const param = p.tree.push_node(if (is_mut0) .partial__type_param_mut else .partial__type_param);
                var param_def: partial.TypeParameter = .{
                    .param_type = early_node0,
                    .name = name,
                    .default_value = default_value,
                    .where_predicate = where_predicate,
                    .where_else_value = where_else_value,
                };
                p.tree.push_extra_childrefs(param, &param_def);
                try params.push(param);
            }
            while (try p.peek_eq_tok(.@"pct_,")) {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_)")) break;
                try params.push(try partial.type_param(p, null));
            }
            try p.eat_assert_tok(.@"pct_)");
            const param_tuple = p.tree.push_node(.partial__type_param_tuple);
            p.tree.push_extra_childrefs(param_tuple, params.view());

            const parent = p.tree.push_node(type_kind);
            var type_def: TypeDefinition = undefined;
            type_def.parameter_tuple = param_tuple;

            if (try p.peek_eq_tok(.kw_sizeof)) {
                p.tok_cursor += 1;
                type_def.sizeof = try any(p, 0);
            } else {
                type_def.sizeof = 0xFFFFFFFF;
            }

            if (try p.peek_eq_tok(.kw_implof) or try p.peek_eq_tok(.@"xpct_@{")) {
                p.tok_cursor += 1;
                type_def.trait_def = try trait(p);
            } else {
                type_def.trait_def = 0xFFFFFFFF;
            }

            p.tree.push_extra_childrefs(parent, &type_def);
            return parent;
        },
        .variant => {
            const variant_kind: ParseTree.Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .def_variant,
                .@"xpct_@@(" => .def_variant_packed,
                .@"xpct_@@@(" => .def_variant_unionsized,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const first = p.tree.push_node(.partial__variant_param);
                var param_def: partial.VariantParameter = .{
                    .name = early_node0,
                    .of_type = of_type,
                    .tag_value = default_value,
                };
                p.tree.push_extra_childrefs(first, &param_def);
                try params.push(first);
            }
            while (try p.peek_eq_tok(.@"xpct_|")) {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_)")) break;
                try params.push(try partial.variant_param(p, null));
            }
            try p.eat_assert_tok(.@"pct_)");
            const param_tuple = p.tree.push_node(.partial__variant_param_tuple);
            p.tree.push_extra_childrefs(param_tuple, params.view());

            const parent = p.tree.push_node(variant_kind);
            var variant_def: VariantDefinition = undefined;
            variant_def.parameter_tuple = param_tuple;

            if (try p.peek_eq_tok(.kw_tagof)) {
                p.tok_cursor += 1;
                variant_def.tagof = try any(p, 0);
            } else {
                variant_def.tagof = 0xFFFFFFFF;
            }

            if (try p.peek_eq_tok(.kw_sizeof)) {
                p.tok_cursor += 1;
                variant_def.sizeof = try any(p, 0);
            } else {
                variant_def.sizeof = 0xFFFFFFFF;
            }

            p.tree.push_extra_childrefs(parent, &variant_def);
            return parent;
        },
    }
}

pub fn trait(p: *Parser) anyerror!u32 {
    p.tok_cursor -= 1; // to know if 'implof' or '@{' was scanned
    var def: TraitDefinition = undefined;

    if (try p.peek_eq_tok(.kw_implof)) {
        p.tok_cursor += 1;
        var impls: FixedStack(64) = .{};
        while (true) {
            try impls.push(try any(p, 0));
            switch (try p.peek_tok()) {
                .@"xpct_@{" => break,
                .@"pct_," => {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"xpct_@{")) break;
                },
                else => return error.IllegalImplofList,
            }
        }
        const implof_tuple = p.tree.push_node(.partial__trait_implof_tuple);
        p.tree.push_extra_childrefs(implof_tuple, impls.view());
        def.implof_tuple = implof_tuple;
    } else {
        def.implof_tuple = 0xFFFFFFFF;
    }

    try p.eat_assert_tok(.@"xpct_@{");
    var members: FixedStack(4096) = .{};
    while (!try p.peek_eq_tok(.@"pct_}")) {
        try members.push(try any(p, 0));
    }
    p.tok_cursor += 1; // consume "}"

    const body = p.tree.push_node(.partial__trait_body);
    p.tree.push_extra_childrefs(body, members.view());
    def.body = body;

    const parent = p.tree.push_node(.def_trait);
    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

pub fn unify_variants(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.unify_variants);
    const childtype = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, childtype);
    return parent;
}

pub fn fun_call(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.fun_call);
    const param_tuple = try partial.fun_call_param_tuple(p);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, param_tuple);
    return parent;
}

pub fn array_index(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.array_index);
    const child = try any(p, 0);
    try p.eat_assert_tok(.@"pct_]");
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, child);
    return parent;
}

pub fn member(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.member);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, child);
    return parent;
}

pub fn dereference(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.dereference);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn address_of(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.address_of);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn inc_postfix(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.inc_postfix);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn dec_postfix(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.dec_postfix);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn gen_lowerbound(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.gen_lowerbound);
    p.tree.set_node_arg0(parent, lhs);
    return parent;
}

pub fn gen_incl(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.gen_incl);
    const upper = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, upper);
    return parent;
}

pub fn gen_excl(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.gen_excl);
    const upper = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, upper);
    return parent;
}

pub fn oftype(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.oftype);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, child);
    return parent;
}

pub fn as(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.as);
    const child = try any(p, 0);
    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, child);
    return parent;
}

pub fn labelarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.labelarrow);
    try p.eat_assert_tok(.identifier);
    var rhs = try any(p, 0);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try partial.destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn optarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.optarrow);
    try p.eat_assert_tok(.identifier);
    var rhs = try any(p, 0);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try partial.destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn errarrow(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.errarrow);
    try p.eat_assert_tok(.identifier);
    var rhs = try any(p, 0);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        rhs = try partial.destructure(p, rhs);
    }

    p.tree.set_node_arg0(parent, lhs);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn errhandle(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.errhandle);
    p.tree.set_node_arg0(parent, lhs);

    if (lookahead.pre[@intFromEnum(try p.pop_tok())]) |f| {
        const child = try f(p);
        p.tree.set_node_arg1(parent, child);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }

    return parent;
}

pub fn opthandle(p: *Parser, lhs: u32) anyerror!u32 {
    const parent = p.tree.push_node(.opthandle);
    p.tree.set_node_arg0(parent, lhs);

    if (lookahead.pre[@intFromEnum(try p.pop_tok())]) |f| {
        const child = try f(p);
        p.tree.set_node_arg1(parent, child);
    } else {
        p.tok_cursor -= 1;
        p.tree.set_node_arg0(parent, 0xFFFFFFFF);
    }

    return parent;
}

pub fn defer_(p: *Parser, lhs: u32) anyerror!u32 {
    if (try p.peek_eq_tok(.kw_deinit)) {
        p.tok_cursor += 1;
        if (lookahead.pre[@intFromEnum(try p.pop_tok())] == null) {
            const parent = p.tree.push_node(.defer_with_deinit);
            p.tree.set_node_arg0(parent, lhs);
            return parent;
        } else {
            p.tok_cursor -= 2;
        }
    }
    const parent = p.tree.push_node(.@"defer");
    p.tree.set_node_arg0(parent, lhs);
    const rhs = try any(p, 0);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn identifier(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.identifier, p.tok_cursor - 1);
}

pub fn int(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.identifier, p.tok_cursor - 1);
}

pub fn float(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.float, p.tok_cursor - 1);
}

pub fn string(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.string, p.tok_cursor - 1);
}

pub fn char(p: *Parser) anyerror!u32 {
    return p.tree.push_data_node(.char, p.tok_cursor - 1);
}
