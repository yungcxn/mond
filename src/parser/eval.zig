const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const partial = @import("partial.zig");
const NodeId = ParseTree.NodeId;
const Node = ParseTree.Node;

// TODO NEXT: assign, quote { }, <>, refl, include, code
// might seem repetitive for now, but makes extensions easy (FOR NOW)

// *** rule templates *** //

pub fn templ_binary(kind: Node.Kind, prec: u8) fn (parser: *Parser, lhs: NodeId) anyerror!NodeId {
    return struct {
        pub fn eval(p: *Parser, lhs: NodeId) anyerror!NodeId {
            const parent = p.tree.push_node(kind);
            const def: Node.LayoutStruct(kind) = .{
                .lhs = lhs,
                .rhs = try any(p, prec + 1),
            };
            p.tree.set_node_arg0(parent, def.lhs);
            p.tree.set_node_arg1(parent, def.rhs);
            return parent;
        }
    }.eval;
}

// *** rule generators end *** //

pub fn any(p: *Parser, prec: u8) anyerror!NodeId {
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
    } else {
        p.tok_cursor -= 1;
    }

    return parent;
}

// function definition start OR some function's type start OR capture start
// `(` is already consumed
pub fn paren(p: *Parser) anyerror!NodeId {
    var parent: NodeId = 0xFFFFFFFF;
    if (!try p.peek_eq_tok(.@"pct_)")) {
        parent = try any(p, 0);
        switch (try p.peek_tok()) {
            .@"pct_,", .@"xpct_=", .kw_where, .identifier => {
                parent = try partial.ee_fun_header(p, parent);
                parent = try ee_def_fun(p, parent);
            },
            .@"pct_)" => {
                p.tok_cursor += 1;
                switch (try p.peek_tok()) {
                    .@"xpct_->", .@"pct_:", .@"pct_{" => {
                        p.tok_cursor -= 1;
                        parent = try partial.ee_fun_header(p, parent);
                        parent = try ee_def_fun(p, parent);
                    },
                    else => {
                        const paren_def: Node.LayoutStruct(.capture) = .{ .subnode = parent };
                        parent = p.tree.push_node(.capture);
                        p.tree.set_node_arg0(parent, paren_def.subnode);
                    },
                }
            },
            else => return error.IllegalParenSyntax,
        }
    } else {
        parent = try partial.ee_fun_header(p, null);
        parent = try ee_def_fun(p, parent);
    }
    return parent;
}

fn ee_def_fun(p: *Parser, early_function_header: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.def_fun);
    var def: Node.LayoutStruct(.def_fun) = undefined;
    def.fun_header = early_function_header;

    switch (try p.peek_tok()) {
        .@"pct_:" => {
            p.tok_cursor += 1;
            if (try p.peek_eq_tok(.@"pct_{")) return error.IllegalBlockAfterColon;
            def.unit = try any(p, 0);
        },
        .@"pct_{" => {
            def.unit = try any(p, 0);
        },
        else => {
            def.unit = 0xFFFFFFFF;
        },
    }

    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}

// array with "[<expr>,]" or "[]", type with "[<expr>]<expr>" or "[]<expr>"
// already consumed "["
pub fn bracket(p: *Parser) anyerror!NodeId {
    var parent: NodeId = undefined;
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
                p.tok_cursor += 1;
                parent = p.tree.push_node(.array);
                p.tree.push_extra_childrefs(parent, children.view());
            },
            .@"pct_]" => { // no comma -> type
                p.tok_cursor += 1;
                const def: Node.LayoutStruct(.type_array) = .{
                    .length = parent,
                    .type = try any(p, 0),
                };
                parent = p.tree.push_node(.type_array);
                p.tree.set_node_arg0(parent, def.length);
                p.tree.set_node_arg1(parent, def.type);
            },
            else => return error.IllegalArraySeparatorTerminator,
        }
    } else {
        p.tok_cursor += 1; // consume "]"
        if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
            const def: Node.LayoutStruct(.type_array) = .{
                .length = 0xFFFFFFFF,
                .type = try any(p, 0),
            };
            parent = p.tree.push_node(.type_array);
            p.tree.set_node_arg0(parent, def.length);
            p.tree.set_node_arg1(parent, def.type);
        } else {
            parent = p.tree.push_node(.array_empty);
        }
    }
    return parent;
}

pub fn typeof(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.typeof);
    const def: Node.LayoutStruct(.typeof) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn sizeof(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.sizeof);
    const def: Node.LayoutStruct(.sizeof) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn neg_num(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.neg_num);
    const def: Node.LayoutStruct(.neg_num) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn neg_logic(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.neg_logic);
    const def: Node.LayoutStruct(.neg_logic) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn inc_prefix(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.inc_prefix);
    const def: Node.LayoutStruct(.inc_prefix) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn dec_prefix(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.dec_prefix);
    const def: Node.LayoutStruct(.dec_prefix) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn gen_upperbound_incl(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_upperbound_incl);
    const def: Node.LayoutStruct(.gen_upperbound_incl) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn gen_upperbound_excl(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_upperbound_excl);
    const def: Node.LayoutStruct(.gen_upperbound_excl) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn true_(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.boolean);
    p.tree.set_node_arg0(parent, 1);
    return parent;
}

pub fn false_(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.boolean);
    p.tree.set_node_arg0(parent, 0);
    return parent;
}

pub fn none(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.none);
}

pub fn err(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.err);
}

pub fn deinit(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.deinit);
    const def: Node.LayoutStruct(.deinit) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn cont(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.cont);
}

pub fn brk(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.brk);
}

pub fn ret(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.ret);
    var def: Node.LayoutStruct(.ret) = undefined;
    if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
        def.opt_subnode = try any(p, 0);
    } else {
        def.opt_subnode = 0xFFFFFFFF;
    }
    p.tree.set_node_arg0(parent, def.opt_subnode);
    return parent;
}

pub fn if_(p: *Parser) anyerror!NodeId {
    var parent = p.tree.push_node(.if_then);
    var def: Node.LayoutStruct(.if_then) = undefined;

    def.cond = try any(p, 0);

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalIfFormat,
    }

    def.then = try any(p, 0);

    p.tree.set_node_arg0(parent, def.cond);
    p.tree.set_node_arg1(parent, def.then);

    if (try p.peek_eq_tok(.kw_else)) {
        p.tok_cursor += 1;
        var else_def: Node.LayoutStruct(.if_else) = undefined;
        else_def.@"else" = try any(p, 0);
        else_def.if_then = parent;

        parent = p.tree.push_node(.if_else);
        p.tree.set_node_arg0(parent, else_def.if_then);
        p.tree.set_node_arg1(parent, else_def.@"else");
    }

    return parent;
}

pub fn while_(p: *Parser) anyerror!NodeId {
    const while_node = p.tree.push_node(.@"while");
    var parent = while_node;

    var def: Node.LayoutStruct(.@"while") = undefined;
    var def_with_repeat: Node.LayoutStruct(.while_with_repeat_stmt) = undefined;

    def.cond = try any(p, 0);

    p.tree.set_node_arg0(while_node, def.cond);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        def_with_repeat.@"while" = while_node;
        def_with_repeat.repeated = try any(p, 0);
        parent = p.tree.push_node(.while_with_repeat_stmt);
        p.tree.set_node_arg0(parent, def_with_repeat.@"while");
        p.tree.set_node_arg1(parent, def_with_repeat.repeated);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalWhileFormat,
    }

    def.body = try any(p, 0);
    p.tree.set_node_arg1(while_node, def.body);

    return parent;
}

pub fn for_(p: *Parser) anyerror!NodeId {
    const for_node = p.tree.push_node(.for_seq);
    var parent = for_node;
    var def: Node.LayoutStruct(.for_seq) = undefined;
    var def_var_extension: Node.LayoutStruct(.for_var_in_seq) = undefined;

    def.seq = try any(p, 0);

    if (try p.peek_eq_tok(.kw_in)) {
        p.tok_cursor += 1;
        def_var_extension.for_seq = for_node;
        def_var_extension.variable = def.seq;
        def.seq = try any(p, 0);
        p.tree.set_node_arg0(for_node, def.seq);
        parent = p.tree.push_node(.for_var_in_seq);
        p.tree.set_node_arg0(parent, def_var_extension.for_seq);
        p.tree.set_node_arg1(parent, def_var_extension.variable);
    } else {
        p.tree.set_node_arg0(for_node, def.seq);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalForFormat,
    }

    def.body = try any(p, 0);
    p.tree.set_node_arg1(for_node, def.body);

    return parent;
}

pub fn loop(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.loop);
    var def: Node.LayoutStruct(.loop) = undefined;
    def.body = try any(p, 0);

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => { // we just had one node here -> no repeat!
            def.opt_repeated = 0xFFFFFFFF;
            p.tree.set_node_arg0(parent, 0xFFFFFFFF);
            p.tree.set_node_arg1(parent, def.body);
            return parent;
        },
    }

    def.opt_repeated = def.body;
    def.body = try any(p, 0);
    p.tree.set_node_arg0(parent, def.opt_repeated);
    p.tree.set_node_arg1(parent, def.body);

    return parent;
}

pub fn match(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.match);
    var def: Node.LayoutStruct(.match) = undefined;

    def.matched = try any(p, 0);
    def.match_body = try partial.match_body(p);

    p.tree.set_node_arg0(parent, def.matched);
    p.tree.set_node_arg1(parent, def.match_body);
    return parent;
}

pub fn type_ptr(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.type_ptr);
    const child: Node.LayoutStruct(.type_ptr) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, child.subnode);
    return parent;
}

pub fn type_ptrmut(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.type_ptrmut);
    const child: Node.LayoutStruct(.type_ptrmut) = .{ .subnode = try any(p, 0) };
    p.tree.set_node_arg0(parent, child.subnode);
    return parent;
}

pub fn type_u8(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_u8);
}

pub fn type_u16(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_u16);
}

pub fn type_u32(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_u32);
}

pub fn type_u64(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_u64);
}

pub fn type_i8(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_i8);
}

pub fn type_i16(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_i16);
}

pub fn type_i32(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_i32);
}

pub fn type_i64(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_i64);
}

pub fn type_f16(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_f16);
}

pub fn type_f32(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_f32);
}

pub fn type_f64(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_f64);
}

pub fn type_bool(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_bool);
}

pub fn type_type(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_type);
}

pub fn type_trait(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_trait);
}

pub fn type_variant(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_variant);
}

pub fn type_inlfun(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_inlfun);
}

pub fn type_fun(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_fun);
}

pub fn type_stcfun(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.type_stcfun);
}

pub fn type_or_variant(p: *Parser) anyerror!NodeId {
    p.tok_cursor -= 1;
    const open_tok = try p.pop_tok();

    if (try p.peek_eq_tok(.@"pct_)")) return error.EmptyTypeOrVariantDef;

    const is_mut0 = try p.peek_eq_tok(.kw_mut);
    if (is_mut0) p.tok_cursor += 1;
    const early_node0 = try any(p, 0);

    var name: NodeId = 0xFFFFFFFF; // shared
    var of_type: NodeId = 0xFFFFFFFF; // only for variant
    var default_value: NodeId = 0xFFFFFFFF; // only for type
    var where_predicate: NodeId = 0xFFFFFFFF; // only for type
    var where_else_value: NodeId = 0xFFFFFFFF; // only for type

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
            const type_kind: Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .def_type,
                .@"xpct_@@(" => .def_type_packed,
                .@"xpct_@@@(" => return error.IllegalUnionsizedTypeDef,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const param = p.tree.push_node(if (is_mut0) .partial__type_param_mut else .partial__type_param);
                var param_def: Node.LayoutStruct(.partial__type_param) = .{
                    .type = early_node0,
                    .identifier = name,
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
            var type_def: Node.LayoutStruct(.def_type) = undefined;
            type_def.param_tuple = param_tuple;

            if (try p.peek_eq_tok(.kw_sizeof)) {
                p.tok_cursor += 1;
                type_def.sizeof = try any(p, 0);
            } else {
                type_def.sizeof = 0xFFFFFFFF;
            }

            if (try p.peek_eq_tok(.kw_implof) or try p.peek_eq_tok(.@"xpct_@{")) {
                p.tok_cursor += 1;
                type_def.def_trait = try trait(p);
            } else {
                type_def.def_trait = 0xFFFFFFFF;
            }

            p.tree.push_extra_childrefs(parent, &type_def);
            return parent;
        },
        .variant => {
            const variant_kind: Node.Kind = switch (open_tok) {
                .@"xpct_@(" => .def_variant,
                .@"xpct_@@(" => .def_variant_packed,
                .@"xpct_@@@(" => .def_variant_unionsized,
                else => unreachable,
            };

            var params: FixedStack(64) = .{};
            {
                const first = p.tree.push_node(.partial__variant_param);
                var param_def: Node.LayoutStruct(.partial__variant_param) = .{
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
            var variant_def: Node.LayoutStruct(.def_variant) = undefined;
            variant_def.param_tuple = param_tuple;

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

pub fn trait(p: *Parser) anyerror!NodeId {
    p.tok_cursor -= 1; // to know if 'implof' or '@{' was scanned
    var def: Node.LayoutStruct(.def_trait) = undefined;

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

pub fn unify_variants(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.unify_variants);
    const def: Node.LayoutStruct(.unify_variants) = .{
        .left_type = lhs,
        .right_type = try any(p, 0),
    };

    p.tree.set_node_arg0(parent, def.left_type);
    p.tree.set_node_arg1(parent, def.right_type);
    return parent;
}

pub fn fun_call(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.fun_call);
    const def: Node.LayoutStruct(.fun_call) = .{
        .callable = lhs,
        .fun_param_tuple = try partial.fun_call_param_tuple(p),
    };
    p.tree.set_node_arg0(parent, def.callable);
    p.tree.set_node_arg1(parent, def.fun_param_tuple);
    return parent;
}

pub fn array_index(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.array_index);
    const def: Node.LayoutStruct(.array_index) = .{
        .indexable = lhs,
        .index = try any(p, 0),
    };
    try p.eat_assert_tok(.@"pct_]");
    p.tree.set_node_arg0(parent, def.indexable);
    p.tree.set_node_arg1(parent, def.index);
    return parent;
}

pub fn member(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.member);
    const def: Node.LayoutStruct(.member) = .{
        .parent = lhs,
        .member = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.parent);
    p.tree.set_node_arg1(parent, def.member);
    return parent;
}

pub fn dereference(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.dereference);
    const def: Node.LayoutStruct(.dereference) = .{
        .subnode = lhs,
    };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn address_of(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.address_of);
    const def: Node.LayoutStruct(.address_of) = .{
        .subnode = lhs,
    };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn inc_postfix(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.inc_postfix);
    const def: Node.LayoutStruct(.inc_postfix) = .{
        .subnode = lhs,
    };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn dec_postfix(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.dec_postfix);
    const def: Node.LayoutStruct(.dec_postfix) = .{
        .subnode = lhs,
    };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn gen_lowerbound(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_lowerbound);
    const def: Node.LayoutStruct(.gen_lowerbound) = .{
        .subnode = lhs,
    };
    p.tree.set_node_arg0(parent, def.subnode);
    return parent;
}

pub fn gen_incl(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_incl);
    const def: Node.LayoutStruct(.gen_incl) = .{
        .lower = lhs,
        .upper = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.lower);
    p.tree.set_node_arg1(parent, def.upper);
    return parent;
}

pub fn gen_excl(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_excl);
    const def: Node.LayoutStruct(.gen_excl) = .{
        .lower = lhs,
        .upper = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.lower);
    p.tree.set_node_arg1(parent, def.upper);
    return parent;
}

pub fn oftype(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.oftype);
    const def: Node.LayoutStruct(.oftype) = .{
        .value = lhs,
        .type = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.type);
    return parent;
}

pub fn as(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.as);
    const def: Node.LayoutStruct(.as) = .{
        .value = lhs,
        .type = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.type);
    return parent;
}

pub fn labelarrow(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.labelarrow);
    var def: Node.LayoutStruct(.labelarrow) = undefined;
    def.value = lhs;

    try p.eat_assert_tok(.identifier);
    def.label = try identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        def.label = try partial.destructure(p, def.label);
    }

    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.label);
    return parent;
}

pub fn optarrow(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.optarrow);
    var def: Node.LayoutStruct(.optarrow) = undefined;
    def.value = lhs;

    try p.eat_assert_tok(.identifier);
    def.label = try identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        def.label = try partial.destructure(p, def.label);
    }

    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.label);
    return parent;
}

pub fn errarrow(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.errarrow);
    var def: Node.LayoutStruct(.errarrow) = undefined;
    def.value = lhs;

    try p.eat_assert_tok(.identifier);
    def.label = try identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        def.label = try partial.destructure(p, def.label);
    }

    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.label);
    return parent;
}

pub fn errhandle(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.errhandle);
    var def: Node.LayoutStruct(.errhandle) = undefined;
    def.value = lhs;
    if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
        def.fallback = try any(p, 0);
    } else {
        def.fallback = 0xFFFFFFFF;
    }
    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.fallback);
    return parent;
}

pub fn opthandle(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.opthandle);
    var def: Node.LayoutStruct(.opthandle) = undefined;
    def.value = lhs;

    if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
        def.fallback = try any(p, 0);
    } else {
        def.fallback = 0xFFFFFFFF;
    }

    p.tree.set_node_arg0(parent, def.value);
    p.tree.set_node_arg1(parent, def.fallback);
    return parent;
}

pub fn defer_(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.@"defer");
    const def: Node.LayoutStruct(.@"defer") = .{
        .left_opt_node = 0xFFFFFFFF,
        .defered = try any(p, 0),
    };
    p.tree.set_node_arg0(parent, def.left_opt_node);
    p.tree.set_node_arg1(parent, def.defered);
    return parent;
}

pub fn defer_inlined(p: *Parser, lhs: NodeId) anyerror!NodeId {
    if (try p.peek_eq_tok(.kw_deinit)) {
        p.tok_cursor += 1;
        if (lookahead.pre[@intFromEnum(try p.peek_tok())] == null) {
            const parent = p.tree.push_node(.defer_with_deinit);
            const def: Node.LayoutStruct(.defer_with_deinit) = .{
                .subnode = lhs,
            };
            p.tree.set_node_arg0(parent, def.subnode);
            return parent;
        }

        p.tok_cursor -= 1;
    }
    const parent = p.tree.push_node(.@"defer");
    p.tree.set_node_arg0(parent, lhs);
    const rhs = try any(p, 0);
    p.tree.set_node_arg1(parent, rhs);
    return parent;
}

pub fn identifier(p: *Parser) anyerror!NodeId {
    return p.tree.push_data_node(.identifier, p.tok_cursor - 1);
}

pub fn int(p: *Parser) anyerror!NodeId {
    return p.tree.push_data_node(.int, p.tok_cursor - 1);
}

pub fn float(p: *Parser) anyerror!NodeId {
    return p.tree.push_data_node(.float, p.tok_cursor - 1);
}

pub fn string(p: *Parser) anyerror!NodeId {
    return p.tree.push_data_node(.string, p.tok_cursor - 1);
}

pub fn char(p: *Parser) anyerror!NodeId {
    return p.tree.push_data_node(.char, p.tok_cursor - 1);
}
