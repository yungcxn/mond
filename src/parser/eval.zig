const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const partial = @import("partial.zig");
const NodeId = ParseTree.NodeId;
const Node = ParseTree.Node;

// TODO NEXT: quote { }, <>, refl, include, code
// might seem repetitive for now, but makes extensions easy (FOR NOW)

// *** rule templates *** //

pub fn templ_binary(kind: Node.Kind, prec: u8) fn (parser: *Parser, lhs: NodeId) anyerror!NodeId {
    return struct {
        pub fn eval(p: *Parser, lhs: NodeId) anyerror!NodeId {
            const parent = p.tree.push_node(kind);
            const def: Node.LayoutStruct(kind) = .{
                .lhs = lhs,
                .rhs = try any(p, .forbid_assign, prec + 1),
            };
            p.tree.set_children(parent, def);
            return parent;
        }
    }.eval;
}

// *** rule generators end *** //

pub fn any(
    p: *Parser,
    comptime assign_mode: enum { forbid_assign, allow_assign, enforce_assign },
    prec: u8,
) anyerror!NodeId {
    if (assign_mode == .enforce_assign) return assign(p);

    if (assign_mode == .allow_assign) switch (try p.peek_tok()) {
        .kw_pub, .kw_mut, .kw_stc => return assign(p),
        else => {},
    };

    const parent = try expr(p, prec);

    if (assign_mode == .allow_assign and !p.prev_eq_tok(.@"pct_}") and lookahead.assign_follows(p)) {
        return ee_assign(p, parent);
    }

    return parent;
}

pub fn expr(p: *Parser, prec: u8) anyerror!NodeId {
    const lookup_f = lookahead.pre[@intFromEnum(try p.pop_tok())] orelse return error.NoRuleFound;

    var parent = try lookup_f(p);

    if (p.prev_eq_tok(.@"pct_}")) return parent;

    while (p.tok_cursor < p.tokens.len()) {
        const post_f = lookahead.post[@intFromEnum(try p.peek_tok())] orelse break;

        p.tok_cursor += 1;
        parent = try post_f(p, parent);
    }

    while (p.tok_cursor < p.tokens.len()) {
        const precd_bin = lookahead.binary_compute[@intFromEnum(try p.peek_tok())] orelse break;
        if (precd_bin.prec < prec) break;

        p.tok_cursor += 1;
        parent = try precd_bin.f(p, parent);
    }

    return parent;
}

pub fn block(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.block);
    var children: FixedStack(4096) = .{};
    while (!try p.peek_eq_tok(.@"pct_}")) {
        try children.push(try any(p, .allow_assign, 0));
        try p.eat_stmt_end();
    }
    p.tok_cursor += 1;
    p.tree.set_children(parent, children.view());
    return parent;
}

// function definition start OR some function's type start OR capture start
// `(` is already consumed
pub fn paren(p: *Parser) anyerror!NodeId {
    if (try p.peek_eq_tok(.@"pct_)")) {
        return ee_def_fun(p, try partial.ee_fun_header(p, null));
    }

    const parent = try any(p, .forbid_assign, 0);

    switch (try p.peek_tok()) {
        .@"pct_,", .@"xpct_=", .kw_where, .identifier, .kw_self, .kw_main, .kw_deinit, .kw_init => {
            return ee_def_fun(p, try partial.ee_fun_header(p, parent));
        },
        .@"pct_)" => {
            p.tok_cursor += 1;
            switch (try p.peek_tok()) {
                .@"xpct_->", .@"pct_:", .@"pct_{" => {
                    p.tok_cursor -= 1;
                    return ee_def_fun(p, try partial.ee_fun_header(p, parent));
                },
                else => return p.tree.push_node_with(.capture, .{ .subnode = parent }),
            }
        },
        else => return error.IllegalParenSyntax,
    }
}

fn ee_def_fun(p: *Parser, early_function_header: NodeId) anyerror!NodeId {
    switch (try p.peek_tok()) {
        .@"pct_:" => {
            p.tok_cursor += 1;
            if (try p.peek_eq_tok(.@"pct_{")) return error.IllegalBlockAfterColon;
            return p.tree.push_node_with(.def_fun, .{
                .fun_header = early_function_header,
                .unit = try any(p, .allow_assign, 0),
            });
        },
        .@"pct_{" => return p.tree.push_node_with(.def_fun, .{
            .fun_header = early_function_header,
            .unit = try any(p, .forbid_assign, 0),
        }),
        else => return p.tree.push_node_with(.def_fun_declaration, .{ .fun_header = early_function_header }),
    }
}

// array with "[<expr>,]" or "[]", type with "[<expr>]<expr>" or "[]<expr>"
// already consumed "["
pub fn bracket(p: *Parser) anyerror!NodeId {
    var parent: NodeId = undefined;
    if (!try p.peek_eq_tok(.@"pct_]")) {
        parent = try any(p, .forbid_assign, 0);
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                var children: FixedStack(4096) = .{};
                try children.push(parent);
                while (true) {
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try children.push(try any(p, .forbid_assign, 0));
                    if (try p.peek_eq_tok(.@"pct_]")) break;
                    try p.eat_assert_tok(.@"pct_,");
                }
                p.tok_cursor += 1;
                parent = p.tree.push_node(.array);
                p.tree.set_children(parent, children.view());
            },
            .@"pct_]" => { // no comma -> type
                p.tok_cursor += 1;
                const def: Node.LayoutStruct(.type_array) = .{
                    .length = parent,
                    .type = try any(p, .forbid_assign, 0),
                };
                parent = p.tree.push_node(.type_array);
                p.tree.set_children(parent, def);
            },
            else => return error.IllegalArraySeparatorTerminator,
        }
    } else {
        p.tok_cursor += 1; // consume "]"
        if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
            parent = p.tree.push_node_with(.type_array_unlengthed, .{ .type = try any(p, .forbid_assign, 0) });
        } else {
            parent = p.tree.push_node(.array_empty);
        }
    }
    return parent;
}

pub fn typeof(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.typeof);
    const def: Node.LayoutStruct(.typeof) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn sizeof(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.sizeof);
    const def: Node.LayoutStruct(.sizeof) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn neg_num(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.neg_num);
    const def: Node.LayoutStruct(.neg_num) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn neg_logic(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.neg_logic);
    const def: Node.LayoutStruct(.neg_logic) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn inc_prefix(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.inc_prefix);
    const def: Node.LayoutStruct(.inc_prefix) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn dec_prefix(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.dec_prefix);
    const def: Node.LayoutStruct(.dec_prefix) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn gen_upperbound_incl(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_upperbound_incl);
    const def: Node.LayoutStruct(.gen_upperbound_incl) = .{ .subnode = try any(p, .forbid_assign, 0) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn gen_upperbound_excl(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_upperbound_excl);
    const def: Node.LayoutStruct(.gen_upperbound_excl) = .{ .subnode = try any(p, .forbid_assign, 0) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn true_(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.boolean_true);
}

pub fn false_(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.boolean_false);
}

pub fn do(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.do);
    const def: Node.LayoutStruct(.do) = .{ .subnode = try any(p, .forbid_assign, 0) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn deinit(p: *Parser) anyerror!NodeId {
    if (lookahead.pre[@intFromEnum(try p.peek_tok())] != null) {
        const parent = p.tree.push_node(.deinit);
        const def: Node.LayoutStruct(.deinit) = .{ .subnode = try any(p, .forbid_assign, 0) };
        p.tree.set_children(parent, def);
        return parent;
    }

    const parent = p.tree.push_node(.identifier_deinit);
    return parent;
}

pub fn cont(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.cont);
}

pub fn brk(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.brk);
}

pub fn ret(p: *Parser) anyerror!NodeId {
    if (lookahead.pre[@intFromEnum(try p.peek_tok())] == null) return p.tree.push_node(.ret_void);

    return p.tree.push_node_with(.ret, .{ .subnode = try any(p, .forbid_assign, 0) });
}

pub fn if_(p: *Parser) anyerror!NodeId {
    return ee_if(p, .if_then, .if_else);
}

pub fn stcif(p: *Parser) anyerror!NodeId {
    return ee_if(p, .stcif_then, .stcif_else);
}

fn ee_if(p: *Parser, comptime then_kind: Node.Kind, comptime else_kind: Node.Kind) anyerror!NodeId {
    var parent = p.tree.push_node(then_kind);
    var def: Node.LayoutStruct(then_kind) = undefined;

    def.cond = try any(p, .forbid_assign, 0);

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalIfFormat,
    }

    def.then = try any(p, .allow_assign, 0);

    p.tree.set_children(parent, def);

    if (try p.peek_eq_tok(.kw_else)) {
        p.tok_cursor += 1;
        if (try p.peek_eq_tok(.@"pct_:")) p.tok_cursor += 1;

        var else_def: Node.LayoutStruct(else_kind) = undefined;
        else_def.@"else" = try any(p, .allow_assign, 0);
        else_def.if_then = parent;

        parent = p.tree.push_node(else_kind);
        p.tree.set_children(parent, else_def);
    }

    return parent;
}

pub fn while_(p: *Parser) anyerror!NodeId {
    return ee_while(p, .@"while", .while_with_repeat_stmt);
}

pub fn stcwhile(p: *Parser) anyerror!NodeId {
    return ee_while(p, .stcwhile, .stcwhile_with_repeat_stmt);
}

fn ee_while(p: *Parser, comptime while_kind: Node.Kind, comptime repeat_kind: Node.Kind) anyerror!NodeId {
    const while_node = p.tree.push_node(while_kind);
    var parent = while_node;

    var def: Node.LayoutStruct(while_kind) = undefined;
    var def_with_repeat: Node.LayoutStruct(repeat_kind) = undefined;

    def.cond = try any(p, .forbid_assign, 0);

    if (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        def_with_repeat.@"while" = while_node;
        def_with_repeat.repeated = try any(p, .allow_assign, 0);
        parent = p.tree.push_node(repeat_kind);
        p.tree.set_children(parent, def_with_repeat);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalWhileFormat,
    }

    def.body = try any(p, .allow_assign, 0);
    p.tree.set_children(while_node, def);

    return parent;
}

pub fn for_(p: *Parser) anyerror!NodeId {
    return ee_for(p, .for_seq, .for_var_in_seq);
}

pub fn stcfor(p: *Parser) anyerror!NodeId {
    return ee_for(p, .stcfor_seq, .stcfor_var_in_seq);
}

fn ee_for(p: *Parser, comptime seq_kind: Node.Kind, comptime var_kind: Node.Kind) anyerror!NodeId {
    const for_node = p.tree.push_node(seq_kind);
    var parent = for_node;
    var def: Node.LayoutStruct(seq_kind) = undefined;
    var def_var_extension: Node.LayoutStruct(var_kind) = undefined;

    def.seq = try any(p, .forbid_assign, 0);

    if (try p.peek_eq_tok(.kw_in)) {
        p.tok_cursor += 1;
        def_var_extension.for_seq = for_node;
        def_var_extension.variable = def.seq;
        def.seq = try any(p, .forbid_assign, 0);
        parent = p.tree.push_node(var_kind);
        p.tree.set_children(parent, def_var_extension);
    }

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return error.IllegalForFormat,
    }

    def.body = try any(p, .allow_assign, 0);
    p.tree.set_children(for_node, def);

    return parent;
}

pub fn loop(p: *Parser) anyerror!NodeId {
    return ee_loop(p, .loop, .loop_with_repeat_stmt);
}

pub fn stcloop(p: *Parser) anyerror!NodeId {
    return ee_loop(p, .stcloop, .stcloop_with_repeat_stmt);
}

fn ee_loop(p: *Parser, comptime loop_kind: Node.Kind, comptime repeat_kind: Node.Kind) anyerror!NodeId {
    const first = try any(p, .allow_assign, 0);

    switch (try p.peek_tok()) {
        .@"pct_:" => p.tok_cursor += 1,
        .@"pct_{" => {},
        else => return p.tree.push_node_with(loop_kind, .{ .body = first }), // we just had one node here -> no repeat!
    }

    return p.tree.push_node_with(repeat_kind, .{
        .repeated = first,
        .body = try any(p, .allow_assign, 0),
    });
}

pub fn match(p: *Parser) anyerror!NodeId {
    return ee_match(p, .match);
}

pub fn stcmatch(p: *Parser) anyerror!NodeId {
    return ee_match(p, .stcmatch);
}

fn ee_match(p: *Parser, comptime match_kind: Node.Kind) anyerror!NodeId {
    const parent = p.tree.push_node(match_kind);
    var def: Node.LayoutStruct(match_kind) = undefined;

    def.matched = try any(p, .forbid_assign, 0);
    def.match_body = try partial.match_body(p);

    p.tree.set_children(parent, def);
    return parent;
}

pub fn type_ptr(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.type_ptr);
    const def: Node.LayoutStruct(.type_ptr) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn type_ptrmut(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.type_ptrmut);
    const def: Node.LayoutStruct(.type_ptrmut) = .{ .subnode = try any(p, .forbid_assign, lookahead.prec_unary) };
    p.tree.set_children(parent, def);
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

pub fn type_(p: *Parser) anyerror!NodeId {
    p.tok_cursor -= 1;
    const parent: Node.Kind = switch (try p.pop_tok()) {
        .@"xpct_*(" => .def_type,
        .@"xpct_**(" => .def_type_packed,
        else => return error.IllegalTypeStart,
    };

    var node = p.tree.push_node(parent);
    p.tree.set_children(node, Node.LayoutStruct(.def_type){ .param_tuple = try partial.type_param_tuple(p) });

    if (try p.peek_eq_tok(.kw_assertsize)) {
        p.tok_cursor += 1;
        node = p.tree.push_node_with(.def_type_assertsize, .{
            .def_type = node,
            .assertsize = try any(p, .forbid_assign, 0),
        });
    }

    switch (try p.peek_tok()) {
        .kw_implof, .@"xpct_!{" => {
            p.tok_cursor += 1;
            node = p.tree.push_node_with(.def_type_implof, .{ .def_type = node, .def_trait = try trait(p) });
        },
        else => {},
    }

    return node;
}

pub fn variant(p: *Parser) anyerror!NodeId {
    p.tok_cursor -= 1;

    const parent: Node.Kind = switch (try p.pop_tok()) {
        .@"xpct_+(" => .def_variant,
        .@"xpct_++(" => .def_variant_unionsized,
        else => return error.IllegalVariantStart,
    };

    var params: FixedStack(64) = .{};
    while (!try p.peek_eq_tok(.@"pct_)")) {
        try params.push(try partial.variant_param(p));
        if (!try p.peek_eq_tok(.@"pct_,")) break;
        p.tok_cursor += 1;
    }
    try p.eat_assert_tok(.@"pct_)");
    if (params.cursor == 0) return error.IllegalVariantParamList;

    const param_tuple = p.tree.push_node(.partial__variant_def_param_tuple);
    p.tree.set_children(param_tuple, params.view());

    var node = p.tree.push_node(parent);
    p.tree.set_children(node, Node.LayoutStruct(.def_variant){ .param_tuple = param_tuple });

    if (try p.peek_eq_tok(.kw_tagof)) {
        p.tok_cursor += 1;
        node = p.tree.push_node_with(.def_variant_tagof, .{
            .def_variant = node,
            .tagof = try any(p, .forbid_assign, 0),
        });
    }

    if (try p.peek_eq_tok(.kw_assertsize)) {
        p.tok_cursor += 1;
        node = p.tree.push_node_with(.def_variant_assertsize, .{
            .def_variant = node,
            .assertsize = try any(p, .forbid_assign, 0),
        });
    }

    switch (try p.peek_tok()) {
        .kw_implof, .@"xpct_!{" => {
            p.tok_cursor += 1;
            node = p.tree.push_node_with(.def_variant_implof, .{ .def_variant = node, .def_trait = try trait(p) });
        },
        else => {},
    }

    return node;
}

pub fn trait(p: *Parser) anyerror!NodeId {
    p.tok_cursor -= 1; // to know if 'implof' or '@{' was scanned
    var opt_implof_tuple: ?NodeId = null;

    if (try p.peek_eq_tok(.kw_implof)) {
        p.tok_cursor += 1;
        var impls: FixedStack(64) = .{};
        while (true) {
            try impls.push(try any(p, .forbid_assign, 0));
            switch (try p.peek_tok()) {
                .@"xpct_!{" => break,
                .@"pct_," => {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"xpct_!{")) break;
                },
                else => return error.IllegalImplofList,
            }
        }
        const implof_tuple = p.tree.push_node(.partial__trait_def_implof_tuple);
        p.tree.set_children(implof_tuple, impls.view());
        opt_implof_tuple = implof_tuple;
    }

    try p.eat_assert_tok(.@"xpct_!{");
    var members: FixedStack(4096) = .{};
    while (!try p.peek_eq_tok(.@"pct_}")) {
        try members.push(try any(p, .allow_assign, 0));
        try p.eat_stmt_end();
    }
    p.tok_cursor += 1; // consume "}"

    const body = p.tree.push_node(.partial__trait_def_body);
    p.tree.set_children(body, members.view());

    if (opt_implof_tuple) |implof_tuple| {
        return p.tree.push_node_with(.def_trait_implof, .{ .implof_tuple = implof_tuple, .body = body });
    }
    return p.tree.push_node_with(.def_trait, .{ .body = body });
}

pub fn unify_variants(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.unify_variants);
    const def: Node.LayoutStruct(.unify_variants) = .{
        .left_type = lhs,
        .right_type = try any(p, .forbid_assign, 0),
    };

    p.tree.set_children(parent, def);
    return parent;
}

pub fn fun_call(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.fun_call);
    const def: Node.LayoutStruct(.fun_call) = .{
        .callable = lhs,
        .fun_param_tuple = try partial.fun_call_param_tuple(p),
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn array_index(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.array_index);
    const def: Node.LayoutStruct(.array_index) = .{
        .indexable = lhs,
        .index = try any(p, .forbid_assign, 0),
    };
    try p.eat_assert_tok(.@"pct_]");
    p.tree.set_children(parent, def);
    return parent;
}

pub fn member(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.member);
    const name = switch (try p.pop_tok()) {
        .identifier => try identifier(p),
        .kw_self => p.tree.push_node(.identifier_self),
        .kw_init => p.tree.push_node(.identifier_init),
        .kw_deinit => p.tree.push_node(.identifier_deinit),
        .kw_main => p.tree.push_node(.identifier_main),
        else => return error.IllegalMemberName,
    };
    const def: Node.LayoutStruct(.member) = .{
        .parent = lhs,
        .member = name,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn dereference(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.dereference);
    const def: Node.LayoutStruct(.dereference) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn address_of(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.address_of);
    const def: Node.LayoutStruct(.address_of) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn inc_postfix(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.inc_postfix);
    const def: Node.LayoutStruct(.inc_postfix) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn dec_postfix(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.dec_postfix);
    const def: Node.LayoutStruct(.dec_postfix) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn gen_lowerbound(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_lowerbound);
    const def: Node.LayoutStruct(.gen_lowerbound) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn gen_incl(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_incl);
    const def: Node.LayoutStruct(.gen_incl) = .{
        .lower = lhs,
        .upper = try any(p, .forbid_assign, 0),
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn gen_excl(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.gen_excl);
    const def: Node.LayoutStruct(.gen_excl) = .{
        .lower = lhs,
        .upper = try any(p, .forbid_assign, 0),
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn oftype(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.oftype);
    const def: Node.LayoutStruct(.oftype) = .{
        .value = lhs,
        .type = try any(p, .forbid_assign, lookahead.prec_unary),
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn as(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.as);
    const def: Node.LayoutStruct(.as) = .{
        .value = lhs,
        .type = try any(p, .forbid_assign, lookahead.prec_unary),
    };
    p.tree.set_children(parent, def);
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

    p.tree.set_children(parent, def);
    return parent;
}

pub fn selftag_arrow(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.selftag_arrow);
    var def: Node.LayoutStruct(.selftag_arrow) = undefined;
    def.value = lhs;

    try p.eat_assert_tok(.identifier);
    def.label = try identifier(p);

    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        def.label = try partial.destructure(p, def.label);
    }

    p.tree.set_children(parent, def);
    return parent;
}

pub fn selftag_unwrap(p: *Parser, lhs: NodeId) anyerror!NodeId {
    if (lookahead.pre[@intFromEnum(try p.peek_tok())] == null) {
        return p.tree.push_node_with(.selftag_unwrap, .{ .value = lhs });
    }

    return p.tree.push_node_with(.selftag_unwrap_fallback, .{
        .value = lhs,
        .fallback = try any(p, .forbid_assign, 0),
    });
}

pub fn defer_(p: *Parser) anyerror!NodeId {
    return p.tree.push_node_with(.@"defer", .{ .defered = try any(p, .allow_assign, 0) });
}

pub fn inlined_defer_deinit(p: *Parser, lhs: NodeId) anyerror!NodeId {
    try p.eat_assert_tok(.kw_deinit);
    const parent = p.tree.push_node(.inlined_defer_deinit);
    const def: Node.LayoutStruct(.inlined_defer_deinit) = .{
        .subnode = lhs,
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn with(p: *Parser, lhs: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.with);
    try p.eat_assert_tok(.@"pct_(");
    const def: Node.LayoutStruct(.with) = .{
        .value = lhs,
        .fun_call_param_tuple = try partial.fun_call_param_tuple(p),
    };
    p.tree.set_children(parent, def);
    return parent;
}

pub fn identifier_self(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.identifier_self);
}

pub fn identifier_init(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.identifier_init);
}

pub fn identifier_main(p: *Parser) anyerror!NodeId {
    return p.tree.push_node(.identifier_main);
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

pub fn assign(p: *Parser) anyerror!NodeId {
    switch (try p.peek_tok()) {
        .kw_stc => {
            p.tok_cursor += 1;
            return p.tree.push_node_with(.mod_stc, .{ .subnode = try assign(p) });
        },
        .kw_pub => {
            p.tok_cursor += 1;
            return p.tree.push_node_with(.mod_pub, .{ .subnode = try assign(p) });
        },
        .kw_mut => {
            p.tok_cursor += 1;
            return p.tree.push_node_with(.mod_mut, .{ .subnode = try assign(p) });
        },
        else => {},
    }

    return ee_assign(p, try expr(p, 0));
}

pub fn ee_assign(p: *Parser, early_lhs: NodeId) anyerror!NodeId {
    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        const assignee = try partial.destructure(p, early_lhs);
        try p.eat_assert_tok(.@"xpct_=");
        return p.tree.push_node_with(.assign, .{ .assignee = assignee, .assigned = try assigned_value(p) });
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        return p.tree.push_node_with(.assign, .{ .assignee = early_lhs, .assigned = try assigned_value(p) });
    }

    // `early_lhs` was not the assignee but its type, the assignee follows
    try p.eat_assert_tok(.identifier);
    var named = try identifier(p);
    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        named = try partial.destructure(p, named);
    }

    const def_var = p.tree.push_node_with(.def_var, .{ .type = early_lhs, .identifier = named });
    if (!try p.peek_eq_tok(.@"xpct_=")) return def_var;

    p.tok_cursor += 1;
    return p.tree.push_node_with(.assign_typed, .{ .def_var = def_var, .assigned = try assigned_value(p) });
}

fn assigned_value(p: *Parser) anyerror!NodeId {
    const value = try any(p, .forbid_assign, 0);
    if (try p.peek_eq_tok(.@"pct_,")) {
        // cursor should be right at first comma
        return partial.assign_multival(p, value);
    }
    return value;
}
