const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const FixedStack = @import("../ds/fixedstack.zig").FixedStack;
const lookahead = @import("lookahead.zig");
const eval = @import("eval.zig");
const NodeId = @import("../ParseTree.zig").NodeId;
const Node = @import("../ParseTree.zig").Node;

// TODO: this can vanish, the evaluators are not needed and should be constructed not through the
// "parse" behaviour for ast nodes in the code, but through building anode structs at compiletime.

// ee refers to early eval'd => we have a part of this node already evaluated.
pub fn ee_fun_header(p: *Parser, early_node0_in_tuple: ?NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_def_header);
    var def: Node.LayoutStruct(.partial__fun_def_header) = undefined;
    def.param_tuple = try ee_fun_param_tuple(p, early_node0_in_tuple);

    if (try p.peek_eq_tok(.@"xpct_->")) {
        p.tok_cursor += 1;
        def.return_type = try eval.any(p, .forbid_assign, 0);
    } else {
        def.return_type = 0xFFFFFFFF;
    }

    p.tree.set_children(parent, def);
    return parent;
}

pub fn ee_fun_param_tuple(p: *Parser, early_node0: ?NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_def_param_tuple);

    if (early_node0 == null and try p.peek_eq_tok(.@"pct_)")) {
        p.tok_cursor += 1;
        return parent;
    }

    var params: FixedStack(64) = .{};
    try params.push(try ee_fun_param(p, early_node0.?));
    while (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        if (try p.peek_eq_tok(.@"pct_)")) break;
        try params.push(try ee_fun_param(p, try eval.any(p, .forbid_assign, 0)));
    }
    try p.eat_assert_tok(.@"pct_)");

    p.tree.set_children(parent, params.view());
    return parent;
}

pub fn ee_fun_param(p: *Parser, early_node0: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_def_param);
    var def: Node.LayoutStruct(.partial__fun_def_param) = undefined;
    // here, we could encounter <expr> <expr> or <expr>
    // + they are followed by , OR ) OR = OR where

    // first expr is safe:
    const a = early_node0;
    const next_tok = try p.peek_tok();
    if (next_tok != .@"pct_," and next_tok != .@"pct_)" and next_tok != .@"xpct_=" and next_tok != .kw_where) {
        try p.eat_assert_tok(.identifier);
        const b = try eval.identifier(p);
        def.type = a;
        def.identifier = b;
    } else {
        def.type = a;
        def.identifier = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.default_value = try eval.any(p, .forbid_assign, 0);
    } else {
        def.default_value = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_where)) {
        p.tok_cursor += 1;
        def.where_predicate = try eval.any(p, .forbid_assign, 0);
        if (try p.peek_eq_tok(.kw_else)) {
            p.tok_cursor += 1;
            def.where_else_value = try eval.any(p, .forbid_assign, 0);
        } else {
            def.where_else_value = 0xFFFFFFFF;
        }
    } else {
        def.where_predicate = 0xFFFFFFFF;
        def.where_else_value = 0xFFFFFFFF;
    }

    p.tree.set_children(parent, &def);
    return parent;
}

pub fn match_body(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__match_body);
    try p.eat_assert_tok(.@"pct_{");
    var match_cases: FixedStack(512) = .{};
    while (true) {
        try match_cases.push(try match_case(p));
        switch (try p.peek_tok()) {
            .@"pct_," => {
                p.tok_cursor += 1;
                if (try p.peek_eq_tok(.@"pct_}")) break;
            },
            .@"pct_}" => break,
            else => return error.IllegalMatchCase,
        }
    }
    p.tok_cursor += 1;
    p.tree.set_children(parent, match_cases.view());
    return parent;
}

// <pattern> => <body> (',' | '}')
// patterns: <node> | <node>, <identifier> | <node>, {'|', <node>}, ['|']
// could be aswell: partial__match_case_pattern_or and partial__match_case_pattern_typecast
pub fn match_case(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__match_case);
    var def: Node.LayoutStruct(.partial__match_case) = undefined;

    def.pattern = try eval.any(p, .forbid_assign, 0);
    switch (try p.peek_tok()) {
        .identifier => {
            p.tok_cursor += 1;
            const typecast_node = p.tree.push_node(.partial__match_case_pattern_typecast);
            const typecast_def = Node.LayoutStruct(.partial__match_case_pattern_typecast){
                .type = def.pattern,
                .casted_var = try eval.identifier(p),
            };
            p.tree.set_children(typecast_node, typecast_def);
            def.pattern = typecast_node;
        },
        .@"xpct_|" => {
            p.tok_cursor += 1;
            var or_patterns: FixedStack(64) = .{};
            try or_patterns.push(def.pattern);
            while (true) {
                try or_patterns.push(try eval.any(p, .forbid_assign, 0));
                if (try p.peek_eq_tok(.@"xpct_|")) {
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"xpct_=>")) break;
                } else {
                    return error.IllegalMatchCasePattern;
                }
            }
            const or_node = p.tree.push_node(.partial__match_case_pattern_or);
            p.tree.set_children(or_node, or_patterns.view());
            def.pattern = or_node;
        },
        else => {},
    }

    try p.eat_assert_tok(.@"xpct_=>");
    def.body = try eval.any(p, .allow_assign, 0);

    p.tree.set_children(parent, def);
    return parent;
}

pub fn fun_call_param_tuple(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_call_param_tuple);
    try p.eat_assert_tok(.@"pct_(");

    if (!try p.peek_eq_tok(.@"pct_)")) {
        var params: FixedStack(64) = .{};
        while (true) {
            const expr_i = try eval.any(p, .forbid_assign, 0);
            switch (try p.peek_tok()) {
                .@"pct_)" => {
                    try params.push(expr_i);
                    break;
                },
                .@"pct_," => {
                    try params.push(expr_i);
                    p.tok_cursor += 1;
                    if (try p.peek_eq_tok(.@"pct_)")) break;
                },
                .@"xpct_=" => {
                    p.tok_cursor += 1;
                    const assigned_pair_node = p.tree.push_node(.partial__fun_call_assigned_param);
                    const assigned_pair: Node.LayoutStruct(.partial__fun_call_assigned_param) = .{
                        .identifier = expr_i,
                        .value = try eval.any(p, .forbid_assign, 0),
                    };
                    p.tree.set_children(assigned_pair_node, assigned_pair);
                    try params.push(assigned_pair_node);

                    switch (try p.peek_tok()) {
                        .@"pct_)" => break,
                        .@"pct_," => {
                            p.tok_cursor += 1;
                            if (try p.peek_eq_tok(.@"pct_)")) break;
                        },
                        else => return error.IllegalFunCallParam,
                    }
                },
                else => return error.IllegalFunCallParam,
            }
        }
        p.tree.set_children(parent, params.view());
        try p.eat_assert_tok(.@"pct_)");
        return parent;
    } else {
        p.tok_cursor += 1;
        return parent;
    }
}

// assumes in expression "<identifier_expr>, <identifier_expr>, ..." first <identifier_expr> is consumed
pub fn destructure(p: *Parser, early_identifier0: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__destructure);

    // , identifier , identifier [,]
    var identifiers: FixedStack(64) = .{};
    try identifiers.push(early_identifier0);
    outer: while (true) {
        switch (try p.pop_tok()) {
            .@"pct_," => {
                switch (try p.pop_tok()) {
                    .identifier => {
                        const id = try eval.identifier(p);
                        try identifiers.push(id);
                    },
                    else => {
                        p.tok_cursor -= 1;
                        break :outer;
                    },
                }
            },
            else => {
                p.tok_cursor -= 1;
                break :outer;
            },
        }
    }
    p.tree.set_children(parent, identifiers.view());
    return parent;
}

pub fn assign_multival(p: *Parser, early_value0: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__assign_multival);

    // , value , value [NO TRAILING COMMA ALLOWED - TODO]
    var values: FixedStack(64) = .{};
    try values.push(early_value0);
    outer: while (true) {
        switch (try p.pop_tok()) {
            .@"pct_," => {
                try values.push(try eval.any(p, .forbid_assign, 0));
            },
            else => {
                p.tok_cursor -= 1;
                break :outer;
            },
        }
    }
    p.tree.set_children(parent, values.view());
    return parent;
}

pub fn type_param(p: *Parser) anyerror!NodeId {
    const m = try p.peek_eq_tok(.kw_mut);
    if (m) p.tok_cursor += 1;
    const is_mut = m;
    const node0 = try eval.any(p, .forbid_assign, 0);

    const parent = p.tree.push_node(if (is_mut) .partial__type_def_param_mut else .partial__type_def_param);
    var def: Node.LayoutStruct(.partial__type_def_param) = undefined;

    const next_tok = try p.peek_tok();
    if (next_tok != .@"pct_," and next_tok != .@"pct_)" and next_tok != .@"xpct_=" and next_tok != .kw_where) {
        def.type = node0;
        def.identifier = try eval.any(p, .forbid_assign, 0);
    } else {
        def.type = node0;
        def.identifier = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.default_value = try eval.any(p, .forbid_assign, 0);
    } else {
        def.default_value = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_where)) {
        p.tok_cursor += 1;
        def.where_predicate = try eval.any(p, .forbid_assign, 0);
        if (try p.peek_eq_tok(.kw_else)) {
            p.tok_cursor += 1;
            def.where_else_value = try eval.any(p, .forbid_assign, 0);
        } else {
            def.where_else_value = 0xFFFFFFFF;
        }
    } else {
        def.where_predicate = 0xFFFFFFFF;
        def.where_else_value = 0xFFFFFFFF;
    }

    p.tree.set_children(parent, &def);

    return parent;
}

pub fn variant_param(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__variant_def_param);
    var def: Node.LayoutStruct(.partial__variant_def_param) = undefined;

    try p.eat_assert_tok(.identifier);
    def.name = try eval.identifier(p);

    if (try p.peek_eq_tok(.@"pct_(")) {
        p.tok_cursor += 1;
        def.opt_def_type = try eval.type_(p);
    } else {
        def.opt_def_type = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.opt_tag_value = try eval.any(p, .forbid_assign, 0);
    } else {
        def.opt_tag_value = 0xFFFFFFFF;
    }

    p.tree.set_children(parent, &def);
    return parent;
}
