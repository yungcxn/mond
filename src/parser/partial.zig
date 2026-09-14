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
    const parent = p.tree.push_node(.partial__fun_header);
    var def: Node.LayoutStruct(.partial__fun_header) = undefined;
    def.param_tuple = try ee_fun_param_tuple(p, early_node0_in_tuple);

    if (try p.peek_eq_tok(.@"xpct_->")) {
        p.tok_cursor += 1;
        def.return_type = try eval.any(p, 0);
    } else {
        def.return_type = 0xFFFFFFFF;
    }

    p.tree.set_node_arg0(parent, def.param_tuple);
    p.tree.set_node_arg1(parent, def.return_type);
    return parent;
}

pub fn ee_fun_param_tuple(p: *Parser, early_node0: ?NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_param_tuple);

    if (early_node0 == null and try p.peek_eq_tok(.@"pct_)")) {
        p.tok_cursor += 1;
        return parent;
    }

    var params: FixedStack(64) = .{};
    try params.push(try ee_fun_param(p, early_node0.?));
    while (try p.peek_eq_tok(.@"pct_,")) {
        p.tok_cursor += 1;
        if (try p.peek_eq_tok(.@"pct_)")) break;
        try params.push(try ee_fun_param(p, try eval.any(p, 0)));
    }
    try p.eat_assert_tok(.@"pct_)");

    p.tree.push_extra_childrefs(parent, params.view());
    return parent;
}

pub fn ee_fun_param(p: *Parser, early_node0: NodeId) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_param);
    var def: Node.LayoutStruct(.partial__fun_param) = undefined;
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
        def.default_value = try eval.any(p, 0);
    } else {
        def.default_value = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_where)) {
        p.tok_cursor += 1;
        def.where_predicate = try eval.any(p, 0);
        if (try p.peek_eq_tok(.kw_else)) {
            p.tok_cursor += 1;
            def.where_else_value = try eval.any(p, 0);
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
    p.tree.push_extra_childrefs(parent, match_cases.view());
    return parent;
}

pub fn match_case(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__match_case);
    var def: Node.LayoutStruct(.partial__match_case) = .{
        .pattern = try eval.any(p, 0),
        .body = 0xFFFFFFFF,
    };

    if (try p.peek_eq_tok(.@"xpct_=>")) {
        p.tok_cursor += 1;
        def.body = try eval.any(p, 0);
    }
    p.tree.set_node_arg0(parent, def.pattern);
    p.tree.set_node_arg1(parent, def.body);
    return parent;
}

pub fn fun_call_param_tuple(p: *Parser) anyerror!NodeId {
    const parent = p.tree.push_node(.partial__fun_call_param_tuple);
    try p.eat_assert_tok(.@"pct_(");

    if (!try p.peek_eq_tok(.@"pct_)")) {
        var params: FixedStack(64) = .{};
        while (true) {
            try params.push(try eval.any(p, 0));
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
    p.tree.push_extra_childrefs(parent, identifiers.view());
    return parent;
}

pub fn type_param(p: *Parser, early: ?struct { is_mut: bool, node0: NodeId }) anyerror!NodeId {
    const is_mut, const node0 = if (early) |e| .{ e.is_mut, e.node0 } else blk: {
        const m = try p.peek_eq_tok(.kw_mut);
        if (m) p.tok_cursor += 1;
        break :blk .{ m, try eval.any(p, 0) };
    };

    const parent = p.tree.push_node(if (is_mut) .partial__type_param_mut else .partial__type_param);
    var def: Node.LayoutStruct(.partial__type_param) = undefined;

    const next_tok = try p.peek_tok();
    if (next_tok != .@"pct_," and next_tok != .@"pct_)" and next_tok != .@"xpct_=" and next_tok != .kw_where) {
        def.type = node0;
        try p.eat_assert_tok(.identifier);
        def.identifier = try eval.identifier(p);
    } else {
        def.type = node0;
        def.identifier = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.default_value = try eval.any(p, 0);
    } else {
        def.default_value = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.kw_where)) {
        p.tok_cursor += 1;
        def.where_predicate = try eval.any(p, 0);
        if (try p.peek_eq_tok(.kw_else)) {
            p.tok_cursor += 1;
            def.where_else_value = try eval.any(p, 0);
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

pub fn variant_param(p: *Parser, early_identifier0: ?NodeId) anyerror!NodeId {
    const name = early_identifier0 orelse blk: {
        try p.eat_assert_tok(.identifier);
        break :blk try eval.identifier(p);
    };

    const parent = p.tree.push_node(.partial__variant_param);
    var def: Node.LayoutStruct(.partial__variant_param) = undefined;
    def.name = name;

    if (try p.peek_eq_tok(.kw_of)) {
        p.tok_cursor += 1;
        def.of_type = try eval.any(p, 0);
    } else {
        def.of_type = 0xFFFFFFFF;
    }

    if (try p.peek_eq_tok(.@"xpct_=")) {
        p.tok_cursor += 1;
        def.tag_value = try eval.any(p, 0);
    } else {
        def.tag_value = 0xFFFFFFFF;
    }

    p.tree.push_extra_childrefs(parent, &def);
    return parent;
}
