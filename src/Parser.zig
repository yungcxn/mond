const std = @import("std");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Tree = struct {
    ast_nodes: DynBuf(NodeType),
    /// (idx_childref0, idx_childreflen) or (childnode0, childnode1)
    ast_node_args: DynBuf(@Vector(2, u32)),
    extra_childrefs: DynBuf(u32),

    data_store: DataStore,

    pub const DataStore = struct {
        alloc: std.mem.Allocator,
        data_identifiers: DynBuf([]const u8),
        data_strings: DynBuf([]const u8),
        data_ints: DynBuf(u64),
        data_floats: DynBuf(f64),
        data_chars: DynBuf(u8),
        data_bools: DynBuf(bool),

        pub fn init(alloc: std.mem.Allocator) @This() {
            return @This(){
                .data_identifiers = .init(alloc, 10000),
                .data_strings = .init(alloc, 10000),
                .data_ints = .init(alloc, 10000),
                .data_floats = .init(alloc, 10000),
                .data_chars = .init(alloc, 10000),
                .data_bools = .init(alloc, 10000),
            };
        }

        pub fn deinit(self: *@This()) void {
            self.data_identifiers.deinit();
            self.data_strings.deinit();
            self.data_ints.deinit();
            self.data_floats.deinit();
            self.data_chars.deinit();
            self.data_bools.deinit();
        }

        pub inline fn store(self: *@This(), store_for_nt: NodeType, data: anytype) u32 {
            var pushed_idx: u32 = undefined;
            switch (store_for_nt) {
                .expr_identifier => {
                    self.data_identifiers.push(data);
                    pushed_idx = self.data_identifiers.head - 1;
                },
                .expr_string => {
                    self.data_strings.push(data);
                    pushed_idx = self.data_strings.head - 1;
                },
                .expr_int => {
                    const parsed_int = parse_u64(data);
                    self.data_ints.push(parsed_int);
                    pushed_idx = self.data_ints.head - 1;
                },
                .expr_float => {
                    const parsed_float = parse_f64(data);
                    self.data_floats.push(parsed_float);
                    pushed_idx = self.data_floats.head - 1;
                },
                .expr_char => {
                    const parsed_char = parse_char(data);
                    self.data_chars.push(parsed_char);
                    pushed_idx = self.data_chars.head - 1;
                },
                .expr_bool => {
                    self.data_bools.push(data);
                    pushed_idx = self.data_bools.head - 1;
                },
            }

            return pushed_idx;
        }

        inline fn parse_u64(s: []const u8) u64 {
            var result: u64 = 0;
            for (s) |c| {
                result = result * 10 + (c - '0');
            }
            return result;
        }

        inline fn parse_f64(s: []const u8) f64 {
            var int_part: u64 = 0;
            var frac_part: u64 = 0;
            var frac_div: f64 = 1;
            var seen_dot = false;

            for (s) |c| {
                if (c == '.') {
                    seen_dot = true;
                    continue;
                }
                if (seen_dot) {
                    frac_part = frac_part * 10 + (c - '0');
                    frac_div *= 10;
                } else {
                    int_part = int_part * 10 + (c - '0');
                }
            }

            return @as(f64, @floatFromInt(int_part)) + @as(f64, @floatFromInt(frac_part)) / frac_div;
        }

        fn parse_char(s: []const u8) u8 {
            if (s[0] == '\\') {
                return switch (s[1]) {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '\'' => '\'',
                    '"' => '"',
                    '0' => 0,
                    else => unreachable,
                };
            }
            return s[0];
        }
    };

    pub fn init(alloc: std.mem.Allocator) @This() {
        return @This(){
            .ast_nodes = .init(alloc, 10000),
            .ast_node_args = .init(alloc, 10000),
            .extra_childrefs = .init(alloc, 10000),
            .data_store = .init(alloc),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.ast_nodes.deinit();
        self.ast_node_args.deinit();
        self.extra_childrefs.deinit();
        self.data_store.deinit();
    }

    pub inline fn set_node_arg0(self: *@This(), target_node: u32, val: u32) void {
        self.ast_node.args[target_node][0] = val;
    }

    pub inline fn set_node_arg1(self: *@This(), target_node: u32, val: u32) void {
        self.ast_node.args[target_node][1] = val;
    }

    // fully registers a new children to a parent node with "n" (>2) children
    pub inline fn new_extra_childref(self: *@This(), parent_idx: u32, childref: u32) void {
        self.extra_childrefs.push(childref);
        if (self.ast_node_args.buf[parent_idx][1] == 0) {
            self.ast_node_args.buf[parent_idx][0] = self.extra_childrefs.head - 1;
        }
        self.ast_node_args.buf[parent_idx][1] += 1;
    }

    // -> `u32`: idx where node was pushed into
    pub inline fn push_node(self: *@This(), nodetype: NodeType) u32 {
        self.ast_nodes.push(nodetype);
        self.ast_node_args.push(.{ 0, 0 });
        return self.ast_nodes.head - 1; // == ast_node_args.head - 1
    }

    pub inline fn push_data_node(self: *@This(), nodetype: NodeType, data: anytype) u32 {
        comptime {
            if (@TypeOf(data) != bool or @TypeOf(data) != []const u8) @compileError("wrong data");
        }

        const new_node_idx = self.push_node(nodetype);
        const stored_idx = self.data_store.store(nodetype, data);
        self.set_node_arg0(new_node_idx, stored_idx);

        return new_node_idx;
    }

    // lexica:
    //  - statement  := not assignable, does not hold a value
    //  - expression := assignable, valued
    pub const NodeType = enum(u8) {
        none,

        /// (?expr_type, expr_identifier, ?param_deftuple, exec_block)
        func_def,
        type_def,

        /// (param_defsingle[])
        param_deftuple,
        /// (expr_type, expr_identifier)
        param_defsingle,

        /// (expr_...[])
        param_calltuple,
        // method_block,

        stmt_assign,
        stmt_funccall,
        // code block for e.g. func, not a struct def block
        /// ?(<statement>[])
        stmt_exec_block,
        /// expr_... (condition), stmt_...
        stmt_if,
        /// expr_... (condition), stmt_..., stmt_...
        stmt_if_else,

        /// (nothing)
        typeexpr_builtin_u8,
        /// (nothing)
        typeexpr_builtin_u32,
        /// (nothing)
        typeexpr_builtin_f32,
        /// (nothing)
        typeexpr_builtin_bool,
        /// (expr_type) (child)
        typeexpr_builtin_pointer,
        /// (expr_type) (child)
        typeexpr_builtin_constpointer,
        /// (expr_type, <undet_array_size> | expr_*) (child)
        typeexpr_builtin_array,

        /// (expr_identifier, type_def)
        typeexpr_type_custom,

        /// ?param_calltuple
        expr_funccall,
        /// (expr_...)
        expr_paren,
        /// (expr_..., expr_...) - expr0[expr1]
        expr_indexed,

        expr_unary_neg,

        expr_binary_add,
        expr_binary_sub,
        expr_binary_mul,
        expr_binary_div,

        // leave nodes with first arg pointing into respective data_* buf //

        expr_identifier,
        expr_string,
        expr_int,
        expr_float,
        expr_char,
        expr_bool,
    };

    pub const tok_to_typeexpr = blk: {
        var t: [256]NodeType = @splat(.none);
        t[@intFromEnum(Lexer.Token.kw_u8)] = .typeexpr_builtin_u8;
        t[@intFromEnum(Lexer.Token.kw_u32)] = .typeexpr_builtin_u32;
        t[@intFromEnum(Lexer.Token.kw_f32)] = .typeexpr_builtin_f32;
        t[@intFromEnum(Lexer.Token.kw_bool)] = .typeexpr_builtin_bool;
        break :blk t;
    };

    pub const tok_to_expr_unary = blk: {
        var t: [256]NodeType = @splat(.none);
        t[@intFromEnum(Lexer.Token.@"xpct_-")] = .expr_unary_neg;
        t[@intFromEnum(Lexer.Token.@"xpct_!")] = .expr_unary_logical_neg;
        break :blk t;
    };

    pub const tok_to_tagged_expr_binary = blk: {
        var t: [256]packed struct { nt: NodeType, prec: u8 } = @splat(.{ .nt = .none, .prec = 0 });

        t[@intFromEnum(Lexer.Token.@"xpct_||")] = .{ .nt = .expr_binary_logical_or, .prec = 3 };
        t[@intFromEnum(Lexer.Token.@"xpct_^^")] = .{ .nt = .expr_binary_logical_xor, .prec = 3 };
        t[@intFromEnum(Lexer.Token.@"xpct_&&")] = .{ .nt = .expr_binary_logical_and, .prec = 4 };
        t[@intFromEnum(Lexer.Token.@"xpct_|")] = .{ .nt = .expr_binary_bitwise_or, .prec = 5 };
        t[@intFromEnum(Lexer.Token.@"xpct_^")] = .{ .nt = .expr_binary_bitwise_xor, .prec = 6 };
        t[@intFromEnum(Lexer.Token.@"xpct_&")] = .{ .nt = .expr_binary_bitwise_and, .prec = 7 };
        t[@intFromEnum(Lexer.Token.@"xpct_==")] = .{ .nt = .expr_binary_eq, .prec = 8 };
        t[@intFromEnum(Lexer.Token.@"xpct_!=")] = .{ .nt = .expr_binary_neq, .prec = 8 };
        t[@intFromEnum(Lexer.Token.@"xpct_<")] = .{ .nt = .expr_binary_less, .prec = 9 };
        t[@intFromEnum(Lexer.Token.@"xpct_>")] = .{ .nt = .expr_binary_greater, .prec = 9 };
        t[@intFromEnum(Lexer.Token.@"xpct_<=")] = .{ .nt = .expr_binary_less_eq, .prec = 9 };
        t[@intFromEnum(Lexer.Token.@"xpct_>=")] = .{ .nt = .expr_binary_greater_eq, .prec = 9 };
        t[@intFromEnum(Lexer.Token.@"xpct_+")] = .{ .nt = .expr_binary_add, .prec = 10 };
        t[@intFromEnum(Lexer.Token.@"xpct_-")] = .{ .nt = .expr_binary_sub, .prec = 10 };
        t[@intFromEnum(Lexer.Token.@"xpct_*")] = .{ .nt = .expr_binary_mul, .prec = 11 };
        t[@intFromEnum(Lexer.Token.@"xpct_/")] = .{ .nt = .expr_binary_div, .prec = 11 };
        t[@intFromEnum(Lexer.Token.@"xpct_%")] = .{ .nt = .expr_binary_mod, .prec = 11 };
        t[@intFromEnum(Lexer.Token.@"xpct_**")] = .{ .nt = .expr_binary_pow, .prec = 12 };

        break :blk t;
    };

    pub const tok_to_expr_data = blk: {
        var t: [256]NodeType = @splat(.none);
        t[@intFromEnum(Lexer.Token.identifier)] = .expr_identifier;
        t[@intFromEnum(Lexer.Token.val_string)] = .expr_string;
        t[@intFromEnum(Lexer.Token.val_int)] = .expr_int;
        t[@intFromEnum(Lexer.Token.val_float)] = .expr_float;
        t[@intFromEnum(Lexer.Token.val_char)] = .expr_char;

        t[@intFromEnum(Lexer.Token.kw_true)] = .expr_bool;
        t[@intFromEnum(Lexer.Token.kw_false)] = .expr_bool;
        break :blk t;
    };

    pub const NonNode = struct {
        pub const undet_array_size: u32 = 0xFFFFFFFF;
        pub const type_def_missing: u32 = 0xFFFFFFFF;
        pub const no_single_paramdef: u32 = 0xFFFFFFFF;
    };
};

// in
tokens: DynBuf(Lexer.AmbigToken),
spans: DynBuf(Lexer.TextSpan),

// internal
tok_cursor: u32 = 0,

// out
tree: Tree,

pub fn init(
    alloc: std.mem.Allocator,
    tokens: DynBuf(Lexer.AmbigToken),
    spans: DynBuf(Lexer.TextSpan),
) @This() {
    return @This(){
        .tokens = tokens,
        .spans = spans,
        .tree = .init(alloc),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
}

inline fn peek_tok(self: *@This()) ?Lexer.Token {
    if (self.tok_cursor >= self.tokens.head) return null;
    return self.tokens.buf[self.tok_cursor].tok;
}

inline fn pop_unspanned_tok(self: *@This()) ?Lexer.Token {
    if (self.tok_cursor >= self.tokens.head) return null;

    defer self.tok_cursor += 1;
    return self.tokens.buf[self.tok_cursor].tok;
}

inline fn pop_spanned_tok(self: *@This()) ?struct { Lexer.Token, []const u8 } {
    if (self.tok_cursor + 4 >= self.tokens.head) return null;

    defer self.tok_cursor += 5;

    const tok = self.tokens.buf[self.tok_cursor].tok;
    const idx: u32 = @bitCast(self.tokens.buf[self.tok_cursor + 1 ..][0..4].*);
    const span: Lexer.TextSpan = self.spans.buf[idx];
    const txt: []const u8 = self.src_code[span[0]..span[1]];

    return .{ tok, txt };
}

inline fn pop_unknown_tok(self: *@This()) ?struct { Lexer.Token, ?[]const u8 } {
    if (self.tok_cursor >= self.tokens.head) return null;

    if (Lexer.Token.needs_textspan(self.tokens.buf[self.tok_cursor])) {
        return self.pop_spanned_tok();
    } else {
        return self.pop_unspanned_tok();
    }
}

inline fn eval_stmt(self: *@This()) !?u32 {
    const tok_data = self.pop_unknown_tok() orelse return null;

    switch (tok_data[0]) {
        .@"pct_{" => {
            const parent_exec_block_idx = self.tree.push_node(.stmt_exec_block);
            while (true) {
                const child_stmt_idx = try self.eval_expr() orelse return error.EOF;
                self.tree.new_extra_childref(parent_exec_block_idx, child_stmt_idx);

                const peeked = self.peek_tok() orelse return error.EOF;
                if (peeked == .@"pct_}") break;
            }
        },
        .kw_if => {
            const child_expr_idx = try self.eval_expr() orelse return error.EOF;
            const child_stmt_idx = try self.eval_stmt() orelse return error.EOF;

            const peeked = self.peek_tok() orelse return error.EOF;
            if (peeked == .kw_else) {
                _ = self.pop_unspanned_tok();
                const alt_child_stmt_idx = try self.eval_stmt() orelse return error.EOF;
                const parent_if_else_idx = self.tree.push_node(.stmt_if_else);
                self.tree.new_extra_childref(parent_if_else_idx, child_expr_idx);
                self.tree.new_extra_childref(parent_if_else_idx, child_stmt_idx);
                self.tree.new_extra_childref(parent_if_else_idx, alt_child_stmt_idx);
            } else {
                const parent_if_idx = self.tree.push_node(.stmt_if);
                self.tree.set_node_arg0(parent_if_idx, child_expr_idx);
                self.tree.set_node_arg1(parent_if_idx, child_stmt_idx);
            }
        },
        else => { // assign or call statement
            if (tok_data[0] == .kw_mut) {}
            // TODO
        },
    }
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
inline fn eval_expr(self: *@This()) !?u32 {
    const P = @TypeOf(self);

    const prec_parse = struct {
        pub inline fn prec_parse(self_: P, min_prec: u32) !?u32 {
            const tok_data = self_.pop_unknown_tok() orelse return null;

            var left_idx: u32 = undefined;

            if (tok_data[0] == .@"pct_(") {
                // nested () just recurses into ourselves at min_prec 0
                const paren_node_idx = self_.tree.push_node(.expr_paren);
                left_idx = try prec_parse(self_, 0) orelse return error.EOF;

                self_.tree.set_node_arg0(paren_node_idx, left_idx);
                left_idx = paren_node_idx;

                const tok_close = self_.pop_unspanned_tok() orelse return error.EOF;
                if (tok_close != .@"pct_)") return error.MissingEnclosingParen;
            } else if (Tree.tok_to_expr_unary[@intFromEnum(tok_data[0])] != .none) {
                const unary_nt = Tree.tok_to_expr_unary[@intFromEnum(tok_data[0])];
                const unary_node_idx = self_.tree.push_node(unary_nt);
                const child_idx = try prec_parse(self_, 0) orelse return error.EOF;
                self_.tree.set_node_arg0(unary_node_idx, child_idx);
                left_idx = unary_node_idx;
            } else {
                const data_nt = Tree.tok_to_expr_data[@intFromEnum(tok_data[0])];
                if (data_nt == .none) return error.SyntaxError;
                left_idx = self_.tree.push_data_node(data_nt, tok_data[1] orelse return error.MissingSpan);
            }

            while (true) {
                const next_tok = self_.peek_tok() orelse break;
                const bin_lookup = Tree.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
                if (bin_lookup.nt == .none) break;
                if (bin_lookup.prec < min_prec) break;

                // op consumption
                _ = self_.pop_unspanned_tok();

                const op_node_idx = self_.tree.push_node(bin_lookup.nt);
                const right_idx = try prec_parse(self_, bin_lookup.prec + 1) orelse return error.EOF;

                self_.tree.set_node_arg0(op_node_idx, left_idx);
                self_.tree.set_node_arg1(op_node_idx, right_idx);

                left_idx = op_node_idx;
            }

            return left_idx;
        }
    };

    return prec_parse(self, 0);
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// also assumed: this func is not used if the token cursor is on a optionally given type
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
inline fn eval_type(self: *@This()) !?u32 {
    var first_node_idx: ?u32 = null;
    var last_parent_idx: ?u32 = null;
    var done: bool = false;

    while (true) {
        const tok_data = self.pop_unknown_tok() orelse return error.SyntaxError;
        var new_child_idx: u32 = undefined;
        switch (tok_data) {
            .@"xpct_*" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_pointer);
            },
            .@"xpct_&" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_constpointer);
            },
            .@"xpct_[" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_array);
                const next_tok = self.peek_tok() orelse return error.EOF;
                if (next_tok == .@"xpct_]") {
                    self.tree.set_node_arg1(new_child_idx, Tree.NonNode.undet_array_size);
                } else {
                    const expr_node_idx = try self.eval_expr() orelse return error.EOF;
                    self.tree.set_node_arg1(new_child_idx, expr_node_idx);
                }
            },
            .kw_u32 => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_u32);
                done = true;
            },
            .identifier => {
                new_child_idx = self.tree.push_node(.typeexpr_type_custom);

                const child_child_idx = self.tree.push_data_node(
                    .expr_identifier,
                    tok_data[1] orelse return error.NoIdentifierString,
                );

                self.tree.set_node_arg0(new_child_idx, child_child_idx);
                self.tree.set_node_arg0(new_child_idx, Tree.NonNode.typedef_missing);
                done = true;
            },
            else => return error.SyntaxError,
        }
        if (first_node_idx == null) first_node_idx = new_child_idx;
        if (last_parent_idx != null) self.tree.set_node_arg0(last_parent_idx.?, new_child_idx);
        if (done) return first_node_idx.?;

        last_parent_idx = new_child_idx.?;
    }
}

// assumed: `tok_cursor` is at first relevant token of a `param_deftuple`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
inline fn eval_param_deftuple(self: *@This()) !?u32 {
    const tok0_data = self.pop_unspanned_tok() orelse return null;

    if (tok0_data[0] != .@"pct_(") return error.ParenAssumed;

    const deftuple_node_idx = self.tree.push_node(.param_deftuple);
    self.tree.set_node_arg0(deftuple_node_idx, Tree.NonNode.no_single_paramdef);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (self.peek_tok() == .@"pct_)") break;

        const defsingle_node_idx = self.tree.push_node(.param_defsingle);
        children_idxs[paramc] = defsingle_node_idx;
        paramc += 1;

        const child_type_idx = try self.eval_type() orelse return error.EOF;

        const next_tok = self.pop_spanned_tok() orelse return error.EOF;
        if (next_tok[0] != .identifier) return error.IdentifierAssumed;
        const child_identifier_idx = self.tree.push_data_node(.expr_identifier, next_tok[1]);

        self.tree.set_node_arg0(defsingle_node_idx, child_type_idx);
        self.tree.set_node_arg1(defsingle_node_idx, child_identifier_idx);
    }

    return deftuple_node_idx;
}

// assumed: `tok_cursor` is at first relevant token of a `func_def`
//   and must exit on cursor being on first token outside of func `exec_block`
// -> `false`: no new func generated
inline fn eval_func(self: *@This()) !bool {
    // func "header":
    const tok_cursor_save = self.tok_cursor;
    const peeked_tok0_data = self.pop_spanned_tok() orelse return false;
    const peeked_tok1_data = self.pop_unknown_tok() orelse return error.EOF; // "func name" or "("
    self.tok_cursor = tok_cursor_save;

    const func_node_idx = self.tree.push_node(.func_def);

    // type, identifier, param_deftuple, stmt
    var children_idxs: [4]u8 = undefined;

    if (peeked_tok0_data[0] == .identifer and peeked_tok1_data[0] == .@"pct_(") {
        // untyped, funcxxx(...)
        children_idxs[0] = self.tree.push_node(.none);
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, peeked_tok0_data[1] orelse return error.MissingSpan);
    } else {
        // typed, typexxx funcxxx(...)
        children_idxs[0] = self.eval_type();

        const next_tok = self.pop_spanned_tok() orelse return error.EOF;
        if (next_tok[0] != .identifier) return error.IdentifierAssumed;
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, next_tok[1]);
    }

    // cursor should be on '(' token
    children_idxs[2] = self.eval_param_deftuple();
    children_idxs[3] = self.eval_stmt();

    inline for (children_idxs) |childidx| {
        self.tree.new_extra_childref(func_node_idx, childidx);
    }
}

pub fn build_ast(self: *@This()) !void {
    const world_idx: u32 = self.tree.push_node(.none); // sentinel to correctly understand argi=0

    // first token guaranteed to be "func_def-relevant"
    while (try self.eval_func(world_idx)) {}
}
