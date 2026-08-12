const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const Tree = struct {
    pub const Node = struct {
        nk: Kind,
        args: @Vector(2, u32),

        pub const Kind = enum(u8) {
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
            expr_unary_logical_neg,

            expr_binary_logical_or,
            expr_binary_logical_xor,
            expr_binary_logical_and,
            expr_binary_bitwise_or,
            expr_binary_bitwise_xor,
            expr_binary_bitwise_and,
            expr_binary_eq,
            expr_binary_neq,
            expr_binary_less,
            expr_binary_greater,
            expr_binary_less_eq,
            expr_binary_greater_eq,
            expr_binary_add,
            expr_binary_sub,
            expr_binary_mul,
            expr_binary_div,
            expr_binary_mod,
            expr_binary_pow,

            // leave nodes with first arg pointing into respective data_* buf //

            expr_identifier,
            expr_string,
            expr_int,
            expr_float,
            expr_char,
            expr_bool,
        };

        pub const tok_to_typeexpr = blk: {
            var t: [256]Node.Kind = @splat(.none);
            t[@intFromEnum(Lexer.Token.Kind.kw_u8)] = .typeexpr_builtin_u8;
            t[@intFromEnum(Lexer.Token.kw_u32)] = .typeexpr_builtin_u32;
            t[@intFromEnum(Lexer.Token.kw_f32)] = .typeexpr_builtin_f32;
            t[@intFromEnum(Lexer.Token.kw_bool)] = .typeexpr_builtin_bool;
            break :blk t;
        };

        pub const tok_to_expr_unary = blk: {
            var t: [256]Node.Kind = @splat(.none);
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .expr_unary_neg;
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_!")] = .expr_unary_logical_neg;
            break :blk t;
        };

        pub const tok_to_tagged_expr_binary = blk: {
            var t: [256]packed struct { nt: Node.Kind, prec: u8 } = @splat(.{ .nt = .none, .prec = 0 });

            t[@intFromEnum(Lexer.Token.Kind.@"xpct_||")] = .{ .nt = .expr_binary_logical_or, .prec = 3 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_^^")] = .{ .nt = .expr_binary_logical_xor, .prec = 3 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_&&")] = .{ .nt = .expr_binary_logical_and, .prec = 4 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_|")] = .{ .nt = .expr_binary_bitwise_or, .prec = 5 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_^")] = .{ .nt = .expr_binary_bitwise_xor, .prec = 6 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_&")] = .{ .nt = .expr_binary_bitwise_and, .prec = 7 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_==")] = .{ .nt = .expr_binary_eq, .prec = 8 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_!=")] = .{ .nt = .expr_binary_neq, .prec = 8 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_<")] = .{ .nt = .expr_binary_less, .prec = 9 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_>")] = .{ .nt = .expr_binary_greater, .prec = 9 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_<=")] = .{ .nt = .expr_binary_less_eq, .prec = 9 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_>=")] = .{ .nt = .expr_binary_greater_eq, .prec = 9 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_+")] = .{ .nt = .expr_binary_add, .prec = 10 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_-")] = .{ .nt = .expr_binary_sub, .prec = 10 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_*")] = .{ .nt = .expr_binary_mul, .prec = 11 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_/")] = .{ .nt = .expr_binary_div, .prec = 11 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_%")] = .{ .nt = .expr_binary_mod, .prec = 11 };
            t[@intFromEnum(Lexer.Token.Kind.@"xpct_**")] = .{ .nt = .expr_binary_pow, .prec = 12 };

            break :blk t;
        };

        pub const tok_to_expr_data = blk: {
            var t: [256]Node.Kind = @splat(.none);
            t[@intFromEnum(Lexer.Token.Kind.identifier)] = .expr_identifier;
            t[@intFromEnum(Lexer.Token.Kind.val_string)] = .expr_string;
            t[@intFromEnum(Lexer.Token.Kind.val_int)] = .expr_int;
            t[@intFromEnum(Lexer.Token.Kind.val_float)] = .expr_float;
            t[@intFromEnum(Lexer.Token.Kind.val_char)] = .expr_char;
            t[@intFromEnum(Lexer.Token.Kind.kw_true)] = .expr_bool;
            t[@intFromEnum(Lexer.Token.Kind.kw_false)] = .expr_bool;
            break :blk t;
        };
    };

    ast_nodes: SoD(Node),
    extra_childrefs: DynBuf(u32), // children of node i must be contiguous here
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
                .alloc = alloc,
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

        pub inline fn store(self: *@This(), store_for_nk: Node.Kind, data: anytype) u32 {
            var pushed_idx: u32 = undefined;
            switch (store_for_nk) {
                .expr_identifier => if (comptime @TypeOf(data) == []const u8) {
                    self.data_identifiers.push(data);
                    pushed_idx = self.data_identifiers.head - 1;
                },
                .expr_string => if (comptime @TypeOf(data) == []const u8) {
                    self.data_strings.push(data);
                    pushed_idx = self.data_strings.head - 1;
                },
                .expr_int => if (comptime @TypeOf(data) == []const u8) {
                    const parsed_int = parse_u64(data);
                    self.data_ints.push(parsed_int);
                    pushed_idx = self.data_ints.head - 1;
                },
                .expr_float => if (comptime @TypeOf(data) == []const u8) {
                    const parsed_float = parse_f64(data);
                    self.data_floats.push(parsed_float);
                    pushed_idx = self.data_floats.head - 1;
                },
                .expr_char => if (comptime @TypeOf(data) == []const u8) {
                    const parsed_char = parse_char(data);
                    self.data_chars.push(parsed_char);
                    pushed_idx = self.data_chars.head - 1;
                },
                .expr_bool => if (comptime @TypeOf(data) == bool) {
                    self.data_bools.push(data);
                    pushed_idx = self.data_bools.head - 1;
                },
                else => unreachable,
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
            .extra_childrefs = .init(alloc, 10000),
            .data_store = .init(alloc),
        };
    }

    pub fn deinit(self: *@This()) void {
        self.ast_nodes.deinit();
        self.extra_childrefs.deinit();
        self.data_store.deinit();
    }

    pub inline fn set_node_arg0(self: *@This(), target_node: u32, val: u32) void {
        const args_ptr = self.ast_nodes.field_ptr(.args, target_node) orelse unreachable;
        args_ptr.*[0] = val;
    }

    pub inline fn set_node_arg1(self: *@This(), target_node: u32, val: u32) void {
        const args_ptr = self.ast_nodes.field_ptr(.args, target_node) orelse unreachable;
        args_ptr.*[1] = val;
    }

    // fully registers a new children to a parent node with "n" (>2) children
    pub inline fn new_extra_childref(self: *@This(), parent_idx: u32, childref: u32) void {
        self.extra_childrefs.push(childref);
        const args_ptr = self.ast_nodes.field_ptr(.args, parent_idx) orelse unreachable;
        if (args_ptr.*[1] == 0) {
            args_ptr.*[0] = self.extra_childrefs.head - 1;
        }
        args_ptr.*[1] += 1;
    }

    // -> `u32`: idx where node was pushed into
    pub inline fn push_node(self: *@This(), nodekind: Node.Kind) u32 {
        self.ast_nodes.push(.{ .nk = nodekind, .args = .{ 0, 0 } });
        return self.ast_nodes.len() - 1;
    }

    pub inline fn push_data_node(self: *@This(), nodekind: Node.Kind, data: anytype) u32 {
        comptime {
            const T = @TypeOf(data);
            if (T != bool and T != []const u8) @compileError("wrong data: " ++ @typeName(T));
        }

        const new_node_idx = self.push_node(nodekind);
        const stored_idx = self.data_store.store(nodekind, data);
        self.set_node_arg0(new_node_idx, stored_idx);

        return new_node_idx;
    }
};

tokens: SoD(Lexer.Token), // in
src_bytes: []const u8, // in
tok_cursor: u32 = 0, //      internal
tree: Tree, //               out

pub fn init(
    alloc: std.mem.Allocator,
    tokens: SoD(Lexer.Token),
    src_bytes: []const u8,
) @This() {
    return @This(){
        .tokens = tokens,
        .src_bytes = src_bytes,
        .tree = .init(alloc),
    };
}

pub fn deinit(self: *@This()) void {
    self.tree.deinit();
}

inline fn peek_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn pop_tok(self: *@This()) ?Lexer.Token {
    defer self.tok_cursor += 1;
    return self.tokens.get(self.tok_cursor);
}

inline fn pop_tok_kind(self: *@This()) ?Lexer.Token.Kind {
    defer self.tok_cursor += 1;
    return self.tokens.get_field(.tk, self.tok_cursor);
}

inline fn realize_span(self: *@This(), span: Lexer.TextSpan) []const u8 {
    return self.src_bytes[span[0]..span[1]];
}

fn eval_stmt(self: *@This()) !u32 {
    const tok = self.pop_tok() orelse return error.EOF;

    switch (tok.tk) {
        .@"pct_{" => {
            const parent_exec_block_idx = self.tree.push_node(.stmt_exec_block);
            while (true) {
                const child_stmt_idx = try self.eval_expr();
                self.tree.new_extra_childref(parent_exec_block_idx, child_stmt_idx);

                const peeked = self.peek_tok_kind() orelse return error.EOF;
                if (peeked == .@"pct_}") break;
            }
        },
        .kw_if => {
            const child_expr_idx = try self.eval_expr();
            const child_stmt_idx = try self.eval_stmt();

            const peeked = self.peek_tok_kind() orelse return error.EOF;
            if (peeked == .kw_else) {
                _ = self.pop_tok();
                const alt_child_stmt_idx = try self.eval_stmt();
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
            if (tok.tk == .kw_mut) {}
            // TODO
        },
    }

    return error.EOF;
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_expr(self: *@This()) !u32 {
    const P = @TypeOf(self);

    const prec_parse = struct {
        pub fn prec_parse(self_: P, min_prec: u32) !u32 {
            const tok = self_.pop_tok() orelse return error.EOF;

            var left_idx: u32 = undefined;

            if (tok.tk == .@"pct_(") {
                // nested () just recurses into ourselves at min_prec 0
                const paren_node_idx = self_.tree.push_node(.expr_paren);
                left_idx = try prec_parse(self_, 0);

                self_.tree.set_node_arg0(paren_node_idx, left_idx);
                left_idx = paren_node_idx;

                const tok_close = self_.pop_tok_kind() orelse return error.EOF;
                if (tok_close != .@"pct_)") return error.MissingEnclosingParen;
            } else if (Tree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)] != .none) {
                const unary_nt = Tree.Node.tok_to_expr_unary[@intFromEnum(tok.tk)];
                const unary_node_idx = self_.tree.push_node(unary_nt);
                const child_idx = try prec_parse(self_, 0);

                self_.tree.set_node_arg0(unary_node_idx, child_idx);
                left_idx = unary_node_idx;
            } else {
                const data_nt = Tree.Node.tok_to_expr_data[@intFromEnum(tok.tk)];
                if (data_nt == .none) return error.SyntaxError;
                left_idx = self_.tree.push_data_node(data_nt, self_.realize_span(tok.span));
            }

            while (true) {
                const next_tok = self_.peek_tok_kind() orelse break;
                const bin_lookup = Tree.Node.tok_to_tagged_expr_binary[@intFromEnum(next_tok)];
                if (bin_lookup.nt == .none) break;
                if (bin_lookup.prec < min_prec) break;

                // op consumption
                self_.tok_cursor += 1;

                const op_node_idx = self_.tree.push_node(bin_lookup.nt);
                const right_idx = try prec_parse(self_, bin_lookup.prec + 1);

                self_.tree.set_node_arg0(op_node_idx, left_idx);
                self_.tree.set_node_arg1(op_node_idx, right_idx);

                left_idx = op_node_idx;
            }

            return left_idx;
        }
    }.prec_parse;

    return prec_parse(self, 0);
}

// assumed: `tok_cursor` is at first relevant token of a `expr_type`
// also assumed: this func is not used if the token cursor is on a optionally given type
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_type(self: *@This()) !u32 {
    var first_node_idx: ?u32 = null;
    var last_parent_idx: ?u32 = null;
    var done: bool = false;

    while (true) {
        const tok = self.pop_tok() orelse return error.SyntaxError;
        var new_child_idx: u32 = undefined;
        switch (tok.tk) {
            .@"xpct_*" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_pointer);
            },
            .@"xpct_&" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_constpointer);
            },
            .@"pct_[" => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_array);
                const next_tok = self.peek_tok_kind() orelse return error.EOF;
                if (next_tok == .@"pct_]") {
                    self.tree.set_node_arg1(new_child_idx, 0xFFFFFFFF);
                } else {
                    const expr_node_idx = try self.eval_expr();
                    self.tree.set_node_arg1(new_child_idx, expr_node_idx);
                }
            },
            .kw_u32 => {
                new_child_idx = self.tree.push_node(.typeexpr_builtin_u32);
                done = true;
            },
            .identifier => {
                new_child_idx = self.tree.push_node(.typeexpr_type_custom);

                const child_child_idx = self.tree.push_data_node(.expr_identifier, self.realize_span(tok.span));

                self.tree.set_node_arg0(new_child_idx, child_child_idx);
                self.tree.set_node_arg0(new_child_idx, 0xFFFFFFFF);
                done = true;
            },
            else => return error.SyntaxError,
        }
        if (first_node_idx == null) first_node_idx = new_child_idx;
        if (last_parent_idx != null) self.tree.set_node_arg0(last_parent_idx.?, new_child_idx);
        if (done) return first_node_idx.?;

        last_parent_idx = new_child_idx;
    }
}

// assumed: `tok_cursor` is at first relevant token of a `param_deftuple`
// -> `null`: outside of text ; `u32`: the index of the topmost parent created here
fn eval_param_deftuple(self: *@This()) !u32 {
    const tok0 = self.pop_tok() orelse return error.EOF;

    if (tok0.tk != .@"pct_(") return error.ParenAssumed;

    const deftuple_node_idx = self.tree.push_node(.param_deftuple);
    self.tree.set_node_arg0(deftuple_node_idx, 0xFFFFFFFF);

    var children_idxs: [64]u32 = undefined;
    var paramc: u8 = 0;

    while (true) {
        if (self.peek_tok_kind() == .@"pct_)") break;

        const defsingle_node_idx = self.tree.push_node(.param_defsingle);
        children_idxs[paramc] = defsingle_node_idx;
        paramc += 1;

        const child_type_idx = try self.eval_type();

        const next_tok = self.pop_tok() orelse return error.EOF;
        if (next_tok.tk != .identifier) return error.IdentifierAssumed;
        const child_identifier_idx = self.tree.push_data_node(.expr_identifier, self.realize_span(next_tok.span));

        self.tree.set_node_arg0(defsingle_node_idx, child_type_idx);
        self.tree.set_node_arg1(defsingle_node_idx, child_identifier_idx);
    }

    return deftuple_node_idx;
}

// assumed: `tok_cursor` is at first relevant token of a `func_def`
//   and must exit on cursor being on first token outside of func `exec_block`
// -> `false`: no new func generated
fn eval_func(self: *@This()) !bool {
    // func "header":
    const tok_cursor_save = self.tok_cursor;
    const peeked_tok0 = self.pop_tok() orelse return false;
    const peeked_tok1 = self.pop_tok() orelse return error.EOF; // "func name" or "("
    self.tok_cursor = tok_cursor_save;

    const func_node_idx = self.tree.push_node(.func_def);

    // type, identifier, param_deftuple, stmt
    var children_idxs: [4]u32 = undefined;

    if (peeked_tok0.tk == .identifier and peeked_tok1.tk == .@"pct_(") {
        // untyped, funcxxx(...)
        children_idxs[0] = self.tree.push_node(.none);
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, self.realize_span(peeked_tok0.span));
    } else {
        // typed, typexxx funcxxx(...)
        children_idxs[0] = try self.eval_type();

        const next_tok = self.pop_tok() orelse return error.EOF;
        if (next_tok.tk != .identifier) return error.IdentifierAssumed;
        children_idxs[1] = self.tree.push_data_node(.expr_identifier, self.realize_span(next_tok.span));
    }

    // cursor should be on '(' token
    children_idxs[2] = try self.eval_param_deftuple();
    children_idxs[3] = try self.eval_stmt();

    inline for (children_idxs) |childidx| {
        self.tree.new_extra_childref(func_node_idx, childidx);
    }

    return true;
}

pub fn build_ast(self: *@This()) !void {
    _ = self.tree.push_node(.none); // sentinel to correctly understand argi=0

    // first token guaranteed to be "func_def-relevant"
    while (try self.eval_func()) {}
}
