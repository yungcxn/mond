const Parser = @import("../Parser.zig");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const NodeId = ParseTree.NodeId;
const eval = @import("eval.zig");

pub const pre = blk: {
    var t: [256]?*const fn (parser: *Parser) anyerror!NodeId = @splat(null);
    t[@backingInt(Lexer.Token.Kind.@"pct_{")] = &eval.block;
    t[@backingInt(Lexer.Token.Kind.@"pct_(")] = &eval.paren;
    t[@backingInt(Lexer.Token.Kind.@"pct_[")] = &eval.bracket;
    t[@backingInt(Lexer.Token.Kind.kw_typeof)] = &eval.templ_prefix(.typeof, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_isstc)] = &eval.templ_prefix(.isstc, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_sizeof)] = &eval.templ_prefix(.sizeof, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_alignof)] = &eval.templ_prefix(.alignof, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_lenof)] = &eval.templ_prefix(.lenof, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_tagof)] = &eval.templ_prefix(.tagof, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.kw_crash)] = &eval.builtin_call;
    t[@backingInt(Lexer.Token.Kind.kw_asm)] = &eval.builtin_call;
    t[@backingInt(Lexer.Token.Kind.kw_syscall)] = &eval.builtin_call;
    t[@backingInt(Lexer.Token.Kind.kw_fresh)] = &eval.builtin_call;
    t[@backingInt(Lexer.Token.Kind.@"xpct_-")] = &eval.templ_prefix(.neg_num, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_!")] = &eval.templ_prefix(.neg_logic, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_++")] = &eval.templ_prefix(.inc_prefix, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_--")] = &eval.templ_prefix(.dec_prefix, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_..=")] = &eval.templ_prefix(.gen_upperbound_incl, prec_above(.@"xpct_..<"));
    t[@backingInt(Lexer.Token.Kind.@"xpct_..<")] = &eval.templ_prefix(.gen_upperbound_excl, prec_above(.@"xpct_..<"));
    t[@backingInt(Lexer.Token.Kind.kw_self)] = &eval.identifier_self;
    t[@backingInt(Lexer.Token.Kind.kw_true)] = &eval.true_;
    t[@backingInt(Lexer.Token.Kind.kw_false)] = &eval.false_;
    t[@backingInt(Lexer.Token.Kind.kw_do)] = &eval.templ_prefix(.do, 0);
    t[@backingInt(Lexer.Token.Kind.kw_deinit)] = &eval.deinit;
    t[@backingInt(Lexer.Token.Kind.kw_defer)] = &eval.defer_;
    t[@backingInt(Lexer.Token.Kind.kw_cont)] = &eval.cont;
    t[@backingInt(Lexer.Token.Kind.kw_brk)] = &eval.brk;
    t[@backingInt(Lexer.Token.Kind.kw_ret)] = &eval.ret;
    t[@backingInt(Lexer.Token.Kind.kw_if)] = &eval.if_;
    t[@backingInt(Lexer.Token.Kind.kw_while)] = &eval.while_;
    t[@backingInt(Lexer.Token.Kind.kw_for)] = &eval.for_;
    t[@backingInt(Lexer.Token.Kind.kw_loop)] = &eval.loop;
    t[@backingInt(Lexer.Token.Kind.kw_match)] = &eval.match;
    t[@backingInt(Lexer.Token.Kind.kw_stcif)] = &eval.stcif;
    t[@backingInt(Lexer.Token.Kind.kw_stcwhile)] = &eval.stcwhile;
    t[@backingInt(Lexer.Token.Kind.kw_stcfor)] = &eval.stcfor;
    t[@backingInt(Lexer.Token.Kind.kw_stcloop)] = &eval.stcloop;
    t[@backingInt(Lexer.Token.Kind.kw_stcmatch)] = &eval.stcmatch;
    t[@backingInt(Lexer.Token.Kind.@"xpct_&")] = &eval.templ_prefix(.type_ptr, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_*")] = &eval.templ_prefix(.type_ptrmut, prec_unary + 1);
    t[@backingInt(Lexer.Token.Kind.@"xpct_&&")] = &eval.type_ptr_ptr;
    t[@backingInt(Lexer.Token.Kind.kw_u8)] = &eval.type_u8;
    t[@backingInt(Lexer.Token.Kind.kw_u16)] = &eval.type_u16;
    t[@backingInt(Lexer.Token.Kind.kw_u32)] = &eval.type_u32;
    t[@backingInt(Lexer.Token.Kind.kw_u64)] = &eval.type_u64;
    t[@backingInt(Lexer.Token.Kind.kw_i8)] = &eval.type_i8;
    t[@backingInt(Lexer.Token.Kind.kw_i16)] = &eval.type_i16;
    t[@backingInt(Lexer.Token.Kind.kw_i32)] = &eval.type_i32;
    t[@backingInt(Lexer.Token.Kind.kw_i64)] = &eval.type_i64;
    t[@backingInt(Lexer.Token.Kind.stc_maybe)] = &eval.stc_maybe;
    t[@backingInt(Lexer.Token.Kind.kw_f16)] = &eval.type_f16;
    t[@backingInt(Lexer.Token.Kind.kw_f32)] = &eval.type_f32;
    t[@backingInt(Lexer.Token.Kind.kw_f64)] = &eval.type_f64;
    t[@backingInt(Lexer.Token.Kind.kw_bool)] = &eval.type_bool;
    t[@backingInt(Lexer.Token.Kind.kw_ast)] = &eval.type_ast;
    t[@backingInt(Lexer.Token.Kind.kw_quote)] = &eval.quote;
    t[@backingInt(Lexer.Token.Kind.@"xpct_@")] = &eval.unquote;
    t[@backingInt(Lexer.Token.Kind.@"xpct_<")] = &eval.splice;
    t[@backingInt(Lexer.Token.Kind.kw_refl)] = &eval.refl;
    t[@backingInt(Lexer.Token.Kind.kw_include)] = &eval.source(.include);
    t[@backingInt(Lexer.Token.Kind.kw_includeraw)] = &eval.source(.include_raw);
    t[@backingInt(Lexer.Token.Kind.kw_type)] = &eval.type_type;
    t[@backingInt(Lexer.Token.Kind.kw_trait)] = &eval.type_trait;
    t[@backingInt(Lexer.Token.Kind.kw_variant)] = &eval.type_variant;
    t[@backingInt(Lexer.Token.Kind.kw_inlfun)] = &eval.type_inlfun;
    t[@backingInt(Lexer.Token.Kind.kw_fun)] = &eval.type_fun;
    t[@backingInt(Lexer.Token.Kind.kw_stcfun)] = &eval.type_stcfun;
    t[@backingInt(Lexer.Token.Kind.@"xpct_*(")] = &eval.type_;
    t[@backingInt(Lexer.Token.Kind.@"xpct_**(")] = &eval.type_;
    t[@backingInt(Lexer.Token.Kind.@"xpct_+(")] = &eval.variant;
    t[@backingInt(Lexer.Token.Kind.@"xpct_++(")] = &eval.variant;
    t[@backingInt(Lexer.Token.Kind.kw_implof)] = &eval.trait;
    t[@backingInt(Lexer.Token.Kind.@"xpct_!{")] = &eval.trait;
    t[@backingInt(Lexer.Token.Kind.identifier)] = &eval.identifier;
    t[@backingInt(Lexer.Token.Kind.val_string)] = &eval.string;
    t[@backingInt(Lexer.Token.Kind.val_int)] = &eval.int;
    t[@backingInt(Lexer.Token.Kind.val_float)] = &eval.float;
    t[@backingInt(Lexer.Token.Kind.val_char)] = &eval.char;
    break :blk t;
};

// the tokens whose prefix rule is macro syntax: the tree then has macros
pub const macro_syntax = blk: {
    var t: [256]bool = @splat(false);
    t[@backingInt(Lexer.Token.Kind.kw_ast)] = true;
    t[@backingInt(Lexer.Token.Kind.kw_quote)] = true;
    t[@backingInt(Lexer.Token.Kind.@"xpct_@")] = true;
    t[@backingInt(Lexer.Token.Kind.@"xpct_<")] = true;
    t[@backingInt(Lexer.Token.Kind.kw_refl)] = true;
    t[@backingInt(Lexer.Token.Kind.kw_include)] = true;
    t[@backingInt(Lexer.Token.Kind.kw_includeraw)] = true;
    t[@backingInt(Lexer.Token.Kind.kw_fresh)] = true;
    break :blk t;
};

pub const post = blk: {
    var t: [256]?*const fn (parser: *Parser, lhs: u32) anyerror!u32 = @splat(null);
    t[@backingInt(Lexer.Token.Kind.@"pct_(")] = &eval.fun_call;
    t[@backingInt(Lexer.Token.Kind.@"pct_[")] = &eval.array_index;
    t[@backingInt(Lexer.Token.Kind.@"xpct_.")] = &eval.member;
    t[@backingInt(Lexer.Token.Kind.@"xpct_.*")] = &eval.dereference;
    t[@backingInt(Lexer.Token.Kind.@"xpct_.&")] = &eval.address_of;
    t[@backingInt(Lexer.Token.Kind.@"xpct_++")] = &eval.inc_postfix;
    t[@backingInt(Lexer.Token.Kind.@"xpct_--")] = &eval.dec_postfix;
    t[@backingInt(Lexer.Token.Kind.kw_oftype)] = &eval.oftype;
    t[@backingInt(Lexer.Token.Kind.kw_as)] = &eval.as;
    t[@backingInt(Lexer.Token.Kind.kw_asbits)] = &eval.asbits;
    t[@backingInt(Lexer.Token.Kind.@"xpct_??")] = &eval.selftag_unwrap;
    t[@backingInt(Lexer.Token.Kind.kw_defer)] = &eval.inlined_defer_deinit;
    t[@backingInt(Lexer.Token.Kind.kw_with)] = &eval.with;
    break :blk t;
};

// `@..xs` spreads trees a macro made into a list: arms, cases, fields
pub inline fn spread_follows(p: *Parser) !bool {
    const next = p.tokens.get_field(.tk, p.tok_cursor + 1) orelse .none;
    return try p.peek_eq_tok(.@"xpct_@") and next == .@"xpct_..";
}

pub inline fn assign_follows(p: *Parser) bool {
    var cur = p.tok_cursor;
    while (p.tokens.get_field(.tk, cur)) |tk| : (cur += 1) switch (tk) {
        .@"xpct_=" => return true,
        .identifier, .kw_deinit => if (cur == p.tok_cursor) return true,
        .@"pct_," => {},
        else => return false,
    };
    return false;
}

pub inline fn multival_follows(p: *Parser) bool {
    if ((p.tokens.get_field(.tk, p.tok_cursor) orelse return false) != .@"pct_,") return false;
    var depth: u32 = 0;
    var cur = p.tok_cursor + 1;
    while (p.tokens.get_field(.tk, cur)) |tk| : (cur += 1) switch (tk) {
        .@"pct_(", .@"pct_[", .@"pct_{", .@"xpct_!{", .@"xpct_*(", .@"xpct_**(", .@"xpct_+(", .@"xpct_++(" => depth += 1,
        .@"pct_)", .@"pct_]", .@"pct_}" => {
            if (depth == 0) return tk == .@"pct_}" and cur != p.tok_cursor + 1;
            depth -= 1;
        },
        .@"xpct_=>" => if (depth == 0) return false,
        .@"pct_;" => if (depth == 0) return true,
        else => {},
    };
    return true;
}

pub const prec_unary: u8 = blk: {
    var highest: u8 = 0;
    for (binary_compute) |entry| {
        if (entry) |bin| {
            if (bin.prec > highest) highest = bin.prec;
        }
    }
    break :blk highest + 1;
};

pub inline fn prec_above(comptime tok: Lexer.Token.Kind) u8 {
    return comptime binary_compute[@backingInt(tok)].?.prec + 1;
}

pub const binary_compute = blk: {
    var t: [256]?struct {
        f: *const fn (parser: *Parser, lhs: NodeId) anyerror!NodeId,
        prec: u8,
    } = @splat(null);

    t[@backingInt(Lexer.Token.Kind.@"xpct_+=")] = .{ .f = &eval.templ_binary(.assign_add, 0), .prec = 0 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_-=")] = .{ .f = &eval.templ_binary(.assign_sub, 0), .prec = 0 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_*=")] = .{ .f = &eval.templ_binary(.assign_mul, 0), .prec = 0 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_/=")] = .{ .f = &eval.templ_binary(.assign_div, 0), .prec = 0 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_%=")] = .{ .f = &eval.templ_binary(.assign_mod, 0), .prec = 0 };
    t[@backingInt(Lexer.Token.Kind.kw_or)] = .{ .f = &eval.templ_binary(.binary_logic_or, 1), .prec = 1 };
    t[@backingInt(Lexer.Token.Kind.kw_xor)] = .{ .f = &eval.templ_binary(.binary_logic_xor, 2), .prec = 2 };
    t[@backingInt(Lexer.Token.Kind.kw_and)] = .{ .f = &eval.templ_binary(.binary_logic_and, 3), .prec = 3 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_&&")] = .{ .f = &eval.templ_binary(.binary_logic_and, 3), .prec = 3 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_|")] = .{ .f = &eval.templ_binary(.binary_num_or, 4), .prec = 4 };
    // types unify looser than any prefix: `&u8 || [2]u8` is `(&u8) || ([2]u8)`
    t[@backingInt(Lexer.Token.Kind.@"xpct_||")] = .{ .f = &eval.templ_unify_variants(.unify_variants, 4), .prec = 4 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_|||")] = .{ .f = &eval.templ_unify_variants(.unify_variants_packed, 4), .prec = 4 };
    // ranges bind looser than arithmetic, shifts and comparisons (`s[i + 1..<n]`), tighter than `|`
    // which separates alternatives of an arm (`1..<3 | 7 =>`)
    t[@backingInt(Lexer.Token.Kind.@"xpct_..")] = .{ .f = &eval.gen_lowerbound, .prec = 5 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_..=")] = .{ .f = &eval.gen_incl, .prec = 5 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_..<")] = .{ .f = &eval.gen_excl, .prec = 5 };
    // a label names all on its left that binds tighter than `|` and logic: `a * 2 <- d > 4`
    t[@backingInt(Lexer.Token.Kind.@"xpct_<-")] = .{ .f = &eval.labelarrow, .prec = 5 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_?<-")] = .{ .f = &eval.selftag_arrow, .prec = 5 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_^")] = .{ .f = &eval.templ_binary(.binary_num_xor, 6), .prec = 6 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_&")] = .{ .f = &eval.templ_binary(.binary_num_and, 7), .prec = 7 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_==")] = .{ .f = &eval.templ_binary(.binary_eq, 8), .prec = 8 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_!=")] = .{ .f = &eval.templ_binary(.binary_neq, 8), .prec = 8 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_<")] = .{ .f = &eval.templ_binary(.binary_less, 9), .prec = 9 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_>")] = .{ .f = &eval.templ_binary(.binary_greater, 9), .prec = 9 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_<=")] = .{ .f = &eval.templ_binary(.binary_less_eq, 9), .prec = 9 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_>=")] = .{ .f = &eval.templ_binary(.binary_greater_eq, 9), .prec = 9 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_<<")] = .{ .f = &eval.templ_binary(.binary_shift_left, 10), .prec = 10 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_>>")] = .{ .f = &eval.templ_binary(.binary_shift_right, 10), .prec = 10 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_+")] = .{ .f = &eval.templ_binary(.binary_add, 11), .prec = 11 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_~")] = .{ .f = &eval.templ_binary(.binary_join, 11), .prec = 11 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_-")] = .{ .f = &eval.templ_binary(.binary_sub, 11), .prec = 11 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_*")] = .{ .f = &eval.templ_binary(.binary_mul, 12), .prec = 12 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_*(")] = .{ .f = &eval.templ_binary_group(.binary_mul, 12), .prec = 12 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_+(")] = .{ .f = &eval.templ_binary_group(.binary_add, 11), .prec = 11 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_/")] = .{ .f = &eval.templ_binary(.binary_div, 12), .prec = 12 };
    t[@backingInt(Lexer.Token.Kind.@"xpct_%")] = .{ .f = &eval.templ_binary(.binary_mod, 12), .prec = 12 };

    break :blk t;
};
