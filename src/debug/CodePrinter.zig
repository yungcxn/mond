// a tree as the source it reads as: what macros expanded to, for the editor and `-p code`
// the grouping a tree has in its shape is written as parentheses, comments and layout are gone
const CodePrinter = @This();
const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const Node = ParseTree.Node;
const NodeId = ParseTree.NodeId;

out: *std.ArrayList(u8),
allocator: std.mem.Allocator,
tree: *const ParseTree,
source: []const u8,
// a splice evaluated in this pass is written as what it expanded to
expand: bool = false,
depth: u32 = 0,
// per name as written, its only spelling in the code `note_names` saw, null when there are several:
// a name hygiene made (``t`1``) is then written as `t`
spellings: std.StringHashMapUnmanaged(?[]const u8) = .empty,

const Error = std.mem.Allocator.Error;

// how tightly a node holds together, one looser than its place asks for goes in parentheses
// binary operators bind from 1 to 12 as the parser has them, `open` ends in an operand that takes
// everything after it (`ret x`, `if c: x`). ranges and the patterns of arms are above `|`
const open: u8 = 0;
const range: u8 = 5;
const cast: u8 = 13;
const prefix: u8 = 14;
const postfix: u8 = 15;
const primary: u8 = 16;

// the statements of a block or of the file, each on a line of its own
pub fn statements(self: *CodePrinter, items: []const NodeId) Error!void {
    for (items) |item| {
        // a splice expanded into statements stands for them, as the rebuilt tree has it
        const tree = self.tree;
        const expansion = if (self.expand and tree.kind(item) == .splice) tree.arg(item, 1) else 0;
        const spread = expansion != 0 and tree.kind(expansion - 1) == .block;
        for (if (spread) tree.manychildren(expansion - 1) else (&item)[0..1]) |statement| {
            try self.indent();
            try self.operand(statement, open, false);
            try self.text(";\n");
        }
    }
}

pub fn expression(self: *CodePrinter, node: NodeId) Error!void {
    return self.operand(node, open, false);
}

// the names of what will be printed, before it is: see `spellings`
pub fn note_names(self: *CodePrinter, node: NodeId) Error!void {
    const tree = self.tree;
    const n = self.unwrapped(node);
    switch (Node.nk_childc[@backingInt(tree.kind(n))]) {
        .data => if (tree.kind(n) == .identifier) {
            const name = tree.text(n, self.source);
            const entry = try self.spellings.getOrPut(self.allocator, written_as(name));
            if (!entry.found_existing) {
                entry.value_ptr.* = name;
            } else if (entry.value_ptr.*) |spelling| {
                if (!std.mem.eql(u8, spelling, name)) entry.value_ptr.* = null;
            }
        },
        .none => {},
        .one, .two, .many => for (tree.children(n)) |child| {
            if (child != 0) try self.note_names(child);
        },
    }
}

// a name without the number hygiene gave it (``t`1``), any other as it is (``ns`name``)
fn written_as(name: []const u8) []const u8 {
    const tick = std.mem.indexOfScalar(u8, name, '`') orelse return name;
    const number = name[tick + 1 ..];
    if (number.len == 0 or std.mem.indexOfNone(u8, number, "0123456789") != null) return name;
    return name[0..tick];
}

// `node` in a place asking for `level`: parenthesized when it binds looser. a left operand is also
// put in parentheses when it ends in one that would take what follows it (`a + b..<c`, `x??`) or
// ends the expression (`{ .. }`)
fn operand(self: *CodePrinter, node: NodeId, level: u8, left: bool) Error!void {
    const tree = self.tree;
    const n = self.unwrapped(node);
    const binding: u8 = switch (tree.kind(n)) {
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => open,
        .binary_logic_or => 1,
        .binary_logic_xor => 2,
        .binary_logic_and => 3,
        .binary_num_or, .unify_variants, .unify_variants_packed => 4,
        .gen_lowerbound, .gen_incl, .gen_excl, .gen_upperbound_incl, .gen_upperbound_excl => range,
        .labelarrow, .selftag_arrow => range,
        .binary_num_xor => 6,
        .binary_num_and => 7,
        .binary_eq, .binary_neq => 8,
        .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => 9,
        .binary_shift_left, .binary_shift_right => 10,
        .binary_add, .binary_sub, .binary_join => 11,
        .binary_mul, .binary_div, .binary_mod => 12,
        .as, .asbits, .oftype => cast,
        .typeof, .isstc, .sizeof, .alignof, .lenof, .tagof, .refl, .include, .include_raw => prefix,
        .neg_num, .neg_logic, .inc_prefix, .dec_prefix, .builtin_call, .stc_maybe => prefix,
        .type_ptr, .type_ptrmut, .type_array, .type_array_unlengthed, .type_slice => prefix,
        .fun_call, .array_index, .member, .dereference, .address_of, .with => postfix,
        .inc_postfix, .dec_postfix, .variant_difference, .inlined_defer_deinit => postfix,
        .selftag_unwrap, .selftag_unwrap_fallback => postfix,
        .quote => if (tree.kind(tree.arg(n, 0)) == .block) primary else open,
        .def_fun => if (tree.kind(tree.arg(n, 1)) == .block) primary else open,
        .def_type_assertsize, .def_variant_assertsize, .def_variant_tagtype => open,
        .do, .deinit, .ret, .ret_void, .@"defer", .hole => open,
        .if_then, .if_else, .stcif_then, .stcif_else => open,
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt => open,
        .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq => open,
        .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => open,
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => open,
        else => primary,
    };
    const start = self.out.items.len;
    const wrapped = binding < level or left and self.ends_open(n);
    if (wrapped) try self.text("(");
    try self.write(n);
    if (wrapped) return self.text(")");

    const written = self.out.items;
    if (left and written.len > start and written[written.len - 1] == '}') {
        try self.out.insert(self.allocator, start, '(');
        try self.text(")");
    }
}

// what stands for `node`: parentheses are in the shape, a splice is its expansion when expanding
fn unwrapped(self: *const CodePrinter, node: NodeId) NodeId {
    var n = node;
    while (true) switch (self.tree.kind(n)) {
        .capture => n = self.tree.arg(n, 0),
        .splice => if (self.expand and self.tree.arg(n, 1) != 0) {
            n = self.tree.arg(n, 1) - 1;
        } else return n,
        else => return n,
    };
}

// a left operand ending in one of these takes what follows it: `x?? - 1` and `x-- B` are other
// operators
fn ends_open(self: *const CodePrinter, n: NodeId) bool {
    const tree = self.tree;
    const children = switch (tree.kind(n)) {
        .selftag_unwrap, .selftag_unwrap_fallback, .labelarrow, .selftag_arrow => return true,
        .dec_postfix => return true,
        // the last operand of an index is in its brackets
        .array_index => return false,
        else => |kind| switch (Node.nk_childc[@backingInt(kind)]) {
            .one, .two => tree.children(n),
            else => return false,
        },
    };
    const last = children[children.len - 1];
    return last != 0 and self.ends_open(self.unwrapped(last));
}

// an `if` without `else` at the end: an `else` after it would be its own
fn dangles(self: *const CodePrinter, node: NodeId) bool {
    const tree = self.tree;
    const n = self.unwrapped(node);
    return switch (tree.kind(n)) {
        .if_then, .stcif_then => true,
        .if_else, .stcif_else => self.dangles(tree.arg(n, 1)),
        else => switch (Node.nk_childc[@backingInt(tree.kind(n))]) {
            .one, .two => for (tree.children(n)) |child| {
                if (child != 0 and self.dangles(child)) break true;
            } else false,
            else => false,
        },
    };
}

fn write(self: *CodePrinter, n: NodeId) Error!void {
    const tree = self.tree;
    const kind = tree.kind(n);
    const a, const b = .{ tree.arg(n, 0), tree.arg(n, 1) };
    switch (kind) {
        .capture => try self.operand(a, open, false),
        .block, .partial__trait_def_body => if (tree.arg(n, 1) == 0) {
            try self.text("{}");
        } else {
            try self.text("{\n");
            self.depth += 1;
            try self.statements(tree.manychildren(n));
            self.depth -= 1;
            try self.indent();
            try self.text("}");
        },
        .def_fun => {
            try self.write(a);
            try self.body(b);
        },
        .def_fun_declaration, .partial__fun_def_header => try self.write(a),
        .partial__fun_def_header_ret => {
            try self.write(a);
            try self.text(" -> ");
            try self.operand(b, open, false);
        },
        .partial__fun_def_param_tuple, .partial__fun_call_param_tuple => {
            try self.list("(", tree.manychildren(n), ")");
        },
        .partial__fun_def_param, .partial__type_def_param => try self.operand(a, open, false),
        .partial__fun_def_param_named, .partial__type_def_param_named => {
            try self.write(a);
            try self.text(" ");
            try self.operand(b, open, false);
        },
        .partial__fun_def_param_default, .partial__type_def_param_default => {
            try self.infix(a, " = ", b);
        },
        .partial__fun_def_param_where, .partial__type_def_param_where => {
            try self.infix(a, " where ", b);
        },
        .partial__fun_def_param_stcwhere => try self.infix(a, " stcwhere ", b),
        .partial__fun_def_param_where_else, .partial__type_def_param_where_else => {
            try self.infix(a, " else ", b);
        },
        .partial__type_def_param_mut => {
            try self.text("mut ");
            try self.write(a);
        },
        .array => try self.list("[", tree.manychildren(n), "]"),
        .array_empty => try self.text("[]"),
        .typeof => try self.prefixed("typeof ", a, prefix),
        .isstc => try self.prefixed("isstc ", a, prefix),
        .sizeof => try self.prefixed("sizeof ", a, prefix),
        .alignof => try self.prefixed("alignof ", a, prefix),
        .lenof => try self.prefixed("lenof ", a, prefix),
        .tagof => try self.prefixed("tagof ", a, prefix),
        .type_array => {
            try self.text("[");
            try self.operand(a, open, false);
            try self.text("]");
            try self.operand(b, prefix, false);
        },
        .type_array_unlengthed => try self.prefixed("[]", a, prefix),
        .type_slice => try self.prefixed("[..]", a, prefix),
        .neg_num => try self.prefixed("-", a, prefix),
        .neg_logic => try self.prefixed("!", a, prefix),
        .inc_prefix => try self.prefixed("++", a, prefix),
        .dec_prefix => try self.prefixed("--", a, prefix),
        .gen_upperbound_incl => try self.prefixed("..=", a, range + 1),
        .gen_upperbound_excl => try self.prefixed("..<", a, range + 1),
        .none => {},
        .do => try self.prefixed("do ", a, open),
        .deinit => try self.prefixed("deinit ", a, open),
        .cont => try self.text("cont"),
        .brk => try self.text("brk"),
        .ret => try self.prefixed("ret ", a, open),
        .ret_void => try self.text("ret"),
        .if_then, .stcif_then => {
            try self.text(if (kind == .if_then) "if " else "stcif ");
            try self.operand(a, open, false);
            try self.body(b);
        },
        .if_else, .stcif_else => {
            const then = tree.arg(a, 1);
            try self.text(if (kind == .if_else) "if " else "stcif ");
            try self.operand(tree.arg(a, 0), open, false);
            // `if a: (if b: x) else: y`, the `else` is not the inner one's
            if (tree.kind(self.unwrapped(then)) != .block and self.dangles(then)) {
                try self.text(": ");
                try self.operand(then, primary + 1, false);
            } else try self.body(then);
            try self.text(" else");
            const otherwise = self.unwrapped(b);
            switch (tree.kind(otherwise)) {
                .if_then, .if_else, .stcif_then, .stcif_else, .block => {
                    try self.text(" ");
                    try self.write(otherwise);
                },
                else => {
                    try self.text(": ");
                    try self.operand(b, open, false);
                },
            }
        },
        .@"while", .stcwhile => {
            try self.text(if (kind == .@"while") "while " else "stcwhile ");
            try self.operand(a, open, false);
            try self.body(b);
        },
        .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => {
            const plain = kind == .while_with_repeat_stmt;
            try self.text(if (plain) "while " else "stcwhile ");
            try self.operand(tree.arg(a, 0), open, false);
            try self.text(", ");
            try self.operand(b, open, false);
            try self.body(tree.arg(a, 1));
        },
        .for_seq, .stcfor_seq => {
            try self.text(if (kind == .for_seq) "for " else "stcfor ");
            try self.operand(a, open, false);
            try self.body(b);
        },
        .for_var_in_seq, .stcfor_var_in_seq => {
            try self.text(if (kind == .for_var_in_seq) "for " else "stcfor ");
            try self.operand(b, open, false);
            try self.text(" in ");
            try self.operand(tree.arg(a, 0), open, false);
            try self.body(tree.arg(a, 1));
        },
        .loop, .stcloop => try self.prefixed(if (kind == .loop) "loop " else "stcloop ", a, open),
        .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => {
            const plain = kind == .loop_with_repeat_stmt;
            try self.prefixed(if (plain) "loop " else "stcloop ", a, open);
            try self.body(b);
        },
        .match, .stcmatch => {
            try self.text(if (kind == .match) "match " else "stcmatch ");
            try self.operand(a, open, false);
            try self.text(" ");
            try self.write(b);
        },
        .partial__match_body => {
            try self.text("{\n");
            self.depth += 1;
            for (tree.manychildren(n)) |arm| {
                try self.indent();
                try self.operand(arm, open, false);
                try self.text(",\n");
            }
            self.depth -= 1;
            try self.indent();
            try self.text("}");
        },
        .partial__match_case => {
            try self.arm_pattern(a);
            try self.text(" => ");
            try self.operand(b, open, false);
        },
        .partial__match_case_pattern_or => for (tree.manychildren(n), 0..) |alternative, i| {
            if (i > 0) try self.text(" | ");
            try self.arm_pattern(alternative);
        },
        .partial__match_case_pattern_typecast => {
            try self.operand(a, range, false);
            try self.text(" ");
            try self.write(b);
        },
        .partial__match_case_where => {
            try self.arm_pattern(a);
            try self.text(" where ");
            try self.operand(b, open, false);
        },
        .partial__match_case_pattern_bits => try self.list("bits(", tree.manychildren(n), ")"),
        .partial__bits_field => {
            try self.operand(a, range, false);
            try self.text(" ");
            try self.operand(b, range, false);
        },
        .partial__bits_rest => {
            try self.text("..");
            if (a != 0) try self.write(a);
        },
        .type_ptrmut => try self.prefixed("*", a, prefix),
        .type_ptr => try self.prefixed("&", a, prefix),
        .type_u8 => try self.text("u8"),
        .type_u16 => try self.text("u16"),
        .type_u32 => try self.text("u32"),
        .type_u64 => try self.text("u64"),
        .type_i8 => try self.text("i8"),
        .type_i16 => try self.text("i16"),
        .type_i32 => try self.text("i32"),
        .type_i64 => try self.text("i64"),
        .type_f16 => try self.text("f16"),
        .type_f32 => try self.text("f32"),
        .type_f64 => try self.text("f64"),
        .type_bool => try self.text("bool"),
        .type_ast => try self.text("ast"),
        .type_type => try self.text("type"),
        .type_trait => try self.text("trait"),
        .type_variant => try self.text("variant"),
        .type_unit => try self.text("()"),
        .type_inlfun => try self.text("inlfun"),
        .type_fun => try self.text("fun"),
        .type_stcfun => try self.text("stcfun"),
        .def_type, .def_type_packed, .def_variant, .def_variant_packed => {
            const opening = switch (kind) {
                .def_type => "*(",
                .def_type_packed => "**(",
                .def_variant => "+(",
                else => "++(",
            };
            try self.list(opening, tree.manychildren(a), ")");
        },
        .def_type_assertsize, .def_variant_assertsize => try self.infix(a, " assertsize ", b),
        .def_variant_tagtype => try self.infix(a, " tagtype ", b),
        .def_variant_notagtype => {
            try self.write(a);
            try self.text(" notagtype");
        },
        .def_type_implof, .def_variant_implof => {
            try self.write(a);
            try self.text(" ");
            try self.write(b);
        },
        .def_trait => {
            try self.text("!");
            try self.write(a);
        },
        .def_trait_implof => {
            try self.list("implof ", tree.manychildren(a), " !");
            try self.write(b);
        },
        .partial__type_def_param_tuple,
        .partial__variant_def_param_tuple,
        .partial__trait_def_implof_tuple,
        .partial__destructure,
        .partial__assign_multival,
        => try self.list("", tree.manychildren(n), ""),
        .partial__variant_def_param => try self.operand(a, open, false),
        .partial__variant_def_param_typed => {
            try self.write(a);
            try self.list("(", tree.manychildren(b), ")");
        },
        .partial__variant_def_param_tagged => try self.infix(a, " = ", b),
        .unify_variants => try self.binary(n, " || ", 4),
        .unify_variants_packed => try self.binary(n, " ||| ", 4),
        .variant_difference => {
            try self.operand(a, postfix, true);
            try self.text(" -- ");
            // `A -- B -- C` is `(A -- B) -- C`
            const chained = tree.kind(self.unwrapped(b)) == .variant_difference;
            try self.operand(b, if (chained) primary + 1 else prefix, false);
        },
        .with => {
            try self.operand(a, postfix, true);
            try self.text(" with ");
            try self.write(b);
        },
        .fun_call => {
            try self.operand(a, postfix, true);
            try self.write(b);
        },
        .builtin_call => {
            try self.write(a);
            // `crash "why"`, `fresh name`
            const arguments = tree.manychildren(b);
            const bare = arguments.len == 1 and
                Node.nk_childc[@backingInt(tree.kind(self.unwrapped(arguments[0])))] == .data;
            if (bare) return self.prefixed(" ", arguments[0], prefix);
            try self.text(" ");
            try self.write(b);
        },
        .partial__fun_call_assigned_param => try self.infix(a, " = ", b),
        .array_index => {
            try self.base(a, true, false);
            try self.text("[");
            try self.operand(b, open, false);
            try self.text("]");
        },
        .member => {
            // `@x.@(n)` names the member by another hole, `(@x).y` is a member of the hole
            try self.base(a, tree.kind(b) != .unquote, true);
            try self.text(".");
            try self.write(b);
        },
        .dereference => try self.postfixed(a, ".*"),
        .address_of => try self.postfixed(a, ".&"),
        .inc_postfix => try self.postfixed(a, "++"),
        .dec_postfix => try self.postfixed(a, "--"),
        .gen_lowerbound => {
            try self.operand(a, range, true);
            try self.text("..");
        },
        .selftag_unwrap => try self.postfixed(a, "??"),
        .inlined_defer_deinit => try self.postfixed(a, " defer deinit"),
        .gen_incl, .gen_excl => {
            try self.operand(a, range, true);
            try self.text(if (kind == .gen_incl) "..=" else "..<");
            try self.operand(b, range + 1, false);
        },
        .oftype, .as, .asbits => {
            try self.operand(a, prefix, true);
            try self.text(switch (kind) {
                .oftype => " oftype ",
                .as => " as ",
                else => " asbits ",
            });
            try self.operand(b, prefix, false);
        },
        .labelarrow, .selftag_arrow => {
            try self.operand(a, range, true);
            try self.text(if (kind == .labelarrow) " <- " else " ?<- ");
            if (tree.kind(b) != .partial__destructure) return self.operand(b, open, false);
            try self.list("(", tree.manychildren(b), ")");
        },
        .selftag_unwrap_fallback => {
            try self.operand(a, postfix, true);
            try self.text(" ?? ");
            // a block right after `??` belongs to what holds the unwrap
            const start = self.out.items.len;
            try self.operand(b, open, false);
            if (self.out.items[start] == '{') {
                try self.out.insert(self.allocator, start, '(');
                try self.text(")");
            }
        },
        .@"defer" => try self.prefixed("defer ", a, open),
        .binary_logic_or => try self.binary(n, " or ", 1),
        .binary_logic_xor => try self.binary(n, " xor ", 2),
        .binary_logic_and => try self.binary(n, " and ", 3),
        .binary_num_or => try self.binary(n, " | ", 4),
        .binary_num_xor => try self.binary(n, " ^ ", 6),
        .binary_num_and => try self.binary(n, " & ", 7),
        .binary_eq => try self.binary(n, " == ", 8),
        .binary_neq => try self.binary(n, " != ", 8),
        .binary_less => try self.binary(n, " < ", 9),
        .binary_greater => try self.binary(n, " > ", 9),
        .binary_less_eq => try self.binary(n, " <= ", 9),
        .binary_greater_eq => try self.binary(n, " >= ", 9),
        .binary_shift_left => try self.binary(n, " << ", 10),
        .binary_shift_right => try self.binary(n, " >> ", 10),
        .binary_add => try self.binary(n, " + ", 11),
        .binary_sub => try self.binary(n, " - ", 11),
        .binary_join => try self.binary(n, " ~ ", 11),
        .binary_mul => try self.binary(n, " * ", 12),
        .binary_div => try self.binary(n, " / ", 12),
        .binary_mod => try self.binary(n, " % ", 12),
        .assign_add => try self.binary(n, " += ", open),
        .assign_sub => try self.binary(n, " -= ", open),
        .assign_mul => try self.binary(n, " *= ", open),
        .assign_div => try self.binary(n, " /= ", open),
        .assign_mod => try self.binary(n, " %= ", open),
        .identifier_self => try self.text("self"),
        .identifier => {
            const name = tree.text(n, self.source);
            const written = written_as(name);
            const only = self.spellings.get(written) orelse null;
            const is_only = only != null and std.mem.eql(u8, only.?, name);
            try self.text(if (is_only) written else name);
        },
        .int => try self.text(tree.text(n, self.source)),
        .float => {
            // a lifted float may have no fraction (`2`), it would read as an integer, or have no
            // literal at all
            const digits = tree.text(n, self.source);
            if (std.mem.eql(u8, digits, "inf")) return self.text("(1.0 / 0.0)");
            if (std.mem.eql(u8, digits, "-inf")) return self.text("(-1.0 / 0.0)");
            if (std.mem.eql(u8, digits, "nan")) return self.text("(0.0 / 0.0)");
            try self.text(digits);
            if (std.mem.indexOfNone(u8, digits, "0123456789_") == null) try self.text(".0");
        },
        .string, .char => {
            const quote = if (kind == .string) "\"" else "'";
            try self.text(quote);
            try self.text(tree.text(n, self.source));
            try self.text(quote);
        },
        .boolean_true => try self.text("true"),
        .boolean_false => try self.text("false"),
        .quote => if (tree.kind(a) == .block) {
            try self.text("quote ");
            try self.write(a);
        } else {
            try self.text("quote: ");
            try self.operand(a, open, false);
        },
        .unquote, .unquote_list => {
            try self.text(if (kind == .unquote) "@" else "@..");
            if (self.is_path(a)) return self.write(a);
            try self.text("(");
            try self.operand(a, open, false);
            try self.text(")");
        },
        .paste => {
            try self.write(a);
            try self.write(b);
        },
        .splice => {
            // a `>` ends the splice, a comparison in it is in parentheses
            try self.prefixed("<", a, 10);
            const last = self.out.items[self.out.items.len - 1];
            if (std.mem.indexOfScalar(u8, "-=<>", last) != null) try self.text(" ");
            try self.text(">");
        },
        .refl => if (tree.kind(a) == .none) {
            try self.text("refl");
        } else try self.prefixed("refl ", a, prefix),
        .include => try self.prefixed("include ", a, prefix),
        .include_raw => try self.prefixed("includeraw ", a, prefix),
        .def_var => {
            try self.operand(a, open, false);
            try self.text(" ");
            try self.operand(b, open, false);
        },
        .assign => try self.infix(a, " = ", b),
        .assign_typed => {
            try self.write(a);
            try self.text(" = ");
            try self.operand(b, open, false);
        },
        .mod_pub => try self.prefixed("pub ", a, open),
        .mod_mut => try self.prefixed("mut ", a, open),
        .mod_stc => try self.prefixed("stc ", a, open),
        .stc_maybe => try self.prefixed("stc? ", a, prefix),
        // a statement that didn't parse
        .hole => try self.text(".."),
    }
}

fn text(self: *CodePrinter, bytes: []const u8) Error!void {
    return self.out.appendSlice(self.allocator, bytes);
}

fn indent(self: *CodePrinter) Error!void {
    return self.out.appendNTimes(self.allocator, ' ', 4 * self.depth);
}

// what an `if`, a loop or a function does: a block, else after `:`
fn body(self: *CodePrinter, node: NodeId) Error!void {
    if (self.tree.kind(self.unwrapped(node)) == .block) {
        try self.text(" ");
        return self.write(self.unwrapped(node));
    }
    try self.text(": ");
    try self.operand(node, open, false);
}

fn list(
    self: *CodePrinter,
    opening: []const u8,
    items: []const NodeId,
    closing: []const u8,
) Error!void {
    try self.text(opening);
    for (items, 0..) |item, i| {
        if (i > 0) try self.text(", ");
        try self.operand(item, open, false);
    }
    try self.text(closing);
}

fn infix(self: *CodePrinter, left: NodeId, middle: []const u8, right: NodeId) Error!void {
    try self.operand(left, open, false);
    try self.text(middle);
    try self.operand(right, open, false);
}

fn binary(self: *CodePrinter, n: NodeId, symbol: []const u8, level: u8) Error!void {
    try self.operand(self.tree.arg(n, 0), level, true);
    try self.text(symbol);
    try self.operand(self.tree.arg(n, 1), level + 1, false);
}

// `symbol` before its operand, apart where the two would read as one token (`- -x`, `* (..)`)
fn prefixed(self: *CodePrinter, symbol: []const u8, node: NodeId, level: u8) Error!void {
    try self.text(symbol);
    const start = self.out.items.len;
    try self.operand(node, level, false);
    if (symbol[symbol.len - 1] == ' ' or start == self.out.items.len) return;

    const first = self.out.items[start];
    const last = symbol[symbol.len - 1];
    const fuses = std.mem.indexOfScalar(u8, "+-*&!<>=.|^%/~?{", first) != null or
        first == '(' and (last == '*' or last == '+');
    if (fuses) try self.out.insert(self.allocator, start, ' ');
}

fn postfixed(self: *CodePrinter, node: NodeId, symbol: []const u8) Error!void {
    try self.base(node, false, symbol[0] == '.' and symbol[1] != '.');
    try self.text(symbol);
}

// what a postfix operator applies to. `@x.y` is one hole, so a hole before `.y` or `[i]` is
// parenthesized when `path` says it would take them, and `5.&` would be a float
fn base(self: *CodePrinter, node: NodeId, path: bool, dot: bool) Error!void {
    const kind = self.tree.kind(self.unwrapped(node));
    const hole = path and (kind == .unquote or kind == .unquote_list);
    const number = dot and kind == .int;
    try self.operand(node, if (hole or number) primary + 1 else postfix, true);
}

// what `@` takes without parentheses: a name, its members and elements
fn is_path(self: *const CodePrinter, n: NodeId) bool {
    const tree = self.tree;
    return switch (tree.kind(n)) {
        .identifier => true,
        .member => tree.kind(tree.arg(n, 1)) == .identifier and self.is_path(tree.arg(n, 0)),
        .array_index => self.is_path(tree.arg(n, 0)),
        else => false,
    };
}

// a pattern of an arm or of one of its alternatives, a quote as it is written there
fn arm_pattern(self: *CodePrinter, node: NodeId) Error!void {
    const n = self.unwrapped(node);
    switch (self.tree.kind(n)) {
        .quote,
        .partial__match_case_pattern_or,
        .partial__match_case_pattern_typecast,
        .partial__match_case_where,
        .partial__match_case_pattern_bits,
        => try self.write(n),
        else => try self.operand(n, range, false),
    }
}
