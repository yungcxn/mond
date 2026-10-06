const ParseTree = @import("../ParseTree.zig");
const DeclPool = @import("DeclPool.zig");
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// the resolver's reading of the parse tree: classes of node kinds and views of the layouts the parser builds,
// nothing here looks further than the tree

pub const Props = packed struct(u8) {
    stc: bool = false,
    loop: bool = false,
    range: bool = false,
    type_expr: bool = false,
    declares: bool = false,
    runit: bool = false,
    literal: bool = false,
    _pad: u1 = 0,
};

const props_of_kind = blk: {
    var t: [256]Props = @splat(.{});

    for ([_]Kind{
        .stcif_then,
        .stcif_else,
        .stcwhile,
        .stcwhile_with_repeat_stmt,
        .stcfor_seq,
        .stcfor_var_in_seq,
        .stcloop,
        .stcloop_with_repeat_stmt,
        .stcmatch,
    }) |k| t[@intFromEnum(k)].stc = true;

    for ([_]Kind{
        .@"while",
        .while_with_repeat_stmt,
        .stcwhile,
        .stcwhile_with_repeat_stmt,
        .for_seq,
        .for_var_in_seq,
        .stcfor_seq,
        .stcfor_var_in_seq,
        .loop,
        .loop_with_repeat_stmt,
        .stcloop,
        .stcloop_with_repeat_stmt,
    }) |k| t[@intFromEnum(k)].loop = true;

    for ([_]Kind{
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
    }) |k| t[@intFromEnum(k)].range = true;

    for (@intFromEnum(Kind.type_ptrmut)..@intFromEnum(Kind.type_stcfun) + 1) |i| t[i].type_expr = true;

    for ([_]Kind{
        .type_array,
        .type_array_unlengthed,
        .def_fun_declaration,
        .typeof,
    }) |k| t[@intFromEnum(k)].type_expr = true;

    for ([_]Kind{
        .def_var,
        .assign,
        .assign_typed,
        .mod_pub,
        .mod_mut,
        .mod_stc,
    }) |k| t[@intFromEnum(k)].declares = true;

    for ([_]Kind{
        .block,
        .if_then,
        .if_else,
        .stcif_then,
        .stcif_else,
        .match,
        .stcmatch,
    }) |k| t[@intFromEnum(k)].runit = true;

    for ([_]Kind{
        .int,
        .float,
        .char,
        .string,
    }) |k| t[@intFromEnum(k)].literal = true;

    break :blk t;
};

pub inline fn props(k: Kind) Props {
    return props_of_kind[@intFromEnum(k)];
}

pub const Param = struct {
    ty: NodeId = 0,
    name: NodeId = 0,
    default: NodeId = 0,
    where: NodeId = 0,
    @"else": NodeId = 0,
    is_mut: bool = false,
    stc: bool = false,

    pub fn from_node(tree: *const ParseTree, n0: NodeId) Param {
        var p = Param{};
        var n = n0;
        while (true) {
            switch (tree.kind(n)) {
                .partial__fun_def_param_named, .partial__type_def_param_named => p.name = tree.arg(n, 1),
                .partial__fun_def_param_default, .partial__type_def_param_default => p.default = tree.arg(n, 1),
                .partial__fun_def_param_where, .partial__type_def_param_where => p.where = tree.arg(n, 1),
                .partial__fun_def_param_stcwhere => {
                    p.where = tree.arg(n, 1);
                    p.stc = true;
                },
                .partial__fun_def_param_where_else, .partial__type_def_param_where_else => p.@"else" = tree.arg(n, 1),
                .partial__type_def_param_mut => p.is_mut = true,
                .partial__fun_def_param, .partial__type_def_param => {
                    p.ty = tree.arg(n, 0);
                    return p;
                },
                else => {
                    p.ty = n;
                    return p;
                },
            }
            n = tree.arg(n, 0);
        }
    }
};

pub const Def = struct {
    core: NodeId,
    body: NodeId = 0,
    size: NodeId = 0,
    tagof: NodeId = 0,

    pub fn from_node(tree: *const ParseTree, n: NodeId) Def {
        var d = Def{ .core = n };
        while (true) : (d.core = tree.arg(d.core, 0)) switch (tree.kind(d.core)) {
            .def_type_implof, .def_variant_implof => d.body = tree.arg(d.core, 1),
            .def_type_assertsize, .def_variant_assertsize => d.size = tree.arg(d.core, 1),
            .def_variant_tagof => d.tagof = tree.arg(d.core, 1),
            else => return d,
        };
    }
};

pub const Loop = struct {
    cond: NodeId = 0,
    repeat: NodeId = 0,
    head: NodeId = 0,
    seq: NodeId = 0,
    variable: NodeId = 0,
    body: NodeId,

    pub fn from_node(tree: *const ParseTree, n: NodeId) Loop {
        const a0 = tree.arg(n, 0);
        const a1 = tree.arg(n, 1);
        return switch (tree.kind(n)) {
            .@"while", .stcwhile => .{ .cond = a0, .body = a1 },
            .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => .{ .cond = tree.arg(a0, 0), .repeat = a1, .head = a0, .body = tree.arg(a0, 1) },
            .loop, .stcloop => .{ .body = a0 },
            .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => .{ .repeat = a0, .body = a1 },
            .for_var_in_seq, .stcfor_var_in_seq => .{ .head = a0, .seq = tree.arg(a0, 0), .variable = a1, .body = tree.arg(a0, 1) },
            else => .{ .head = n, .seq = a0, .body = a1 },
        };
    }
};

pub const Range = struct {
    lo: NodeId,
    hi: NodeId,
    incl: bool,

    pub fn from_node(tree: *const ParseTree, n: NodeId) Range {
        const k = tree.kind(n);
        const two = k == .gen_incl or k == .gen_excl;
        return .{
            .lo = if (two or k == .gen_lowerbound) tree.arg(n, 0) else 0,
            .hi = if (two) tree.arg(n, 1) else if (k == .gen_lowerbound) 0 else tree.arg(n, 0),
            .incl = k == .gen_incl or k == .gen_upperbound_incl,
        };
    }
};

pub fn literal_core(tree: *const ParseTree, node: NodeId, neg: *bool) NodeId {
    var n = node;
    while (true) switch (tree.kind(n)) {
        .capture => n = tree.arg(n, 0),
        .neg_num => {
            neg.* = !neg.*;
            n = tree.arg(n, 0);
        },
        else => return n,
    };
}

pub fn is_literal(tree: *const ParseTree, node: NodeId) bool {
    var neg = false;
    return props(tree.kind(literal_core(tree, node, &neg))).literal;
}

pub fn type_kind(tree: *const ParseTree, n: NodeId) DeclPool.Entry.Kind {
    return switch (tree.kind(Def.from_node(tree, n).core)) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

pub fn decl_kind(tree: *const ParseTree, type_node: NodeId, value: NodeId) DeclPool.Entry.Kind {
    const tk = type_kind(tree, value);
    return switch (tree.kind(type_node)) {
        .type_fun => .function,
        .type_stcfun => .static_function,
        .type_inlfun => .inlined_function,
        .type_type, .type_variant, .type_trait => if (value != 0 and tree.kind(value) == .def_fun) .static_function else switch (tree.kind(type_node)) {
            .type_type => if (tk == .record) .record else .type_alias,
            .type_variant => if (tk == .variant) .variant else .type_alias,
            else => if (tk == .trait) .trait else .type_alias,
        },
        .none => if (value != 0 and (tree.kind(value) == .def_fun or tree.kind(value) == .def_fun_declaration)) .function else .variable,
        else => .variable,
    };
}

// what a stcfun declared as `type` / `variant` / `trait` produces
pub fn template_kind(tree: *const ParseTree, decl_node: NodeId) DeclPool.Entry.Kind {
    if (tree.kind(decl_node) != .assign_typed or tree.kind(tree.arg(decl_node, 1)) != .def_fun) return .variable;
    return switch (tree.kind(tree.arg(tree.arg(decl_node, 0), 0))) {
        .type_type => .record,
        .type_variant => .variant,
        .type_trait => .trait,
        else => .variable,
    };
}

pub fn params_of(tree: *const ParseTree, v: NodeId) []const NodeId {
    if (tree.kind(v) != .def_fun and tree.kind(v) != .def_fun_declaration) return &.{};
    return tree.manychildren(tree.arg(tree.arg(v, 0), 0));
}

pub fn fields_of(tree: *const ParseTree, c: NodeId) []const NodeId {
    return if (tree.kind(c) == .partial__type_def_param_tuple) tree.manychildren(c) else tree.manychildren(tree.arg(c, 0));
}

pub fn arg_value(tree: *const ParseTree, a: NodeId) NodeId {
    return if (tree.kind(a) == .partial__fun_call_assigned_param) tree.arg(a, 1) else a;
}

pub fn narrowed(tree: *const ParseTree, target: NodeId) NodeId {
    const inner = if (tree.kind(target) == .type_ptr or tree.kind(target) == .type_ptrmut) tree.arg(target, 0) else target;
    return if (tree.kind(inner) == .type_array) Range.from_node(tree, tree.arg(inner, 0)).lo else 0;
}
