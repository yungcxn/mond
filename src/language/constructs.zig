const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const Kind = ParseTree.Node.Kind;

// what the language does with a node: every node kind belongs to exactly one construct
// phases switch over it without `else`, so new kinds and constructs fail to compile until handled
pub const Construct = enum {
    literal,
    numeric_negation,
    // `!`: logical on booleans, bitwise on integers
    logical_not,
    name,
    // parentheses, a tree keeps its grouping in its shape
    grouping,
    block,
    declaration,
    compound_assignment,
    increment,
    // operators of `operators.binary_table`: arithmetic, bitwise and shifts
    arithmetic,
    comparison,
    short_circuit_logic,
    logical_xor,
    call,
    // `x with (field = ..)`: a copy of a record with some fields replaced
    record_update,
    // `a ~ b`: the elements of two arrays or slices, one after the other
    join,
    member_access,
    index,
    dereference,
    address_of,
    array_literal,
    cast,
    bit_cast,
    type_test,
    type_of,
    // `isstc x`: whether `x` is a static value here (a `stc?` parameter given one)
    static_test,
    size_of,
    length_or_tag,
    branch,
    loop,
    range,
    match,
    return_value,
    return_void,
    loop_jump,
    do,
    @"defer",
    deinit,
    deferred_deinit,
    // `??`, `?<-` and `<-`: the payload of a self-tagged variant, or a label bound to it
    unwrap,
    macro,
    lambda,
    type_expression,
    type_definition,
    // a piece of a bigger node (parameters, match arms, ..), only ever looked at through its parent
    part,
};

const construct_table = .{
    .{ .literal, .{ .int, .float, .char, .string, .boolean_true, .boolean_false } },
    .{ .numeric_negation, .{.neg_num} },
    .{ .logical_not, .{.neg_logic} },
    .{ .name, .{ .identifier, .identifier_self } },
    .{ .grouping, .{.capture} },
    .{ .block, .{.block} },
    .{ .declaration, .{ .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc } },
    .{ .compound_assignment, .{ .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod } },
    .{ .increment, .{ .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix } },
    .{ .arithmetic, .{
        .binary_add,        .binary_sub,         .binary_mul,    .binary_div,     .binary_mod,
        .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and,
    } },
    .{ .comparison, .{
        .binary_eq,
        .binary_neq,
        .binary_less,
        .binary_greater,
        .binary_less_eq,
        .binary_greater_eq,
    } },
    .{ .short_circuit_logic, .{ .binary_logic_and, .binary_logic_or } },
    .{ .logical_xor, .{.binary_logic_xor} },
    .{ .call, .{ .fun_call, .builtin_call } },
    .{ .record_update, .{.with} },
    .{ .join, .{.binary_join} },
    .{ .member_access, .{.member} },
    .{ .index, .{.array_index} },
    .{ .dereference, .{.dereference} },
    .{ .address_of, .{.address_of} },
    .{ .array_literal, .{ .array, .array_empty } },
    .{ .cast, .{.as} },
    .{ .bit_cast, .{.asbits} },
    .{ .type_test, .{.oftype} },
    .{ .type_of, .{.typeof} },
    .{ .static_test, .{.isstc} },
    .{ .size_of, .{ .sizeof, .alignof } },
    .{ .length_or_tag, .{ .lenof, .tagof } },
    .{ .branch, .{ .if_then, .if_else, .stcif_then, .stcif_else } },
    .{ .loop, .{
        .@"while",                  .while_with_repeat_stmt, .stcwhile,
        .stcwhile_with_repeat_stmt, .for_seq,                .for_var_in_seq,
        .stcfor_seq,                .stcfor_var_in_seq,      .loop,
        .loop_with_repeat_stmt,     .stcloop,                .stcloop_with_repeat_stmt,
    } },
    .{ .range, .{
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
    } },
    .{ .match, .{ .match, .stcmatch } },
    .{ .return_value, .{.ret} },
    .{ .return_void, .{.ret_void} },
    .{ .loop_jump, .{ .brk, .cont } },
    .{ .do, .{.do} },
    .{ .@"defer", .{.@"defer"} },
    .{ .deinit, .{.deinit} },
    .{ .deferred_deinit, .{.inlined_defer_deinit} },
    .{ .unwrap, .{ .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow } },
    .{ .macro, .{ .quote, .splice, .refl, .include, .include_raw, .unquote, .unquote_list, .paste } },
    .{ .lambda, .{.def_fun} },
    .{ .type_expression, .{
        .type_array,          .type_array_unlengthed, .type_ptr,       .type_ptrmut,
        .type_u8,             .type_u16,              .type_u32,       .type_u64,
        .type_i8,             .type_i16,              .type_i32,       .type_i64,
        .type_f16,            .type_f32,              .type_f64,       .type_bool,
        .type_ast,            .type_type,             .type_trait,     .type_variant,
        .type_unit,           .type_inlfun,           .type_fun,       .type_stcfun,
        .def_fun_declaration, .unify_variants_packed, .unify_variants, .type_slice,
        .variant_difference,
    } },
    .{ .type_definition, .{
        .def_type,           .def_type_packed,    .def_type_assertsize, .def_type_implof,
        .def_variant,        .def_variant_packed, .def_variant_tagtype, .def_variant_assertsize,
        .def_variant_implof, .def_trait,          .def_trait_implof,    .def_variant_notagtype,
    } },
    .{ .part, .{
        .none,                               .partial__fun_def_header,
        .partial__fun_def_header_ret,        .partial__fun_def_param_tuple,
        .partial__fun_def_param,             .partial__fun_def_param_named,
        .partial__fun_def_param_default,     .partial__fun_def_param_where,
        .partial__fun_def_param_stcwhere,    .partial__fun_def_param_where_else,
        .partial__match_body,                .partial__match_case,
        .partial__match_case_pattern_or,     .partial__match_case_pattern_typecast,
        .partial__type_def_param_tuple,      .partial__type_def_param,
        .partial__type_def_param_mut,        .partial__type_def_param_named,
        .partial__type_def_param_default,    .partial__type_def_param_where,
        .partial__type_def_param_where_else, .partial__variant_def_param_tuple,
        .partial__variant_def_param,         .partial__variant_def_param_typed,
        .partial__variant_def_param_tagged,  .partial__trait_def_implof_tuple,
        .partial__trait_def_body,            .partial__fun_call_param_tuple,
        .partial__fun_call_assigned_param,   .partial__destructure,
        .partial__assign_multival,           .partial__match_case_where,
        .partial__match_case_pattern_bits,   .partial__bits_field,
        .partial__bits_rest,                 .stc_maybe,
        .hole,
    } },
};

const kind_count = @typeInfo(Kind).@"enum".field_names.len;

const construct_of_kind: [kind_count]Construct = blk: {
    @setEvalBranchQuota(100_000);
    var table: [kind_count]?Construct = @splat(null);
    for (construct_table) |row| for (row[1]) |kind| {
        const i = @backingInt(@as(Kind, kind));
        if (table[i] != null) @compileError("node kind listed twice: " ++ @tagName(kind));
        table[i] = row[0];
    };
    var complete: [kind_count]Construct = undefined;
    for (table, 0..) |construct, i| {
        const kind: Kind = @fromBackingInt(i);
        complete[i] = construct orelse
            @compileError("node kind without a construct: " ++ @tagName(kind));
    }
    break :blk complete;
};

pub inline fn construct_of(kind: Kind) Construct {
    return construct_of_kind[@backingInt(kind)];
}
