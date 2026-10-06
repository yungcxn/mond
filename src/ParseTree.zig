const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

const ParseTree = @This();

pub const NodeId = u32;
pub const none_node: NodeId = std.math.maxInt(NodeId);

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    const DefTable = .{
        .{ "CodeBlock", "block", []const NodeId },
        .{ "FunctionDefinition", "def_fun", struct { fun_header: NodeId, unit: NodeId } },
        .{ "FunctionDeclaration", "def_fun_declaration", struct { fun_header: NodeId } },
        .{ "PartialExpression_FunctionDefinitionHeader", "partial__fun_def_header", struct { param_tuple: NodeId } },
        .{ "PartialExpression_FunctionDefinitionHeaderReturning", "partial__fun_def_header_ret", struct { param_tuple: NodeId, return_type: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterTuple", "partial__fun_def_param_tuple", []const NodeId },
        .{ "PartialExpression_FunctionDefinitionParameter", "partial__fun_def_param", struct { type: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterNamed", "partial__fun_def_param_named", struct { param: NodeId, identifier: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterDefaulted", "partial__fun_def_param_default", struct { param: NodeId, default_value: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterWhere", "partial__fun_def_param_where", struct { param: NodeId, where_predicate: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterStaticWhere", "partial__fun_def_param_stcwhere", struct { param: NodeId, where_predicate: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterWhereElse", "partial__fun_def_param_where_else", struct { param: NodeId, where_else_value: NodeId } },
        .{ "Capture", "capture", struct { subnode: NodeId } },
        .{ "Array", "array", []const NodeId },
        .{ "ArrayEmpty", "array_empty", .leaf },
        .{ "TypeOf", "typeof", struct { subnode: NodeId } },
        .{ "SizeOf", "sizeof", struct { subnode: NodeId } },
        .{ "TypeArray", "type_array", struct { length: NodeId, type: NodeId } },
        .{ "TypeArrayUnlengthed", "type_array_unlengthed", struct { type: NodeId } },
        .{ "NegateNumerical", "neg_num", struct { subnode: NodeId } },
        .{ "NegateLogical", "neg_logic", struct { subnode: NodeId } },
        .{ "IncrementPrefix", "inc_prefix", struct { subnode: NodeId } },
        .{ "DecrementPrefix", "dec_prefix", struct { subnode: NodeId } },
        .{ "GenUpperboundIncl", "gen_upperbound_incl", struct { subnode: NodeId } },
        .{ "GenUpperboundExcl", "gen_upperbound_excl", struct { subnode: NodeId } },
        .{ "None", "none", .leaf },
        .{ "Do", "do", struct { subnode: NodeId } },
        .{ "Deinit", "deinit", struct { subnode: NodeId } },
        .{ "Continue", "cont", .leaf },
        .{ "Break", "brk", .leaf },
        .{ "Return", "ret", struct { subnode: NodeId } },
        .{ "ReturnVoid", "ret_void", .leaf },
        .{ "IfThen", "if_then", struct { cond: NodeId, then: NodeId } },
        .{ "IfElse", "if_else", struct { if_then: NodeId, @"else": NodeId } },
        .{ "StaticIfThen", "stcif_then", struct { cond: NodeId, then: NodeId } },
        .{ "StaticIfElse", "stcif_else", struct { if_then: NodeId, @"else": NodeId } },
        .{ "While", "while", struct { cond: NodeId, body: NodeId } },
        .{ "WhileWithRepeatStmt", "while_with_repeat_stmt", struct { @"while": NodeId, repeated: NodeId } },
        .{ "StaticWhile", "stcwhile", struct { cond: NodeId, body: NodeId } },
        .{ "StaticWhileWithRepeatStmt", "stcwhile_with_repeat_stmt", struct { @"while": NodeId, repeated: NodeId } },
        .{ "ForSeq", "for_seq", struct { seq: NodeId, body: NodeId } },
        .{ "ForVarInSeq", "for_var_in_seq", struct { for_seq: NodeId, variable: NodeId } },
        .{ "StaticForSeq", "stcfor_seq", struct { seq: NodeId, body: NodeId } },
        .{ "StaticForVarInSeq", "stcfor_var_in_seq", struct { for_seq: NodeId, variable: NodeId } },
        .{ "Loop", "loop", struct { body: NodeId } },
        .{ "LoopWithRepeatStmt", "loop_with_repeat_stmt", struct { repeated: NodeId, body: NodeId } },
        .{ "StaticLoop", "stcloop", struct { body: NodeId } },
        .{ "StaticLoopWithRepeatStmt", "stcloop_with_repeat_stmt", struct { repeated: NodeId, body: NodeId } },
        .{ "Match", "match", struct { matched: NodeId, match_body: NodeId } },
        .{ "StaticMatch", "stcmatch", struct { matched: NodeId, match_body: NodeId } },
        .{ "PartialExpression_MatchBody", "partial__match_body", []const NodeId },
        .{ "PartialExpression_MatchCase", "partial__match_case", struct { pattern: NodeId, body: NodeId } },
        .{ "PartialExpression_MatchCasePatternOr", "partial__match_case_pattern_or", []const NodeId },
        .{ "PartialExpression_MatchCasePatternTypeCast", "partial__match_case_pattern_typecast", struct { type: NodeId, casted_var: NodeId } },
        .{ "TypePointerMutable", "type_ptrmut", struct { subnode: NodeId } },
        .{ "TypePointer", "type_ptr", struct { subnode: NodeId } },
        .{ "TypeUnsignedInteger8", "type_u8", .leaf },
        .{ "TypeUnsignedInteger16", "type_u16", .leaf },
        .{ "TypeUnsignedInteger32", "type_u32", .leaf },
        .{ "TypeUnsignedInteger64", "type_u64", .leaf },
        .{ "TypeSignedInteger8", "type_i8", .leaf },
        .{ "TypeSignedInteger16", "type_i16", .leaf },
        .{ "TypeSignedInteger32", "type_i32", .leaf },
        .{ "TypeSignedInteger64", "type_i64", .leaf },
        .{ "TypeFloat16", "type_f16", .leaf },
        .{ "TypeFloat32", "type_f32", .leaf },
        .{ "TypeFloat64", "type_f64", .leaf },
        .{ "TypeBool", "type_bool", .leaf },
        .{ "TypeType", "type_type", .leaf },
        .{ "TypeTrait", "type_trait", .leaf },
        .{ "TypeVariant", "type_variant", .leaf },
        .{ "TypeUnit", "type_unit", .leaf },
        .{ "TypeInlinedFunction", "type_inlfun", .leaf },
        .{ "TypeFunction", "type_fun", .leaf },
        .{ "TypeStaticFunction", "type_stcfun", .leaf },
        .{ "TypeDefinition", "def_type", struct { param_tuple: NodeId } },
        .{ "TypeDefinitionPacked", "def_type_packed", struct { param_tuple: NodeId } },
        .{ "TypeDefinitionWithAssertedSize", "def_type_assertsize", struct { def_type: NodeId, assertsize: NodeId } },
        .{ "TypeDefinitionWithTrait", "def_type_implof", struct { def_type: NodeId, def_trait: NodeId } },
        .{ "TypeVariant", "def_variant", struct { param_tuple: NodeId } },
        .{ "TypeVariantUnionsized", "def_variant_unionsized", struct { param_tuple: NodeId } },
        .{ "TypeVariantWithTag", "def_variant_tagof", struct { def_variant: NodeId, tagof: NodeId } },
        .{ "TypeVariantWithAssertedSize", "def_variant_assertsize", struct { def_variant: NodeId, assertsize: NodeId } },
        .{ "TypeVariantWithTrait", "def_variant_implof", struct { def_variant: NodeId, def_trait: NodeId } },
        .{ "TypeTrait", "def_trait", struct { body: NodeId } },
        .{ "TypeTraitWithImplementations", "def_trait_implof", struct { implof_tuple: NodeId, body: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterTuple", "partial__type_def_param_tuple", []const NodeId },
        .{ "PartialExpression_TypeDefinitionParameter", "partial__type_def_param", struct { type: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterMutable", "partial__type_def_param_mut", struct { param: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterNamed", "partial__type_def_param_named", struct { param: NodeId, identifier: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterDefaulted", "partial__type_def_param_default", struct { param: NodeId, default_value: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterWhere", "partial__type_def_param_where", struct { param: NodeId, where_predicate: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterWhereElse", "partial__type_def_param_where_else", struct { param: NodeId, where_else_value: NodeId } },
        .{ "PartialExpression_VariantDefinitionParameterTuple", "partial__variant_def_param_tuple", []const NodeId },
        .{ "PartialExpression_VariantDefinitionParameter", "partial__variant_def_param", struct { name: NodeId } },
        .{ "PartialExpression_VariantDefinitionParameterTyped", "partial__variant_def_param_typed", struct { param: NodeId, def_type: NodeId } },
        .{ "PartialExpression_VariantDefinitionParameterTagged", "partial__variant_def_param_tagged", struct { param: NodeId, tag_value: NodeId } },
        .{ "PartialExpression_TraitDefinitionImplementationTuple", "partial__trait_def_implof_tuple", []const NodeId },
        .{ "PartialExpression_TraitDefinitionBody", "partial__trait_def_body", []const NodeId },
        .{ "UnifyVariants", "unify_variants", struct { left_type: NodeId, right_type: NodeId } },
        .{ "With", "with", struct { value: NodeId, fun_call_param_tuple: NodeId } },
        .{ "FunctionCall", "fun_call", struct { callable: NodeId, fun_param_tuple: NodeId } },
        .{ "PartialExpression_FunctionCallParameterTuple", "partial__fun_call_param_tuple", []const NodeId },
        .{ "PartialExpression_FunctionCallAssignedParameter", "partial__fun_call_assigned_param", struct { identifier: NodeId, value: NodeId } },
        .{ "ArrayIndexing", "array_index", struct { indexable: NodeId, index: NodeId } },
        .{ "MemberAccess", "member", struct { parent: NodeId, member: NodeId } },
        .{ "Dereference", "dereference", struct { subnode: NodeId } },
        .{ "AddressOf", "address_of", struct { subnode: NodeId } },
        .{ "IncrementPostfix", "inc_postfix", struct { subnode: NodeId } },
        .{ "DecrementPostfix", "dec_postfix", struct { subnode: NodeId } },
        .{ "GenerateLowerBound", "gen_lowerbound", struct { subnode: NodeId } },
        .{ "GenerateInclusive", "gen_incl", struct { lower: NodeId, upper: NodeId } },
        .{ "GenerateExclusive", "gen_excl", struct { lower: NodeId, upper: NodeId } },
        .{ "OfType", "oftype", struct { value: NodeId, type: NodeId } },
        .{ "As", "as", struct { value: NodeId, type: NodeId } },
        .{ "AsBits", "asbits", struct { value: NodeId, type: NodeId } },
        .{ "LabelArrow", "labelarrow", struct { value: NodeId, label: NodeId } },
        .{ "SelfTagArrow", "selftag_arrow", struct { value: NodeId, label: NodeId } },
        .{ "PartialExpression_Destructure", "partial__destructure", []const NodeId },
        .{ "SelfTagUnwrap", "selftag_unwrap", struct { value: NodeId } },
        .{ "SelfTagUnwrapWithFallback", "selftag_unwrap_fallback", struct { value: NodeId, fallback: NodeId } },
        .{ "Defer", "defer", struct { defered: NodeId } },
        .{ "InlinedDeferDeinit", "inlined_defer_deinit", struct { subnode: NodeId } },
        .{ "BinaryLogicalOr", "binary_logic_or", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryLogicalXor", "binary_logic_xor", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryLogicalAnd", "binary_logic_and", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryNumericalOr", "binary_num_or", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryNumericalXor", "binary_num_xor", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryNumericalAnd", "binary_num_and", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryEquals", "binary_eq", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryNotEquals", "binary_neq", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryLess", "binary_less", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryGreater", "binary_greater", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryLessOrEqual", "binary_less_eq", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryGreaterOrEqual", "binary_greater_eq", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryAdd", "binary_add", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinarySubtract", "binary_sub", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryMultiply", "binary_mul", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryDivide", "binary_div", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryModulus", "binary_mod", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryShiftLeft", "binary_shift_left", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryShiftRight", "binary_shift_right", struct { lhs: NodeId, rhs: NodeId } },
        .{ "IdentifierSelf", "identifier_self", .leaf },
        .{ "Identifier", "identifier", .references_token },
        .{ "StringValue", "string", .references_token },
        .{ "IntegerValue", "int", .references_token },
        .{ "FloatingPointValue", "float", .references_token },
        .{ "CharacterValue", "char", .references_token },
        .{ "BooleanTrue", "boolean_true", .leaf },
        .{ "BooleanFalse", "boolean_false", .leaf },
        .{ "VariableDefinition", "def_var", struct { type: NodeId, identifier: NodeId } },
        .{ "Assignment", "assign", struct { assignee: NodeId, assigned: NodeId } },
        .{ "AssignmentTyped", "assign_typed", struct { def_var: NodeId, assigned: NodeId } },
        .{ "ModifierPublic", "mod_pub", struct { subnode: NodeId } },
        .{ "ModifierMutable", "mod_mut", struct { subnode: NodeId } },
        .{ "ModifierStatic", "mod_stc", struct { subnode: NodeId } },
        .{ "AssignmentAdd", "assign_add", struct { lhs: NodeId, rhs: NodeId } },
        .{ "AssignmentSubtract", "assign_sub", struct { lhs: NodeId, rhs: NodeId } },
        .{ "AssignmentMultiply", "assign_mul", struct { lhs: NodeId, rhs: NodeId } },
        .{ "AssignmentDivide", "assign_div", struct { lhs: NodeId, rhs: NodeId } },
        .{ "AssignmentModulus", "assign_mod", struct { lhs: NodeId, rhs: NodeId } },
        .{ "PartialExpression_MultipleAssignedValues", "partial__assign_multival", []const NodeId },
    };

    pub const Kind = blk: {
        var field_names: [DefTable.len][]const u8 = undefined;
        var field_values: [DefTable.len]u8 = undefined;

        for (DefTable, 0..) |def, i| {
            field_names[i] = def[1];
            field_values[i] = i;
        }

        break :blk @Enum(u8, .exhaustive, &field_names, &field_values);
    };

    pub fn LayoutStruct(comptime nk: Kind) type {
        const t = DefTable[@intFromEnum(nk)][2];
        if (@TypeOf(t) == @EnumLiteral() and t == .leaf) @compileError("leaf nodes have no layout struct");
        if (@TypeOf(t) == @EnumLiteral() and t == .references_token) @compileError("data nodes have no layout struct");
        return t;
    }

    pub const nk_childc = blk: {
        var t: [256]enum(u8) { none, one, two, many, data } = undefined;
        for (DefTable, 0..) |def, i| {
            const layout = def[2];
            if (@TypeOf(layout) == type and @typeInfo(layout) == .@"struct") {
                const n = @typeInfo(layout).@"struct".fields.len;
                t[i] = switch (n) {
                    0 => .none,
                    1 => .one,
                    2 => .two,
                    else => .many,
                };
            } else if (@TypeOf(layout) == type and layout == []const NodeId) {
                t[i] = .many;
            } else if (@TypeOf(layout) == @EnumLiteral() and layout == .leaf) {
                t[i] = .none;
            } else if (@TypeOf(layout) == @EnumLiteral() and layout == .references_token) {
                t[i] = .data;
            } else {
                @compileError("unexpected layout type for " ++ def[1]);
            }
        }
        break :blk t;
    };

    // field names of struct layouts, used to label children in the debug print
    pub const nk_field_names = blk: {
        var t: [DefTable.len][2][]const u8 = @splat(.{ "", "" });
        for (DefTable, 0..) |def, i| {
            const layout = def[2];
            if (@TypeOf(layout) == type and @typeInfo(layout) == .@"struct") {
                for (@typeInfo(layout).@"struct".fields, 0..) |field, j| t[i][j] = field.name;
            }
        }
        break :blk t;
    };

    pub const nk_props = blk: {
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

        t[@intFromEnum(Kind.identifier)].name = true;
        t[@intFromEnum(Kind.identifier_self)].name = true;

        for ([_]Kind{
            .identifier,
            .identifier_self,
            .member,
            .array_index,
            .dereference,
            .capture,
        }) |k| t[@intFromEnum(k)].assignable = true;

        t[@intFromEnum(Kind.def_fun)].function = true;
        t[@intFromEnum(Kind.def_fun_declaration)].function = true;
        t[@intFromEnum(Kind.type_ptr)].pointer = true;
        t[@intFromEnum(Kind.type_ptrmut)].pointer = true;

        break :blk t;
    };
};

// how the language reads the nodes the parser builds: classes of kinds and the layouts of compound nodes
pub const Props = packed struct(u16) {
    stc: bool = false,
    loop: bool = false,
    range: bool = false,
    type_expr: bool = false,
    declares: bool = false,
    runit: bool = false,
    literal: bool = false,
    name: bool = false,
    // can be written to: names, fields, elements, dereferences
    assignable: bool = false,
    function: bool = false,
    pointer: bool = false,
    _pad: u5 = 0,
};

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

pub const Branch = struct {
    cond: NodeId,
    then: NodeId,
    @"else": NodeId = 0,

    pub fn from_node(tree: *const ParseTree, n: NodeId) Branch {
        const has_else = tree.kind(n) == .if_else or tree.kind(n) == .stcif_else;
        const it = if (has_else) tree.arg(n, 0) else n;
        return .{ .cond = tree.arg(it, 0), .then = tree.arg(it, 1), .@"else" = if (has_else) tree.arg(n, 1) else 0 };
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

ast_nodes: SoD(Node),
extra_childrefs: DynBuf(NodeId), // children of node i must be contiguous here
span_store: []const Lexer.TextSpan,

pub fn init(alloc: std.mem.Allocator, span_store: []const Lexer.TextSpan) @This() {
    return @This(){
        .ast_nodes = .init(alloc, 10000),
        .extra_childrefs = .init(alloc, 10000),
        .span_store = span_store,
    };
}

pub fn deinit(self: *@This()) void {
    self.ast_nodes.deinit();
    self.extra_childrefs.deinit();
}

// a node holds at most 2 direct children, a `[]const NodeId` is copied into `extra_childrefs` (which is contiguous)
pub inline fn set_children(
    self: *@This(),
    parent_idx: NodeId,
    childrefs: anytype,
) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, parent_idx) orelse unreachable;
    const ti = @typeInfo(@TypeOf(childrefs));

    if (@TypeOf(childrefs) == NodeId or @TypeOf(childrefs) == comptime_int) {
        args_ptr.*[0] = childrefs;
    } else if (ti == .@"struct") {
        comptime if (ti.@"struct".fields.len > 2) @compileError(
            "node layout holds more than 2 children, split it into wrapper kinds: " ++ @typeName(@TypeOf(childrefs)),
        );

        inline for (ti.@"struct".fields, 0..) |field, i| {
            args_ptr.*[i] = @field(childrefs, field.name);
        }
    } else {
        args_ptr.*[0] = self.extra_childrefs.head;
        args_ptr.*[1] = @intCast(childrefs.len);
        self.extra_childrefs.append(childrefs);
    }
}

// -> `NodeId`: idx where node was pushed into
pub inline fn push_node(self: *@This(), nodekind: Node.Kind) NodeId {
    self.ast_nodes.push(.{ .nk = nodekind, .args = .{ 0, 0 } });
    return self.ast_nodes.len() - 1;
}

// -> `NodeId`: idx where node was pushed into, children are set from the node kind's layout
pub inline fn push_node_with(
    self: *@This(),
    comptime nodekind: Node.Kind,
    childrefs: Node.LayoutStruct(nodekind),
) NodeId {
    const new_node_idx = self.push_node(nodekind);
    self.set_children(new_node_idx, childrefs);

    return new_node_idx;
}

pub inline fn push_data_node(self: *@This(), nodekind: Node.Kind, span_idx: u32) NodeId {
    const new_node_idx = self.push_node(nodekind);
    self.set_children(new_node_idx, span_idx);

    return new_node_idx;
}

// utility for navigating the tree structure, we assume n to be valid //

pub inline fn kind(self: *const @This(), n: NodeId) Node.Kind {
    return self.ast_nodes.pool.nk.buf[n];
}

pub inline fn arg(self: *const @This(), n: NodeId, i: u1) NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.ast_nodes.pool.args.buf[n]);
    return slots[i];
}

pub inline fn arg_ptr(self: *const @This(), n: NodeId, i: u1) *const NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.ast_nodes.pool.args.buf[n]);
    return &slots[i];
}

// we assert for this, that `n` is an id for a node that has "many" children
pub inline fn manychildren(self: *const @This(), n: NodeId) []const NodeId {
    const a = self.ast_nodes.pool.args.buf[n];
    return self.extra_childrefs.buf[a[0]..][0..a[1]];
}

pub inline fn laidout_children(self: *const @This(), comptime nk: Node.Kind, n: NodeId) Node.LayoutStruct(nk) {
    const nk_childc = comptime Node.nk_childc[@intFromEnum(nk)];

    switch (comptime nk_childc) {
        .data => unreachable,
        .none => unreachable,
        .one => return {
            const Type = Node.LayoutStruct(nk);
            var build: Type = undefined;
            @field(build, @typeInfo(Type).@"struct".fields[0].name) = self.arg(n, 0);
            return build;
        },
        .two => return {
            const Type = Node.LayoutStruct(nk);
            var build: Type = undefined;
            @field(build, @typeInfo(Type).@"struct".fields[0].name) = self.arg(n, 0);
            @field(build, @typeInfo(Type).@"struct".fields[1].name) = self.arg(n, 1);
            return build;
        },
        .many => return self.manychildren(n),
    }
}

pub inline fn span(self: *const @This(), n: NodeId) Lexer.TextSpan {
    return self.span_store[self.arg(n, 0)];
}

pub fn subtree(self: *const @This(), n: NodeId) [2]NodeId {
    var s: [2]NodeId = .{ n, n + 1 };

    const slots: *const [2]NodeId = @ptrCast(&self.ast_nodes.pool.args.buf[n]);
    const children = switch (Node.nk_childc[@intFromEnum(self.kind(n))]) {
        .one => slots[0..1],
        .two => slots,
        .many => self.manychildren(n),
        else => &.{},
    };

    for (children) |c| {
        const x = self.subtree(c);
        s = .{ @min(s[0], x[0]), @max(s[1], x[1]) };
    }
    return s;
}

// questions about nodes, nothing here looks further than the tree

// the classes of the node's kind
pub inline fn props(self: *const @This(), n: NodeId) Props {
    return Node.nk_props[@intFromEnum(self.kind(n))];
}

pub fn literal_core(self: *const @This(), node: NodeId, neg: *bool) NodeId {
    var n = node;
    while (true) switch (self.kind(n)) {
        .capture => n = self.arg(n, 0),
        .neg_num => {
            neg.* = !neg.*;
            n = self.arg(n, 0);
        },
        else => return n,
    };
}

pub fn is_literal(self: *const @This(), node: NodeId) bool {
    var neg = false;
    return self.props(self.literal_core(node, &neg)).literal;
}

pub fn params_of(self: *const @This(), v: NodeId) []const NodeId {
    if (!self.props(v).function) return &.{};
    return self.manychildren(self.arg(self.arg(v, 0), 0));
}

pub fn fields_of(self: *const @This(), c: NodeId) []const NodeId {
    return if (self.kind(c) == .partial__type_def_param_tuple) self.manychildren(c) else self.manychildren(self.arg(c, 0));
}

// the name node of a named argument (`f(x = 1)`), 0 for a positional one
pub fn arg_name(self: *const @This(), a: NodeId) NodeId {
    return if (self.kind(a) == .partial__fun_call_assigned_param) self.arg(a, 0) else 0;
}

pub fn arg_value(self: *const @This(), a: NodeId) NodeId {
    return if (self.kind(a) == .partial__fun_call_assigned_param) self.arg(a, 1) else a;
}

pub fn narrowed(self: *const @This(), target: NodeId) NodeId {
    const inner = if (self.props(target).pointer) self.arg(target, 0) else target;
    return if (self.kind(inner) == .type_array) Range.from_node(self, self.arg(inner, 0)).lo else 0;
}
