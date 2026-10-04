const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

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
        .{ "BinaryPower", "binary_pow", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryWrappingAdd", "binary_add_wrap", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryWrappingSubtract", "binary_sub_wrap", struct { lhs: NodeId, rhs: NodeId } },
        .{ "BinaryWrappingMultiply", "binary_mul_wrap", struct { lhs: NodeId, rhs: NodeId } },
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
