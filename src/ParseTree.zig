const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");

pub const NodeId = u32;

pub const Node = struct {
    nk: Kind,
    args: @Vector(2, u32),

    const DefTable = .{
        .{ "CodeBlock", "block", []NodeId },
        .{ "FunctionDefinition", "def_fun", struct { fun_header: NodeId, unit: NodeId } },
        .{ "PartialExpression_FunctionDefinitionHeader", "partial__fun_def_header", struct { param_tuple: NodeId, return_type: NodeId } },
        .{ "PartialExpression_FunctionDefinitionParameterTuple", "partial__fun_def_param_tuple", []NodeId },
        .{ "PartialExpression_FunctionDefinitionParameter", "partial__fun_def_param", struct { type: NodeId, identifier: NodeId, default_value: NodeId, where_predicate: NodeId, where_else_value: NodeId } },
        .{ "Capture", "capture", struct { subnode: NodeId } },
        .{ "Array", "array", []NodeId },
        .{ "ArrayEmpty", "array_empty", .leaf },
        .{ "TypeOf", "typeof", struct { subnode: NodeId } },
        .{ "SizeOf", "sizeof", struct { subnode: NodeId } },
        .{ "TypeArray", "type_array", struct { length: NodeId, type: NodeId } },
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
        .{ "Return", "ret", struct { opt_subnode: NodeId } },
        .{ "IfThen", "if_then", struct { cond: NodeId, then: NodeId } },
        .{ "IfElse", "if_else", struct { if_then: NodeId, @"else": NodeId } },
        .{ "While", "while", struct { cond: NodeId, body: NodeId } },
        .{ "WhileWithRepeatStmt", "while_with_repeat_stmt", struct { @"while": NodeId, repeated: NodeId } },
        .{ "ForSeq", "for_seq", struct { seq: NodeId, body: NodeId } },
        .{ "ForVarInSeq", "for_var_in_seq", struct { for_seq: NodeId, variable: NodeId } },
        .{ "Loop", "loop", struct { opt_repeated: NodeId, body: NodeId } },
        .{ "Match", "match", struct { matched: NodeId, match_body: NodeId } },
        .{ "PartialExpression_MatchBody", "partial__match_body", []NodeId },
        .{ "PartialExpression_MatchCase", "partial__match_case", struct { pattern: NodeId, body: NodeId } },
        .{ "PartialExpression_MatchCasePatternOr", "partial__match_case_pattern_or", []NodeId },
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
        .{ "TypeInlinedFunction", "type_inlfun", .leaf },
        .{ "TypeFunction", "type_fun", .leaf },
        .{ "TypeStaticFunction", "type_stcfun", .leaf },
        .{ "TypeDefinition", "def_type", struct { param_tuple: NodeId, assertsize: NodeId, def_trait: NodeId } },
        .{ "TypeDefinitionPacked", "def_type_packed", struct { param_tuple: NodeId, assertsize: NodeId, def_trait: NodeId } },
        .{ "TypeVariant", "def_variant", struct { param_tuple: NodeId, tagof: NodeId, assertsize: NodeId, def_trait: NodeId } },
        .{ "TypeVariantUnionsized", "def_variant_unionsized", struct { param_tuple: NodeId, tagof: NodeId, assertsize: NodeId, def_trait: NodeId } },
        .{ "TypeTrait", "def_trait", struct { implof_tuple: NodeId, body: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterTuple", "partial__type_def_param_tuple", []NodeId },
        .{ "PartialExpression_TypeDefinitionParameter", "partial__type_def_param", struct { type: NodeId, identifier: NodeId, default_value: NodeId, where_predicate: NodeId, where_else_value: NodeId } },
        .{ "PartialExpression_TypeDefinitionParameterMutable", "partial__type_def_param_mut", struct { type: NodeId, identifier: NodeId, default_value: NodeId, where_predicate: NodeId, where_else_value: NodeId } },
        .{ "PartialExpression_VariantDefinitionParameterTuple", "partial__variant_def_param_tuple", []NodeId },
        .{ "PartialExpression_VariantDefinitionParameter", "partial__variant_def_param", struct { name: NodeId, opt_def_type: NodeId, opt_tag_value: NodeId } },
        .{ "PartialExpression_TraitDefinitionImplementationTuple", "partial__trait_def_implof_tuple", []NodeId },
        .{ "PartialExpression_TraitDefinitionBody", "partial__trait_def_body", []NodeId },
        .{ "UnifyVariants", "unify_variants", struct { left_type: NodeId, right_type: NodeId } },
        .{ "With", "with", struct { value: NodeId, fun_call_param_tuple: NodeId } },
        .{ "FunctionCall", "fun_call", struct { callable: NodeId, fun_param_tuple: NodeId } },
        .{ "PartialExpression_FunctionCallParameterTuple", "partial__fun_call_param_tuple", []NodeId },
        .{ "PartialExpression_FunctionCallAssignedParameter", "partial__fun_call_assigned_param", struct { identifier: NodeId, value: NodeId } },
        .{ "ArrayIndexing", "array_index", struct { indexable: NodeId, index: NodeId } },
        .{ "MemberAccess", "member", struct { parent: NodeId, member: NodeId } },
        .{ "Dereference", "dereference", struct { subnode: NodeId } },
        .{ "AddressOf", "address_of", struct { subnode: NodeId } },
        .{ "IncrementPostfix", "inc_postfix", struct { subnode: NodeId } },
        .{ "DecrementPostfix", "dec_postfix", struct { subnode: NodeId } },
        .{ "GenerateLowerBound", "gen_lowerbound", struct { subnode: NodeId } },
        .{ "GenerateUpperBound", "gen_upperbound", struct { subnode: NodeId } },
        .{ "GenerateInclusive", "gen_incl", struct { lower: NodeId, upper: NodeId } },
        .{ "GenerateExclusive", "gen_excl", struct { lower: NodeId, upper: NodeId } },
        .{ "OfType", "oftype", struct { value: NodeId, type: NodeId } },
        .{ "As", "as", struct { value: NodeId, type: NodeId } },
        .{ "LabelArrow", "labelarrow", struct { value: NodeId, label: NodeId } },
        .{ "SelfTagArrow", "selftag_arrow", struct { value: NodeId, label: NodeId } },
        .{ "PartialExpression_Destructure", "partial__destructure", []NodeId },
        .{ "SelfTagUnwrap", "selftag_unwrap", struct { value: NodeId, fallback: NodeId } },
        .{ "Defer", "defer", struct { left_opt_node: NodeId, defered: NodeId } },
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
        .{ "IdentifierSelf", "identifier_self", .leaf },
        .{ "IdentifierInit", "identifier_init", .leaf },
        .{ "IdentifierDeinit", "identifier_deinit", .leaf },
        .{ "IdentifierMain", "identifier_main", .leaf },
        .{ "Identifier", "identifier", .references_token },
        .{ "StringValue", "string", .references_token },
        .{ "IntegerValue", "int", .references_token },
        .{ "FloatingPointValue", "float", .references_token },
        .{ "CharacterValue", "char", .references_token },
        .{ "BooleanTrue", "boolean_true", .leaf },
        .{ "BooleanFalse", "boolean_false", .leaf },
        .{ "AssignmentPublicMutable", "assign_pub_mut", struct { opt_type: NodeId, assignee: NodeId, assigned: NodeId } },
        .{ "AssignmentPublic", "assign_pub", struct { opt_type: NodeId, assignee: NodeId, assigned: NodeId } },
        .{ "AssignmentMutable", "assign_mut", struct { opt_type: NodeId, assignee: NodeId, assigned: NodeId } },
        .{ "Assignment", "assign", struct { opt_type: NodeId, assignee: NodeId, assigned: NodeId } },
        .{ "PartialExpression_MultipleAssignedValues", "partial__assign_multival", []NodeId },
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
        return DefTable[@intFromEnum(nk)][2];
    }

    const nk_childc = blk: {
        var t: [256]enum(u8) { none, one, two, many } = undefined;
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
            } else if (@TypeOf(layout) == type and layout == []NodeId) {
                t[i] = .many;
            } else if (@TypeOf(layout) == @EnumLiteral() and layout == .leaf) {
                t[i] = .none;
            } else if (@TypeOf(layout) == @EnumLiteral() and layout == .references_token) {
                t[i] = .one;
            } else {
                @compileError("unexpected layout type for " ++ def[1]);
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

// more than 2 children are passed as pointers to be copied into `extra_childrefs` (which is contiguous)
pub inline fn set_children(
    self: *@This(),
    parent_idx: NodeId,
    childrefs: anytype,
) void {
    const args_ptr = self.ast_nodes.field_ptr(.args, parent_idx) orelse unreachable;
    const ti = @typeInfo(@TypeOf(childrefs));

    if (@TypeOf(childrefs) == NodeId or @TypeOf(childrefs) == comptime_int or @TypeOf(childrefs) == u32) {
        args_ptr.*[0] = childrefs;
    } else if (ti == .@"struct" and ti.@"struct".fields.len == 1) {
        args_ptr.*[0] = @field(childrefs, ti.@"struct".fields[0].name);
    } else if (ti == .@"struct" and ti.@"struct".fields.len == 2) {
        args_ptr.*[0] = @field(childrefs, ti.@"struct".fields[0].name);
        args_ptr.*[1] = @field(childrefs, ti.@"struct".fields[1].name);
    } else {
        const ChildT = ti.pointer.child;
        const child_ti = @typeInfo(ChildT);

        if (child_ti == .@"struct") {
            const n = child_ti.@"struct".fields.len;
            comptime if (@sizeOf(ChildT) != n * @sizeOf(u32)) @compileError("unexpected size for " ++ @typeName(ChildT));
            const arr_ptr: *const [n]u32 = @ptrCast(childrefs);
            self.extra_childrefs.append(arr_ptr);

            args_ptr.*[0] = self.extra_childrefs.head;
            args_ptr.*[1] += @intCast(n);
        } else {
            self.extra_childrefs.append(childrefs);

            args_ptr.*[0] = self.extra_childrefs.head;
            args_ptr.*[1] += @intCast(childrefs.len);
        }
    }
}

// -> `NodeId`: idx where node was pushed into
pub inline fn push_node(self: *@This(), nodekind: Node.Kind) NodeId {
    self.ast_nodes.push(.{ .nk = nodekind, .args = .{ 0, 0 } });
    return self.ast_nodes.len() - 1;
}

pub inline fn push_data_node(self: *@This(), nodekind: Node.Kind, span_idx: u32) NodeId {
    const new_node_idx = self.push_node(nodekind);
    self.set_children(new_node_idx, span_idx);

    return new_node_idx;
}

const COL_RESET = "\x1b[0m";
const COL_DIM = "\x1b[90m";
const COL_KIND = "\x1b[36m";
const COL_LEAF = "\x1b[32m";
const COL_FUNC = "\x1b[1;35m";
const COL_ERR = "\x1b[31m";
const COL_NONE = "\x1b[2;37m";

fn wr(io: std.Io, s: []const u8) void {
    std.Io.File.stdout().writeStreamingAll(io, s) catch @panic("print failed");
}

fn leaf_label(self: *@This(), src_bytes: []const u8, node: Node) []const u8 {
    const idx = node.args[0];
    const span = self.span_store[idx];
    return src_bytes[span[0]..span[1]];
}

fn print_placeholder(io: std.Io, prefix: []const u8, is_last: bool) void {
    wr(io, prefix);
    wr(io, if (is_last) "└── " else "├── ");
    wr(io, COL_NONE ++ "∅ (none)" ++ COL_RESET ++ "\n");
}

fn print_node(self: *@This(), io: std.Io, src_bytes: []const u8, idx: u32, prefix: []const u8, is_first: bool, is_last: bool) anyerror!void {
    wr(io, prefix);
    wr(io, if (is_first) "" else if (is_last) "└── " else "├── ");

    const node = self.ast_nodes.get(idx) orelse {
        wr(io, COL_ERR);
        wr(io, "<missing node #");
        var idx_buf: [16]u8 = undefined;
        wr(io, std.fmt.bufPrint(&idx_buf, "{d}", .{idx}) catch "?");
        wr(io, ">");
        wr(io, COL_RESET);
        wr(io, "\n");
        return;
    };

    const is_leaf = Node.nk_childc[@intFromEnum(node.nk)] == .none;

    if (!is_first) {
        wr(io, if (is_leaf) COL_LEAF else COL_KIND);
        wr(io, @tagName(node.nk));
        wr(io, COL_RESET);
    }

    if (is_leaf) {
        const label = self.leaf_label(src_bytes, node);
        if (label.len != 0) {
            wr(io, COL_DIM);
            wr(io, "  \"");
            wr(io, label);
            wr(io, "\"");
            wr(io, COL_RESET);
        }
    }

    if (!is_first) wr(io, "\n");

    if (is_leaf) return;

    var prefix_buf: [1024]u8 = undefined;
    const ext = if (is_first) "" else if (is_last) "    " else "\xe2\x94\x82   "; // "│   "
    const new_prefix = std.fmt.bufPrint(&prefix_buf, "{s}{s}", .{ prefix, ext }) catch prefix;

    if (Node.nk_childc[@intFromEnum(node.nk)] == .many) {
        const start = node.args[0];
        const count = node.args[1];

        var i: u32 = 0;
        while (i < count) : (i += 1) {
            const childref = self.extra_childrefs.buf[start + i];
            const child_is_last = i == count - 1;
            if (childref == 0xFFFFFFFF) {
                print_placeholder(io, new_prefix, child_is_last);
            } else {
                try self.print_node(io, src_bytes, childref, new_prefix, false, child_is_last);
            }
        }
        return;
    }

    var children: [2]NodeId = undefined;
    var childc: usize = 0;
    const a = node.args[0];
    const b = node.args[1];
    if (a != 0 and a != 0xFFFFFFFF) {
        children[childc] = a;
        childc += 1;
    }
    if (b != 0 and b != 0xFFFFFFFF) {
        children[childc] = b;
        childc += 1;
    }

    for (children[0..childc], 0..) |child_idx, i| {
        try self.print_node(io, src_bytes, child_idx, new_prefix, false, i == childc - 1);
    }
}

pub fn debug_print_tree(self: *@This(), io: std.Io, src_bytes: []const u8, func_ids: []const NodeId) !void {
    wr(io, COL_DIM);
    wr(io, "[DEBUG PARSER AST DUMP]\n");
    wr(io, COL_RESET);

    for (func_ids, 0..) |funcid, i| {
        const node = self.ast_nodes.get(funcid) orelse {
            wr(io, COL_ERR);
            wr(io, "func: <missing>\n\n");
            wr(io, COL_RESET);
            continue;
        };

        var num_buf: [16]u8 = undefined;
        const num_str = std.fmt.bufPrint(&num_buf, "{d}", .{i}) catch "?";

        wr(io, COL_FUNC);
        wr(io, @tagName(node.nk));
        wr(io, " (#");
        wr(io, num_str);
        wr(io, ")");
        wr(io, COL_RESET);
        wr(io, "\n");

        try self.print_node(io, src_bytes, funcid, "", true, true);
        wr(io, "\n");
    }

    var stats_buf: [64]u8 = undefined;
    const stats = std.fmt.bufPrint(&stats_buf, "{d} functions, {d} nodes total", .{ func_ids.len, self.ast_nodes.len() }) catch "";
    wr(io, COL_DIM);
    wr(io, stats);
    wr(io, "\n" ++ COL_RESET);
}
