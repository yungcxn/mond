// the lowered high ir as c-like text: globals, then every function block by block
const std = @import("std");
const HighLowerer = @import("../HighLowerer.zig");
const Ir = @import("../high_lowerer/HighIr.zig");
const StaticPool = @import("../resolver/StaticPool.zig");
const DeclPool = @import("../resolver/DeclPool.zig");
const declaration_name = @import("source.zig").declaration_name;
const style = @import("style.zig");

const reset = style.reset;
const dim = style.dim;
const bold = style.bold;
const kind_color = style.kind_color;
const type_color = style.type_color;

const Writer = std.Io.Writer;

pub fn print(io: std.Io, lowerer: *HighLowerer) !void {
    var buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const writer = &file_writer.interface;
    const ir = &lowerer.ir;

    try writer.writeAll(dim ++ "[DEBUG HIGH IR]\n" ++ reset);

    const global_count = ir.globals.columns().decl.len;
    for (0..global_count) |global_index| try print_global(writer, lowerer, global_index);

    const function_count = ir.functions.columns().decl.len;
    for (0..function_count) |function_index| try print_function(writer, lowerer, function_index);

    const summary_format = dim ++ "\n{d} functions, {d} blocks, {d} instructions, {d} globals\n" ++
        reset;
    try writer.print(summary_format, .{
        function_count,
        ir.blocks.len(),
        ir.insts.len(),
        global_count,
    });
    try writer.flush();
}

pub fn print_global(writer: *Writer, lowerer: *HighLowerer, global_index: usize) !void {
    const global = lowerer.ir.globals.get(@intCast(global_index)).?;

    try writer.writeAll(kind_color ++ "static " ++ reset);
    try print_type(writer, lowerer, global.ty);
    const name = declaration_name(lowerer.resolver, global.decl);
    try writer.print(" " ++ bold ++ "{s}" ++ reset, .{name});

    if (global.init != .none) {
        try writer.writeAll(" = ");
        try print_value(writer, lowerer, global.init);
    }
    try writer.print(";" ++ dim ++ "  @{d}\n" ++ reset, .{global_index});
}

pub fn print_function(writer: *Writer, lowerer: *HighLowerer, function_index: usize) !void {
    const functions = lowerer.ir.functions.columns();
    const function_type = lowerer.static_pool.get(functions.ty[function_index]).function_type;

    try writer.writeAll("\n");
    try print_type(writer, lowerer, function_type.return_type);
    // the module initializer has no declaration
    const declaration = lowerer.ir.functions.column(.decl)[function_index];
    const name = if (declaration == .none)
        "$init"
    else
        declaration_name(lowerer.resolver, declaration);
    try writer.print(" " ++ style.function_color ++ "{s}" ++ reset ++ "(", .{name});

    // a function without blocks is extern, only the types of its parameters are known
    const block_count = functions.blocks[function_index];
    if (block_count == 0) {
        for (function_type.parameters, 0..) |parameter_type, i| {
            if (i > 0) try writer.writeAll(", ");
            try print_type(writer, lowerer, parameter_type);
        }
        return writer.print(");" ++ dim ++ "  extern #{d}\n" ++ reset, .{function_index});
    }

    // the `param` instructions of the entry block are the parameters
    const ir = &lowerer.ir;
    const entry = ir.blocks.get(functions.first_block[function_index]).?;

    var parameter_count: usize = 0;
    for (entry.start..entry.start + entry.len) |local| {
        const instruction_index = functions.first_inst[function_index] + @as(u32, @intCast(local));
        const instruction = ir.insts.get(instruction_index).?;
        if (instruction.op != .param) continue;

        if (parameter_count > 0) try writer.writeAll(", ");
        try print_type(writer, lowerer, instruction.ty);
        try writer.print(" %{d}", .{local});
        parameter_count += 1;
    }
    try writer.print(") " ++ dim ++ "#{d}", .{function_index});

    const capture_count = functions.captures[function_index];
    if (capture_count > 0) {
        const plural = if (capture_count == 1) "" else "s";
        try writer.print(", first {d} capture{s}", .{ capture_count, plural });
    }
    try writer.writeAll(reset ++ " {\n");

    for (0..block_count) |block_offset| {
        const first_block = ir.functions.column(.first_block)[function_index];
        const block = ir.blocks.get(first_block + @as(u32, @intCast(block_offset))).?;

        try writer.print(style.leaf_color ++ "b{d}:" ++ reset, .{block_offset});

        const predecessors = ir.list(block.preds);
        if (predecessors.len > 0) {
            try writer.writeAll(dim ++ "  // from");
            for (predecessors) |predecessor| try writer.print(" b{d}", .{predecessor});
            try writer.writeAll(reset);
        }
        try writer.writeAll("\n");

        for (block.start..block.start + block.len) |local| {
            const first_instruction = lowerer.ir.functions.column(.first_inst)[function_index];
            const instruction =
                lowerer.ir.insts.get(first_instruction + @as(u32, @intCast(local))).?;
            if (instruction.op == .param) continue;

            try writer.writeAll("    ");

            const defines_value = instruction.ty != .unit_type and
                !instruction.op.is_terminator() and
                instruction.op != .store;
            if (defines_value) {
                try print_type(writer, lowerer, instruction.ty);
                try writer.print(" %{d} = ", .{local});
            }

            const context: InstructionContext = .{
                .writer = writer,
                .lowerer = lowerer,
                .function_index = function_index,
                .instruction = instruction,
            };
            switch (instruction.op) {
                .param => unreachable,
                .add => try context.print_binary("+"),
                .sub => try context.print_binary("-"),
                .mul => try context.print_binary("*"),
                .div => try context.print_binary("/"),
                .rem => try context.print_binary("%"),
                .shl => try context.print_binary("<<"),
                .shr => try context.print_binary(">>"),
                .bit_and => try context.print_binary("&"),
                .bit_or => try context.print_binary("|"),
                .bit_xor => try context.print_binary("^"),
                .eq => try context.print_binary("=="),
                .ne => try context.print_binary("!="),
                .lt => try context.print_binary("<"),
                .gt => try context.print_binary(">"),
                .le => try context.print_binary("<="),
                .ge => try context.print_binary(">="),
                .undef => try writer.writeAll(kind_color ++ "undefined" ++ reset),
                .zeroed => try writer.writeAll("{0}"),
                .phi => try context.print_phi(predecessors),
                .bytes_eq => try context.print_bytes_equal(),
                .neg, .not => {
                    const unary_symbol = if (instruction.op == .neg)
                        "-"
                    else if (instruction.ty == .bool_type)
                        "!"
                    else
                        "~";
                    try writer.writeAll(unary_symbol);
                    try context.reference(instruction.a);
                },
                .convert, .cast => try context.print_conversion(),
                .alloca => try context.print_alloca(),
                .load => try print_place(writer, lowerer, instruction.a),
                .store => {
                    try print_place(writer, lowerer, instruction.a);
                    try writer.writeAll(" = ");
                    try context.reference(instruction.b);
                },
                .field_ptr => {
                    try writer.writeAll("&");
                    try context.reference(instruction.a);
                    const record_type = operand_type(lowerer, function_index, instruction.a);
                    try writer.print("->{s}", .{field_name(lowerer, record_type, instruction.b)});
                },
                .index_ptr => {
                    try writer.writeAll("&");
                    try context.reference(instruction.a);
                    try writer.writeAll("[");
                    try context.reference(instruction.b);
                    try writer.writeAll("]");
                },
                .dyn => try context.print_dynamic_array(),
                .aggregate => try context.print_aggregate(),
                .extract => try context.print_extract(),
                .variant_make => try context.print_variant_make(),
                .variant_tag => {
                    try context.reference(instruction.a);
                    try writer.writeAll(".tag");
                },
                .variant_payload => {
                    try context.reference(instruction.a);
                    const variant_type = operand_type(lowerer, function_index, instruction.a);
                    try writer.print(".{s}", .{case_name(lowerer, variant_type, instruction.b)});
                },
                .call => try context.print_call(),
                .closure => try context.print_closure(),
                .syscall => {
                    try writer.writeAll(kind_color ++ "syscall" ++ reset ++ " ");
                    for (lowerer.ir.list(instruction.b), 0..) |operand, i| {
                        if (i > 0) try writer.writeAll(", ");
                        try print_reference(writer, lowerer, operand);
                    }
                },
                .inline_asm => {
                    try writer.writeAll(kind_color ++ "asm" ++ reset ++ " ");
                    try context.reference(instruction.a);
                },
                .select => try context.print_select(),
                .@"switch" => {
                    try context.print_switch();
                    continue;
                },
                .br => try writer.print(kind_color ++ "goto" ++ reset ++ " b{d}", .{instruction.a}),
                .cond_br => try context.print_conditional_branch(),
                .ret => try context.print_return(),
                .@"unreachable" => try writer.writeAll(kind_color ++ "unreachable" ++ reset),
            }
            try writer.writeAll(";\n");
        }
    }
    try writer.writeAll("}\n");
}

pub fn print_type_definition(
    writer: *Writer,
    lowerer: *HighLowerer,
    type_index: StaticPool.Index,
) !void {
    const pool = lowerer.static_pool;
    switch (pool.get(type_index)) {
        .record_type => |record| {
            try print_record_definition(writer, lowerer, type_index, record);
        },
        .variant_type => |variant| {
            try print_variant_definition(writer, lowerer, type_index, variant);
        },
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .pointer_type,
        .function_type,
        .variant_case_type,
        .unified_variant_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .aggregate_value,
        .variant_value,
        .function_value,
        .tree_value,
        => {
            try writer.writeAll(kind_color ++ "typedef " ++ reset);
            try print_type(writer, lowerer, type_index);
        },
    }

    const layout = pool.layout(type_index);
    const alignment = @as(u64, 1) << @intCast(layout.align_log2);
    const layout_format = ";" ++ dim ++ "  // size {d}, align {d}\n" ++ reset;
    try writer.print(layout_format, .{ layout.size, alignment });
}

fn print_record_definition(
    writer: *Writer,
    lowerer: *HighLowerer,
    type_index: StaticPool.Index,
    record: StaticPool.RecordType,
) !void {
    try writer.writeAll(kind_color ++ "struct " ++ reset);
    try print_type(writer, lowerer, type_index);
    try writer.writeAll(" {");

    for (record.field_types, record.field_names) |field_type, field_name_index| {
        try writer.writeAll("\n    ");
        try print_type(writer, lowerer, field_type);
        const field_text = lowerer.resolver.name_pool.text_of(field_name_index);
        try writer.print(" " ++ style.field_color ++ "{s}" ++ reset ++ ";", .{field_text});
    }
    try writer.writeAll("\n}");
}

fn print_variant_definition(
    writer: *Writer,
    lowerer: *HighLowerer,
    type_index: StaticPool.Index,
    variant: StaticPool.VariantType,
) !void {
    try writer.writeAll(kind_color ++ "variant " ++ reset);
    try print_type(writer, lowerer, type_index);
    if (variant.tag_type != .none) {
        try writer.writeAll(" : ");
        try print_type(writer, lowerer, variant.tag_type);
    }
    try writer.writeAll(" {");

    for (variant.cases) |case_index| {
        const case = lowerer.static_pool.get(case_index).variant_case_type;
        const case_name_text = lowerer.resolver.name_pool.text_of(case.name);
        try writer.print("\n    " ++ style.field_color ++ "{s}" ++ reset, .{case_name_text});

        if (case.tag != .none) {
            try writer.writeAll(" = ");
            try print_value(writer, lowerer, case.tag);
        }
        if (case.payload != .none) {
            try writer.writeAll(" (");
            try print_type(writer, lowerer, case.payload);
            try writer.writeAll(")");
        }
        try writer.writeAll(";");
    }
    try writer.writeAll("\n}");
}

fn print_type(
    writer: *Writer,
    lowerer: *HighLowerer,
    type_index: StaticPool.Index,
) Writer.Error!void {
    const pool = lowerer.static_pool;
    if (type_index == .none) return writer.writeAll(type_color ++ "?" ++ reset);

    try writer.writeAll(type_color);
    defer writer.writeAll(reset) catch {};

    switch (pool.get(type_index)) {
        .simple_type => |simple| try writer.writeAll(simple_type_name(simple)),
        .meta_type => |meta| try writer.writeAll(@tagName(meta)),
        .pointer_type => |pointer| try print_pointer_type(writer, lowerer, pointer),
        .array_type => |array| {
            try print_type(writer, lowerer, array.element);
            try writer.writeAll(type_color ++ "[");
            if (array.length != StaticPool.dyn_len) {
                try pool.format(&lowerer.resolver.name_pool, array.length, writer);
            }
            try writer.writeAll("]");
        },
        .function_type => |function| try print_function_type(writer, lowerer, function),
        .record_type => |record| {
            if (try print_nominal(writer, lowerer, record.declaration)) return;
            try print_structural_record(writer, lowerer, record);
        },
        .variant_type => |variant| {
            if (try print_nominal(writer, lowerer, variant.declaration)) return;
            try writer.writeAll("variant");
        },
        .trait_type => |trait| {
            if (try print_nominal(writer, lowerer, trait.declaration)) return;
            try writer.writeAll("trait");
        },
        .variant_case_type => |case| {
            try print_type(writer, lowerer, case.variant);
            const name = lowerer.resolver.name_pool.text_of(case.name);
            try writer.print(type_color ++ ".{s}", .{name});
        },
        .unified_variant_type => |unified| {
            const separator = if (unified.is_packed) " ||| " else " || ";
            for (unified.members, 0..) |member, i| {
                if (i > 0) try writer.print(type_color ++ "{s}", .{separator});
                try print_type(writer, lowerer, member);
            }
        },
        .int_type,
        .float_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .aggregate_value,
        .variant_value,
        .function_value,
        .tree_value,
        => try pool.format(&lowerer.resolver.name_pool, type_index, writer),
    }
}

fn simple_type_name(simple: StaticPool.SimpleType) []const u8 {
    return switch (simple) {
        .unit, .runit => "void",
        .never => "noreturn",
        .bool => "bool",
        .poison => "poison",
    };
}

fn print_pointer_type(
    writer: *Writer,
    lowerer: *HighLowerer,
    pointer: StaticPool.PointerType,
) Writer.Error!void {
    const pool = lowerer.static_pool;
    // a pointer to a runtime-length array is that array itself, it gets no `*`
    const to_runtime_array = pool.get(pointer.pointee) == .array_type and
        pool.get(pointer.pointee).array_type.length == StaticPool.dyn_len;

    if (!pointer.is_mutable) try writer.writeAll("const ");
    try print_type(writer, lowerer, pointer.pointee);
    if (!to_runtime_array) try writer.writeAll(type_color ++ "*");
}

fn print_function_type(
    writer: *Writer,
    lowerer: *HighLowerer,
    function: StaticPool.FunctionType,
) Writer.Error!void {
    try writer.writeAll("fn(");
    for (function.parameters, 0..) |parameter_type, i| {
        if (i > 0) try writer.writeAll(type_color ++ ", ");
        try print_type(writer, lowerer, parameter_type);
    }
    try writer.writeAll(type_color ++ ") -> ");
    try print_type(writer, lowerer, function.return_type);
}

fn print_structural_record(
    writer: *Writer,
    lowerer: *HighLowerer,
    record: StaticPool.RecordType,
) Writer.Error!void {
    try writer.writeAll("struct {");
    for (record.field_types, record.field_names, 0..) |field_type, field_name_index, i| {
        try writer.writeAll(if (i > 0) type_color ++ "; " else " ");
        try print_type(writer, lowerer, field_type);
        const name = lowerer.resolver.name_pool.text_of(field_name_index);
        try writer.print(type_color ++ " {s}", .{name});
    }
    try writer.writeAll(type_color ++ " }");
}

// false for an anonymous type, which the caller prints structurally
fn print_nominal(
    writer: *Writer,
    lowerer: *HighLowerer,
    declaration: DeclPool.Index,
) Writer.Error!bool {
    const name = lowerer.resolver.decl_pool.get(declaration, .name);
    if (name == .empty or name == .none) return false;
    try writer.writeAll(lowerer.resolver.name_pool.text_of(name));

    const realizations = lowerer.resolver.generics.realization_arguments;
    const generic_arguments = realizations.get(declaration) orelse return true;
    const arguments = lowerer.static_pool.get(generic_arguments).aggregate_value.elements;
    try writer.writeAll("(");
    for (arguments, 0..) |argument, i| {
        if (i > 0) try writer.writeAll(type_color ++ ", ");
        try print_value(writer, lowerer, argument);
    }
    try writer.writeAll(type_color ++ ")");
    return true;
}

fn print_value(writer: *Writer, lowerer: *HighLowerer, value: StaticPool.Index) Writer.Error!void {
    const pool = lowerer.static_pool;
    switch (pool.tag(value)) {
        .function_value => {
            const name = declaration_name(lowerer.resolver, pool.get(value).function_value);
            try writer.print(style.function_color ++ "{s}" ++ reset, .{name});
        },
        .simple_value => {
            const simple_value_text = if (value == .unit_value)
                "void"
            else if (value == .bool_true)
                "true"
            else
                "false";
            try writer.print(style.leaf_color ++ "{s}" ++ reset, .{simple_value_text});
        },
        .int_value, .float_value, .string_value, .aggregate_value, .variant_value => {
            try writer.writeAll(style.leaf_color);
            try pool.format(&lowerer.resolver.name_pool, value, writer);
            try writer.writeAll(reset);
        },
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .pointer_type,
        .mutable_pointer_type,
        .function_type,
        .record_type,
        .variant_type,
        .variant_case_type,
        .unified_variant_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .tree_value,
        => try print_type(writer, lowerer, value),
    }
}

fn print_reference(writer: *Writer, lowerer: *HighLowerer, operand: u32) !void {
    const reference: Ir.Ref = @enumFromInt(operand);
    if (reference == .none) return writer.writeAll(dim ++ "void" ++ reset);
    if (reference.is_global()) {
        const declaration = lowerer.ir.globals.column(.decl)[reference.index()];
        const name = declaration_name(lowerer.resolver, declaration);
        return writer.print("&" ++ bold ++ "{s}" ++ reset, .{name});
    }
    if (!reference.is_const()) return writer.print("%{d}", .{operand});
    try print_value(writer, lowerer, reference.value());
}

// what a pointer operand points at: a global by name, else the dereferenced operand
fn print_place(writer: *Writer, lowerer: *HighLowerer, operand: u32) !void {
    const reference: Ir.Ref = @enumFromInt(operand);
    if (reference.is_global()) {
        const declaration = lowerer.ir.globals.column(.decl)[reference.index()];
        const name = declaration_name(lowerer.resolver, declaration);
        return writer.print(bold ++ "{s}" ++ reset, .{name});
    }
    try writer.writeAll("*");
    try print_reference(writer, lowerer, operand);
}

fn operand_type(lowerer: *HighLowerer, function_index: usize, operand: u32) StaticPool.Index {
    const reference: Ir.Ref = @enumFromInt(operand);
    if (reference == .none) return .none;
    if (reference.is_const()) return lowerer.static_pool.type_of(reference.value());
    if (reference.is_global()) {
        // a global operand is its address
        const global_type = lowerer.ir.globals.column(.ty)[reference.index()];
        return lowerer.static_pool.intern(.{
            .pointer_type = .{ .pointee = global_type, .is_mutable = true },
        });
    }
    const first_instruction = lowerer.ir.functions.column(.first_inst)[function_index];
    return lowerer.ir.insts.column(.ty)[first_instruction + operand];
}

fn field_name(lowerer: *HighLowerer, record_or_pointer: StaticPool.Index, field: u32) []const u8 {
    // the type a field or case is looked up in: through a pointer, and from a case to its variant
    const record = blk: {
        const type_index = record_or_pointer;
        if (type_index == .none) break :blk type_index;
        const pool = lowerer.static_pool;
        if (pool.get(type_index) == .pointer_type) {
            break :blk pool.get(type_index).pointer_type.pointee;
        }
        if (pool.tag(type_index) == .variant_case_type) {
            break :blk pool.get(type_index).variant_case_type.variant;
        }
        break :blk type_index;
    };
    if (record == .none or lowerer.static_pool.tag(record) != .record_type) return "?";

    const names = lowerer.static_pool.get(record).record_type.field_names;
    if (field >= names.len) return "?";
    return lowerer.resolver.name_pool.text_of(names[field]);
}

fn case_name(lowerer: *HighLowerer, variant_or_pointer: StaticPool.Index, case: u32) []const u8 {
    // the type a field or case is looked up in: through a pointer, and from a case to its variant
    const variant = blk: {
        const type_index = variant_or_pointer;
        if (type_index == .none) break :blk type_index;
        const pool = lowerer.static_pool;
        if (pool.get(type_index) == .pointer_type) {
            break :blk pool.get(type_index).pointer_type.pointee;
        }
        if (pool.tag(type_index) == .variant_case_type) {
            break :blk pool.get(type_index).variant_case_type.variant;
        }
        break :blk type_index;
    };
    if (variant == .none or lowerer.static_pool.tag(variant) != .variant_type) return "?";

    const cases = lowerer.static_pool.get(variant).variant_type.cases;
    if (case >= cases.len) return "?";
    const case_type = lowerer.static_pool.get(cases[case]).variant_case_type;
    return lowerer.resolver.name_pool.text_of(case_type.name);
}

// the printing state of one instruction, so its helpers take no long parameter lists
const InstructionContext = struct {
    writer: *Writer,
    lowerer: *HighLowerer,
    function_index: usize,
    instruction: Ir.Inst,

    fn reference(context: InstructionContext, operand: u32) !void {
        return print_reference(context.writer, context.lowerer, operand);
    }

    fn operand_list(context: InstructionContext) []const u32 {
        return context.lowerer.ir.list(context.instruction.b);
    }

    fn print_binary(context: InstructionContext, symbol: []const u8) !void {
        try context.reference(context.instruction.a);
        try context.writer.print(" {s} ", .{symbol});
        try context.reference(context.instruction.b);
    }

    // an incoming value per predecessor, in the order of the predecessors
    fn print_phi(context: InstructionContext, predecessors: []const u32) !void {
        const writer = context.writer;
        try writer.writeAll(kind_color ++ "phi" ++ reset ++ "(");
        for (context.operand_list(), 0..) |operand, i| {
            if (i > 0) try writer.writeAll(", ");
            const predecessor = if (i < predecessors.len) predecessors[i] else 0;
            try writer.print(dim ++ "b{d}: " ++ reset, .{predecessor});
            try context.reference(operand);
        }
        try writer.writeAll(")");
    }

    fn print_bytes_equal(context: InstructionContext) !void {
        try context.writer.writeAll(kind_color ++ "memeq" ++ reset ++ "(");
        try context.reference(context.instruction.a);
        try context.writer.writeAll(", ");
        try context.reference(context.instruction.b);
        try context.writer.writeAll(")");
    }

    fn print_conversion(context: InstructionContext) !void {
        const writer = context.writer;
        const instruction = context.instruction;
        try writer.writeAll("(");
        try print_type(writer, context.lowerer, instruction.ty);
        try writer.writeAll(") ");
        try context.reference(instruction.a);
        const conversion_name = if (instruction.op == .convert)
            @tagName(@as(StaticPool.CoercionKind, @enumFromInt(instruction.b)))
        else
            @tagName(@as(StaticPool.CastKind, @enumFromInt(instruction.b)));
        try writer.print(dim ++ "  /* {s} */" ++ reset, .{conversion_name});
    }

    fn print_alloca(context: InstructionContext) !void {
        const writer = context.writer;
        const instruction = context.instruction;
        const allocated_type = context.lowerer.static_pool.get(instruction.ty).pointer_type.pointee;

        try writer.writeAll(kind_color ++ "alloca" ++ reset ++ "(");
        try print_type(writer, context.lowerer, allocated_type);
        // the optional operand is the element count
        if (@as(Ir.Ref, @enumFromInt(instruction.a)) != .none) {
            try writer.writeAll("[");
            try context.reference(instruction.a);
            try writer.writeAll("]");
        }
        try writer.writeAll(")");
    }

    fn print_dynamic_array(context: InstructionContext) !void {
        const bounds = context.operand_list();
        try context.reference(context.instruction.a);
        try context.writer.writeAll("[");
        try context.reference(bounds[0]);
        try context.writer.writeAll("..");
        try context.reference(bounds[1]);
        try context.writer.writeAll("]");
    }

    fn print_aggregate(context: InstructionContext) !void {
        const writer = context.writer;
        const lowerer = context.lowerer;
        const aggregate_type = context.instruction.ty;
        const is_record = lowerer.static_pool.tag(aggregate_type) == .record_type;

        try writer.writeAll("(");
        try print_type(writer, lowerer, aggregate_type);
        try writer.writeAll("){");
        for (context.operand_list(), 0..) |operand, i| {
            if (i > 0) try writer.writeAll(", ");
            if (is_record) {
                try writer.print(".{s} = ", .{field_name(lowerer, aggregate_type, @intCast(i))});
            }
            try context.reference(operand);
        }
        try writer.writeAll("}");
    }

    fn print_extract(context: InstructionContext) !void {
        const instruction = context.instruction;
        const lowerer = context.lowerer;
        try context.reference(instruction.a);

        const aggregate_type = operand_type(lowerer, context.function_index, instruction.a);
        const is_record = aggregate_type != .none and
            lowerer.static_pool.tag(aggregate_type) == .record_type;
        if (is_record) {
            const name = field_name(lowerer, aggregate_type, instruction.b);
            return context.writer.print(".{s}", .{name});
        }
        try context.writer.print(".{d}", .{instruction.b});
    }

    fn print_variant_make(context: InstructionContext) !void {
        const writer = context.writer;
        const instruction = context.instruction;
        const lowerer = context.lowerer;

        try writer.writeAll("(");
        try print_type(writer, lowerer, instruction.ty);
        const name = case_name(lowerer, instruction.ty, instruction.a);
        try writer.print(") " ++ kind_color ++ "{s}" ++ reset, .{name});

        try writer.writeAll("(");
        const has_payload = @as(Ir.Ref, @enumFromInt(instruction.b)) != .none;
        if (has_payload) try context.reference(instruction.b);
        try writer.writeAll(")");
    }

    fn print_call(context: InstructionContext) !void {
        const writer = context.writer;
        try context.reference(context.instruction.a);
        try writer.writeAll("(");
        for (context.lowerer.ir.list(context.instruction.b), 0..) |operand, i| {
            if (i > 0) try writer.writeAll(", ");
            try print_reference(writer, context.lowerer, operand);
        }
        try writer.writeAll(")");
    }

    fn print_closure(context: InstructionContext) !void {
        const writer = context.writer;
        const lowerer = context.lowerer;
        const instruction = context.instruction;

        // the module initializer has no declaration
        const declaration = lowerer.ir.functions.column(.decl)[instruction.a];
        const name = if (declaration == .none)
            "$init"
        else
            declaration_name(lowerer.resolver, declaration);
        const closure_format = kind_color ++ "closure" ++ reset ++ "(" ++
            style.function_color ++ "{s}" ++ reset;
        try writer.print(closure_format, .{name});

        if (context.operand_list().len > 0) try writer.writeAll(", ");
        for (lowerer.ir.list(instruction.b), 0..) |operand, i| {
            if (i > 0) try writer.writeAll(", ");
            try print_reference(writer, lowerer, operand);
        }
        try writer.writeAll(")");
    }

    fn print_select(context: InstructionContext) !void {
        const choices = context.operand_list();
        try context.reference(context.instruction.a);
        try context.writer.writeAll(" ? ");
        try context.reference(choices[0]);
        try context.writer.writeAll(" : ");
        try context.reference(choices[1]);
    }

    // the operand list is the default block, then (value, block) pairs
    fn print_switch(context: InstructionContext) !void {
        const writer = context.writer;
        const cases = context.operand_list();

        try writer.writeAll(kind_color ++ "switch" ++ reset ++ " (");
        try context.reference(context.instruction.a);
        try writer.writeAll(") {\n");

        const case_count = cases.len / 2;
        for (0..case_count) |case_index| {
            const value = cases[1 + 2 * case_index];
            const target = cases[2 + 2 * case_index];

            // consecutive cases jumping to one block share a line and its goto
            const shares_previous_target = case_index > 0 and cases[2 * case_index] == target;
            const own_line_prefix = kind_color ++ "        case " ++ reset;
            const shared_line_prefix = kind_color ++ " case " ++ reset;
            const case_prefix = if (shares_previous_target) shared_line_prefix else own_line_prefix;
            try writer.writeAll(case_prefix);
            try context.reference(value);
            try writer.writeAll(":");

            const shares_next_target = case_index + 1 < case_count and
                cases[4 + 2 * case_index] == target;
            if (shares_next_target) continue;
            try writer.print(kind_color ++ " goto" ++ reset ++ " b{d};\n", .{target});
        }

        const default_format = kind_color ++ "        default: goto" ++ reset ++ " b{d};\n    }}\n";
        try writer.print(default_format, .{cases[0]});
    }

    fn print_conditional_branch(context: InstructionContext) !void {
        const writer = context.writer;
        const targets = context.operand_list();

        try writer.writeAll(kind_color ++ "if" ++ reset ++ " (");
        try context.reference(context.instruction.a);
        const branch_format = ") " ++ kind_color ++ "goto" ++ reset ++ " b{d}; " ++
            kind_color ++ "else goto" ++ reset ++ " b{d}";
        try writer.print(branch_format, .{ targets[0], targets[1] });
    }

    fn print_return(context: InstructionContext) !void {
        try context.writer.writeAll(kind_color ++ "return" ++ reset);
        if (@as(Ir.Ref, @enumFromInt(context.instruction.a)) == .none) return;
        try context.writer.writeAll(" ");
        try context.reference(context.instruction.a);
    }
};
