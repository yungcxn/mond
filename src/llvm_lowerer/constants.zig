const std = @import("std");
const llvm = @import("llvm_c");
const mond = @import("mond");
const LLVMLowerer = @import("../LLVMLowerer.zig");
const tag_bits = @import("values.zig").tag_bits;
const StaticPool = mond.StaticPool;
const Index = StaticPool.Index;
const Value = LLVMLowerer.Value;
const Type = LLVMLowerer.Type;

// pool values as llvm constants. a value in memory (a record, array or variant) is a constant
// global, the instruction gets its address. llvm has no constant of a variant's type with a
// payload in its room (the room is ints, the payload a record), so such an initializer is made of
// its bytes instead: a packed struct laid out like the value

// the value as an operand of an instruction
pub fn operand(lowerer: *LLVMLowerer, value: Index) Value {
    const pool = lowerer.pool;
    if (pool.tag(value) == .function_value) return lower(lowerer, value, .none);
    if (pool.tag(value) == .string_value) return string_pointer(lowerer, value);
    const value_type = if (pool.tag(value) == .variant_case_type)
        pool.get(value).variant_case_type.variant
    else
        pool.type_of(value);
    if (!lowerer.types.is_in_memory(value_type)) return lower(lowerer, value, value_type);

    const slot = &lowerer.value_globals[@intFromEnum(value)];
    if (slot.* == null) {
        const initializer = lower(lowerer, value, value_type);
        slot.* = constant_global(lowerer, initializer, lowerer.alignment_of(value_type));
    }
    return slot.*;
}

pub fn zeros(lowerer: *LLVMLowerer, zeroed_type: Index) Value {
    const slot = &lowerer.zero_globals[@intFromEnum(zeroed_type)];
    if (slot.* == null) {
        const initializer = llvm.LLVMConstNull(lowerer.types.of(zeroed_type));
        slot.* = constant_global(lowerer, initializer, lowerer.alignment_of(zeroed_type));
    }
    return slot.*;
}

// `value` as an initializer of `expected` (its own type when none), of bytes when it holds a
// variant with a payload
pub fn lower(lowerer: *LLVMLowerer, value: Index, expected: Index) Value {
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const into = if (expected == .none) pool.type_of(value) else expected;
    return switch (pool.get(value)) {
        .int_value => |int| {
            const into_type = types.of(into);
            return switch (llvm.LLVMGetTypeKind(into_type)) {
                llvm.LLVMIntegerTypeKind => llvm.LLVMConstInt(into_type, int.bits, 0),
                llvm.LLVMPointerTypeKind => llvm.LLVMConstIntToPtr(
                    llvm.LLVMConstInt(types.length, int.bits, 0),
                    into_type,
                ),
                llvm.LLVMHalfTypeKind, llvm.LLVMFloatTypeKind, llvm.LLVMDoubleTypeKind => {
                    const number: f64 = if (lowerer.is_signed(int.value_type))
                        @floatFromInt(@as(i64, @bitCast(int.bits)))
                    else
                        @floatFromInt(int.bits);
                    return llvm.LLVMConstReal(into_type, number);
                },
                else => llvm.LLVMConstInt(types.of(int.value_type), int.bits, 0),
            };
        },
        .float_value => |float| llvm.LLVMConstReal(types.of(into), float.value),
        .simple_value => |simple| switch (simple) {
            .bool_true => llvm.LLVMConstInt(llvm.LLVMInt1TypeInContext(lowerer.context), 1, 0),
            .bool_false => llvm.LLVMConstInt(llvm.LLVMInt1TypeInContext(lowerer.context), 0, 0),
            .unit => llvm.LLVMConstNull(types.unit),
        },
        .string_value => |bytes| {
            if (types.of(into) == types.pointer) return string_pointer(lowerer, value);
            return llvm.LLVMConstStringInContext2(lowerer.context, bytes.ptr, bytes.len, 1);
        },
        .aggregate_value => |aggregate| {
            const aggregate_type = if (aggregate.value_type == .none)
                into
            else
                aggregate.value_type;
            return lower_aggregate(lowerer, value, aggregate_type);
        },
        .variant_value => |variant| lower_variant(lowerer, variant, into),
        .variant_case_type => lower_variant(lowerer, .{ .case = value, .payload = .none }, into),
        .function_value => |declaration| {
            const function = lowerer.function_of_declaration[@intFromEnum(declaration)];
            return pair(lowerer, lowerer.thunk(function), llvm.LLVMConstNull(types.pointer));
        },
        // types and trees are static only, and so is what stands for them
        else => llvm.LLVMConstNull(types.of(into)),
    };
}

// the bytes of a string with a zero byte behind, which c functions need
pub fn string_pointer(lowerer: *LLVMLowerer, value: Index) Value {
    const slot = &lowerer.value_globals[@intFromEnum(value)];
    if (slot.* == null) {
        const bytes = lowerer.pool.get(value).string_value;
        const text = llvm.LLVMConstStringInContext2(lowerer.context, bytes.ptr, bytes.len, 0);
        slot.* = constant_global(lowerer, text, 1);
    }
    return slot.*;
}

fn constant_global(lowerer: *LLVMLowerer, initializer: Value, alignment: c_uint) Value {
    const global = llvm.LLVMAddGlobal(lowerer.module, llvm.LLVMTypeOf(initializer), "");
    llvm.LLVMSetInitializer(global, initializer);
    llvm.LLVMSetGlobalConstant(global, 1);
    llvm.LLVMSetLinkage(global, llvm.LLVMPrivateLinkage);
    llvm.LLVMSetUnnamedAddress(global, llvm.LLVMGlobalUnnamedAddr);
    llvm.LLVMSetAlignment(global, alignment);
    return global;
}

fn pair(lowerer: *LLVMLowerer, first: Value, second: Value) Value {
    var parts = [_]Value{ first, second };
    return llvm.LLVMConstStructInContext(lowerer.context, &parts, parts.len, 0);
}

// a record or array, made of bytes when one of its parts is
fn lower_aggregate(lowerer: *LLVMLowerer, value: Index, aggregate_type: Index) Value {
    const pool = lowerer.pool;
    const allocator = lowerer.allocator;
    const element_count = pool.get(value).aggregate_value.elements.len;
    const parts = allocator.alloc(Part, element_count) catch @panic("OOM");
    defer allocator.free(parts);

    const is_record = pool.tag(aggregate_type) == .record_type;
    const element_type = if (is_record) .none else pool.get(aggregate_type).array_type.element;
    var offset: u64 = 0;
    var of_bytes = false;
    for (parts, 0..) |*part, i| {
        // read anew: lowering a part may intern and move the pool's memory
        const element = pool.get(value).aggregate_value.elements[i];
        const part_type = if (is_record) pool.field_type(aggregate_type, i) else element_type;
        const part_layout = pool.layout(part_type);
        const is_packed = is_record and pool.get(aggregate_type).record_type.is_packed;
        if (!is_packed) offset = std.mem.alignForward(
            u64,
            offset,
            @as(u64, 1) << @intCast(part_layout.align_log2),
        );
        part.* = .{
            .offset = offset,
            .size = part_layout.size,
            .value = lower(lowerer, element, part_type),
        };
        of_bytes = of_bytes or llvm.LLVMTypeOf(part.value) != lowerer.types.of(part_type);
        offset += part_layout.size;
    }

    const lowered_type = lowerer.types.of(aggregate_type);
    const part_values = allocator.alloc(Value, element_count) catch @panic("OOM");
    defer allocator.free(part_values);
    for (parts, part_values) |part, *part_value| part_value.* = part.value;

    // a runtime-length array points to its elements in a constant global
    if (lowerer.types.is_runtime_array(aggregate_type)) {
        const elements = if (of_bytes)
            packed_struct(lowerer, parts, offset)
        else
            llvm.LLVMConstArray2(lowerer.types.of(element_type), part_values.ptr, element_count);
        return constant_global(lowerer, elements, lowerer.alignment_of(element_type));
    }
    if (of_bytes) return packed_struct(lowerer, parts, pool.layout(aggregate_type).size);
    if (is_record) return llvm.LLVMConstNamedStruct(
        lowered_type,
        part_values.ptr,
        @intCast(element_count),
    );
    return llvm.LLVMConstArray2(lowerer.types.of(element_type), part_values.ptr, element_count);
}

// a case of a variant, also seen as a case of a union of it
fn lower_variant(lowerer: *LLVMLowerer, variant_value: StaticPool.VariantValue, into: Index) Value {
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const case = pool.get(variant_value.case).variant_case_type;
    const into_union = pool.tag(into) == .variant_union_type;
    const container = if (into_union) into else case.variant;
    const self_tagged = types.is_self_tagged(case.variant);
    const first_field = if (variant_value.payload == .none)
        Index.none
    else
        pool.get(variant_value.payload).aggregate_value.elements[0];

    if (self_tagged and !into_union) {
        if (first_field == .none) return llvm.LLVMConstInt(
            types.of(case.variant),
            tag_bits(lowerer, variant_value.case),
            0,
        );
        return lower(lowerer, first_field, pool.get(case.variant).variant_type.tag_type);
    }

    const offset = if (into_union) pool.union_offset(into, case.variant) else 0;
    const tag_type = types.of(types.tag_type(container));
    const tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, variant_value.case) + offset, 0);
    const container_type = types.of(container);
    if (variant_value.payload == .none and !self_tagged) {
        var fields = [_]Value{ tag, llvm.LLVMConstNull(llvm.LLVMStructGetTypeAtIndex(
            container_type,
            1,
        )) };
        return llvm.LLVMConstNamedStruct(container_type, &fields, fields.len);
    }

    // the tag, then the payload where the room starts
    const room = types.payload_room(container);
    const tag_size = pool.layout(types.tag_type(container)).size;
    const room_offset = std.mem.alignForward(
        u64,
        tag_size,
        @as(u64, 1) << @intCast(room.align_log2),
    );
    // a `tagof self` member keeps its int in the union's room
    const payload_type = if (self_tagged)
        pool.get(case.variant).variant_type.tag_type
    else
        case.payload;
    const payload = if (!self_tagged)
        lower(lowerer, variant_value.payload, case.payload)
    else if (first_field == .none)
        llvm.LLVMConstInt(types.of(payload_type), tag_bits(lowerer, variant_value.case), 0)
    else
        lower(lowerer, first_field, payload_type);
    const parts = [_]Part{
        .{ .offset = 0, .size = tag_size, .value = tag },
        .{ .offset = room_offset, .size = pool.layout(payload_type).size, .value = payload },
    };
    return packed_struct(lowerer, &parts, pool.layout(container).size);
}

const Part = struct { offset: u64, size: u64, value: Value };

// the parts at their offsets, zero bytes in between and up to `size`
fn packed_struct(lowerer: *LLVMLowerer, parts: []const Part, size: u64) Value {
    const allocator = lowerer.allocator;
    var fields: std.ArrayList(Value) = .empty;
    defer fields.deinit(allocator);
    const byte = llvm.LLVMInt8TypeInContext(lowerer.context);
    var at: u64 = 0;
    for (parts) |part| {
        if (part.offset > at) {
            const padding = llvm.LLVMConstNull(llvm.LLVMArrayType2(byte, part.offset - at));
            fields.append(allocator, padding) catch @panic("OOM");
        }
        fields.append(allocator, part.value) catch @panic("OOM");
        at = part.offset + part.size;
    }
    if (size > at) {
        fields.append(allocator, llvm.LLVMConstNull(llvm.LLVMArrayType2(byte, size - at))) catch {
            @panic("OOM");
        };
    }
    return llvm.LLVMConstStructInContext(
        lowerer.context,
        fields.items.ptr,
        @intCast(fields.items.len),
        1,
    );
}
