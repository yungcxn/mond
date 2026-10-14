const std = @import("std");
const llvm = @import("llvm_c");
const mond = @import("mond");
const LLVMLowerer = @import("../LLVMLowerer.zig");
const StaticPool = mond.StaticPool;
const HighIr = mond.HighIr;
const Ref = HighIr.Ref;
const Index = StaticPool.Index;
const Value = LLVMLowerer.Value;
const Type = LLVMLowerer.Type;

// the instructions of `HighIr` that depend on how values are laid out: conversions and casts,
// comparisons, places, aggregates and variants. a value in memory (see `Types.is_in_memory`) is
// the address of its own copy, which the instruction making it writes once and nothing changes
// afterwards; the room of a variant holds the record of its case

// comparisons

pub fn compare(
    lowerer: *LLVMLowerer,
    op: HighIr.Op,
    operand_type: Index,
    left: Value,
    right: Value,
) Value {
    const builder = lowerer.builder;
    if (!lowerer.types.is_in_memory(operand_type)) {
        const kind = llvm.LLVMGetTypeKind(llvm.LLVMTypeOf(left));
        if (is_float_kind(kind)) {
            const predicate: llvm.LLVMRealPredicate = switch (op) {
                .eq => llvm.LLVMRealOEQ,
                .ne => llvm.LLVMRealUNE,
                .lt => llvm.LLVMRealOLT,
                .gt => llvm.LLVMRealOGT,
                .le => llvm.LLVMRealOLE,
                .ge => llvm.LLVMRealOGE,
                else => unreachable,
            };
            return llvm.LLVMBuildFCmp(builder, predicate, left, right, "");
        }
        if (kind == llvm.LLVMIntegerTypeKind or kind == llvm.LLVMPointerTypeKind) {
            const signed = lowerer.is_signed(operand_type);
            const predicate: llvm.LLVMIntPredicate = switch (op) {
                .eq => llvm.LLVMIntEQ,
                .ne => llvm.LLVMIntNE,
                .lt => if (signed) llvm.LLVMIntSLT else llvm.LLVMIntULT,
                .gt => if (signed) llvm.LLVMIntSGT else llvm.LLVMIntUGT,
                .le => if (signed) llvm.LLVMIntSLE else llvm.LLVMIntULE,
                .ge => if (signed) llvm.LLVMIntSGE else llvm.LLVMIntUGE,
                else => unreachable,
            };
            return llvm.LLVMBuildICmp(builder, predicate, left, right, "");
        }
    }
    // anything else only compares equal or not
    const is_equal = equals(lowerer, operand_type, left, right);
    return if (op == .eq) is_equal else llvm.LLVMBuildNot(builder, is_equal, "");
}

fn is_float_kind(kind: llvm.LLVMTypeKind) bool {
    return kind == llvm.LLVMHalfTypeKind or kind == llvm.LLVMFloatTypeKind or
        kind == llvm.LLVMDoubleTypeKind;
}

// field by field, element by element, case by case
fn equals(lowerer: *LLVMLowerer, value_type: Index, left: Value, right: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    var result = true_value(lowerer);
    if (!lowerer.types.is_in_memory(value_type)) {
        const lowered_type = llvm.LLVMTypeOf(left);
        const kind = llvm.LLVMGetTypeKind(lowered_type);
        if (is_float_kind(kind)) return llvm.LLVMBuildFCmp(
            builder,
            llvm.LLVMRealOEQ,
            left,
            right,
            "",
        );
        if (kind == llvm.LLVMIntegerTypeKind or kind == llvm.LLVMPointerTypeKind) {
            return llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left, right, "");
        }
        // pointers with a length and function values: the same address, length and environment
        if (lowered_type != lowerer.types.slice and lowered_type != lowerer.types.closure) {
            return result;
        }
        for (0..2) |i| {
            const left_part = llvm.LLVMBuildExtractValue(builder, left, @intCast(i), "");
            const right_part = llvm.LLVMBuildExtractValue(builder, right, @intCast(i), "");
            const same = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_part, right_part, "");
            result = llvm.LLVMBuildAnd(builder, result, same, "");
        }
        return result;
    }

    switch (pool.get(value_type)) {
        .record_type => |record| for (0..record.field_types.len) |i| {
            const field_type = pool.field_type(value_type, i);
            const left_field = part(lowerer, value_type, left, @intCast(i), field_type);
            const right_field = part(lowerer, value_type, right, @intCast(i), field_type);
            const same = equals(lowerer, field_type, left_field, right_field);
            result = llvm.LLVMBuildAnd(builder, result, same, "");
        },
        .array_type => |array| {
            const length = pool.static_length(value_type) orelse 0;
            // past a few elements the bytes are compared, which assumes they have no padding
            if (length > 16) return memory_equal(
                lowerer,
                left,
                right,
                pool.layout(value_type).size,
            );
            for (0..length) |i| {
                const left_element = part(lowerer, value_type, left, @intCast(i), array.element);
                const right_element = part(lowerer, value_type, right, @intCast(i), array.element);
                const same = equals(lowerer, array.element, left_element, right_element);
                result = llvm.LLVMBuildAnd(builder, result, same, "");
            }
        },
        else => return variants_equal(lowerer, lowerer.types.variant_of(value_type), left, right),
    }
    return result;
}

// the same tag, and for a case with a payload the same payload
fn variants_equal(lowerer: *LLVMLowerer, variant_or_union: Index, left: Value, right: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const left_tag = tag_of(lowerer, variant_or_union, left);
    const right_tag = tag_of(lowerer, variant_or_union, right);
    const tag_type = llvm.LLVMTypeOf(left_tag);
    const same_tag = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_tag, right_tag, "");

    var same_payload = true_value(lowerer);
    const is_union = pool.tag(variant_or_union) == .variant_union_type;
    const members: []const Index = if (is_union)
        pool.get(variant_or_union).variant_union_type
    else
        &.{variant_or_union};
    for (members) |member| {
        const offset = if (is_union) pool.union_offset(variant_or_union, member) else 0;
        for (pool.get(member).variant_type.cases) |case| {
            const payload = pool.get(case).variant_case_type.payload;
            if (payload == .none) continue;
            const left_payload = room(lowerer, variant_or_union, left);
            const right_payload = room(lowerer, variant_or_union, right);
            const same = equals(lowerer, payload, left_payload, right_payload);
            const tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, case) + offset, 0);
            const is_case = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_tag, tag, "");
            same_payload = llvm.LLVMBuildSelect(builder, is_case, same, same_payload, "");
        }
    }
    return llvm.LLVMBuildAnd(builder, same_tag, same_payload, "");
}

// strings by their bytes: arrays of the same length, slices by length and bytes, and pointers as
// the zero-terminated strings of c (string constants end in a zero byte)
pub fn bytes_equal(lowerer: *LLVMLowerer, operand_type: Index, left: Value, right: Value) Value {
    const builder = lowerer.builder;
    if (lowerer.types.is_in_memory(operand_type)) {
        return memory_equal(lowerer, left, right, lowerer.pool.layout(operand_type).size);
    }
    if (llvm.LLVMTypeOf(left) == lowerer.types.slice) {
        const left_length = llvm.LLVMBuildExtractValue(builder, left, 1, "");
        const right_length = llvm.LLVMBuildExtractValue(builder, right, 1, "");
        const same_length = llvm.LLVMBuildICmp(
            builder,
            llvm.LLVMIntEQ,
            left_length,
            right_length,
            "",
        );
        const zero = llvm.LLVMConstNull(lowerer.types.length);
        const compared = llvm.LLVMBuildSelect(builder, same_length, left_length, zero, "");
        const left_bytes = llvm.LLVMBuildExtractValue(builder, left, 0, "");
        const right_bytes = llvm.LLVMBuildExtractValue(builder, right, 0, "");
        const same_bytes = memory_compare(lowerer, left_bytes, right_bytes, compared);
        return llvm.LLVMBuildAnd(builder, same_length, same_bytes, "");
    }
    const int = llvm.LLVMInt32TypeInContext(lowerer.context);
    var parameters = [_]Type{ lowerer.types.pointer, lowerer.types.pointer };
    const strcmp_type = llvm.LLVMFunctionType(int, &parameters, parameters.len, 0);
    const strcmp = lowerer.runtime_function("strcmp", strcmp_type);
    const order = lowerer.build_call(strcmp_type, strcmp, &.{ left, right });
    return llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, order, llvm.LLVMConstNull(int), "");
}

fn memory_equal(lowerer: *LLVMLowerer, left: Value, right: Value, size: u64) Value {
    return memory_compare(lowerer, left, right, llvm.LLVMConstInt(lowerer.types.length, size, 0));
}

fn memory_compare(lowerer: *LLVMLowerer, left: Value, right: Value, length: Value) Value {
    const int = llvm.LLVMInt32TypeInContext(lowerer.context);
    var parameters = [_]Type{ lowerer.types.pointer, lowerer.types.pointer, lowerer.types.length };
    const memcmp_type = llvm.LLVMFunctionType(int, &parameters, parameters.len, 0);
    const memcmp = lowerer.runtime_function("memcmp", memcmp_type);
    const order = lowerer.build_call(memcmp_type, memcmp, &.{ left, right, length });
    return llvm.LLVMBuildICmp(lowerer.builder, llvm.LLVMIntEQ, order, llvm.LLVMConstNull(int), "");
}

fn true_value(lowerer: *LLVMLowerer) Value {
    return llvm.LLVMConstInt(llvm.LLVMInt1TypeInContext(lowerer.context), 1, 0);
}

// conversions and casts

pub fn convert(lowerer: *LLVMLowerer, kind: StaticPool.CoercionKind, to: Index, source: Ref) Value {
    const builder = lowerer.builder;
    const value = lowerer.operand(source);
    const from = lowerer.type_of_ref(source);
    return switch (kind) {
        // an array in memory is the address of its first byte already
        .identity,
        .unified,
        .never_to_any,
        .poison,
        .ptr_mut_to_ptr,
        .case_to_variant,
        .payload_to_self_tagged,
        .impl_to_trait,
        .unit_to_runit,
        .incompatible,
        .string_to_ptr,
        => value,
        .int_widen => llvm.LLVMBuildIntCast2(
            builder,
            value,
            lowerer.types.of(to),
            @intFromBool(lowerer.is_signed(from)),
            "",
        ),
        .float_widen => llvm.LLVMBuildFPExt(builder, value, lowerer.types.of(to), ""),
        .array_ptr_to_elem_ptr => if (llvm.LLVMTypeOf(value) == lowerer.types.slice)
            llvm.LLVMBuildExtractValue(builder, value, 0, "")
        else
            value,
        // the slice of an array value points into that value's own copy
        .to_dyn => {
            if (llvm.LLVMTypeOf(value) == lowerer.types.slice) return value;
            const length = lowerer.pool.static_length(lowerer.pool.pointee(from)) orelse 0;
            return lowerer.pair(
                lowerer.types.slice,
                value,
                llvm.LLVMConstInt(lowerer.types.length, length, 0),
            );
        },
        .variant_to_union => into_union(lowerer, lowerer.types.variant_of(from), to, value),
    };
}

pub fn cast(lowerer: *LLVMLowerer, kind: StaticPool.CastKind, to: Index, source: Ref) Value {
    const builder = lowerer.builder;
    const value = lowerer.operand(source);
    const from = lowerer.type_of_ref(source);
    const lowered_type = lowerer.types.of(to);
    return switch (kind) {
        .identity, .invalid => value,
        .int_resize => llvm.LLVMBuildIntCast2(
            builder,
            value,
            lowered_type,
            @intFromBool(lowerer.is_signed(from)),
            "",
        ),
        .int_to_float => if (lowerer.is_signed(from))
            llvm.LLVMBuildSIToFP(builder, value, lowered_type, "")
        else
            llvm.LLVMBuildUIToFP(builder, value, lowered_type, ""),
        .float_to_int => if (lowerer.is_signed(to))
            llvm.LLVMBuildFPToSI(builder, value, lowered_type, "")
        else
            llvm.LLVMBuildFPToUI(builder, value, lowered_type, ""),
        .float_resize => llvm.LLVMBuildFPCast(builder, value, lowered_type, ""),
        .bit_reinterpret, .bit_extend => reinterpret(lowerer, value, from, to),
        .variant_retag => retag(lowerer, from, to, value),
        .payload_wrap => {
            const case = lowerer.pool.get(to).variant_case_type;
            const payload = lowerer.entry_alloca(lowerer.types.of(case.payload));
            store_part(
                lowerer,
                case.payload,
                payload,
                0,
                lowerer.pool.field_type(case.payload, 0),
                value,
            );
            return make_variant(lowerer, case.variant, case.case_index, payload);
        },
        // a relengthed pointer still points to the first element
        .pointer_relength => if (lowered_type == lowerer.types.slice)
            relength(lowerer, source, value)
        else
            value,
        // lowered by HighLowerer as a relengthed pointer, and traits are realized per type
        .array_narrow, .trait_narrow => unreachable,
    };
}

// HighLowerer relengthes the pointer to an element of an array: the slice reaches from there to
// the array's end
fn relength(lowerer: *LLVMLowerer, source: Ref, first: Value) Value {
    const builder = lowerer.builder;
    const element = lowerer.instruction_of(source).?;
    const array = @as(Ref, @enumFromInt(element.a));
    const array_value = lowerer.operand(array);
    const length = if (llvm.LLVMTypeOf(array_value) == lowerer.types.slice)
        llvm.LLVMBuildExtractValue(builder, array_value, 1, "")
    else
        llvm.LLVMConstInt(
            lowerer.types.length,
            lowerer.pool.static_length(lowerer.pointee_of_ref(array)) orelse 0,
            0,
        );
    const start = lowerer.index_value(@enumFromInt(element.b));
    return lowerer.pair(lowerer.types.slice, first, llvm.LLVMBuildSub(builder, length, start, ""));
}

// the bytes of `value` read as `to`, zero-extended when `to` is larger
fn reinterpret(lowerer: *LLVMLowerer, value: Value, from: Index, to: Index) Value {
    const types = &lowerer.types;
    if (!types.is_in_memory(to) and llvm.LLVMTypeOf(value) == types.of(to)) return value;
    const from_size = lowerer.pool.layout(from).size;
    const to_size = lowerer.pool.layout(to).size;
    const byte = llvm.LLVMInt8TypeInContext(lowerer.context);
    const bytes = lowerer.entry_alloca(llvm.LLVMArrayType2(byte, @max(from_size, to_size)));
    llvm.LLVMSetAlignment(bytes, @max(lowerer.alignment_of(from), lowerer.alignment_of(to)));
    if (to_size > from_size) {
        _ = llvm.LLVMBuildStore(
            lowerer.builder,
            llvm.LLVMConstNull(llvm.LLVMGetAllocatedType(bytes)),
            bytes,
        );
    }
    store_value(lowerer, from, bytes, value);
    if (types.is_in_memory(to)) return bytes;
    return llvm.LLVMBuildLoad2(lowerer.builder, types.of(to), bytes, "");
}

// places

// a field of a record, or of the payload of a case
pub fn field_pointer(lowerer: *LLVMLowerer, base: Ref, field: u32) Value {
    const pool = lowerer.pool;
    var pointer = lowerer.operand(base);
    var record = lowerer.pointee_of_ref(base);
    if (pool.tag(record) == .variant_case_type) {
        pointer = room(lowerer, record, pointer);
        record = pool.get(record).variant_case_type.payload;
    }
    return llvm.LLVMBuildStructGEP2(lowerer.builder, lowerer.types.of(record), pointer, field, "");
}

// an element of an array (checked against its length), or a pointer moved by `index` elements
pub fn index_pointer(lowerer: *LLVMLowerer, result_type: Index, base: Ref, index: Ref) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const base_value = lowerer.operand(base);
    const offset = lowerer.index_value(index);
    const element = pool.pointee(result_type);
    const element_type = lowerer.types.of(element);

    if (llvm.LLVMTypeOf(base_value) == lowerer.types.slice) {
        const length = llvm.LLVMBuildExtractValue(builder, base_value, 1, "");
        lowerer.trap_if(llvm.LLVMBuildICmp(builder, llvm.LLVMIntUGE, offset, length, ""));
        const first = llvm.LLVMBuildExtractValue(builder, base_value, 0, "");
        var indices = [_]Value{offset};
        return llvm.LLVMBuildInBoundsGEP2(builder, element_type, first, &indices, 1, "");
    }

    const array = lowerer.pointee_of_ref(base);
    const indexes_array = pool.tag(array) == .array_type and
        pool.get(array).array_type.element == element;
    if (indexes_array) {
        const length = pool.static_length(array) orelse 0;
        const length_value = llvm.LLVMConstInt(lowerer.types.length, length, 0);
        lowerer.trap_if(llvm.LLVMBuildICmp(builder, llvm.LLVMIntUGE, offset, length_value, ""));
        var indices = [_]Value{ llvm.LLVMConstNull(lowerer.types.length), offset };
        return llvm.LLVMBuildInBoundsGEP2(
            builder,
            lowerer.types.of(array),
            base_value,
            &indices,
            2,
            "",
        );
    }
    var indices = [_]Value{offset};
    return llvm.LLVMBuildGEP2(builder, element_type, base_value, &indices, 1, "");
}

// aggregates

// a record or array of `parts`; a runtime-length array points to its elements in the frame
pub fn aggregate(lowerer: *LLVMLowerer, aggregate_type: Index, parts: []const u32) Value {
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const is_slice = types.of(aggregate_type) == types.slice;
    const element: Index = if (pool.tag(aggregate_type) == .array_type)
        pool.get(aggregate_type).array_type.element
    else
        .none;
    const memory_type = if (is_slice)
        llvm.LLVMArrayType2(types.of(element), parts.len)
    else
        types.of(aggregate_type);
    const slot = lowerer.entry_alloca(memory_type);
    for (parts, 0..) |part_ref, i| {
        const part_type = if (element != .none) element else pool.field_type(aggregate_type, i);
        const value = lowerer.operand_as(@enumFromInt(part_ref), types.value_of(part_type));
        store_value(
            lowerer,
            part_type,
            part_address(lowerer, memory_type, slot, @intCast(i)),
            value,
        );
    }
    if (!is_slice) return slot;
    return lowerer.pair(types.slice, slot, llvm.LLVMConstInt(types.length, parts.len, 0));
}

// a field of a record or case value, or an element of an array value
pub fn extract(lowerer: *LLVMLowerer, result_type: Index, aggregate_ref: Ref, index: u32) Value {
    const pool = lowerer.pool;
    var aggregate_type = lowerer.type_of_ref(aggregate_ref);
    var pointer = lowerer.operand(aggregate_ref);
    if (pool.tag(aggregate_type) == .variant_case_type) {
        pointer = room(lowerer, aggregate_type, pointer);
        aggregate_type = pool.get(aggregate_type).variant_case_type.payload;
    }
    return part(lowerer, aggregate_type, pointer, index, result_type);
}

// part `index` of an aggregate in memory: its address when it lives in memory too, else loaded
fn part(
    lowerer: *LLVMLowerer,
    aggregate_type: Index,
    pointer: Value,
    index: u32,
    part_type: Index,
) Value {
    const address = part_address(lowerer, lowerer.types.of(aggregate_type), pointer, index);
    if (lowerer.types.is_in_memory(part_type)) return address;
    return llvm.LLVMBuildLoad2(lowerer.builder, lowerer.types.of(part_type), address, "");
}

fn part_address(lowerer: *LLVMLowerer, memory_type: Type, pointer: Value, index: u32) Value {
    if (llvm.LLVMGetTypeKind(memory_type) != llvm.LLVMArrayTypeKind) {
        return llvm.LLVMBuildStructGEP2(lowerer.builder, memory_type, pointer, index, "");
    }
    var indices = [_]Value{
        llvm.LLVMConstNull(lowerer.types.length),
        llvm.LLVMConstInt(lowerer.types.length, index, 0),
    };
    return llvm.LLVMBuildInBoundsGEP2(lowerer.builder, memory_type, pointer, &indices, 2, "");
}

fn store_part(
    lowerer: *LLVMLowerer,
    aggregate_type: Index,
    pointer: Value,
    index: u32,
    part_type: Index,
    value: Value,
) void {
    const address = part_address(lowerer, lowerer.types.of(aggregate_type), pointer, index);
    store_value(lowerer, part_type, address, value);
}

fn store_value(lowerer: *LLVMLowerer, value_type: Index, address: Value, value: Value) void {
    if (lowerer.types.is_in_memory(value_type)) return lowerer.copy(address, value, value_type);
    _ = llvm.LLVMBuildStore(lowerer.builder, value, address);
}

// variants

pub fn tag_bits(lowerer: *LLVMLowerer, case: Index) u64 {
    const tag = lowerer.pool.get(case).variant_case_type.tag;
    if (lowerer.pool.tag(tag) != .int_value) return 0;
    return lowerer.pool.get(tag).int_value.bits;
}

// where the payload of a variant or union value starts
fn room(lowerer: *LLVMLowerer, variant_type: Index, pointer: Value) Value {
    const lowered_type = lowerer.types.of(lowerer.types.variant_of(variant_type));
    return llvm.LLVMBuildStructGEP2(lowerer.builder, lowered_type, pointer, 1, "");
}

pub fn variant_make(
    lowerer: *LLVMLowerer,
    variant_type: Index,
    case_index: u32,
    payload: Ref,
) Value {
    const payload_value = if (payload == .none) null else lowerer.operand(payload);
    return make_variant(lowerer, lowerer.types.variant_of(variant_type), case_index, payload_value);
}

fn make_variant(lowerer: *LLVMLowerer, variant: Index, case_index: u32, payload: Value) Value {
    const builder = lowerer.builder;
    const case = lowerer.pool.get(variant).variant_type.cases[case_index];
    const tag_type = lowerer.types.of(lowerer.types.tag_type(variant));
    const tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, case), 0);
    // a `tagof self` variant is its payload's int, or the tag of a case without payload
    if (lowerer.types.is_self_tagged(variant)) {
        if (payload == null) return tag;
        return llvm.LLVMBuildLoad2(builder, tag_type, payload, "");
    }
    const lowered_type = lowerer.types.of(variant);
    const slot = lowerer.entry_alloca(lowered_type);
    _ = llvm.LLVMBuildStore(
        builder,
        tag,
        llvm.LLVMBuildStructGEP2(builder, lowered_type, slot, 0, ""),
    );
    if (payload != null) {
        const payload_type = lowerer.pool.get(case).variant_case_type.payload;
        lowerer.copy(room(lowerer, variant, slot), payload, payload_type);
    }
    return slot;
}

// the tag of a variant or union value, for `tagof self` the tag of the case its int stands for
pub fn variant_tag(lowerer: *LLVMLowerer, value_type: Index, value: Value) Value {
    return tag_of(lowerer, lowerer.types.variant_of(value_type), value);
}

fn tag_of(lowerer: *LLVMLowerer, variant: Index, value: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const tag_type = lowerer.types.of(lowerer.types.tag_type(variant));
    if (!lowerer.types.is_self_tagged(variant)) {
        const field = llvm.LLVMBuildStructGEP2(builder, lowerer.types.of(variant), value, 0, "");
        return llvm.LLVMBuildLoad2(builder, tag_type, field, "");
    }
    var tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, pool.first_payload_case(variant)), 0);
    for (pool.get(variant).variant_type.cases) |case| {
        if (pool.get(case).variant_case_type.payload != .none) continue;
        const case_tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, case), 0);
        const is_case = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, value, case_tag, "");
        tag = llvm.LLVMBuildSelect(builder, is_case, case_tag, tag, "");
    }
    return tag;
}

pub fn variant_payload(
    lowerer: *LLVMLowerer,
    record: Index,
    value_type: Index,
    value: Value,
) Value {
    const variant = lowerer.types.variant_of(value_type);
    if (!lowerer.types.is_self_tagged(variant)) return room(lowerer, variant, value);
    const payload = lowerer.entry_alloca(lowerer.types.of(record));
    store_part(lowerer, record, payload, 0, lowerer.pool.field_type(record, 0), value);
    return payload;
}

// a variant into a union of it: the tag moved into the member's range, the payload copied
fn into_union(lowerer: *LLVMLowerer, variant: Index, union_type: Index, value: Value) Value {
    const builder = lowerer.builder;
    const union_lowered = lowerer.types.of(union_type);
    const union_tag_type = llvm.LLVMStructGetTypeAtIndex(union_lowered, 0);
    const offset = llvm.LLVMConstInt(
        union_tag_type,
        lowerer.pool.union_offset(union_type, variant),
        0,
    );
    const member_tag = llvm.LLVMBuildIntCast2(
        builder,
        tag_of(lowerer, variant, value),
        union_tag_type,
        0,
        "",
    );
    const slot = lowerer.entry_alloca(union_lowered);
    const tag = llvm.LLVMBuildAdd(builder, member_tag, offset, "");
    _ = llvm.LLVMBuildStore(
        builder,
        tag,
        llvm.LLVMBuildStructGEP2(builder, union_lowered, slot, 0, ""),
    );
    const union_room = room(lowerer, union_type, slot);
    if (lowerer.types.is_self_tagged(variant)) {
        _ = llvm.LLVMBuildStore(builder, value, union_room);
    } else {
        const length = llvm.LLVMConstInt(
            lowerer.types.length,
            lowerer.types.payload_room(variant).size,
            0,
        );
        _ = llvm.LLVMBuildMemCpy(builder, union_room, 1, room(lowerer, variant, value), 1, length);
    }
    return slot;
}

// `as V.Case` sets the case's tag, and a union narrowed to a member moves the tag back into the
// member's own range
fn retag(lowerer: *LLVMLowerer, from: Index, to: Index, value: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const from_variant = types.variant_of(from);
    const to_variant = types.variant_of(to);
    const tag_type = types.of(types.tag_type(to_variant));
    if (from_variant == to_variant) {
        if (pool.tag(to) != .variant_case_type) return value;
        const tag = llvm.LLVMConstInt(tag_type, tag_bits(lowerer, to), 0);
        if (types.is_self_tagged(to_variant)) {
            return if (pool.get(to).variant_case_type.payload == .none) tag else value;
        }
        const slot = lowerer.entry_alloca(types.of(to_variant));
        lowerer.copy(slot, value, to_variant);
        _ = llvm.LLVMBuildStore(
            builder,
            tag,
            llvm.LLVMBuildStructGEP2(builder, types.of(to_variant), slot, 0, ""),
        );
        return slot;
    }

    // from a union to its member `to_variant`
    const union_tag = tag_of(lowerer, from_variant, value);
    const offset = llvm.LLVMConstInt(
        llvm.LLVMTypeOf(union_tag),
        pool.union_offset(from_variant, to_variant),
        0,
    );
    const member_tag = llvm.LLVMBuildIntCast2(
        builder,
        llvm.LLVMBuildSub(builder, union_tag, offset, ""),
        tag_type,
        0,
        "",
    );
    const union_room = room(lowerer, from_variant, value);
    if (types.is_self_tagged(to_variant)) {
        // the room holds the int of a payload case, the tag is the int of the others
        const payload_int = llvm.LLVMBuildLoad2(builder, tag_type, union_room, "");
        const payload_tag = llvm.LLVMConstInt(
            tag_type,
            tag_bits(lowerer, pool.first_payload_case(to_variant)),
            0,
        );
        const is_payload = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, member_tag, payload_tag, "");
        return llvm.LLVMBuildSelect(builder, is_payload, payload_int, member_tag, "");
    }
    const member_type = types.of(to_variant);
    const slot = lowerer.entry_alloca(member_type);
    _ = llvm.LLVMBuildStore(
        builder,
        member_tag,
        llvm.LLVMBuildStructGEP2(builder, member_type, slot, 0, ""),
    );
    const length = llvm.LLVMConstInt(types.length, types.payload_room(to_variant).size, 0);
    _ = llvm.LLVMBuildMemCpy(builder, room(lowerer, to_variant, slot), 1, union_room, 1, length);
    return slot;
}
