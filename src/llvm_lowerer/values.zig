const std = @import("std");
const builtin = @import("builtin");
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
        // function values: the same function and environment
        if (lowered_type != lowerer.types.closure) {
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
        // the same length and the same bytes; slices of different lengths compare none of them
        .slice_type => |slice| {
            const left_length = part(lowerer, value_type, left, 1, .u64_type);
            const right_length = part(lowerer, value_type, right, 1, .u64_type);
            const same_length =
                llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_length, right_length, "");
            const zero = llvm.LLVMConstNull(lowerer.types.length);
            const compared = llvm.LLVMBuildSelect(builder, same_length, left_length, zero, "");
            const element_size =
                llvm.LLVMConstInt(lowerer.types.length, pool.layout(slice.element).size, 0);
            const size = llvm.LLVMBuildMul(builder, compared, element_size, "");
            const left_first = part(lowerer, value_type, left, 0, slice.pointer);
            const right_first = part(lowerer, value_type, right, 0, slice.pointer);
            const same_bytes = memory_compare(lowerer, left_first, right_first, size);
            return llvm.LLVMBuildAnd(builder, same_length, same_bytes, "");
        },
        else => return variants_equal(lowerer, lowerer.types.variant_of(value_type), left, right),
    }
    return result;
}

// the same tag, and for a case with a payload the same payload
fn variants_equal(
    lowerer: *LLVMLowerer,
    variant_or_unified: Index,
    left: Value,
    right: Value,
) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    // values of one case of a packed variant: their payloads
    if (pool.tag(variant_or_unified) == .variant_case_type) {
        const payload = pool.get(variant_or_unified).variant_case_type.payload;
        if (payload == .none) return true_value(lowerer);
        const left_payload = room(lowerer, variant_or_unified, left);
        return equals(lowerer, payload, left_payload, room(lowerer, variant_or_unified, right));
    }
    // stored by a strategy: the same bits
    if (custom_variant(lowerer, variant_or_unified)) {
        return llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left, right, "");
    }
    const left_tag = tag_of(lowerer, variant_or_unified, left);
    const right_tag = tag_of(lowerer, variant_or_unified, right);
    const tag_type = llvm.LLVMTypeOf(left_tag);
    const same_tag = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_tag, right_tag, "");

    var same_payload = true_value(lowerer);
    const is_unified = pool.tag(variant_or_unified) == .unified_variant_type;
    const members: []const Index = if (is_unified)
        pool.get(variant_or_unified).unified_variant_type.members
    else
        &.{variant_or_unified};
    for (members) |member| {
        if (is_unified and !pool.brings_cases(member)) {
            const left_member = member_in_room(lowerer, variant_or_unified, left, member);
            const right_member = member_in_room(lowerer, variant_or_unified, right, member);
            const same = equals(lowerer, member, left_member, right_member);
            const tag = llvm.LLVMConstInt(tag_type, pool.tag_in(variant_or_unified, member), 0);
            const is_member = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_tag, tag, "");
            same_payload = llvm.LLVMBuildSelect(builder, is_member, same, same_payload, "");
            continue;
        }
        for (pool.get(member).variant_type.cases) |case| {
            const payload = pool.get(case).variant_case_type.payload;
            if (payload == .none) continue;
            const left_payload = room(lowerer, variant_or_unified, left);
            const right_payload = room(lowerer, variant_or_unified, right);
            const same = equals(lowerer, payload, left_payload, right_payload);
            const tag = llvm.LLVMConstInt(tag_type, pool.tag_in(variant_or_unified, case), 0);
            const is_case = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_tag, tag, "");
            same_payload = llvm.LLVMBuildSelect(builder, is_case, same, same_payload, "");
        }
    }
    return llvm.LLVMBuildAnd(builder, same_tag, same_payload, "");
}

// strings by their bytes: arrays of the same length, and pointers and runtime-length arrays as the
// zero-terminated strings of c (string constants end in a zero byte)
pub fn bytes_equal(lowerer: *LLVMLowerer, operand_type: Index, left: Value, right: Value) Value {
    const builder = lowerer.builder;
    if (lowerer.types.is_in_memory(operand_type)) {
        return memory_equal(lowerer, left, right, lowerer.pool.layout(operand_type).size);
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
        // a slice is made by the high lowerer
        .to_slice => unreachable,
        // an array in memory is the address of its first byte already
        .identity,
        .unified,
        .never_to_any,
        .poison,
        .ptr_mut_to_ptr,
        .case_to_variant,
        .payload_to_self_tagged,
        .member_to_packed,
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
        // the address of the first element, of an array value its own copy
        .array_ptr_to_elem_ptr, .to_dyn => value,
        .member_to_unified => into_unified(lowerer, lowerer.types.variant_of(from), to, value),
    };
}

pub fn cast(lowerer: *LLVMLowerer, kind: StaticPool.CastKind, to: Index, source: Ref) Value {
    const builder = lowerer.builder;
    const value = lowerer.operand(source);
    const from = lowerer.type_of_ref(source);
    const lowered_type = lowerer.types.of(to);
    return switch (kind) {
        .identity, .invalid => value,
        // made by the high lowerer
        .array_to_slice, .slice_to_pointer => unreachable,
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
        .float_to_int => blk: {
            const name = if (lowerer.is_signed(to)) "llvm.fptosi.sat" else "llvm.fptoui.sat";
            const id = llvm.LLVMLookupIntrinsicID(name, name.len);
            var overloads = [_]Type{ lowered_type, llvm.LLVMTypeOf(value) };
            const function = llvm.LLVMGetIntrinsicDeclaration(lowerer.module, id, &overloads, 2);
            const function_type = llvm.LLVMIntrinsicGetType(lowerer.context, id, &overloads, 2);
            var arguments = [_]Value{value};
            break :blk llvm.LLVMBuildCall2(builder, function_type, function, &arguments, 1, "");
        },
        .float_resize => if (builtin.cpu.arch != .x86_64 or from != .f64_type or to != .f16_type)
            llvm.LLVMBuildFPCast(builder, value, lowered_type, "")
        else blk: {
            const context = lowerer.context;
            const float = llvm.LLVMFloatTypeInContext(context);
            const bits_type = llvm.LLVMInt32TypeInContext(context);
            const single = llvm.LLVMBuildFPTrunc(builder, value, float, "");
            const back = llvm.LLVMBuildFPExt(builder, single, llvm.LLVMTypeOf(value), "");
            const inexact = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealONE, back, value, "");
            const zero = llvm.LLVMConstNull(llvm.LLVMTypeOf(value));
            const negative = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOLT, value, zero, "");
            const below = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOLT, back, value, "");
            const above = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOGT, back, value, "");
            const away = llvm.LLVMBuildSelect(builder, negative, below, above, "");
            var bits = llvm.LLVMBuildBitCast(builder, single, bits_type, "");
            const one = llvm.LLVMConstInt(bits_type, 1, 0);
            const toward_zero = llvm.LLVMBuildSub(builder, bits, one, "");
            bits = llvm.LLVMBuildSelect(builder, away, toward_zero, bits, "");
            const odd = llvm.LLVMBuildOr(builder, bits, one, "");
            bits = llvm.LLVMBuildSelect(builder, inexact, odd, bits, "");
            const rounded = llvm.LLVMBuildBitCast(builder, bits, float, "");
            break :blk llvm.LLVMBuildFPTrunc(builder, rounded, lowered_type, "");
        },
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
        .pointer_relength => value,
        // lowered by HighLowerer as a relengthed pointer, and traits are realized per type
        .array_narrow, .trait_narrow => unreachable,
    };
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
    if (bit_packed(lowerer, record)) |fields| {
        return byte_address(lowerer, pointer, pool.field_offset(fields, field));
    }
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

    // an array of a static length is checked, one of a runtime length is its first element
    const array = lowerer.pointee_of_ref(base);
    const indexes_array = pool.tag(array) == .array_type and
        pool.get(array).array_type.element == element and
        !lowerer.types.is_runtime_array(array);
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

// a record or array of `parts`; a runtime-length array is the address of its elements
pub fn aggregate(lowerer: *LLVMLowerer, aggregate_type: Index, parts: []const u32) Value {
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const is_runtime_array = types.is_runtime_array(aggregate_type);
    const element: Index = if (pool.tag(aggregate_type) == .array_type)
        pool.get(aggregate_type).array_type.element
    else
        .none;
    const memory_type = if (is_runtime_array)
        llvm.LLVMArrayType2(types.of(element), parts.len)
    else
        types.of(aggregate_type);
    const slot = lowerer.entry_alloca(memory_type);
    // a bit-packed record is its bytes, each field put in where it starts
    if (bit_packed(lowerer, aggregate_type)) |record| {
        _ = llvm.LLVMBuildStore(lowerer.builder, llvm.LLVMConstNull(memory_type), slot);
        for (parts, 0..) |part_ref, i| {
            const value = lowerer.operand(@fromBackingInt(part_ref));
            if (pool.is_bit_field(record, i)) {
                // the bytes around the field read, its bits replaced, written back
                const builder = lowerer.builder;
                const field: u32 = @intCast(i);
                const address, const window, const shift = bit_window(lowerer, record, slot, field);
                const bits = pool.field_bits(record.field_types[i]);
                const window_bits = llvm.LLVMGetIntTypeWidth(window);
                const shift_value = llvm.LLVMConstInt(window, shift, 0);
                const ones = llvm.LLVMConstAllOnes(window);
                const unused = llvm.LLVMConstInt(window, window_bits - bits, 0);
                const low = llvm.LLVMBuildLShr(builder, ones, unused, "");
                const mask = llvm.LLVMBuildShl(builder, low, shift_value, "");
                const widened = llvm.LLVMBuildZExt(builder, value, window, "");
                const placed = llvm.LLVMBuildShl(builder, widened, shift_value, "");
                const old = llvm.LLVMBuildLoad2(builder, window, address, "");
                llvm.LLVMSetAlignment(old, 1);
                const outside = llvm.LLVMBuildNot(builder, mask, "");
                const kept = llvm.LLVMBuildAnd(builder, old, outside, "");
                const masked = llvm.LLVMBuildAnd(builder, placed, mask, "");
                const new = llvm.LLVMBuildOr(builder, kept, masked, "");
                llvm.LLVMSetAlignment(llvm.LLVMBuildStore(builder, new, address), 1);
                continue;
            }
            const address = byte_address(lowerer, slot, pool.field_offset(record, i));
            const part_type = record.field_types[i];
            if (types.is_in_memory(part_type)) {
                lowerer.copy(address, value, part_type);
            } else {
                llvm.LLVMSetAlignment(llvm.LLVMBuildStore(lowerer.builder, value, address), 1);
            }
        }
        return slot;
    }
    for (parts, 0..) |part_ref, i| {
        const part_type = if (element != .none) element else pool.field_type(aggregate_type, i);
        const value = lowerer.operand(@fromBackingInt(part_ref));
        store_value(
            lowerer,
            part_type,
            part_address(lowerer, memory_type, slot, @intCast(i)),
            value,
        );
    }
    return slot;
}

// a field of a record or case value, or an element of an array value
pub fn extract(lowerer: *LLVMLowerer, result_type: Index, aggregate_ref: Ref, index: u32) Value {
    const pool = lowerer.pool;
    var aggregate_type = lowerer.type_of_ref(aggregate_ref);
    var pointer = lowerer.operand(aggregate_ref);
    // a case stored by a strategy: its payload as `unwrap` gives it back
    const is_custom_case = pool.tag(aggregate_type) == .variant_case_type and
        custom_variant(lowerer, pool.get(aggregate_type).variant_case_type.variant);
    if (is_custom_case) {
        const payload = pool.get(aggregate_type).variant_case_type.payload;
        pointer = unwrapped_payload(lowerer, aggregate_type, payload, pointer);
        aggregate_type = payload;
    } else if (pool.tag(aggregate_type) == .variant_case_type) {
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
    if (bit_packed(lowerer, aggregate_type)) |record| {
        if (lowerer.pool.is_bit_field(record, index)) {
            const builder = lowerer.builder;
            const address, const window, const shift = bit_window(lowerer, record, pointer, index);
            const loaded = llvm.LLVMBuildLoad2(builder, window, address, "");
            llvm.LLVMSetAlignment(loaded, 1);
            const shift_value = llvm.LLVMConstInt(window, shift, 0);
            const shifted = llvm.LLVMBuildLShr(builder, loaded, shift_value, "");
            const bits = lowerer.pool.field_bits(part_type);
            const field_int = llvm.LLVMIntTypeInContext(lowerer.context, @intCast(bits));
            const value = llvm.LLVMBuildTrunc(builder, shifted, field_int, "");
            if (part_type != .bool_type) return value;
            const zero = llvm.LLVMConstNull(field_int);
            return llvm.LLVMBuildICmp(builder, llvm.LLVMIntNE, value, zero, "");
        }
        const address = byte_address(lowerer, pointer, lowerer.pool.field_offset(record, index));
        if (lowerer.types.is_in_memory(part_type)) return address;
        const part_lowered = lowerer.types.of(part_type);
        const loaded = llvm.LLVMBuildLoad2(lowerer.builder, part_lowered, address, "");
        llvm.LLVMSetAlignment(loaded, 1);
        return loaded;
    }
    const address = part_address(lowerer, lowerer.types.of(aggregate_type), pointer, index);
    if (lowerer.types.is_in_memory(part_type)) return address;
    return llvm.LLVMBuildLoad2(lowerer.builder, lowerer.types.of(part_type), address, "");
}

// the record a type is when it is bit-packed (see `StaticPool.is_bit_packed`)
fn bit_packed(lowerer: *LLVMLowerer, type_index: Index) ?StaticPool.RecordType {
    if (lowerer.pool.tag(type_index) != .record_type) return null;
    const record = lowerer.pool.get(type_index).record_type;
    return if (lowerer.pool.is_bit_packed(record)) record else null;
}

fn byte_address(lowerer: *LLVMLowerer, pointer: Value, offset: u64) Value {
    const byte = llvm.LLVMInt8TypeInContext(lowerer.context);
    var indices = [_]Value{llvm.LLVMConstInt(lowerer.types.length, offset, 0)};
    return llvm.LLVMBuildInBoundsGEP2(lowerer.builder, byte, pointer, &indices, 1, "");
}

// the bytes a bit field is in, read or written as one integer: its address, its type and where
// in it the field starts
fn bit_window(
    lowerer: *LLVMLowerer,
    record: StaticPool.RecordType,
    pointer: Value,
    field: u32,
) struct { Value, Type, u64 } {
    const offset = lowerer.pool.field_bit_offset(record, field);
    const bits = lowerer.pool.field_bits(record.field_types[field]);
    const shift = offset % 8;
    const bytes = std.math.divCeil(u64, shift + bits, 8) catch unreachable;
    const window = llvm.LLVMIntTypeInContext(lowerer.context, @intCast(bytes * 8));
    return .{ byte_address(lowerer, pointer, offset / 8), window, shift };
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

// a tag as a constant, the empty `{}` for a variant without one (`notagtype`)
pub fn tag_constant(tag_type: Type, bits: u64) Value {
    const is_int = llvm.LLVMGetTypeKind(tag_type) == llvm.LLVMIntegerTypeKind;
    return if (is_int) llvm.LLVMConstInt(tag_type, bits, 0) else llvm.LLVMConstNull(tag_type);
}

// where the payload of a variant or unified variant value starts
fn room(lowerer: *LLVMLowerer, variant_type: Index, pointer: Value) Value {
    // a variant tagged in a field of its payload is that payload
    if (lowerer.types.is_field_tagged(lowerer.types.variant_of(variant_type))) return pointer;
    const lowered_type = lowerer.types.of(lowerer.types.variant_of(variant_type));
    return llvm.LLVMBuildStructGEP2(lowerer.builder, lowered_type, pointer, 1, "");
}

// a variant whose cases a strategy stores (`tagtype ranges(1000)`)
fn custom_variant(lowerer: *LLVMLowerer, type_index: Index) bool {
    const pool = lowerer.pool;
    const variant = if (pool.tag(type_index) == .variant_case_type)
        pool.get(type_index).variant_case_type.variant
    else
        type_index;
    return pool.tag(variant) == .variant_type and
        pool.get(variant).variant_type.tag_mode == .custom;
}

// `wrap` (1), `case_of` (2) or `unwrap` (3) of a variant's strategy, called with the values given
fn strategy_call(
    lowerer: *LLVMLowerer,
    variant: Index,
    which: u32,
    arguments: []const Value,
) Value {
    const pool = lowerer.pool;
    const declaring = if (pool.tag(variant) == .variant_case_type)
        pool.get(variant).variant_case_type.variant
    else
        variant;
    const strategy = pool.get(declaring).variant_type.strategy;
    const function = pool.get(pool.get(strategy).aggregate_value.elements[which]).function_value;
    const mark = lowerer.value_stack.items.len;
    defer lowerer.value_stack.shrinkRetainingCapacity(mark);
    lowerer.value_stack.appendSlice(lowerer.allocator, arguments) catch @panic("OOM");
    const function_index = lowerer.function_of_declaration[@backingInt(function)];
    return lowerer.call_function(function_index, mark, null);
}

// the payload record of a case as `unwrap` gives its bits back
fn unwrapped_payload(
    lowerer: *LLVMLowerer,
    case_or_variant: Index,
    record: Index,
    value: Value,
) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const case = if (pool.tag(case_or_variant) == .variant_case_type)
        case_or_variant
    else
        pool.first_payload_case(case_or_variant);
    const length = lowerer.types.length;
    const stored = llvm.LLVMBuildZExt(builder, value, length, "");
    const u32_type = llvm.LLVMInt32TypeInContext(lowerer.context);
    const tag = llvm.LLVMConstInt(u32_type, pool.case_tag(case), 0);
    const bits = strategy_call(lowerer, case_or_variant, 3, &.{ stored, tag });
    const field_type = pool.field_type(record, 0);
    const props = pool.properties(field_type);
    const field_value = if (props.is_pointer)
        llvm.LLVMBuildIntToPtr(builder, bits, lowerer.types.pointer, "")
    else if (field_type == .bool_type)
        llvm.LLVMBuildICmp(builder, llvm.LLVMIntNE, bits, llvm.LLVMConstNull(length), "")
    else blk: {
        const width = if (props.is_float)
            pool.layout(field_type).size * 8
        else
            pool.get(field_type).int_type.bits;
        const int_type = llvm.LLVMIntTypeInContext(lowerer.context, @intCast(width));
        const int = llvm.LLVMBuildTrunc(builder, bits, int_type, "");
        if (!props.is_float) break :blk int;
        break :blk llvm.LLVMBuildBitCast(builder, int, lowerer.types.of(field_type), "");
    };
    const slot = lowerer.entry_alloca(lowerer.types.of(record));
    store_part(lowerer, record, slot, 0, field_type, field_value);
    return slot;
}

// the field of a payload record holding the tag of a variant tagged in it
fn tag_field_address(lowerer: *LLVMLowerer, variant: Index, pointer: Value) Value {
    const pool = lowerer.pool;
    var record = pool.get(pool.first_payload_case(variant)).variant_case_type.payload;
    var address = pointer;
    for (pool.get(variant).variant_type.tag_path) |field| {
        const lowered = lowerer.types.of(record);
        address = llvm.LLVMBuildStructGEP2(lowerer.builder, lowered, address, field, "");
        record = pool.field_type(record, field);
    }
    return address;
}

// a member of a unified variant that is one case, as a value of its own: it fills the room
fn member_in_room(lowerer: *LLVMLowerer, unified_type: Index, value: Value, member: Index) Value {
    const member_room = room(lowerer, unified_type, value);
    if (lowerer.types.is_in_memory(member)) return member_room;
    return llvm.LLVMBuildLoad2(lowerer.builder, lowerer.types.of(member), member_room, "");
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
    // a case of a packed variant is made as itself
    const case = if (lowerer.pool.tag(variant) == .variant_case_type)
        variant
    else
        lowerer.pool.get(variant).variant_type.cases[case_index];
    const tag_type = lowerer.types.of(lowerer.types.tag_type(variant));
    const tag = tag_constant(tag_type, lowerer.pool.case_tag(case));
    // a `tagof self` variant is its payload's int, or the tag of a case without payload
    if (lowerer.types.is_self_tagged(variant)) {
        if (payload == null) return tag;
        return llvm.LLVMBuildLoad2(builder, tag_type, payload, "");
    }
    // stored by a strategy: what its `wrap` makes of the tag and the payload's bits, those of the
    // one field of its payload as a `u64`
    if (custom_variant(lowerer, variant)) {
        const length = lowerer.types.length;
        const bits = if (payload) |pointer| bits: {
            const record = lowerer.pool.get(case).variant_case_type.payload;
            const field_type = lowerer.pool.field_type(record, 0);
            const field = part(lowerer, record, pointer, 0, field_type);
            const props = lowerer.pool.properties(field_type);
            if (props.is_pointer) break :bits llvm.LLVMBuildPtrToInt(builder, field, length, "");
            const as_int = if (props.is_float) as_int: {
                const size = lowerer.pool.layout(field_type).size * 8;
                const int = llvm.LLVMIntTypeInContext(lowerer.context, @intCast(size));
                break :as_int llvm.LLVMBuildBitCast(builder, field, int, "");
            } else field;
            break :bits llvm.LLVMBuildZExtOrBitCast(builder, as_int, length, "");
        } else llvm.LLVMConstNull(length);
        const u32_type = llvm.LLVMInt32TypeInContext(lowerer.context);
        const tag_value = llvm.LLVMConstInt(u32_type, lowerer.pool.case_tag(case), 0);
        const stored = strategy_call(lowerer, variant, 1, &.{ tag_value, bits });
        return llvm.LLVMBuildTrunc(builder, stored, lowerer.types.of(variant), "");
    }
    // tagged in a field of the payload: the payload, or zeros with the tag in that field
    if (lowerer.types.is_field_tagged(variant)) {
        if (payload != null) return payload.?;
        const slot = lowerer.entry_alloca(lowerer.types.of(variant));
        _ = llvm.LLVMBuildStore(builder, llvm.LLVMConstNull(lowerer.types.of(variant)), slot);
        _ = llvm.LLVMBuildStore(builder, tag, tag_field_address(lowerer, variant, slot));
        return slot;
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

// the tag of a variant or unified variant value, or at the address of a packed variant, for
// `tagof self` the tag of the case its int stands for
pub fn variant_tag(lowerer: *LLVMLowerer, value_type: Index, value: Value) Value {
    const variant_type = if (lowerer.pool.is_pointer(value_type))
        lowerer.pool.pointee(value_type)
    else
        value_type;
    return tag_of(lowerer, lowerer.types.variant_of(variant_type), value);
}

fn tag_of(lowerer: *LLVMLowerer, variant: Index, value: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const tag_type = lowerer.types.of(lowerer.types.tag_type(variant));
    // a value of a case of a packed variant is known to be of it, at an address of some case of
    // one every case starts with the tag
    if (pool.tag(variant) == .variant_case_type) {
        return tag_constant(tag_type, pool.case_tag(variant));
    }
    if (pool.tag(variant) == .variant_type and pool.get(variant).variant_type.is_packed) {
        return llvm.LLVMBuildLoad2(builder, tag_type, value, "");
    }
    if (custom_variant(lowerer, variant)) {
        const stored = llvm.LLVMBuildZExt(builder, value, lowerer.types.length, "");
        return strategy_call(lowerer, variant, 2, &.{stored});
    }
    const field_tagged = lowerer.types.is_field_tagged(variant);
    if (!lowerer.types.is_self_tagged(variant) and !field_tagged) {
        const field = llvm.LLVMBuildStructGEP2(builder, lowerer.types.of(variant), value, 0, "");
        return llvm.LLVMBuildLoad2(builder, tag_type, field, "");
    }
    // the bits that tell the cases apart: the value, or the field of the payload holding them
    const bits = if (field_tagged)
        llvm.LLVMBuildLoad2(builder, tag_type, tag_field_address(lowerer, variant, value), "")
    else
        value;
    const payload_case = pool.first_payload_case(variant);
    var tag = llvm.LLVMConstInt(tag_type, pool.case_tag(payload_case), 0);
    for (pool.get(variant).variant_type.cases) |case| {
        if (pool.get(case).variant_case_type.payload != .none) continue;
        const case_tag = llvm.LLVMConstInt(tag_type, pool.case_tag(case), 0);
        const is_case = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, bits, case_tag, "");
        tag = llvm.LLVMBuildSelect(builder, is_case, case_tag, tag, "");
    }
    return tag;
}

pub fn variant_payload(
    lowerer: *LLVMLowerer,
    record: Index,
    value_type: Index,
    value: Value,
    case_index: u32,
) Value {
    const variant = lowerer.types.variant_of(value_type);
    if (custom_variant(lowerer, variant)) {
        const declaring = lowerer.pool.whole_of(variant);
        const case = lowerer.pool.get(declaring).variant_type.cases[case_index];
        return unwrapped_payload(lowerer, case, record, value);
    }
    if (!lowerer.types.is_self_tagged(variant)) return room(lowerer, variant, value);
    const payload = lowerer.entry_alloca(lowerer.types.of(record));
    store_part(lowerer, record, payload, 0, lowerer.pool.field_type(record, 0), value);
    return payload;
}

// a member into a unified variant of it: a variant's tag moved into the member's range and its
// payload copied, a member that is one case is its tag and the whole value
fn into_unified(lowerer: *LLVMLowerer, variant: Index, unified_type: Index, value: Value) Value {
    const builder = lowerer.builder;
    const unified_lowered = lowerer.types.of(unified_type);
    const unified_tag_type = llvm.LLVMStructGetTypeAtIndex(unified_lowered, 0);
    const offset = llvm.LLVMConstInt(
        unified_tag_type,
        lowerer.pool.unified_offset(unified_type, variant),
        0,
    );
    const is_one_case = !lowerer.pool.brings_cases(variant);
    const tag = if (is_one_case) offset else blk: {
        const member_tag = llvm.LLVMBuildIntCast2(
            builder,
            tag_of(lowerer, variant, value),
            unified_tag_type,
            0,
            "",
        );
        break :blk llvm.LLVMBuildAdd(builder, member_tag, offset, "");
    };
    const slot = lowerer.entry_alloca(unified_lowered);
    _ = llvm.LLVMBuildStore(
        builder,
        tag,
        llvm.LLVMBuildStructGEP2(builder, unified_lowered, slot, 0, ""),
    );
    const unified_room = room(lowerer, unified_type, slot);
    if (is_one_case) {
        store_value(lowerer, variant, unified_room, value);
    } else if (lowerer.types.is_self_tagged(variant)) {
        _ = llvm.LLVMBuildStore(builder, value, unified_room);
    } else {
        const length = llvm.LLVMConstInt(
            lowerer.types.length,
            lowerer.types.payload_room(variant).size,
            0,
        );
        const payload = room(lowerer, variant, value);
        _ = llvm.LLVMBuildMemCpy(builder, unified_room, 1, payload, 1, length);
    }
    return slot;
}

// `as V.Case` sets the case's tag, and a unified variant narrowed to a member moves the tag back
// into the member's own range
fn retag(lowerer: *LLVMLowerer, from: Index, to: Index, value: Value) Value {
    const builder = lowerer.builder;
    const pool = lowerer.pool;
    const types = &lowerer.types;
    const from_variant = types.variant_of(from);
    const to_variant = types.variant_of(to);
    if (from_variant != to_variant and !pool.brings_cases(to_variant)) {
        return member_in_room(lowerer, from_variant, value, to_variant);
    }
    const tag_type = types.of(types.tag_type(to_variant));
    if (from_variant == to_variant) {
        if (pool.tag(to) != .variant_case_type) return value;
        const tag = tag_constant(tag_type, pool.case_tag(to));
        if (types.is_self_tagged(to_variant)) {
            return if (pool.get(to).variant_case_type.payload == .none) tag else value;
        }
        // a strategy's value already is of the case it stands for
        if (custom_variant(lowerer, to_variant)) return value;
        if (types.is_field_tagged(to_variant)) {
            if (pool.get(to).variant_case_type.payload != .none) return value;
            const case_index = pool.get(to).variant_case_type.case_index;
            return make_variant(lowerer, to_variant, case_index, null);
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

    // from a unified variant to its member `to_variant`
    const unified_tag = tag_of(lowerer, from_variant, value);
    const offset = llvm.LLVMConstInt(
        llvm.LLVMTypeOf(unified_tag),
        pool.unified_offset(from_variant, to_variant),
        0,
    );
    const member_tag = llvm.LLVMBuildIntCast2(
        builder,
        llvm.LLVMBuildSub(builder, unified_tag, offset, ""),
        tag_type,
        0,
        "",
    );
    const unified_room = room(lowerer, from_variant, value);
    if (types.is_self_tagged(to_variant)) {
        // the room holds the int of a payload case, the tag is the int of the others
        const payload_int = llvm.LLVMBuildLoad2(builder, tag_type, unified_room, "");
        const payload_tag = llvm.LLVMConstInt(
            tag_type,
            pool.case_tag(pool.first_payload_case(to_variant)),
            0,
        );
        const is_payload = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, member_tag, payload_tag, "");
        return llvm.LLVMBuildSelect(builder, is_payload, payload_int, member_tag, "");
    }
    const member_type = types.of(to_variant);
    // tagged in a field of the payload: the room's payload, or zeros with the tag in that field
    if (types.is_field_tagged(to_variant)) {
        const size = llvm.LLVMConstInt(types.length, pool.layout(to_variant).size, 0);
        const payload = lowerer.entry_alloca(member_type);
        _ = llvm.LLVMBuildMemCpy(builder, payload, 1, unified_room, 1, size);
        const tagged = lowerer.entry_alloca(member_type);
        _ = llvm.LLVMBuildStore(builder, llvm.LLVMConstNull(member_type), tagged);
        const field = tag_field_address(lowerer, to_variant, tagged);
        _ = llvm.LLVMBuildStore(builder, member_tag, field);
        const payload_case = pool.first_payload_case(to_variant);
        const payload_tag = llvm.LLVMConstInt(tag_type, pool.case_tag(payload_case), 0);
        const is_payload = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, member_tag, payload_tag, "");
        return llvm.LLVMBuildSelect(builder, is_payload, payload, tagged, "");
    }
    const slot = lowerer.entry_alloca(member_type);
    _ = llvm.LLVMBuildStore(
        builder,
        member_tag,
        llvm.LLVMBuildStructGEP2(builder, member_type, slot, 0, ""),
    );
    const length = llvm.LLVMConstInt(types.length, types.payload_room(to_variant).size, 0);
    _ = llvm.LLVMBuildMemCpy(builder, room(lowerer, to_variant, slot), 1, unified_room, 1, length);
    return slot;
}
