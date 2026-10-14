const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const target = @import("../../mond.zig").target;
const Index = StaticPool.Index;
const Layout = StaticPool.Layout;
const SimpleType = StaticPool.SimpleType;
const dyn_len = StaticPool.dyn_len;

// the memory layout of types in c order (fields are never reordered), memoized per pool entry.
// the pointer size comes from `target` in mond.zig

const pointer_bytes: u64 = target.pointer_bits / 8;

// a layout while it is computed: sizes so far and whether a part was infinite or not known yet
const Partial = struct {
    size: u64 = 0,
    align_log2: u8 = 0,
    niche: Layout.Niche = std.mem.zeroes(Layout.Niche),
    infinite: bool = false,
    incomplete: bool = false,
};

pub fn layout(pool: *StaticPool, type_index: Index) Layout {
    // a nominal type reserved but not completed yet reads as poison
    const reserved = type_index != .poison_type and pool.tag(type_index) == .simple_type and
        pool.items.column(.data)[@intFromEnum(type_index)] == @intFromEnum(SimpleType.poison);
    if (reserved) return std.mem.zeroes(Layout);
    // a case is laid out as its variant, before its own entry is marked in progress
    if (pool.tag(type_index) == .variant_case_type) {
        return pool.layout(pool.get(type_index).variant_case_type.variant);
    }
    const i = @intFromEnum(type_index);
    const state = &pool.layouts.column(.state)[i];
    switch (state.*) {
        .done, .infinite => return pool.layouts.get(i).?,
        // a type met again while its own layout is computed contains itself by value
        .in_progress => {
            state.* = .infinite;
            return pool.layouts.get(i).?;
        },
        .unknown => state.* = .in_progress,
    }

    const partial = switch (pool.get(type_index)) {
        .int_type => |int_type| primitive(int_type.bits),
        .float_type => |float_type| primitive(float_type.bits),
        // a bool is one byte whose values 2..255 are free for a self-tagged variant's other cases
        .simple_type => |simple| if (simple == .bool) Partial{
            .size = 1,
            .niche = .{ .offset = 0, .bits = 8, .start = 2, .count = 254 },
        } else Partial{},
        .pointer_type, .function_type => pointer_layout(pool, type_index),
        .array_type => |array| array_layout(pool, array),
        .record_type => |record| record_layout(pool, record),
        .variant_type => |variant| variant_layout(pool, type_index, variant),
        .variant_case_type => unreachable,
        .variant_union_type => |members| union_layout(pool, type_index, members),
        // static-only entries and values have no memory
        .meta_type, .trait_type, .static_function, .template_type => Partial{},
        .type_variable, .ast_type => Partial{},
        .int_value, .float_value, .simple_value, .string_value, .aggregate_value => Partial{},
        .variant_value, .function_value, .tree_value => Partial{},
    };

    const alignment = @as(u64, 1) << @intCast(partial.align_log2);
    const result_state: Layout.State = if (partial.infinite or state.* == .infinite)
        .infinite
    else if (partial.incomplete)
        .unknown
    else
        .done;
    const result = Layout{
        .size = std.mem.alignForward(u64, partial.size, alignment),
        .align_log2 = partial.align_log2,
        .state = result_state,
        .niche = partial.niche,
    };
    pool.layouts.column(.size)[i] = result.size;
    pool.layouts.column(.align_log2)[i] = result.align_log2;
    pool.layouts.column(.niche)[i] = result.niche;
    pool.layouts.column(.state)[i] = result.state;
    return result;
}

fn primitive(bits: u16) Partial {
    const size = bits / 8;
    return .{ .size = size, .align_log2 = std.math.log2_int(u64, size) };
}

// a pointer to a runtime-length array carries its length too, and a function value the
// environment of its captures. the null address is the niche
fn pointer_layout(pool: *StaticPool, type_index: Index) Partial {
    const key = pool.get(type_index);
    const pointee = if (key == .pointer_type) pool.get(key.pointer_type.pointee) else key;
    const to_runtime_length = key == .pointer_type and pointee == .array_type and
        pointee.array_type.length == dyn_len;
    const is_pair = to_runtime_length or key == .function_type;
    return .{
        .size = pointer_bytes * @as(u64, if (is_pair) 2 else 1),
        .align_log2 = std.math.log2_int(u64, pointer_bytes),
        .niche = .{ .offset = 0, .bits = target.pointer_bits, .start = 0, .count = 1 },
    };
}

fn array_layout(pool: *StaticPool, array: StaticPool.ArrayType) Partial {
    // a runtime-length array is a pointer and a length
    if (array.length == dyn_len) {
        return .{ .size = pointer_bytes * 2, .align_log2 = std.math.log2_int(u64, pointer_bytes) };
    }
    if (pool.tag(array.length) != .int_value) return .{};
    const element = pool.layout(array.element);
    var partial = Partial{
        .size = pool.get(array.length).int_value.bits * element.size,
        .align_log2 = element.align_log2,
    };
    partial.infinite = element.state == .infinite;
    partial.incomplete = element.state == .unknown;
    return partial;
}

fn record_layout(pool: *StaticPool, record: StaticPool.RecordType) Partial {
    var partial = Partial{};
    for (record.field_types) |field_type| {
        const field = pool.layout(field_type);
        partial.infinite = partial.infinite or field.state == .infinite;
        partial.incomplete = partial.incomplete or field.state == .unknown;
        if (!record.is_packed) partial.align_log2 = @max(partial.align_log2, field.align_log2);
    }
    // the unpadded end of the last field, a field still unknown above is laid out anew
    for (record.field_types) |field_type| {
        const field = pool.layout(field_type);
        if (!record.is_packed) {
            const field_alignment = @as(u64, 1) << @intCast(field.align_log2);
            partial.size = std.mem.alignForward(u64, partial.size, field_alignment);
        }
        partial.size += field.size;
    }
    return partial;
}

// the tag, then the largest payload aligned behind it.
// a self-tagged variant without payload bytes is its tag
fn variant_layout(pool: *StaticPool, type_index: Index, variant: StaticPool.VariantType) Partial {
    var payload_size: u64 = 0;
    var payload_align_log2: u8 = 0;
    const payload_state = widest_payload(pool, type_index, &payload_size, &payload_align_log2);
    const tag = if (variant.tag_mode == .int)
        pool.layout(variant.tag_type)
    else
        std.mem.zeroes(Layout);
    var partial = Partial{ .align_log2 = @max(payload_align_log2, tag.align_log2) };
    partial.infinite = payload_state == .infinite;
    partial.incomplete = payload_state == .unknown;
    if (variant.tag_mode == .self and payload_size == 0) {
        partial.size = pool.layout(variant.tag_type).size;
    } else {
        const payload_alignment = @as(u64, 1) << @intCast(payload_align_log2);
        partial.size = std.mem.alignForward(u64, tag.size, payload_alignment) + payload_size;
    }
    return partial;
}

// the members share one tag (see `union_tag_type`) and the room of the widest payload of any member
fn union_layout(pool: *StaticPool, type_index: Index, members: []const Index) Partial {
    var partial = Partial{};
    var payload_size: u64 = 0;
    var payload_align_log2: u8 = 0;
    for (members) |member| {
        const state = widest_payload(pool, member, &payload_size, &payload_align_log2);
        partial.infinite = partial.infinite or state == .infinite;
        partial.incomplete = partial.incomplete or state == .unknown;
    }
    const tag = pool.layout(pool.union_tag_type(type_index));
    partial.align_log2 = @max(payload_align_log2, tag.align_log2);
    const payload_alignment = @as(u64, 1) << @intCast(payload_align_log2);
    partial.size = std.mem.alignForward(u64, tag.size, payload_alignment) + payload_size;
    return partial;
}

// grows `size` and `align_log2` to fit every payload of the variant,
// the worst state of them is returned
fn widest_payload(pool: *StaticPool, variant: Index, size: *u64, align_log2: *u8) Layout.State {
    var state: Layout.State = .done;
    for (pool.get(variant).variant_type.cases) |case| {
        const payload = pool.get(case).variant_case_type.payload;
        if (payload == .none) continue;
        const payload_layout = pool.layout(payload);
        if (payload_layout.state != .done) state = payload_layout.state;
        size.* = @max(size.*, payload_layout.size);
        align_log2.* = @max(align_log2.*, payload_layout.align_log2);
    }
    return state;
}

// one more than the highest tag of the variant, at least its case count
pub fn tag_range(pool: *const StaticPool, variant: Index) u64 {
    const variant_type = pool.get(variant).variant_type;
    var end: u64 = variant_type.cases.len;
    if (variant_type.tag_mode != .int) return end;
    for (variant_type.cases) |case| {
        const tag = pool.get(case).variant_case_type.tag;
        if (pool.tag(tag) == .int_value) end = @max(end, pool.get(tag).int_value.bits + 1);
    }
    return end;
}

// the members of a union are numbered one after another: where `member`'s tags start
pub fn union_offset(pool: *const StaticPool, union_type: Index, member: Index) u64 {
    var offset: u64 = 0;
    for (pool.get(union_type).variant_union_type) |other| {
        if (other == member) return offset;
        offset += pool.tag_range(other);
    }
    return offset;
}

pub fn union_tag_type(pool: *const StaticPool, union_type: Index) Index {
    const members = pool.get(union_type).variant_union_type;
    return smallest_tag_type(if (members.len == 0) 1 else pool.union_offset(union_type, .none));
}

pub fn smallest_tag_type(case_count: u64) Index {
    if (case_count <= 1 << 8) return .u8_type;
    if (case_count <= 1 << 16) return .u16_type;
    if (case_count <= 1 << 32) return .u32_type;
    return .u64_type;
}
