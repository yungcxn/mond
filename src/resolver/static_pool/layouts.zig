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
        pool.items.column(.data)[@backingInt(type_index)] == @backingInt(SimpleType.poison);
    if (reserved) return std.mem.zeroes(Layout);
    // a case is laid out as its variant, before its own entry is marked in progress; a case of a
    // packed variant has a size of its own
    if (pool.tag(type_index) == .variant_case_type) {
        const variant = pool.get(type_index).variant_case_type.variant;
        if (!pool.get(variant).variant_type.is_packed) return pool.layout(variant);
    }
    // a subset is laid out as its whole
    if (pool.tag(type_index) == .variant_subset_type) return pool.layout(pool.whole_of(type_index));
    const i = @backingInt(type_index);
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
        // the address of the first element and the length
        .slice_type => Partial{
            .size = pointer_bytes + 8,
            .align_log2 = std.math.log2_int(u64, @max(pointer_bytes, 8)),
        },
        .array_type => |array| array_layout(pool, array),
        .record_type => |record| record_layout(pool, record),
        // a packed variant has no size, only each of its cases
        .variant_type => |variant| if (variant.is_packed)
            Partial{}
        else if (variant.tag_mode == .custom) blk: {
            // a strategy stores every case in its `storage` (an integer, else reported)
            const storage = pool.get(variant.strategy).aggregate_value.elements[0];
            if (pool.tag(storage) != .int_type) break :blk Partial{};
            break :blk primitive(pool.get(storage).int_type.bits);
        } else tagged_layout(pool, type_index, variant.tag_mode, variant.tag_type),
        .variant_case_type => |case| blk: {
            const variant = pool.get(case.variant).variant_type;
            break :blk tagged_layout(pool, type_index, variant.tag_mode, variant.tag_type);
        },
        // the members share one tag (see `unified_tag_type`), a packed one has no size
        .unified_variant_type => |unified| if (unified.is_packed)
            Partial{}
        else
            tagged_layout(pool, type_index, .int, pool.unified_tag_type(type_index)),
        // laid out as its whole above
        .variant_subset_type => unreachable,
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

// a width without a keyword (`u7`, `i24`) takes the bytes of the next one that has one
fn primitive(bits: u16) Partial {
    const bytes = std.math.divCeil(u16, bits, 8) catch unreachable;
    const size = std.math.ceilPowerOfTwoAssert(u64, bytes);
    return .{ .size = size, .align_log2 = std.math.log2_int(u64, size) };
}

// an address, a function value also the environment of its captures. the null address is the
// niche
fn pointer_layout(pool: *StaticPool, type_index: Index) Partial {
    const is_pair = pool.tag(type_index) == .function_type;
    return .{
        .size = pointer_bytes * @as(u64, if (is_pair) 2 else 1),
        .align_log2 = std.math.log2_int(u64, pointer_bytes),
        .niche = .{ .offset = 0, .bits = target.pointer_bits, .start = 0, .count = 1 },
    };
}

fn array_layout(pool: *StaticPool, array: StaticPool.ArrayType) Partial {
    // a runtime-length array is the address of its first element
    if (array.length == dyn_len) {
        return .{ .size = pointer_bytes, .align_log2 = std.math.log2_int(u64, pointer_bytes) };
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
    if (is_bit_packed(pool, record)) {
        const last = record.field_types.len - 1;
        const last_bits = field_bits(pool, record.field_types[last]);
        const end = field_bit_offset(pool, record, last) + last_bits;
        partial.size = std.math.divCeil(u64, end, 8) catch unreachable;
        return partial;
    }
    for (record.field_types) |field_type| {
        const field = pool.layout(field_type);
        partial.infinite = partial.infinite or field.state == .infinite;
        partial.incomplete = partial.incomplete or field.state == .unknown;
        if (!record.is_packed) partial.align_log2 = @max(partial.align_log2, field.align_log2);
    }
    // the unpadded end of the last field, a field still unknown above is laid out anew
    if (record.field_types.len > 0) {
        const last = record.field_types.len - 1;
        const last_size = pool.layout(record.field_types[last]).size;
        partial.size = field_offset(pool, record, last) + last_size;
    }
    return partial;
}

// the size the record would have with its fields ordered by alignment, largest first, which
// leaves no padding between them; `order` gets the field indices in that order. the language
// server hints at it, the compiler never reorders
pub fn reordered_size(pool: *StaticPool, record: StaticPool.RecordType, order: []u32) u64 {
    const Fields = struct { pool: *StaticPool, types: []const Index };
    for (order, 0..) |*field, i| field.* = @intCast(i);
    std.mem.sort(u32, order, Fields{ .pool = pool, .types = record.field_types }, struct {
        fn wider(fields: Fields, left: u32, right: u32) bool {
            const left_align = fields.pool.layout(fields.types[left]).align_log2;
            return left_align > fields.pool.layout(fields.types[right]).align_log2;
        }
    }.wider);
    var size: u64 = 0;
    var align_log2: u8 = 0;
    for (record.field_types) |field_type| {
        size += pool.layout(field_type).size;
        align_log2 = @max(align_log2, pool.layout(field_type).align_log2);
    }
    return std.mem.alignForward(u64, size, @as(u64, 1) << @intCast(align_log2));
}

// where a field starts: behind the one before it, aligned unless the record is packed. in a
// bit-packed record the byte its first bit is in
pub fn field_offset(pool: *StaticPool, record: StaticPool.RecordType, field: usize) u64 {
    if (is_bit_packed(pool, record)) return field_bit_offset(pool, record, field) / 8;
    var offset: u64 = 0;
    for (record.field_types[0 .. field + 1], 0..) |field_type, i| {
        const field_layout = pool.layout(field_type);
        if (!record.is_packed) {
            const field_alignment = @as(u64, 1) << @intCast(field_layout.align_log2);
            offset = std.mem.alignForward(u64, offset, field_alignment);
        }
        if (i == field) break;
        offset += field_layout.size;
    }
    return offset;
}

// a packed record with an integer of a width without a keyword (`**(u3 a, u5 b)`) is laid out bit
// by bit: each field right behind the one before it, an integer in its own width, anything else
// in its bytes
pub fn is_bit_packed(pool: *StaticPool, record: StaticPool.RecordType) bool {
    if (!record.is_packed) return false;
    for (record.field_types) |field_type| {
        if (pool.tag(field_type) == .int_type and pool.get(field_type).int_type.bits % 8 != 0) {
            return true;
        }
    }
    return false;
}

pub fn field_bits(pool: *StaticPool, field_type: Index) u64 {
    if (pool.tag(field_type) == .int_type) return pool.get(field_type).int_type.bits;
    return pool.layout(field_type).size * 8;
}

pub fn field_bit_offset(pool: *StaticPool, record: StaticPool.RecordType, field: usize) u64 {
    if (!is_bit_packed(pool, record)) return field_offset(pool, record, field) * 8;
    var offset: u64 = 0;
    for (record.field_types[0..field]) |field_type| offset += field_bits(pool, field_type);
    return offset;
}

// a field of a bit-packed record that shares a byte with another, read and written through the
// bytes around it
pub fn is_bit_field(pool: *StaticPool, record: StaticPool.RecordType, field: usize) bool {
    if (!is_bit_packed(pool, record)) return false;
    const offset = field_bit_offset(pool, record, field);
    return offset % 8 != 0 or field_bits(pool, record.field_types[field]) % 8 != 0;
}

// the tag, then the room of the payloads aligned behind it. a self-tagged variant without payload
// bytes is its tag
fn tagged_layout(
    pool: *StaticPool,
    type_index: Index,
    tag_mode: StaticPool.VariantTagMode,
    tag_type: Index,
) Partial {
    const room = pool.payload_room(type_index);
    const tag = if (tag_mode == .int) pool.layout(tag_type) else std.mem.zeroes(Layout);
    var partial = Partial{ .align_log2 = @max(room.align_log2, tag.align_log2) };
    partial.infinite = room.state == .infinite;
    partial.incomplete = room.state == .unknown;
    if (tag_mode == .self and room.size == 0) {
        partial.size = pool.layout(tag_type).size;
    } else {
        const room_alignment = @as(u64, 1) << @intCast(room.align_log2);
        partial.size = std.mem.alignForward(u64, tag.size, room_alignment) + room.size;
    }
    return partial;
}

pub const Room = struct { size: u64 = 0, align_log2: u8 = 0, state: Layout.State = .done };

// where payloads live: the room of the widest payload of a variant's cases or of a unified
// variant's members (a member that is one case is a payload itself), a case of a packed variant
// only has its own
pub fn payload_room(pool: *StaticPool, type_index: Index) Room {
    var room = Room{};
    switch (pool.get(type_index)) {
        .variant_type => widen_by_cases(pool, &room, type_index),
        .variant_case_type => |case| widen(pool, &room, case.payload),
        .unified_variant_type => |unified| for (unified.members) |member| {
            if (pool.brings_cases(member)) {
                widen_by_cases(pool, &room, member);
            } else {
                widen(pool, &room, member);
            }
        },
        .variant_subset_type => |subset| return pool.payload_room(subset.whole),
        else => {},
    }
    return room;
}

fn widen_by_cases(pool: *StaticPool, room: *Room, variant: Index) void {
    for (pool.get(variant).variant_type.cases) |case| {
        widen(pool, room, pool.get(case).variant_case_type.payload);
    }
}

// grows the room to fit the payload, keeping the worst state of any
fn widen(pool: *StaticPool, room: *Room, payload: Index) void {
    if (payload == .none) return;
    const payload_layout = pool.layout(payload);
    if (payload_layout.state != .done) room.state = payload_layout.state;
    room.size = @max(room.size, payload_layout.size);
    room.align_log2 = @max(room.align_log2, payload_layout.align_log2);
}

// one more than the highest tag of the variant (a self-tagged one's too: a unified variant keeps
// them), at least its case count
pub fn tag_range(pool: *const StaticPool, variant: Index) u64 {
    const variant_type = pool.get(variant).variant_type;
    var end: u64 = variant_type.cases.len;
    if (variant_type.tag_mode == .none) return end;
    for (variant_type.cases) |case| {
        const tag = pool.get(case).variant_case_type.tag;
        if (pool.tag(tag) == .int_value) end = @max(end, pool.get(tag).int_value.bits + 1);
    }
    return end;
}

// a member of a unified variant brings its cases when they have tags, any other type is one case
pub fn brings_cases(pool: *const StaticPool, member: Index) bool {
    return pool.tag(member) == .variant_type and pool.get(member).variant_type.tag_mode != .none;
}

// the tag a case is written with, 0 for one that has none
pub fn case_tag(pool: *const StaticPool, case: Index) u64 {
    const tag = pool.get(case).variant_case_type.tag;
    return if (pool.tag(tag) == .int_value) pool.get(tag).int_value.bits else 0;
}

// the tag a value of a case has in `container`: its own in its variant, in a unified variant moved
// into its member's range; a member that is one case (`u32` of `u32 || f32`) is its range's start
pub fn tag_in(pool: *const StaticPool, subset_or_container: Index, case_or_member: Index) u64 {
    const container = pool.whole_of(subset_or_container);
    const is_case = pool.tag(case_or_member) == .variant_case_type;
    const own = if (is_case) pool.case_tag(case_or_member) else 0;
    if (pool.tag(container) != .unified_variant_type) return own;
    const member = if (is_case)
        pool.get(case_or_member).variant_case_type.variant
    else
        case_or_member;
    const offset = pool.unified_offset(container, member);
    return if (pool.brings_cases(member)) offset + own else offset;
}

// the members of a unified variant are numbered one after another: where `member`'s tags start
pub fn unified_offset(pool: *const StaticPool, unified_type: Index, member: Index) u64 {
    var offset: u64 = 0;
    for (pool.get(unified_type).unified_variant_type.members) |other| {
        if (other == member) return offset;
        offset += if (pool.brings_cases(other)) pool.tag_range(other) else 1;
    }
    return offset;
}

pub fn unified_tag_type(pool: *const StaticPool, unified_type: Index) Index {
    const members = pool.get(unified_type).unified_variant_type.members;
    return smallest_tag_type(if (members.len == 0) 1 else pool.unified_offset(unified_type, .none));
}

pub fn smallest_tag_type(case_count: u64) Index {
    if (case_count <= 1 << 8) return .u8_type;
    if (case_count <= 1 << 16) return .u16_type;
    if (case_count <= 1 << 32) return .u32_type;
    return .u64_type;
}
