const std = @import("std");
const TypeVariables = @import("TypeVariables.zig");
const NamePool = @import("NamePool.zig");
const DeclPool = @import("DeclPool.zig");
const ParseTree = @import("../ParseTree.zig");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const type_queries = @import("static_pool/queries.zig");
const type_layouts = @import("static_pool/layouts.zig");
const type_relations = @import("static_pool/relations.zig");
const type_formatting = @import("static_pool/format.zig");

// every static (compile-time) value lives here, from integers to types: interned once, named by an
// `Index`. types are values too, so a type is compared by comparing two indices
const StaticPool = @This();

// types whose value either does not exist, or is not needed to be stored (like booleans)
pub const SimpleType = enum(u8) { bool, unit, runit, never, poison };
pub const SimpleValue = enum(u8) { bool_true, bool_false, unit };
// the types of types: what a type expression of each kind produces
pub const MetaType = enum(u8) { type, trait, variant, fun, stcfun, inlfun };

pub const IntType = struct {
    signedness: Signedness,
    bits: u16,
    pub const Signedness = enum(u1) { unsigned, signed };
};

pub const FloatType = struct { bits: u16 };

// the length is a pool entry: a static int, a type variable (unlengthed, set per call or value)
// or `dyn_len`
pub const ArrayType = struct { length: Index, element: Index };
pub const PointerType = struct { pointee: Index, is_mutable: bool };

pub const FunctionType = struct {
    category: Category,
    parameters: []const Index,
    return_type: Index,
    // not part: parameter names, defaults or where-clauses, read from the tree when needed

    pub const Category = enum(u8) { default, static, inlined };
};

pub const RecordType = struct {
    declaration: DeclPool.Index,
    is_packed: bool,
    field_names: []const NamePool.Index,
    field_types: []const Index,
    traits: []const Index,
    // read from the tree on demand: field mutability, defaults and where-clauses
};

// `custom`: a strategy of the program stores the cases (`tagtype ranges(1000)`)
pub const VariantTagMode = enum(u8) { none, int, self, custom };

pub const VariantType = struct {
    declaration: DeclPool.Index,
    tag_mode: VariantTagMode,
    tag_type: Index,
    // with `tagtype self` the fields from the payload down to the one holding the tag
    tag_path: []const u32 = &.{},
    // with a strategy, its record: `storage`, `wrap`, `case_of` and `unwrap` (see Types)
    strategy: Index = .none,
    is_packed: bool,
    cases: []const Index,
    traits: []const Index,
};

// `A || B`, packed `A ||| B`
pub const UnifiedVariantType = struct { members: []const Index, is_packed: bool };
// `[..]T`: the address of the first element and the length, a record of `*T` and `u64`
// (`slice_of` makes one)
pub const SliceType = struct { element: Index, pointer: Index };
// `V -- V.A`: the variant or unified variant `whole` without the cases (or one-case members) in
// `removed`, sorted. it keeps the whole's layout and tags, so a value of it is a value of the whole
pub const VariantSubsetType = struct { whole: Index, removed: []const Index };

pub const VariantCaseType = struct {
    variant: Index,
    case_index: u32,
    name: NamePool.Index,
    tag: Index,
    payload: Index,
};

pub const TraitType = struct {
    declaration: DeclPool.Index,
    member_names: []const NamePool.Index,
    member_types: []const Index,
    super_traits: []const Index,
};

// a tree producing `produces` (`ast(i32)`, none for any: `ast`),
// `root_kind` the kind of its root + 1 (`ast.Identifier`, 0 for any)
pub const AstType = struct { produces: Index, root_kind: u16 };
// a tree of the program or of a macro: its root, typed `ast(..)`, or `*ast(..)` to be written into
pub const TreeValue = struct { tree_type: Index, node: ParseTree.NodeId };

// the value of a stcfun declaration, called at compile time
pub const StaticFunction = struct {
    declaration: DeclPool.Index,
    result_kind: MetaType,
};

// ints and floats are max 64 bit here, the type of a value always comes first (see `type_of`)
pub const IntValue = struct { value_type: Index, bits: u64 };
pub const FloatValue = struct { value_type: Index, value: f64 };
pub const AggregateValue = struct { value_type: Index, elements: []const Index };
pub const VariantValue = struct { case: Index, payload: Index };

pub const Layout = struct {
    size: u64,
    align_log2: u8,
    state: State,
    niche: Niche,

    pub const State = enum(u8) { unknown, in_progress, done, infinite };

    // invalid bit patterns of a type that a self-tagged variant (`tagof self`) can use to
    // encode its other cases without an extra tag byte (e.g. 0xFF in `Opt8`)
    pub const Niche = struct {
        offset: u32,
        bits: u8,
        start: u64,
        count: u64,
    };
};

pub const Member = union(enum) {
    none,
    field: struct { index: u32, field_type: Index },
    method: DeclPool.Index,
    trait_method: struct { trait: Index, index: u32 },
    case: Index,
    builtin_len,
    builtin_init,
    builtin_deinit,
};

pub const UnifyResult = enum(u8) { ok, mismatch, infinite };

// how a value of one type may be used where another type is expected, without `as`
pub const CoercionKind = enum(u8) {
    identity,
    unified,
    never_to_any,
    poison,
    int_widen,
    float_widen,
    string_to_ptr,
    array_ptr_to_elem_ptr,
    to_dyn,
    // an array, or one behind a pointer, as a slice of its elements
    to_slice,
    ptr_mut_to_ptr,
    case_to_variant,
    payload_to_self_tagged,
    member_to_unified,
    // a value or address of a case or member as its packed variant: realized per type, it stays
    member_to_packed,
    impl_to_trait,
    unit_to_runit,
    incompatible,
};

// what an explicit `as` does
pub const CastKind = enum(u8) {
    identity,
    int_resize,
    int_to_float,
    float_to_int,
    float_resize,
    bit_reinterpret,
    bit_extend,
    variant_retag,
    payload_wrap,
    pointer_relength,
    array_narrow,
    trait_narrow,
    // `a as [..]T`: an array or a pointer to one seen whole as a slice
    array_to_slice,
    // `s as &[]T`, `s as &T`: the address of a slice's first element
    slice_to_pointer,
    invalid,
};

pub const JoinResult = struct {
    joined_type: Index,
    left: CoercionKind,
    right: CoercionKind,
};

// `A || B`, `A ||| B`, or the side of no size that can be no member
pub const UnifiedOf = union(enum) { unified: Index, sizeless_side: u1 };

// `A -- B`, or the side that is wrong: no tagged variant left, no part of it right
pub const DifferenceOf = union(enum) { difference: Index, wrong_side: u1 };
// how many of what a value may be another type covers (see `units_covered`)
pub const Covered = enum(u8) { none, some, all };

// the first entries are fixed, so `u8`, `bool`, ... are known without any lookup
pub const Index = enum(u32) {
    u8_type,
    u16_type,
    u32_type,
    u64_type,
    i8_type,
    i16_type,
    i32_type,
    i64_type,
    f16_type,
    f32_type,
    f64_type,
    bool_type,
    unit_type,
    runit_type,
    never_type,
    poison_type,
    type_type,
    trait_type,
    variant_type,
    fun_type,
    stcfun_type,
    inlfun_type,
    bool_true,
    bool_false,
    unit_value,
    ast_type,
    none = std.math.maxInt(u32),
    _,

    // the integers of a width without a keyword (`u7`, `i24`): unsigned, then signed, by width
    pub const first_odd_int: u32 = @backingInt(Index.ast_type) + 1;
    pub const first_dynamic: u32 = first_odd_int + 2 * odd_widths.len;
    pub const odd_widths = blk: {
        var widths: [60]u7 = undefined;
        var count = 0;
        for (1..65) |bits| {
            if (bits == 8 or bits == 16 or bits == 32 or bits == 64) continue;
            widths[count] = bits;
            count += 1;
        }
        break :blk widths;
    };

    // the integer type of a width and signedness, `u8` to `i64` or a fixed odd one
    pub fn int_of(signedness: IntType.Signedness, bits: u7) Index {
        const signed: u32 = @intFromBool(signedness == .signed);
        const standard: u32 = switch (bits) {
            8 => 0,
            16 => 1,
            32 => 2,
            64 => 3,
            else => {
                const rank = std.mem.indexOfScalar(u7, &odd_widths, bits).?;
                return @fromBackingInt(@intCast(first_odd_int + signed * odd_widths.len + rank));
            },
        };
        return @fromBackingInt(signed * 4 + standard);
    }
};

// the length of a runtime-length array, a fixed entry no static length can be
pub const dyn_len: Index = .unit_value;

// what a type is built from, for the walks that look into types (unify, substitution, occurs
// checks, template and tree searches). nominal types and values are leaves, their members are
// reached by name instead
pub const Composition = enum(u8) {
    leaf,
    // `*T`, `&T`: the pointee
    pointer,
    // `[n]T`: the length and the element
    array,
    // `[..]T`: the element
    slice,
    // the parameters and the return type
    function,
    // `A || B`: the member variants
    unified_variants,
    // `ast(T)`: what the tree produces
    tree,
};

pub const TagProperties = packed struct(u16) {
    is_type: bool = false,
    is_value: bool = false,
    is_integer: bool = false,
    is_float: bool = false,
    is_pointer: bool = false,
    is_aggregate: bool = false,
    // compared by declaration: two records with the same fields are still two types
    is_nominal: bool = false,
    is_variant: bool = false,
    is_trait: bool = false,
    is_callable: bool = false,
    is_static_only: bool = false,
    has_layout: bool = false,
    _padding: u4 = 0,
};

// what an entry can be, one row per tag: its name, its decoded payload, what it is built from and
// its properties. `Tag`, `Key` and the lookups are generated from here, a new kind of entry is one
// new row. a row with a fifth element shares the key of that tag (a pointer's mutability is a tag)
const tag_table = .{
    .{ "int_type", IntType, .leaf, TagProperties{
        .is_type = true,
        .is_integer = true,
        .has_layout = true,
    } },
    .{ "float_type", FloatType, .leaf, TagProperties{
        .is_type = true,
        .is_float = true,
        .has_layout = true,
    } },
    .{ "simple_type", SimpleType, .leaf, TagProperties{ .is_type = true, .has_layout = true } },
    .{ "meta_type", MetaType, .leaf, TagProperties{ .is_type = true, .is_static_only = true } },
    .{ "array_type", ArrayType, .array, TagProperties{
        .is_type = true,
        .is_aggregate = true,
        .has_layout = true,
    } },
    .{ "pointer_type", PointerType, .pointer, TagProperties{
        .is_type = true,
        .is_pointer = true,
        .has_layout = true,
    } },
    .{ "mutable_pointer_type", PointerType, .pointer, TagProperties{
        .is_type = true,
        .is_pointer = true,
        .has_layout = true,
    }, "pointer_type" },
    .{ "slice_type", SliceType, .slice, TagProperties{
        .is_type = true,
        .is_aggregate = true,
        .has_layout = true,
    } },
    .{ "function_type", FunctionType, .function, TagProperties{
        .is_type = true,
        .is_callable = true,
        .has_layout = true,
    } },
    .{ "record_type", RecordType, .leaf, TagProperties{
        .is_type = true,
        .is_aggregate = true,
        .is_nominal = true,
        .has_layout = true,
    } },
    .{ "variant_type", VariantType, .leaf, TagProperties{
        .is_type = true,
        .is_nominal = true,
        .is_variant = true,
        .has_layout = true,
    } },
    .{ "variant_case_type", VariantCaseType, .leaf, TagProperties{
        .is_type = true,
        .is_variant = true,
        .has_layout = true,
    } },
    .{ "unified_variant_type", UnifiedVariantType, .unified_variants, TagProperties{
        .is_type = true,
        .is_variant = true,
        .has_layout = true,
    } },
    // made of concrete types only, a leaf of the walks
    .{ "variant_subset_type", VariantSubsetType, .leaf, TagProperties{
        .is_type = true,
        .is_variant = true,
        .has_layout = true,
    } },
    .{ "trait_type", TraitType, .leaf, TagProperties{
        .is_type = true,
        .is_nominal = true,
        .is_trait = true,
        .is_static_only = true,
    } },
    .{ "static_function", StaticFunction, .leaf, TagProperties{
        .is_value = true,
        .is_callable = true,
        .is_static_only = true,
    } },
    .{ "template_type", DeclPool.Index, .leaf, TagProperties{
        .is_type = true,
        .is_static_only = true,
    } },
    .{ "type_variable", TypeVariables.Index, .leaf, TagProperties{ .is_type = true } },
    .{ "ast_type", AstType, .tree, TagProperties{ .is_type = true, .is_static_only = true } },
    .{ "int_value", IntValue, .leaf, TagProperties{ .is_value = true } },
    .{ "float_value", FloatValue, .leaf, TagProperties{ .is_value = true } },
    .{ "simple_value", SimpleValue, .leaf, TagProperties{ .is_value = true } },
    .{ "string_value", []const u8, .leaf, TagProperties{ .is_value = true } },
    .{ "aggregate_value", AggregateValue, .leaf, TagProperties{ .is_value = true } },
    .{ "variant_value", VariantValue, .leaf, TagProperties{ .is_value = true } },
    .{ "function_value", DeclPool.Index, .leaf, TagProperties{
        .is_value = true,
        .is_callable = true,
    } },
    .{ "tree_value", TreeValue, .leaf, TagProperties{ .is_value = true } },
};

pub const Tag = blk: {
    var names: [tag_table.len][]const u8 = undefined;
    var values: [tag_table.len]u8 = undefined;
    for (tag_table, 0..) |row, i| {
        names[i] = row[0];
        values[i] = i;
    }
    break :blk @Enum(u8, .exhaustive, &names, &values);
};

// an entry decoded, never stored: storage is always the packed `Item`
pub const Key = blk: {
    var count = 0;
    var names: [tag_table.len][]const u8 = undefined;
    var types: [tag_table.len]type = undefined;
    for (tag_table) |row| if (row.len == 4) {
        names[count] = row[0];
        types[count] = row[1];
        count += 1;
    };
    const KeyTag = @Enum(u8, .exhaustive, names[0..count], &std.simd.iota(u8, count));
    break :blk @Union(.auto, KeyTag, names[0..count], types[0..count], &@splat(.{}));
};

const properties_of_tag = blk: {
    var table: [tag_table.len]TagProperties = undefined;
    for (tag_table, 0..) |row, i| table[i] = row[3];
    break :blk table;
};

const composition_of_tag = blk: {
    var table: [tag_table.len]Composition = undefined;
    for (tag_table, 0..) |row, i| table[i] = row[2];
    break :blk table;
};

fn is_nominal_key(comptime key_tag: std.meta.Tag(Key)) bool {
    return properties_of_tag[@backingInt(@field(Tag, @tagName(key_tag)))].is_nominal;
}

// one stored entry is only 5 bytes: a tag and one u32. small payloads live directly in `data`
// (a pointer type stores its pointee there, a type variable its index), bigger payloads store an
// offset into `payload_words`. no pointers, no allocation per type, the scheme of zig's InternPool
pub const Item = struct {
    tag: Tag,
    data: u32,
};

// the functions answering questions about entries live in static_pool/, by topic
pub const is_concrete = type_queries.is_concrete;
pub const through_pointer = type_queries.through_pointer;
pub const template_of = type_queries.template_of;
pub const trait_of = type_queries.trait_of;
pub const is_realized_per_type = type_queries.is_realized_per_type;
pub const packed_of = type_queries.packed_of;
pub const realized_for = type_queries.realized_for;
pub const is_parameter_only = type_queries.is_parameter_only;
pub const contains_parameter_only = type_queries.contains_parameter_only;
pub const contains_template = type_queries.contains_template;
pub const has_open_type_variable = type_queries.has_open_type_variable;
pub const is_poisoned = type_queries.is_poisoned;
pub const is_length_generic = type_queries.is_length_generic;
pub const has_only_template_parameters = type_queries.has_only_template_parameters;
pub const is_generic_parameter = type_queries.is_generic_parameter;
pub const unwrapped = type_queries.unwrapped;
pub const nominal_declaration = type_queries.nominal_declaration;
pub const argument_length = type_queries.argument_length;
pub const payload_of = type_queries.payload_of;
pub const is_element_pointer = type_queries.is_element_pointer;
pub const element_type = type_queries.element_type;
pub const implements = type_queries.implements;
pub const tag_type_of = type_queries.tag_type_of;
pub const stored_tag_type = type_queries.stored_tag_type;
pub const lookup_member = type_queries.lookup_member;
pub const first_payload_case = type_queries.first_payload_case;
pub const is_field_tagged = type_queries.is_field_tagged;
pub const fallback_case = type_queries.fallback_case;
pub const niche_case = type_queries.niche_case;
pub const single_payload = type_queries.single_payload;
pub const fits = type_queries.fits;
pub const ast_type_of = type_queries.ast_type_of;
pub const is_tree = type_queries.is_tree;
pub const contains_trees = type_queries.contains_trees;
pub const holds_function_value = type_queries.holds_function_value;
pub const holds_address = type_queries.holds_address;
pub const is_untagged = type_queries.is_untagged;
pub const is_untagged_at_run_time = type_queries.is_untagged_at_run_time;
pub const is_member = type_queries.is_member;
pub const holds_untagged_variant = type_queries.holds_untagged_variant;
pub const zero_unit = type_queries.zero_unit;
pub const holds_unzeroable = type_queries.holds_unzeroable;
pub const is_unstorable = type_queries.is_unstorable;
pub const tag_range = type_layouts.tag_range;
pub const unified_offset = type_layouts.unified_offset;
pub const Room = type_layouts.Room;
pub const payload_room = type_layouts.payload_room;
pub const field_offset = type_layouts.field_offset;
pub const is_bit_packed = type_layouts.is_bit_packed;
pub const field_bits = type_layouts.field_bits;
pub const field_bit_offset = type_layouts.field_bit_offset;
pub const is_bit_field = type_layouts.is_bit_field;
pub const brings_cases = type_layouts.brings_cases;
pub const case_tag = type_layouts.case_tag;
pub const tag_in = type_layouts.tag_in;
pub const unified_tag_type = type_layouts.unified_tag_type;
pub const layout = type_layouts.layout;
pub const smallest_tag_type = type_layouts.smallest_tag_type;
pub const unify = type_relations.unify;
pub const coercion = type_relations.coercion;
pub const join = type_relations.join;
pub const unified_of = type_relations.unified_of;
pub const difference_of = type_relations.difference_of;
pub const difference_by_units = type_relations.difference_by_units;
pub const whole_of = type_relations.whole_of;
pub const push_units = type_relations.push_units;
pub const units_covered = type_relations.units_covered;
pub const covers_unit = type_relations.covers_unit;
pub const is_removed = type_relations.is_removed;
pub const cast_kind = type_relations.cast_kind;
pub const substitute_type_variables = type_relations.substitute_type_variables;
pub const occurs_in = type_relations.occurs_in;
pub const format = type_formatting.format;

allocator: std.mem.Allocator,

// tags and data in two arrays: asking "what kind is entry i" never pulls the data into cache
items: StructOfArrays(Item),

// variable-length payloads (parameter lists, field lists, ...) as flat u32 runs
payload_words: DynamicBuffer(u32),

string_bytes: DynamicBuffer(u8),

// one bit per entry: the type contains a type variable somewhere inside. set once when interned,
// it lets `substitute_type_variables` skip every variable-free type, which is almost all of them
type_variable_bits: DynamicBuffer(u64),

// the dedupe table stores only the 4-byte index per slot: the key stays in items/payload_words
// and is compared through `KeyAdapter`, small slots make probing fast
deduplication: std.HashMapUnmanaged(
    Index,
    void,
    IndexContext,
    std.hash_map.default_max_load_percentage,
),

// memoized layouts, one row per entry, filled the first time a size is asked
layouts: StructOfArrays(Layout),

// lists rebuilt by `substitute_type_variables`, nested ones stack above, read by index as the
// buffer may move
scratch: DynamicBuffer(Index),

// placeholders for types not known yet and what they turned out to be
type_variables: TypeVariables,

pub const IndexContext = struct {
    pool: *const StaticPool,

    pub fn hash(context: IndexContext, index: Index) u64 {
        return KeyAdapter.hash(.{ .pool = context.pool }, context.pool.get(index));
    }

    pub fn eql(context: IndexContext, a: Index, b: Index) bool {
        _ = context;
        return a == b;
    }
};

pub const KeyAdapter = struct {
    pool: *const StaticPool,

    pub fn hash(adapter: KeyAdapter, key: Key) u64 {
        _ = adapter;
        var hasher = std.hash.Wyhash.init(@backingInt(std.meta.activeTag(key)));
        switch (key) {
            inline else => |payload, key_tag| if (comptime is_nominal_key(key_tag))
                feed(&hasher, payload.declaration)
            else
                feed(&hasher, payload),
        }
        return hasher.final();
    }

    pub fn eql(adapter: KeyAdapter, key: Key, index: Index) bool {
        const stored = adapter.pool.get(index);
        if (std.meta.activeTag(key) != std.meta.activeTag(stored)) return false;
        return switch (key) {
            inline else => |payload, key_tag| deep_eql(payload, @field(stored, @tagName(key_tag))),
        };
    }
};

fn feed(hasher: *std.hash.Wyhash, value: anytype) void {
    switch (@typeInfo(@TypeOf(value))) {
        .@"struct" => |info| inline for (info.field_names) |fname| {
            feed(hasher, @field(value, fname));
        },
        .pointer => for (value) |item| feed(hasher, item),
        else => hasher.update(std.mem.asBytes(&word64(value))),
    }
}

fn deep_eql(a: anytype, b: @TypeOf(a)) bool {
    switch (@typeInfo(@TypeOf(a))) {
        .@"struct" => |info| {
            inline for (info.field_names) |fname| {
                if (!deep_eql(@field(a, fname), @field(b, fname))) return false;
            }
            return true;
        },
        .pointer => return std.mem.eql(std.meta.Child(@TypeOf(a)), a, b),
        else => return word64(a) == word64(b),
    }
}

fn word64(value: anytype) u64 {
    return switch (@typeInfo(@TypeOf(value))) {
        .@"enum" => @intCast(@backingInt(value)),
        .bool => @intFromBool(value),
        .float => @bitCast(value),
        else => @intCast(value),
    };
}

fn is_list(comptime T: type) bool {
    return @typeInfo(T) == .pointer;
}

// generic encoding: an enum payload lives in `data`, a list is `len, items..`, a struct is
// `scalars.., list lengths.., list items..` in payload_words (u64 / f64 scalars take two words)
fn put(self: *StaticPool, payload: anytype) u32 {
    const T = @TypeOf(payload);
    const at = self.payload_words.len;
    switch (@typeInfo(T)) {
        .@"enum" => return @intCast(@backingInt(payload)),
        .pointer => {
            self.payload_words.push(@intCast(payload.len));
            for (payload) |item| self.payload_words.push(@intCast(word64(item)));
        },
        .@"struct" => |info| {
            const names = info.field_names;
            const types = info.field_types;
            inline for (names, types) |fname, ftype| if (!comptime is_list(ftype)) {
                const word = word64(@field(payload, fname));
                self.payload_words.push(@truncate(word));
                if (@sizeOf(ftype) == 8) self.payload_words.push(@intCast(word >> 32));
            };
            inline for (names, types) |fname, ftype| if (comptime is_list(ftype)) {
                self.payload_words.push(@intCast(@field(payload, fname).len));
            };
            inline for (names, types) |fname, ftype| if (comptime is_list(ftype)) {
                for (@field(payload, fname)) |item| {
                    self.payload_words.push(@intCast(word64(item)));
                }
            };
        },
        else => @compileError("no encoding for " ++ @typeName(T)),
    }
    return at;
}

fn take(self: *const StaticPool, comptime T: type, data: u32) T {
    const words = self.payload_words.buffer;
    switch (@typeInfo(T)) {
        .@"enum" => return @fromBackingInt(@intCast(data)),
        .pointer => return @ptrCast(words[data + 1 ..][0..words[data]]),
        .@"struct" => |info| {
            const names = info.field_names;
            const types = info.field_types;
            var result: T = undefined;
            var at = data;
            inline for (names, types) |fname, ftype| if (!comptime is_list(ftype)) {
                const low: u64 = words[at];
                const wide = @sizeOf(ftype) == 8;
                const word = if (wide) low | @as(u64, words[at + 1]) << 32 else low;
                at += if (wide) 2 else 1;
                @field(result, fname) = switch (@typeInfo(ftype)) {
                    .@"enum" => @fromBackingInt(@intCast(word)),
                    .bool => word != 0,
                    .float => @bitCast(word),
                    else => @intCast(word),
                };
            };
            var list_lengths: [types.len]u32 = undefined;
            inline for (types, 0..) |ftype, j| if (comptime is_list(ftype)) {
                list_lengths[j] = words[at];
                at += 1;
            };
            inline for (names, types, 0..) |fname, ftype, j| if (comptime is_list(ftype)) {
                @field(result, fname) = @ptrCast(words[at..][0..list_lengths[j]]);
                at += list_lengths[j];
            };
            return result;
        },
        else => @compileError("no decoding for " ++ @typeName(T)),
    }
}

fn push_item(self: *StaticPool, item: Item, holds_type_variables: bool) Index {
    const i = self.items.len();
    if (i % 64 == 0) self.type_variable_bits.push(0);
    const bit = @as(u64, @intFromBool(holds_type_variables)) << @intCast(i % 64);
    self.type_variable_bits.buffer[i / 64] |= bit;
    self.items.push(item);
    self.layouts.push(.{
        .size = 0,
        .align_log2 = 0,
        .state = .unknown,
        .niche = std.mem.zeroes(Layout.Niche),
    });
    return @fromBackingInt(i);
}

fn any_type_variables(self: *const StaticPool, payload: anytype) bool {
    const T = @TypeOf(payload);
    if (T == Index) return payload != .none and self.has_type_variables(payload);
    if (T == []const Index) {
        for (payload) |item| if (self.has_type_variables(item)) return true;
        return false;
    }
    if (@typeInfo(T) != .@"struct") return false;
    inline for (@typeInfo(T).@"struct".field_names) |fname| {
        if (self.any_type_variables(@field(payload, fname))) return true;
    }
    return false;
}

fn encode(self: *StaticPool, key: Key, string_type: Index) Item {
    return switch (key) {
        .pointer_type => |pointer| .{
            .tag = if (pointer.is_mutable) .mutable_pointer_type else .pointer_type,
            .data = @backingInt(pointer.pointee),
        },
        .string_value => |bytes| blk: {
            const at = self.payload_words.len;
            const header = [_]u32{
                self.string_bytes.len,
                @intCast(bytes.len),
                @backingInt(string_type),
            };
            self.payload_words.append(&header);
            if (bytes.len > 0) self.string_bytes.append(bytes);
            break :blk .{ .tag = .string_value, .data = at };
        },
        // the tag a key encodes into, the first row naming it
        inline else => |payload, key_tag| .{
            .tag = @field(Tag, @tagName(key_tag)),
            .data = self.put(payload),
        },
    };
}

pub fn init(allocator: std.mem.Allocator) StaticPool {
    var self = StaticPool{
        .allocator = allocator,
        .items = .init(allocator, 1024),
        .payload_words = .init(allocator, 4096),
        .string_bytes = .init(allocator, 1024),
        .type_variable_bits = .init(allocator, 16),
        .deduplication = .empty,
        .layouts = .init(allocator, 1024),
        .scratch = .init(allocator, 64),
        .type_variables = .init(allocator),
    };
    // the fixed entries, in the order of `Index`
    for ([_]u16{ 8, 16, 32, 64, 8, 16, 32, 64 }, 0..) |bits, i| {
        const signedness: IntType.Signedness = if (i < 4) .unsigned else .signed;
        _ = self.intern(.{ .int_type = .{ .signedness = signedness, .bits = bits } });
    }
    for ([_]u16{ 16, 32, 64 }) |bits| _ = self.intern(.{ .float_type = .{ .bits = bits } });
    inline for (@typeInfo(SimpleType).@"enum".field_values) |fvalue| {
        _ = self.intern(.{ .simple_type = @fromBackingInt(fvalue) });
    }
    inline for (@typeInfo(MetaType).@"enum".field_values) |fvalue| {
        _ = self.intern(.{ .meta_type = @fromBackingInt(fvalue) });
    }
    inline for (@typeInfo(SimpleValue).@"enum".field_values) |fvalue| {
        _ = self.intern(.{ .simple_value = @fromBackingInt(fvalue) });
    }
    _ = self.intern(.{ .ast_type = .{ .produces = .none, .root_kind = 0 } });
    for ([_]IntType.Signedness{ .unsigned, .signed }) |signedness| for (Index.odd_widths) |bits| {
        _ = self.intern(.{ .int_type = .{ .signedness = signedness, .bits = bits } });
    };
    std.debug.assert(self.items.len() == Index.first_dynamic);
    return self;
}

pub fn deinit(self: *StaticPool) void {
    self.items.deinit();
    self.payload_words.deinit();
    self.string_bytes.deinit();
    self.type_variable_bits.deinit();
    self.deduplication.deinit(self.allocator);
    self.layouts.deinit();
    self.scratch.deinit();
    self.type_variables.deinit();
}

pub fn intern(self: *StaticPool, key: Key) Index {
    // a string knows its own `[n]u8` type, interned before the map is touched
    const string_type = if (key == .string_value) self.intern(.{ .array_type = .{
        .length = self.intern(.{ .int_value = .{
            .value_type = .u64_type,
            .bits = key.string_value.len,
        } }),
        .element = .u8_type,
    } }) else .none;
    const found = self.deduplication.getOrPutContextAdapted(
        self.allocator,
        key,
        KeyAdapter{ .pool = self },
        IndexContext{ .pool = self },
    ) catch @panic("OOM");
    if (found.found_existing) return found.key_ptr.*;

    const holds_type_variables = switch (key) {
        .type_variable => true,
        inline else => |payload, key_tag| if (comptime is_nominal_key(key_tag))
            false
        else
            self.any_type_variables(payload),
    };
    const index = self.push_item(self.encode(key, string_type), holds_type_variables);
    found.key_ptr.* = index;
    return index;
}

// a row for a nominal type before its members are known, so they can point back at it (`*Tree`).
// until `complete_nominal` writes it, the entry reads as poison
pub fn reserve_nominal(self: *StaticPool, declaration: DeclPool.Index) Index {
    _ = declaration;
    return self.push_item(.{ .tag = .simple_type, .data = @backingInt(SimpleType.poison) }, false);
}

pub fn complete_nominal(self: *StaticPool, reserved: Index, key: Key) void {
    const item = self.encode(key, .none);
    self.items.column(.tag)[@backingInt(reserved)] = item.tag;
    self.items.column(.data)[@backingInt(reserved)] = item.data;
    const context = IndexContext{ .pool = self };
    self.deduplication.putContext(self.allocator, reserved, {}, context) catch @panic("OOM");
}

pub fn get(self: *const StaticPool, index: Index) Key {
    const entry_tag = self.tag(index);
    const data = self.items.column(.data)[@backingInt(index)];
    return switch (entry_tag) {
        .pointer_type, .mutable_pointer_type => .{ .pointer_type = .{
            .pointee = @fromBackingInt(data),
            .is_mutable = entry_tag == .mutable_pointer_type,
        } },
        .string_value => {
            const start = self.payload_words.buffer[data];
            const len = self.payload_words.buffer[data + 1];
            return .{ .string_value = self.string_bytes.buffer[start..][0..len] };
        },
        inline else => |tag_value| blk: {
            // the key field a tag decodes into
            const row = tag_table[@backingInt(tag_value)];
            const field_name = if (row.len > 4) row[4] else row[0];
            break :blk @unionInit(Key, field_name, self.take(@FieldType(Key, field_name), data));
        },
    };
}

pub fn tag(self: *const StaticPool, index: Index) Tag {
    return self.items.column(.tag)[@backingInt(index)];
}

pub inline fn properties(self: *const StaticPool, index: Index) TagProperties {
    return properties_of_tag[@backingInt(self.tag(index))];
}

pub inline fn composition(self: *const StaticPool, index: Index) Composition {
    return composition_of_tag[@backingInt(self.tag(index))];
}

pub fn has_type_variables(self: *const StaticPool, index: Index) bool {
    const i = @backingInt(index);
    return (self.type_variable_bits.buffer[i / 64] >> @intCast(i % 64)) & 1 != 0;
}

pub fn is_pointer(self: *const StaticPool, type_index: Index) bool {
    if (type_index == .none) return false;
    return self.tag(type_index) == .pointer_type or self.tag(type_index) == .mutable_pointer_type;
}

// the pointee of a pointer type, any other type itself
pub fn pointee(self: *const StaticPool, type_index: Index) Index {
    if (!self.is_pointer(type_index)) return type_index;
    return @fromBackingInt(self.items.column(.data)[@backingInt(type_index)]);
}

pub fn array_element(self: *const StaticPool, type_index: Index) Index {
    if (type_index == .none or self.tag(type_index) != .array_type) return .none;
    return self.get(type_index).array_type.element;
}

pub fn is_numeric(self: *const StaticPool, type_index: Index) bool {
    if (type_index == .none) return false;
    return self.properties(type_index).is_integer or self.properties(type_index).is_float;
}

pub fn pointer_to(self: *StaticPool, pointee_type: Index, is_mutable: bool) Index {
    return self.intern(.{ .pointer_type = .{ .pointee = pointee_type, .is_mutable = is_mutable } });
}

pub fn array_of(self: *StaticPool, length: u64, element: Index) Index {
    const length_value = self.intern(.{ .int_value = .{
        .value_type = .u64_type,
        .bits = length,
    } });
    return self.intern(.{ .array_type = .{ .length = length_value, .element = element } });
}

// the length of an array type when it is static
pub fn static_length(self: *const StaticPool, type_index: Index) ?u64 {
    if (type_index == .none or type_index == .poison_type) return null;
    if (self.tag(type_index) != .array_type) return null;
    const length = self.get(type_index).array_type.length;
    return if (self.tag(length) == .int_value) self.get(length).int_value.bits else null;
}

pub fn fresh_type_variable(self: *StaticPool, origin: u32) Index {
    return self.intern(.{ .type_variable = self.type_variables.create(origin) });
}

pub fn field_type(self: *const StaticPool, record: Index, field: usize) Index {
    if (self.tag(record) == .slice_type) {
        return if (field == 0) self.get(record).slice_type.pointer else .u64_type;
    }
    return self.get(record).record_type.field_types[field];
}

pub fn slice_of(self: *StaticPool, element: Index) Index {
    const pointer = self.pointer_to(element, true);
    return self.intern(.{ .slice_type = .{ .element = element, .pointer = pointer } });
}

pub fn trait_method_declaration(
    self: *const StaticPool,
    method: @FieldType(Member, "trait_method"),
) DeclPool.Index {
    return self.get(method.trait).trait_type.declaration.member(method.index);
}

// the type of a static value, a type's type is its meta type
pub fn type_of(self: *const StaticPool, value: Index) Index {
    const data = self.items.column(.data)[@backingInt(value)];
    return switch (self.tag(value)) {
        .int_value, .float_value, .aggregate_value, .variant_value, .tree_value => {
            return @fromBackingInt(self.payload_words.buffer[data]);
        },
        .string_value => @fromBackingInt(self.payload_words.buffer[data + 2]),
        .simple_value => if (data == @backingInt(SimpleValue.unit)) .unit_type else .bool_type,
        .function_value => .fun_type,
        .static_function => .stcfun_type,
        .trait_type => .trait_type,
        .variant_type, .unified_variant_type, .variant_subset_type => .variant_type,
        .int_type, .float_type, .simple_type, .meta_type, .array_type => .type_type,
        .pointer_type, .mutable_pointer_type, .function_type, .record_type => .type_type,
        .slice_type => .type_type,
        .variant_case_type, .template_type, .type_variable, .ast_type => .type_type,
    };
}
