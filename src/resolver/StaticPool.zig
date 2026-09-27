const std = @import("std");
const Resolver = @import("../Resolver.zig");
const AbstractPool = @import("AbstractPool.zig");
const SoD = @import("../ds/dynbuf.zig").SoD;
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;

// this is the classical "Pool", where a compiler stores all non-runtime (here called "static"/`stc`)
//   values.
const StaticPool = @This();

// types whose value either does not exist, or is not needed to be stored (like booleans)
pub const SimpleType = enum(u8) { bool, unit, runit, never, poison };
pub const SimpleValue = enum(u8) { bool_true, bool_false, unit };
pub const TypeType = enum(u8) { type, trait, variant, fun, stcfun, inlfun };

pub const FunType = struct {
    category: Category,
    params: []const Index,
    ret: Index,
    // not part: parameter names, defaults or where-clauses

    pub const Category = enum(u8) { default, static, inlined };
};

pub const VariantTagMode = enum(u8) { none, int, self };

pub const IntType = struct {
    signedness: Signedness,
    bits: u16,
    pub const Signedness = enum(u1) { unsigned, signed };
};

pub const FloatType = struct { bits: u16 };

// array-length is a pool entry and not a plain number
// - either lengthed (static int), or unlengthed (type var)
// - as parameter: length set per call
pub const ArrayType = struct { len: Index, elem: Index };
pub const PtrType = struct { child: Index, mutable: bool };

pub const CustomType = struct {
    decl: Resolver.Decl.Index,
    is_packed: bool,
    field_names: []const Resolver.NamePool.Index,
    field_types: []const Index,
    traits: []const Index,
    // read from ast on demand: field mutability, defaults and where-clauses
};

pub const VariantType = struct {
    decl: Resolver.Decl.Index,
    tag_mode: VariantTagMode,
    tag_type: Index,
    is_unionsized: bool,
    cases: []const Index,
    traits: []const Index,
};

pub const SubVariantType = struct {
    variant: Index,
    case: u32,
    name: Resolver.NamePool.Index,
    tag: Index,
    payload: Index,
};

pub const TraitType = struct {
    decl: Resolver.Decl.Index,
    member_names: []const Resolver.NamePool.Index,
    member_types: []const Index,
    supers: []const Index,
};

pub const StaticFun = struct {
    decl: Resolver.Decl.Index,
    result_kind: TypeType,
};

// ints and floats are max 64 bit here
pub const IntValue = struct { ty: Index, bits: u64 };
pub const FloatValue = struct { ty: Index, value: f64 };
pub const Aggregate = struct { ty: Index, elems: []const Index };
pub const VariantValue = struct { case: Index, payload: Index };

pub const Layout = struct {
    size: u64,
    align_log2: u8,
    state: State,
    niche: Niche,

    pub const State = enum(u8) { unknown, in_progress, done, infinite };

    // invalid bit patterns of a type that a self-tagged variant (`tagof self`) can use to
    // encode its other cases without an extra tag byte (e.g. 0xFF in `Opt8`).
    pub const Niche = struct {
        offset: u32,
        bits: u8,
        start: u64,
        count: u64,
    };
};

pub const Member = union(enum) {
    none,
    field: struct { index: u32, ty: Index },
    method: Resolver.Decl.Index,
    trait_method: struct { trait: Index, index: u32 },
    case: Index,
    builtin_len,
    builtin_init,
    builtin_deinit,
};

pub const UnifyResult = enum(u8) { ok, mismatch, infinite };

// how a value of one type may be used where another type is expected, without `as`.
pub const CoercionKind = enum(u8) {
    identity,
    unified,
    never_to_any,
    poison,
    int_widen,
    float_widen,
    string_to_ptr,
    ptr_mut_to_ptr,
    case_to_variant,
    payload_to_self_tagged,
    variant_to_union,
    unit_to_runit,
    incompatible,
};

// what an explicit `as` does.
pub const CastKind = enum(u8) {
    identity,
    int_resize,
    int_to_float,
    float_to_int,
    float_resize,
    bit_reinterpret,
    variant_retag,
    payload_wrap,
    pointer_relength,
    invalid,
};

pub const JoinResult = struct {
    ty: Index,
    left: CoercionKind,
    right: CoercionKind,
};

// - every static (non-runtime) value is a u32 index into the pool
// - the first entries are fixed, so `u8`, `bool`, ... are known without any lookup and
// - types are first-class, share pool with values
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
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(Index.unit_value) + 1;
};

// one stored entry is only 5 bytes: a tag and one u32.
// small payloads live directly in `data` (a pointer type stores its child type there,
// a type var its AbstractPool.Index). bigger payloads store an offset into `Pool.extra`, a flat u32 array.
// fixed-size entries mean: no pointers, no allocation per type, indexing is one multiply,
// and the whole pool is a few flat arrays the cpu can prefetch. same scheme as zig's InternPool.
pub const Item = struct {
    tag: Tag,
    data: u32,

    pub const Tag = enum(u8) {
        int_type,
        float_type,
        simple_type,
        meta_type,
        array_type,
        ptr_type,
        ptr_mut_type,
        function_type,
        record_type,
        variant_type,
        variant_case_type,
        variant_union_type,
        trait_type,
        generic,
        type_var,
        int_value,
        float_value,
        simple_value,
        string_value,
        aggregate_value,
        variant_value,
        function_value,
    };
};

// never stored: storage is always the packed form
pub const Key = union(enum) {
    int_type: IntType,
    float_type: FloatType,
    simple_type: SimpleType,
    meta_type: TypeType,
    array_type: ArrayType,
    ptr_type: PtrType,
    function_type: FunType,
    custom_type: CustomType,
    variant_type: VariantType,
    variant_case_type: SubVariantType,
    variant_union_type: []const Resolver.Index,
    trait_type: TraitType,
    static_fun: StaticFun,
    abstract_type: AbstractPool.Index,
    int: IntValue,
    float: FloatValue,
    simple_value: SimpleValue,
    string: []const u8,
    aggregate: Aggregate,
    variant_value: VariantValue,
    function: Resolver.Decl.Index,
};

// needed to map templates / generics to realizations
// - e.g. of a `stcfun`, or of a function with unlengthed array param., or abstract types
// - since the arguments are one pool index, the whole key is 8 bytes and compares as one.
pub const AbstractKey = packed struct(u64) {
    generic_tuple: Resolver.Decl.Index,
    args_tuple: Resolver.Index, // due to them being a single `static_pool` index
};

// cheap yes/no questions about an entry ("is it a pointer?", "is it an integer?").
// they depend almost only on the tag, so they come from a comptime table indexed by tag
// instead of being stored per entry: zero memory, one table load.
pub const Class = packed struct(u16) {
    is_type: bool = false,
    is_value: bool = false,
    is_integer: bool = false,
    is_float: bool = false,
    is_pointer: bool = false,
    is_aggregate: bool = false,
    is_nominal: bool = false,
    is_variant: bool = false,
    is_trait: bool = false,
    is_callable: bool = false,
    is_static_only: bool = false,
    has_layout: bool = false,
    _pad: u4 = 0,
};

alloc: std.mem.Allocator,

// struct-of-arrays: tags and data live in two separate arrays. code that only asks
// "what kind is entry i" reads one byte per entry and never pulls the data into cache.
items: SoD(Item),

// variable-length payloads (parameter lists, field lists, ...) as flat u32 runs.
extra: DynBuf(u32),

// bytes of string values.
bytes: DynBuf(u8),

// one bit per entry: does this type contain a type var somewhere inside?
// set once when the entry is interned (a type contains vars if any child does).
// lets `apply_vars` skip every var-free type in O(1) - which is almost all of them.
var_bits: DynBuf(u64),

// the dedupe table. it stores only the 4-byte index per slot; the key itself stays in
// items/extra and is compared through the adapter below. small slots = more slots per
// cache line = faster probing.
map: std.HashMapUnmanaged(Index, void, IndexContext, std.hash_map.default_max_load_percentage),

// memoized layouts, one row per pool entry, filled lazily the first time a size is asked.
// most types (all static-only ones) never get asked, so they cost nothing but the row.
layouts: SoD(Layout),

// FROM Resolver originally
// covers templates / generics -> resulting type / function / value.
// - covers `stcfun` calls and functions compiled per array length (args = the tuple of lengths).
realized_abstracts: std.AutoHashMapUnmanaged(AbstractKey, Index),

pub const IndexContext = struct {
    pool: *const StaticPool,

    pub fn hash(ctx: IndexContext, index: Index) u64 {
        // hash the decoded key of index, must equal KeyAdapter.hash of the same key
        _ = .{ ctx, index };
        @panic("unimplemented");
    }

    pub fn eql(ctx: IndexContext, a: Index, b: Index) bool {
        // entries are unique, so equal keys means equal indices
        _ = .{ ctx, a, b };
        @panic("unimplemented");
    }
};

pub const KeyAdapter = struct {
    pool: *const StaticPool,

    pub fn hash(adapter: KeyAdapter, key: Key) u64 {
        // hash tag + every field + every list element
        // nominal types (record / variant / trait) hash only their decl, which is unique anyway
        _ = .{ adapter, key };
        @panic("unimplemented");
    }

    pub fn eql(adapter: KeyAdapter, key: Key, index: Index) bool {
        // compare key with the stored entry without decoding it into allocated memory
        _ = .{ adapter, key, index };
        @panic("unimplemented");
    }
};

pub fn init(alloc: std.mem.Allocator) StaticPool {
    // create all buffers and intern the fixed entries in exact Index order
    // figure out: assert once (debug builds) that every fixed entry landed on its enum value
    _ = alloc;
    @panic("unimplemented");
}

pub fn deinit(self: *StaticPool) void {
    _ = self;
    @panic("unimplemented");
}

pub fn intern(self: *StaticPool, key: Key) Index {
    // getOrPutAdapted with KeyAdapter; on a miss encode key into one item + extra words
    // lists inside the key are copied into extra, strings into bytes, and the var bit is set
    // figure out: the exact encoding per tag (what goes into data, what into extra)
    // future (multithreading): per-thread shards of the pool, or a lock around intern
    _ = .{ self, key };
    @panic("unimplemented");
}

pub fn reserve_nominal(self: *StaticPool, decl: Resolver.Decl.Index) Index {
    // push an entry for a record / variant / trait before its fields are known, so a
    // recursive type (`*Tree` inside Tree) can already point at itself
    _ = .{ self, decl };
    @panic("unimplemented");
}

pub fn complete_nominal(self: *StaticPool, reserved: Index, key: Key) void {
    // fill the reserved entry, then insert it into the map
    _ = .{ self, reserved, key };
    @panic("unimplemented");
}

pub fn get(self: *const StaticPool, index: Index) Key {
    // decode item + extra into a key
    // figure out: lists in the returned key point into extra and are invalidated when extra grows - copy, or never intern while holding them
    _ = .{ self, index };
    @panic("unimplemented");
}

pub fn tag(self: *const StaticPool, index: Index) Item.Tag {
    _ = .{ self, index };
    @panic("unimplemented");
}

pub fn has_vars(self: *const StaticPool, index: Index) bool {
    // one bit test in var_bits
    _ = .{ self, index };
    @panic("unimplemented");
}

pub fn type_of(self: *const StaticPool, value: Index) Index {
    // type of a static value; types themselves are values of type_type / trait_type / variant_type
    _ = .{ self, value };
    @panic("unimplemented");
}

// ------------------------------------------------------------------------------------------ //
// 5. questions about a type
// ------------------------------------------------------------------------------------------ //

pub fn class(self: *const StaticPool, index: Index) Class {
    // comptime table lookup by tag
    _ = .{ self, index };
    @panic("unimplemented");
}

pub fn implements(self: *const StaticPool, ty: Index, trait: Index) bool {
    // scan the type's trait list and recurse into supers; lists are tiny, no precomputed closure needed
    // generic traits (`Comparable(Money)`) compare as instances, not as the generic
    _ = .{ self, ty, trait };
    @panic("unimplemented");
}

pub fn lookup_member(self: *StaticPool, ty: Index, name: Index) Member {
    // field, own method, trait method, variant case, builtin (len / init / deinit)
    // auto-deref like zig: a pointer is looked through once before searching
    // figure out: `$0` names for unnamed fields
    _ = .{ self, ty, name };
    @panic("unimplemented");
}

pub fn layout(self: *StaticPool, ty: Index) Layout {
    // memoized in `layouts`; in_progress while computing detects infinite by-value types
    // figure out: target pointer width - pass a target description into the pool
    // figure out: `tagof self` niche search, tag type when no `tagof` is given, `++(` vs `+(` sizes
    _ = .{ self, ty };
    @panic("unimplemented");
}

pub fn field_offset(self: *StaticPool, record: Index, field: u32) u64 {
    // figure out: keep declaration order (c compatible) or reorder fields for smaller size
    _ = .{ self, record, field };
    @panic("unimplemented");
}

pub fn niche_of(self: *StaticPool, ty: Index) Layout.Niche {
    // invalid bit patterns of ty, e.g. 0xFF for `Opt8`'s None
    _ = .{ self, ty };
    @panic("unimplemented");
}

pub fn smallest_tag_type(case_count: u64) Index {
    _ = case_count;
    @panic("unimplemented");
}

pub fn fits(self: *const StaticPool, value: Index, ty: Index) bool {
    // does a static int / float value fit into ty without loss (used for literals)
    _ = .{ self, value, ty };
    @panic("unimplemented");
}

pub fn format(self: *const StaticPool, names: *const @import("NamePool.zig"), vars: *const AbstractPool, index: Index, writer: *std.Io.Writer) !void {
    // readable type name for diagnostics, unbound vars print as `?1`, `?2`, ...
    _ = .{ self, names, vars, index, writer };
    @panic("unimplemented");
}

// ------------------------------------------------------------------------------------------ //
// 6. relations between two types
// ------------------------------------------------------------------------------------------ //

pub fn unify(self: *StaticPool, vars: *AbstractPool, a: Index, b: Index) UnifyResult {
    // make a and b the same type, filling type vars on the way
    //   - follow both through `vars.find` first
    //   - a var on either side: bind it to the other side (after the occurs check)
    //   - same index: already equal (the common case, one compare)
    //   - both compound with the same tag (array, ptr, function, union): unify children pairwise,
    //     for arrays that includes the length, so an inferred length gets bound to the other side's length
    //   - anything else: mismatch
    _ = .{ self, vars, a, b };
    @panic("unimplemented");
}

pub fn coerce(self: *StaticPool, vars: *AbstractPool, from: Index, to: Index) CoercionKind {
    // implicit conversion (no `as` written) when a value of `from` is used where `to` is expected
    // if either side still contains vars, unify instead (inference decides, not conversion)
    // literals never come here, they take the expected type directly (checked with fits)
    // figure out: which of these are allowed - int / float widening (same signedness only?), string literal -> &u8, *T -> &T, case -> variant, payload -> self tagged, variant -> union, never -> anything
    // figure out: one step only, or chains like payload -> self tagged -> union
    _ = .{ self, vars, from, to };
    @panic("unimplemented");
}

pub fn join(self: *StaticPool, vars: *AbstractPool, a: Index, b: Index) JoinResult {
    // common type of two if / match branches
    // runit + T -> T, never + T -> T, unit + value -> runit_mixing, two cases of one variant -> the variant
    // a var on one side: unify
    _ = .{ self, vars, a, b };
    @panic("unimplemented");
}

pub fn cast(self: *StaticPool, from: Index, to: Index) CastKind {
    // classify an explicit `as`
    // figure out: allowed reinterpretations - float bits, retag (`reg as Register.AsLower`), pointer relength (`&[]u8 as &[n]u8`)
    _ = .{ self, from, to };
    @panic("unimplemented");
}

pub fn apply_vars(self: *StaticPool, vars: *AbstractPool, index: Index) Index {
    // rebuild index with every bound var replaced by its type ("zonking"); var-free types return immediately via has_vars
    _ = .{ self, vars, index };
    @panic("unimplemented");
}

pub fn occurs(self: *const StaticPool, vars: *AbstractPool, v: AbstractPool.Index, index: Index) bool {
    // does var v appear inside index? binding v to such a type would make it infinite (`?1 = []?1`)
    _ = .{ self, vars, v, index };
    @panic("unimplemented");
}
