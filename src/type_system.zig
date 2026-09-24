const std = @import("std");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const SoD = @import("ds/dynbuf.zig").SoD;

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
    empty_tuple,
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(Index.empty_tuple) + 1;
};

pub const TypeId = Index;
pub const ValueId = Index;

pub const NameId = enum(u32) {
    empty,
    underscore,
    dollar_it,
    self,
    init,
    deinit,
    main,
    len,
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(NameId.len) + 1;
};

pub const DeclId = enum(u32) { none = std.math.maxInt(u32), _ };
pub const MetaVarId = enum(u32) { none = std.math.maxInt(u32), _ };

pub const Span = struct { start: u32, len: u32 };

pub const Tag = enum(u8) {
    int_type,
    float_type,
    simple_type,
    meta_type,
    array_type,
    slice_type,
    ptr_type,
    ptr_mut_type,
    function_type,
    tuple_type,
    record_type,
    variant_type,
    variant_case_type,
    variant_union_type,
    trait_type,
    generic,
    metavar,
    int_value,
    float_value,
    simple_value,
    string_value,
    tuple_value,
    aggregate_value,
    variant_value,
    function_value,
    decl_ref_value,
};

pub const Item = struct {
    tag: Tag,
    data: u32,
};

pub const Signedness = enum(u1) { unsigned, signed };
pub const SimpleType = enum(u8) { bool, unit, runit, never, poison };
pub const SimpleValue = enum(u8) { bool_true, bool_false, unit };
pub const MetaKind = enum(u8) { type, trait, variant, fun, stcfun, inlfun };
pub const FnCategory = enum(u8) { default, static, inlined };
pub const TagMode = enum(u8) { none, int, self };

pub const IntType = struct { signedness: Signedness, bits: u16 };
pub const FloatType = struct { bits: u16 };
pub const ArrayType = struct { len: u64, elem: TypeId };
pub const PtrType = struct { child: TypeId, mutable: bool };

pub const FunctionType = struct {
    category: FnCategory,
    params: []const TypeId,
    ret: TypeId,
};

pub const RecordType = struct {
    decl: DeclId,
    is_packed: bool,
    fields: []const TypeId,
    field_info: Span,
    own_trait: TypeId,
    traits: []const TypeId,
};

pub const VariantType = struct {
    decl: DeclId,
    tag_mode: TagMode,
    tag_type: TypeId,
    is_unionsized: bool,
    cases: []const TypeId,
    own_trait: TypeId,
    traits: []const TypeId,
};

pub const VariantCaseType = struct {
    variant: TypeId,
    case: u32,
    name: NameId,
    tag: ValueId,
    payload: TypeId,
};

pub const TraitType = struct {
    decl: DeclId,
    member_names: []const NameId,
    member_types: []const TypeId,
    supers: []const TypeId,
};

pub const Generic = struct {
    decl: DeclId,
    params: []const TypeId,
    result_kind: MetaKind,
};

pub const IntValue = struct { ty: TypeId, bits: u64 };

pub const FloatValue = struct { ty: TypeId, value: f64 };
pub const Aggregate = struct { ty: TypeId, elems: []const ValueId };
pub const VariantValue = struct { case: TypeId, payload: ValueId };

pub const Key = union(enum) {
    int_type: IntType,
    float_type: FloatType,
    simple_type: SimpleType,
    meta_type: MetaKind,
    array_type: ArrayType,
    slice_type: TypeId,
    ptr_type: PtrType,
    function_type: FunctionType,
    tuple_type: []const TypeId,
    record_type: RecordType,
    variant_type: VariantType,
    variant_case_type: VariantCaseType,
    variant_union_type: []const TypeId,
    trait_type: TraitType,
    generic: Generic,
    metavar: MetaVarId,
    int: IntValue,
    float: FloatValue,
    simple_value: SimpleValue,
    string: []const u8,
    tuple: []const ValueId,
    aggregate: Aggregate,
    variant_value: VariantValue,
    function: DeclId,
    decl_ref: DeclId,
};

pub const FieldFlags = packed struct(u8) {
    is_mut: bool = false,
    is_unnamed: bool = false,
    has_default: bool = false,
    has_where: bool = false,
    has_where_else: bool = false,
    _pad: u3 = 0,
};

pub const FieldInfo = struct {
    name: NameId,
    flags: FieldFlags,
    default_node: u32,
    where_node: u32,
    where_else_node: u32,
};

pub const Class = packed struct(u16) {
    is_type: bool = false,
    is_value: bool = false,
    is_integer: bool = false,
    is_signed: bool = false,
    is_float: bool = false,
    is_pointer: bool = false,
    is_aggregate: bool = false,
    is_nominal: bool = false,
    is_variant: bool = false,
    is_trait: bool = false,
    is_callable: bool = false,
    is_static_only: bool = false,
    has_layout: bool = false,
    _pad: u3 = 0,
};

pub const LayoutState = enum(u8) { unknown, in_progress, done, infinite };

pub const Niche = struct {
    offset: u32,
    bits: u8,
    start: u64,
    count: u64,
};

pub const Layout = struct {
    size: u64,
    align_log2: u8,
    state: LayoutState,
    niche: Niche,
};

pub const Coercion = enum(u8) {
    identity,
    never_to_any,
    poison,
    int_widen,
    float_widen,
    array_to_slice,
    array_ptr_to_slice_ptr,
    ptr_mut_to_ptr,
    case_to_variant,
    payload_to_self_tagged,
    variant_to_union,
    unit_to_runit,
    incompatible,
};

pub const CastKind = enum(u8) {
    identity,
    int_resize,
    int_to_float,
    float_to_int,
    float_resize,
    bit_reinterpret,
    variant_retag,
    payload_wrap,
    pointer_reslice,
    trait_upcast,
    invalid,
};

pub const UnifyResult = enum(u8) { ok, mismatch, occurs, arity, static_mismatch };

pub const JoinResult = struct {
    ty: TypeId,
    left: Coercion,
    right: Coercion,
};

pub const Member = union(enum) {
    none,
    field: struct { index: u32, ty: TypeId },
    method: DeclId,
    trait_method: struct { trait: TypeId, index: u32 },
    case: TypeId,
    builtin_len,
    builtin_init,
    builtin_deinit,
};

pub fn HashIndex(comptime Id: type) type {
    return struct {
        hashes: []u32,
        slots: []Id,
        count: u32,
        mask: u32,

        pub const Probe = struct { slot: u32, found: bool };

        pub fn init(alloc: std.mem.Allocator, capacity_log2: u5) @This() {
            // allocate a power-of-two table, all slots empty (none)
            // figure out: store the u32 hash next to each slot so most mismatches skip the key compare
            // figure out: no deletion ever happens, so no tombstones are needed - confirm
            _ = .{ alloc, capacity_log2 };
            @panic("unimplemented");
        }

        pub fn deinit(self: *@This(), alloc: std.mem.Allocator) void {
            // free hashes and slots
            _ = .{ self, alloc };
            @panic("unimplemented");
        }

        pub fn probe(self: *const @This(), hash: u64, ctx: anytype) Probe {
            // find the slot for a hash, ctx.eql(id) compares the key behind a stored id
            // figure out: linear vs quadratic probing
            // figure out: is swiss-table style simd group probing worth it at your table sizes
            _ = .{ self, hash, ctx };
            @panic("unimplemented");
        }

        pub fn insert(self: *@This(), alloc: std.mem.Allocator, probed: Probe, hash: u64, id: Id) void {
            // write id + hash into the probed slot, grow when the load factor is exceeded
            // figure out: max load factor (0.5 - 0.875)
            _ = .{ self, alloc, probed, hash, id };
            @panic("unimplemented");
        }

        pub fn grow(self: *@This(), alloc: std.mem.Allocator) void {
            // double the table and reinsert using the stored hashes (no key access needed)
            _ = .{ self, alloc };
            @panic("unimplemented");
        }
    };
}

pub const NamePool = struct {
    alloc: std.mem.Allocator,
    bytes: DynBuf(u8),
    starts: DynBuf(u32),
    table: HashIndex(NameId),

    pub fn init(alloc: std.mem.Allocator) NamePool {
        // set up bytes, starts and the hash index
        // figure out: initial capacity from the token count
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *NamePool) void {
        // free bytes, starts and the table
        _ = self;
        @panic("unimplemented");
    }

    pub fn seed(self: *NamePool) void {
        // intern the fixed names in exact NameId order ("", "_", "$it", "self", "init", "deinit", "main", "len")
        // figure out: assert the order once in debug builds
        _ = self;
        @panic("unimplemented");
    }

    pub fn intern(self: *NamePool, bytes: []const u8) NameId {
        // hash the bytes, probe, append bytes + start offset if the name is new
        // figure out: store a sentinel start at the end so get() needs no length column
        _ = .{ self, bytes };
        @panic("unimplemented");
    }

    pub fn get(self: *const NamePool, name: NameId) []const u8 {
        // slice bytes[starts[id]..starts[id + 1]]
        _ = .{ self, name };
        @panic("unimplemented");
    }
};

pub const MetaVar = struct {
    parent: MetaVarId,
    rank: u8,
    level: u16,
    binding: TypeId,
    origin: u32,
};

pub const MetaVars = struct {
    vars: SoD(MetaVar),

    pub fn init(alloc: std.mem.Allocator) MetaVars {
        // set up the metavar table
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *MetaVars) void {
        // free the metavar table
        _ = self;
        @panic("unimplemented");
    }

    pub fn fresh(self: *MetaVars, level: u16, origin: u32) MetaVarId {
        // new root - parent = itself, rank 0, binding none, remember level and origin node
        _ = .{ self, level, origin };
        @panic("unimplemented");
    }

    pub fn find(self: *MetaVars, id: MetaVarId) MetaVarId {
        // find the root with path halving (tarjan union-find)
        _ = .{ self, id };
        @panic("unimplemented");
    }

    pub fn merge(self: *MetaVars, a: MetaVarId, b: MetaVarId) MetaVarId {
        // union by rank, the merged root keeps the smaller level
        // figure out: merging two bound vars - caller must unify the bindings first
        _ = .{ self, a, b };
        @panic("unimplemented");
    }

    pub fn bind(self: *MetaVars, id: MetaVarId, ty: TypeId) void {
        // set the binding of the root, the occurs check is the caller's job (Pool.occurs)
        _ = .{ self, id, ty };
        @panic("unimplemented");
    }

    pub fn binding(self: *MetaVars, id: MetaVarId) TypeId {
        // binding of the root, or none
        _ = .{ self, id };
        @panic("unimplemented");
    }

    pub fn adjust_level(self: *MetaVars, id: MetaVarId, level: u16) void {
        // lower levels while unifying (remy / ocaml style levels)
        // figure out: are levels needed at all - mond has no let-polymorphism, generics go through stcfun
        _ = .{ self, id, level };
        @panic("unimplemented");
    }
};

pub const Pool = struct {
    alloc: std.mem.Allocator,
    items: SoD(Item),
    extra: DynBuf(u32),
    bytes: DynBuf(u8),
    table: HashIndex(Index),
    classes: DynBuf(Class),
    layouts: SoD(Layout),
    field_infos: SoD(FieldInfo),
    trait_closure: DynBuf(u64),

    pub fn init(alloc: std.mem.Allocator) Pool {
        // set up all tables and call seed
        // figure out: initial capacities
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *Pool) void {
        // free every table
        _ = self;
        @panic("unimplemented");
    }

    pub fn seed(self: *Pool) void {
        // intern the primitive types and values in exact Index order
        // figure out: assert index == expected enum value for every seeded key
        _ = self;
        @panic("unimplemented");
    }

    pub fn intern(self: *Pool, key: Key) Index {
        // hash the key, probe, encode into item + extra if missing, return the index
        // slices of the key are copied into extra, strings into bytes, int values are always <= 64 bit so they fit two extra words
        // figure out: fill classes and an empty layout row at the same time
        // figure out: thread safety for step 23 - global lock, sharded tables, or per-thread pools merged later
        _ = .{ self, key };
        @panic("unimplemented");
    }

    pub fn fresh_nominal(self: *Pool, decl: DeclId, kind: MetaKind) Index {
        // push a nominal item without dedupe, used as placeholder for recursive types
        // figure out: how get() and layout() behave on a not yet completed placeholder
        _ = .{ self, decl, kind };
        @panic("unimplemented");
    }

    pub fn complete_nominal(self: *Pool, placeholder: Index, key: Key) void {
        // fill a placeholder with its final key
        // figure out: nominal keys contain the decl, so hashing after completion stays unique
        _ = .{ self, placeholder, key };
        @panic("unimplemented");
    }

    pub fn get(self: *const Pool, index: Index) Key {
        // decode item + extra into a Key
        // figure out: returned slices point into extra and become invalid when extra grows - copy or document
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn tag(self: *const Pool, index: Index) Tag {
        // items.tag at index
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn class(self: *const Pool, index: Index) Class {
        // read the precomputed class bits of index
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn type_of(self: *const Pool, value: ValueId) TypeId {
        // type of a value, types themselves have type_type / trait_type / variant_type
        // figure out: type of a generic (stcfun) value
        _ = .{ self, value };
        @panic("unimplemented");
    }

    pub fn push_field_infos(self: *Pool, infos: []const FieldInfo) Span {
        // append field infos, return their span (stored inside the record key)
        _ = .{ self, infos };
        @panic("unimplemented");
    }

    pub fn field_info(self: *const Pool, span: Span, field: u32) FieldInfo {
        // field info at span.start + field
        _ = .{ self, span, field };
        @panic("unimplemented");
    }

    pub fn coerce(self: *Pool, from: TypeId, to: TypeId) Coercion {
        // implicit conversion (no `as` written) when a value of type from is used where type to is expected
        // literals are not coerced here - an untyped literal takes the expected type directly in step 23 (checked by fits)
        // figure out: which of these are allowed - widening (same signedness only?), string literal -> &u8, array -> slice, *T -> &T, case -> variant, payload -> self tagged (`Opt8 x = 42`), variant -> union, never -> anything
        // figure out: may coercions chain (payload -> self tagged -> union) or only one step
        _ = .{ self, from, to };
        @panic("unimplemented");
    }

    pub fn join(self: *Pool, metavars: *MetaVars, a: TypeId, b: TypeId) JoinResult {
        // least upper bound for if / match branches
        // runit marks a branch that yields no value on purpose, so the other branches decide the type: `if c: 42 else: do print()` is i32
        // branches that are brk / ret / cont (never) or nested if / match are auto runit, a plain unit call needs `do`
        // unit (without do) + value -> runit_mixing error, runit + T -> T, never + T -> T, two cases of one variant -> the variant
        // figure out: when join fails - error at the branch or fall back to poison
        _ = .{ self, metavars, a, b };
        @panic("unimplemented");
    }

    pub fn unify(self: *Pool, metavars: *MetaVars, a: TypeId, b: TypeId) UnifyResult {
        // structural unification with metavars
        // figure out: when to unify (inference) vs coerce (checking against an expected type)
        // figure out: unify static values inside types (array lengths, instance args)
        _ = .{ self, metavars, a, b };
        @panic("unimplemented");
    }

    pub fn cast(self: *Pool, from: TypeId, to: TypeId) CastKind {
        // classify an explicit `as`
        // figure out: allowed reinterpretations - float bits, retag (`reg as Register.AsLower`), pointer reslice (`&[]u8 as &[n]u8`)
        // figure out: which casts may fail at runtime and need a check
        _ = .{ self, from, to };
        @panic("unimplemented");
    }

    pub fn close_traits(self: *Pool, traits: []const TypeId) void {
        // compute the implof closure bitsets for the given traits
        _ = .{ self, traits };
        @panic("unimplemented");
    }

    pub fn implements(self: *const Pool, ty: TypeId, trait: TypeId) bool {
        // bit test in the closure of ty
        // figure out: generic traits - compare instances, not the generic
        _ = .{ self, ty, trait };
        @panic("unimplemented");
    }

    pub fn lookup_member(self: *Pool, ty: TypeId, name: NameId) Member {
        // find what `ty.name` refers to - field, own method, trait method, variant case, builtin
        // auto-deref like zig - member access and indexing see through one pointer level (`ptr.field`, `arr_ptr[i]`, `arr_ptr.len`)
        // figure out: exactly one pointer level like zig, or through `* *T` chains too
        // figure out: `$0` style names for unnamed fields
        _ = .{ self, ty, name };
        @panic("unimplemented");
    }

    pub fn substitute(self: *Pool, index: Index, params: []const ValueId, args: []const ValueId) Index {
        // replace generic params by args inside a type or value
        // figure out: needed at all, or does static evaluation produce instances directly
        _ = .{ self, index, params, args };
        @panic("unimplemented");
    }

    pub fn zonk(self: *Pool, metavars: *MetaVars, index: Index) Index {
        // rebuild index with every metavar replaced by its binding
        _ = .{ self, metavars, index };
        @panic("unimplemented");
    }

    pub fn occurs(self: *const Pool, metavars: *MetaVars, id: MetaVarId, index: Index) bool {
        // does metavar id appear inside index (prevents infinite types)
        _ = .{ self, metavars, id, index };
        @panic("unimplemented");
    }

    pub fn layout(self: *Pool, ty: TypeId) Layout {
        // memoized size / align / niche of ty, in_progress marks cycles
        // figure out: target dependent sizes (pointer width) - pass a target struct into the pool
        _ = .{ self, ty };
        @panic("unimplemented");
    }

    pub fn field_offset(self: *Pool, record: TypeId, field: u32) u64 {
        // offset of a field, respecting packed vs natural alignment
        // figure out: field reordering for smaller size, or keep declaration order (c compatible)
        _ = .{ self, record, field };
        @panic("unimplemented");
    }

    pub fn niche_of(self: *Pool, ty: TypeId) Niche {
        // invalid bit patterns of ty that a self tagged variant can use to store other cases
        // figure out: niches of bool, pointers (0), enum-like variants (unused tags), nested records
        _ = .{ self, ty };
        @panic("unimplemented");
    }

    pub fn smallest_tag_type(case_count: u64) TypeId {
        // smallest unsigned int that holds case_count tags
        _ = case_count;
        @panic("unimplemented");
    }

    pub fn fits(self: *const Pool, value: ValueId, ty: TypeId) bool {
        // does a static int / float value fit into ty without loss
        _ = .{ self, value, ty };
        @panic("unimplemented");
    }

    pub fn format(self: *const Pool, names: *const NamePool, index: Index, writer: *std.Io.Writer) !void {
        // print a type readable for diagnostics
        // figure out: nominal types print their decl name - pool needs access to decl names (pass a callback?)
        _ = .{ self, names, index, writer };
        @panic("unimplemented");
    }

    fn hash_key(key: Key) u64 {
        // hash a key structurally (tag + every word + every slice element)
        // figure out: hash nominal types only by decl
        _ = key;
        @panic("unimplemented");
    }

    fn eql_key(self: *const Pool, key: Key, index: Index) bool {
        // compare a key with the decoded item at index without allocating
        _ = .{ self, key, index };
        @panic("unimplemented");
    }

    fn encode(self: *Pool, key: Key) Item {
        // write a key into one item + extra words
        // figure out: encoding of each tag (which fields go into data, which into extra)
        _ = .{ self, key };
        @panic("unimplemented");
    }
};
