const std = @import("std");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const SoD = @import("ds/dynbuf.zig").SoD;

// how to read this file:
//   1. ids          - every type, value, name and declaration is a u32 id
//   2. keys         - what a type or value looks like when you create or inspect it
//   3. the pool     - where keys are stored, packed and deduplicated
//   4. type vars    - placeholders for types that are not known yet (type inference)
//   5. questions    - class, layout, member lookup
//   6. relations    - unify, coerce, join, cast: how two types relate
//
// the one idea to keep in mind: after interning, a type is just a number, and two types are
// the same type exactly when their numbers are equal.

// ------------------------------------------------------------------------------------------ //
// 1. ids
// ------------------------------------------------------------------------------------------ //

// every type and every compile-time value is one u32 index into the pool.
// the first entries are fixed, so `u8`, `bool`, ... are known without any lookup and
// a check like `ty == .bool_type` is a single integer compare.
// types and values share one pool because `stcfun` arguments can be both (`Matrix(f32, 4, 4)`).
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

pub const TypeId = Index;
pub const ValueId = Index;

// every identifier string is interned once into a u32. comparing two names is then an
// integer compare instead of a string compare, and arrays of names can be scanned very fast.
// fixed names get fixed ids so the resolver can test `name == .self` without hashing.
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

// index into the resolver's declaration table, shared here because nominal types
// (records, variants, traits) remember the declaration that created them.
pub const DeclId = enum(u32) { none = std.math.maxInt(u32), _ };

// index into the type variable table (section 4).
pub const VarId = enum(u32) { none = std.math.maxInt(u32), _ };

// ------------------------------------------------------------------------------------------ //
// 2. keys - what a type or value looks like
// ------------------------------------------------------------------------------------------ //

pub const Signedness = enum(u1) { unsigned, signed };

// types without any payload.
// runit: "this branch yields no value on purpose" (`else: do print()`, `else: ret`), the other
//        branches decide the type of the if / match.
// never: the type of brk / ret / cont, an expression that does not produce a value at all.
// poison: the type of an expression that already had an error; it is compatible with
//         everything, so one mistake does not cause a cascade of follow-up errors.
pub const SimpleType = enum(u8) { bool, unit, runit, never, poison };

pub const SimpleValue = enum(u8) { bool_true, bool_false, unit };

// the "type of a type": `type`, `trait`, `variant`, `fun`, `stcfun`, `inlfun` keywords.
pub const MetaKind = enum(u8) { type, trait, variant, fun, stcfun, inlfun };

pub const FnCategory = enum(u8) { default, static, inlined };

// how a variant stores which case it holds: no tag, an int tag, or inside the payload (`tagof self`).
pub const TagMode = enum(u8) { none, int, self };

pub const IntType = struct { signedness: Signedness, bits: u16 };
pub const FloatType = struct { bits: u16 };
// an array always has a length, but it does not have to be written:
// `[4]u8` has a known length, `[]u8` ("unlengthed") has a length that is inferred.
// that is why len is a pool entry and not a plain number: it is either a static int value,
// or a type var standing in for the length until it is known (`[]u8 x = [5, 6, 7]` -> 3).
// in a parameter the length is filled per call, and the function is compiled once per length used - for
// `[]u8 arr` (array by value, copied), `&[]u8 arr` (immutable pointer) and `*[]u8 arr` (mutable pointer) alike.
pub const ArrayType = struct { len: ValueId, elem: TypeId };
pub const PtrType = struct { child: TypeId, mutable: bool };

// parameter names, defaults and where-clauses are not part of a function type:
// `(i32 a) -> i32` and `(i32 b = 5) -> i32` are the same type. those details are read
// from the parse tree when a call needs them, so they are never copied into the pool.
pub const FunctionType = struct {
    category: FnCategory,
    params: []const TypeId,
    ret: TypeId,
};

// records are nominal: the declaration is part of the key, so two identical
// `*(i32 x)` declarations are different types. field mutability, defaults and
// where-clauses are read from the declaration's parse tree node when needed.
pub const RecordType = struct {
    decl: DeclId,
    is_packed: bool,
    field_names: []const NameId,
    field_types: []const TypeId,
    traits: []const TypeId,
};

pub const VariantType = struct {
    decl: DeclId,
    tag_mode: TagMode,
    tag_type: TypeId,
    is_unionsized: bool,
    cases: []const TypeId,
    traits: []const TypeId,
};

// one case of a variant is a type of its own (`Register.AsLower lower = ...`).
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

// an uninstantiated `stcfun`. calling it with static arguments produces an instance,
// memoized by the resolver, so `Vec2T(i32)` written twice is analyzed once.
pub const Generic = struct {
    decl: DeclId,
    result_kind: MetaKind,
};

// mond ints are at most 64 bit, so every static int value fits into a u64 bit pattern;
// the type says how to read it (signed / unsigned, width).
pub const IntValue = struct { ty: TypeId, bits: u64 };
pub const FloatValue = struct { ty: TypeId, value: f64 };
pub const Aggregate = struct { ty: TypeId, elems: []const ValueId };
pub const VariantValue = struct { case: TypeId, payload: ValueId };

// the unpacked, convenient form of an entry. used to create entries (`intern`) and to
// read them (`get`). it is never stored; storage is always the packed form of section 3.
pub const Key = union(enum) {
    int_type: IntType,
    float_type: FloatType,
    simple_type: SimpleType,
    meta_type: MetaKind,
    array_type: ArrayType,
    ptr_type: PtrType,
    function_type: FunctionType,
    record_type: RecordType,
    variant_type: VariantType,
    variant_case_type: VariantCaseType,
    variant_union_type: []const TypeId,
    trait_type: TraitType,
    generic: Generic,
    type_var: VarId,
    int: IntValue,
    float: FloatValue,
    simple_value: SimpleValue,
    string: []const u8,
    aggregate: Aggregate,
    variant_value: VariantValue,
    function: DeclId,
};

// ------------------------------------------------------------------------------------------ //
// 3. the pool - packed, deduplicated storage
// ------------------------------------------------------------------------------------------ //

// the kind of a stored entry, it decides how `Item.data` is read.
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

// one stored entry is only 5 bytes: a tag and one u32.
// small payloads live directly in `data` (a pointer type stores its child type there,
// a type var its VarId). bigger payloads store an offset into `Pool.extra`, a flat u32 array.
// fixed-size entries mean: no pointers, no allocation per type, indexing is one multiply,
// and the whole pool is a few flat arrays the cpu can prefetch. same scheme as zig's InternPool.
pub const Item = struct {
    tag: Tag,
    data: u32,
};

// maps identifier text to its NameId. the keys point straight into the source file, so
// interning never copies strings. `strings` is the reverse direction (id -> text) and is
// only touched when printing diagnostics, so it stays cold.
pub const NamePool = struct {
    alloc: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(NameId),
    strings: DynBuf([]const u8),

    pub fn init(alloc: std.mem.Allocator) NamePool {
        // create the map and the strings buffer, then seed the fixed names in NameId order
        // figure out: initial capacity from the token count (identifiers are roughly a third)
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *NamePool) void {
        // free map and strings, the key texts belong to the source buffer
        _ = self;
        @panic("unimplemented");
    }

    pub fn intern(self: *NamePool, text: []const u8) NameId {
        // getOrPut on the map, on a miss push text into strings and use its position as the id
        _ = .{ self, text };
        @panic("unimplemented");
    }

    pub fn get(self: *const NamePool, name: NameId) []const u8 {
        // strings[id], only for diagnostics
        _ = .{ self, name };
        @panic("unimplemented");
    }
};

pub const Pool = struct {
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

    pub const IndexContext = struct {
        pool: *const Pool,

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
        pool: *const Pool,

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

    pub fn init(alloc: std.mem.Allocator) Pool {
        // create all buffers and intern the fixed entries in exact Index order
        // figure out: assert once (debug builds) that every fixed entry landed on its enum value
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *Pool) void {
        _ = self;
        @panic("unimplemented");
    }

    pub fn intern(self: *Pool, key: Key) Index {
        // getOrPutAdapted with KeyAdapter; on a miss encode key into one item + extra words
        // lists inside the key are copied into extra, strings into bytes, and the var bit is set
        // figure out: the exact encoding per tag (what goes into data, what into extra)
        // future (multithreading): per-thread shards of the pool, or a lock around intern
        _ = .{ self, key };
        @panic("unimplemented");
    }

    pub fn reserve_nominal(self: *Pool, decl: DeclId) Index {
        // push an entry for a record / variant / trait before its fields are known, so a
        // recursive type (`*Tree` inside Tree) can already point at itself
        _ = .{ self, decl };
        @panic("unimplemented");
    }

    pub fn complete_nominal(self: *Pool, reserved: Index, key: Key) void {
        // fill the reserved entry, then insert it into the map
        _ = .{ self, reserved, key };
        @panic("unimplemented");
    }

    pub fn get(self: *const Pool, index: Index) Key {
        // decode item + extra into a key
        // figure out: lists in the returned key point into extra and are invalidated when extra grows - copy, or never intern while holding them
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn tag(self: *const Pool, index: Index) Tag {
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn has_vars(self: *const Pool, index: Index) bool {
        // one bit test in var_bits
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn type_of(self: *const Pool, value: ValueId) TypeId {
        // type of a static value; types themselves are values of type_type / trait_type / variant_type
        _ = .{ self, value };
        @panic("unimplemented");
    }

    // ------------------------------------------------------------------------------------------ //
    // 5. questions about a type
    // ------------------------------------------------------------------------------------------ //

    pub fn class(self: *const Pool, index: Index) Class {
        // comptime table lookup by tag
        _ = .{ self, index };
        @panic("unimplemented");
    }

    pub fn implements(self: *const Pool, ty: TypeId, trait: TypeId) bool {
        // scan the type's trait list and recurse into supers; lists are tiny, no precomputed closure needed
        // generic traits (`Comparable(Money)`) compare as instances, not as the generic
        _ = .{ self, ty, trait };
        @panic("unimplemented");
    }

    pub fn lookup_member(self: *Pool, ty: TypeId, name: NameId) Member {
        // field, own method, trait method, variant case, builtin (len / init / deinit)
        // auto-deref like zig: a pointer is looked through once before searching
        // figure out: `$0` names for unnamed fields
        _ = .{ self, ty, name };
        @panic("unimplemented");
    }

    pub fn layout(self: *Pool, ty: TypeId) Layout {
        // memoized in `layouts`; in_progress while computing detects infinite by-value types
        // figure out: target pointer width - pass a target description into the pool
        // figure out: `tagof self` niche search, tag type when no `tagof` is given, `++(` vs `+(` sizes
        _ = .{ self, ty };
        @panic("unimplemented");
    }

    pub fn field_offset(self: *Pool, record: TypeId, field: u32) u64 {
        // figure out: keep declaration order (c compatible) or reorder fields for smaller size
        _ = .{ self, record, field };
        @panic("unimplemented");
    }

    pub fn niche_of(self: *Pool, ty: TypeId) Niche {
        // invalid bit patterns of ty, e.g. 0xFF for `Opt8`'s None
        _ = .{ self, ty };
        @panic("unimplemented");
    }

    pub fn smallest_tag_type(case_count: u64) TypeId {
        _ = case_count;
        @panic("unimplemented");
    }

    pub fn fits(self: *const Pool, value: ValueId, ty: TypeId) bool {
        // does a static int / float value fit into ty without loss (used for literals)
        _ = .{ self, value, ty };
        @panic("unimplemented");
    }

    pub fn format(self: *const Pool, names: *const NamePool, vars: *const TypeVars, index: Index, writer: *std.Io.Writer) !void {
        // readable type name for diagnostics, unbound vars print as `?1`, `?2`, ...
        _ = .{ self, names, vars, index, writer };
        @panic("unimplemented");
    }

    // ------------------------------------------------------------------------------------------ //
    // 6. relations between two types
    // ------------------------------------------------------------------------------------------ //

    pub fn unify(self: *Pool, vars: *TypeVars, a: TypeId, b: TypeId) UnifyResult {
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

    pub fn coerce(self: *Pool, vars: *TypeVars, from: TypeId, to: TypeId) Coercion {
        // implicit conversion (no `as` written) when a value of `from` is used where `to` is expected
        // if either side still contains vars, unify instead (inference decides, not conversion)
        // literals never come here, they take the expected type directly (checked with fits)
        // figure out: which of these are allowed - int / float widening (same signedness only?), string literal -> &u8, *T -> &T, case -> variant, payload -> self tagged, variant -> union, never -> anything
        // figure out: one step only, or chains like payload -> self tagged -> union
        _ = .{ self, vars, from, to };
        @panic("unimplemented");
    }

    pub fn join(self: *Pool, vars: *TypeVars, a: TypeId, b: TypeId) JoinResult {
        // common type of two if / match branches
        // runit + T -> T, never + T -> T, unit + value -> runit_mixing, two cases of one variant -> the variant
        // a var on one side: unify
        _ = .{ self, vars, a, b };
        @panic("unimplemented");
    }

    pub fn cast(self: *Pool, from: TypeId, to: TypeId) CastKind {
        // classify an explicit `as`
        // figure out: allowed reinterpretations - float bits, retag (`reg as Register.AsLower`), pointer relength (`&[]u8 as &[n]u8`)
        _ = .{ self, from, to };
        @panic("unimplemented");
    }

    pub fn apply_vars(self: *Pool, vars: *TypeVars, index: Index) Index {
        // rebuild index with every bound var replaced by its type ("zonking"); var-free types return immediately via has_vars
        _ = .{ self, vars, index };
        @panic("unimplemented");
    }

    pub fn occurs(self: *const Pool, vars: *TypeVars, v: VarId, index: Index) bool {
        // does var v appear inside index? binding v to such a type would make it infinite (`?1 = []?1`)
        _ = .{ self, vars, v, index };
        @panic("unimplemented");
    }
};

// ------------------------------------------------------------------------------------------ //
// 4. type vars - type inference
// ------------------------------------------------------------------------------------------ //

// a type var is a placeholder for a type the resolver does not know yet, for example:
//   - the return type of `fun f = (i32 x): if x == 0: 0 else: f(x - 1)` while its own body is checked
//   - the element type of `x = [];` until something is pushed or assigned
//   - the length of an unlengthed array `[]u8 x = ...` until the value shows it
//   - two induced functions calling each other
// it is interned like any type (tag type_var), so it can sit inside other types (`[?2]?1`),
// including in the length slot of an array.
// when unify learns what the var must be, it is "bound" to that type.
//
// vars that are unified with each other form groups; a group is stored as a tree with a
// representative at the root (union-find). `find` walks to the root and shortens the path on the
// way, so later lookups are nearly O(1). only the root carries the binding.
//
// no levels / generalization: mond has no hidden polymorphism, generics are explicit via stcfun.
pub const TypeVar = struct {
    parent: VarId,
    binding: TypeId,
    origin: u32,
};

pub const TypeVars = struct {
    // struct-of-arrays: `find` only walks the parent column.
    vars: SoD(TypeVar),

    pub fn init(alloc: std.mem.Allocator) TypeVars {
        _ = alloc;
        @panic("unimplemented");
    }

    pub fn deinit(self: *TypeVars) void {
        _ = self;
        @panic("unimplemented");
    }

    pub fn fresh(self: *TypeVars, origin: u32) VarId {
        // new var that is its own root, binding none, origin = the node that needed it (for error messages)
        _ = .{ self, origin };
        @panic("unimplemented");
    }

    pub fn find(self: *TypeVars, v: VarId) VarId {
        // walk to the root, pointing every visited var at its grandparent (path halving)
        _ = .{ self, v };
        @panic("unimplemented");
    }

    pub fn bind(self: *TypeVars, v: VarId, ty: TypeId) void {
        // set the binding of the root of v, the occurs check is done by Pool.unify before
        _ = .{ self, v, ty };
        @panic("unimplemented");
    }

    pub fn link(self: *TypeVars, a: VarId, b: VarId) void {
        // join two unbound groups by pointing one root at the other
        _ = .{ self, a, b };
        @panic("unimplemented");
    }

    pub fn binding(self: *TypeVars, v: VarId) TypeId {
        // binding of the root of v, or none
        _ = .{ self, v };
        @panic("unimplemented");
    }

    pub fn count(self: *const TypeVars) u32 {
        // zero means no inference happened at all, so the final fix-up pass can be skipped
        _ = self;
        @panic("unimplemented");
    }
};

// ------------------------------------------------------------------------------------------ //
// result types of sections 5 and 6
// ------------------------------------------------------------------------------------------ //

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

pub const LayoutState = enum(u8) { unknown, in_progress, done, infinite };

// invalid bit patterns of a type that a self-tagged variant (`tagof self`) can use to
// encode its other cases without an extra tag byte (e.g. 0xFF in `Opt8`).
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

pub const UnifyResult = enum(u8) { ok, mismatch, infinite };

// how a value of one type may be used where another type is expected, without `as`.
pub const Coercion = enum(u8) {
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

pub const JoinResult = struct {
    ty: TypeId,
    left: Coercion,
    right: Coercion,
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
