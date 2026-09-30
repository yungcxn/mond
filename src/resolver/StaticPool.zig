const std = @import("std");
const Resolver = @import("../Resolver.zig");
const AbstractPool = @import("AbstractPool.zig");
const NamePool = @import("NamePool.zig");
const target = @import("../main.zig").target;
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
    field_names: []const NamePool.Index,
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
    name: NamePool.Index,
    tag: Index,
    payload: Index,
};

pub const TraitType = struct {
    decl: Resolver.Decl.Index,
    member_names: []const NamePool.Index,
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
    builtin_tag,
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
    array_ptr_to_elem_ptr,
    to_dyn,
    ptr_mut_to_ptr,
    case_to_variant,
    payload_to_self_tagged,
    variant_to_union,
    impl_to_trait,
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
    bit_extend,
    variant_retag,
    payload_wrap,
    pointer_relength,
    array_narrow,
    trait_narrow,
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
        template_type,
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
    variant_union_type: []const Index,
    trait_type: TraitType,
    static_fun: StaticFun,
    template_type: Resolver.Decl.Index,
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
    args_tuple: Index, // due to them being a single `static_pool` index
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
        return KeyAdapter.hash(.{ .pool = ctx.pool }, ctx.pool.get(index));
    }

    pub fn eql(ctx: IndexContext, a: Index, b: Index) bool {
        _ = ctx;
        return a == b;
    }
};

pub const KeyAdapter = struct {
    pool: *const StaticPool,

    pub fn hash(adapter: KeyAdapter, key: Key) u64 {
        _ = adapter;
        var h = std.hash.Wyhash.init(@intFromEnum(std.meta.activeTag(key)));
        switch (key) {
            inline .custom_type, .variant_type, .trait_type => |n| feed(&h, n.decl),
            inline else => |payload| feed(&h, payload),
        }
        return h.final();
    }

    pub fn eql(adapter: KeyAdapter, key: Key, index: Index) bool {
        const stored = adapter.pool.get(index);
        if (std.meta.activeTag(key) != std.meta.activeTag(stored)) return false;
        return switch (key) {
            inline else => |payload, t| deep_eql(payload, @field(stored, @tagName(t))),
        };
    }
};

fn feed(h: *std.hash.Wyhash, v: anytype) void {
    switch (@typeInfo(@TypeOf(v))) {
        .@"struct" => |s| inline for (s.fields) |f| feed(h, @field(v, f.name)),
        .pointer => for (v) |x| feed(h, x),
        else => h.update(std.mem.asBytes(&word64(v))),
    }
}

fn deep_eql(a: anytype, b: @TypeOf(a)) bool {
    switch (@typeInfo(@TypeOf(a))) {
        .@"struct" => |s| {
            inline for (s.fields) |f| if (!deep_eql(@field(a, f.name), @field(b, f.name))) return false;
            return true;
        },
        .pointer => return std.mem.eql(std.meta.Child(@TypeOf(a)), a, b),
        else => return word64(a) == word64(b),
    }
}

fn word64(v: anytype) u64 {
    return switch (@typeInfo(@TypeOf(v))) {
        .@"enum" => @intCast(@intFromEnum(v)),
        .bool => @intFromBool(v),
        .float => @bitCast(v),
        else => @intCast(v),
    };
}

// key field <-> item tag, where the names differ
const tag_pairs = .{
    .{ "custom_type", "record_type" }, .{ "static_fun", "generic" },       .{ "abstract_type", "type_var" },
    .{ "int", "int_value" },           .{ "float", "float_value" },        .{ "string", "string_value" },
    .{ "aggregate", "aggregate_value" }, .{ "function", "function_value" },
};

fn item_tag(comptime k: std.meta.Tag(Key)) Item.Tag {
    inline for (tag_pairs) |p| if (comptime std.mem.eql(u8, p[0], @tagName(k))) return @field(Item.Tag, p[1]);
    return @field(Item.Tag, @tagName(k));
}

fn key_field(comptime t: Item.Tag) []const u8 {
    if (t == .ptr_mut_type) return "ptr_type";
    inline for (tag_pairs) |p| if (comptime std.mem.eql(u8, p[1], @tagName(t))) return p[0];
    return @tagName(t);
}

fn is_list(comptime T: type) bool {
    return @typeInfo(T) == .pointer;
}

// generic encoding: an enum payload lives in `data`, a list is `len, elems..`, a struct is
// `scalars.., list lens.., list elems..` in extra (u64 / f64 scalars take two words)
fn put(self: *StaticPool, v: anytype) u32 {
    const T = @TypeOf(v);
    const at = self.extra.head;
    switch (@typeInfo(T)) {
        .@"enum" => return @intCast(@intFromEnum(v)),
        .pointer => {
            self.extra.push(@intCast(v.len));
            for (v) |x| self.extra.push(@intCast(word64(x)));
        },
        .@"struct" => |s| {
            inline for (s.fields) |f| if (!comptime is_list(f.type)) {
                const w = word64(@field(v, f.name));
                self.extra.push(@truncate(w));
                if (@sizeOf(f.type) == 8) self.extra.push(@intCast(w >> 32));
            };
            inline for (s.fields) |f| if (comptime is_list(f.type)) self.extra.push(@intCast(@field(v, f.name).len));
            inline for (s.fields) |f| if (comptime is_list(f.type)) for (@field(v, f.name)) |x| self.extra.push(@intCast(word64(x)));
        },
        else => @compileError("no encoding for " ++ @typeName(T)),
    }
    return at;
}

fn take(self: *const StaticPool, comptime T: type, data: u32) T {
    const w = self.extra.buf;
    switch (@typeInfo(T)) {
        .@"enum" => return @enumFromInt(data),
        .pointer => return @ptrCast(w[data + 1 ..][0..w[data]]),
        .@"struct" => |s| {
            var r: T = undefined;
            var i = data;
            inline for (s.fields) |f| if (!comptime is_list(f.type)) {
                const lo: u64 = w[i];
                const x = if (@sizeOf(f.type) == 8) lo | @as(u64, w[i + 1]) << 32 else lo;
                i += if (@sizeOf(f.type) == 8) 2 else 1;
                @field(r, f.name) = switch (@typeInfo(f.type)) {
                    .@"enum" => @enumFromInt(x),
                    .bool => x != 0,
                    .float => @bitCast(x),
                    else => @intCast(x),
                };
            };
            var lens: [s.fields.len]u32 = undefined;
            inline for (s.fields, 0..) |f, j| if (comptime is_list(f.type)) {
                lens[j] = w[i];
                i += 1;
            };
            inline for (s.fields, 0..) |f, j| if (comptime is_list(f.type)) {
                @field(r, f.name) = @ptrCast(w[i..][0..lens[j]]);
                i += lens[j];
            };
            return r;
        },
        else => @compileError("no decoding for " ++ @typeName(T)),
    }
}

fn push_item(self: *StaticPool, item: Item, vars: bool) Index {
    const i = self.items.len();
    if (i % 64 == 0) self.var_bits.push(0);
    self.var_bits.buf[i / 64] |= @as(u64, @intFromBool(vars)) << @intCast(i % 64);
    self.items.push(item);
    self.layouts.push(.{ .size = 0, .align_log2 = 0, .state = .unknown, .niche = std.mem.zeroes(Layout.Niche) });
    return @enumFromInt(i);
}

fn any_vars(self: *const StaticPool, v: anytype) bool {
    const T = @TypeOf(v);
    if (T == Index) return v != .none and self.has_vars(v);
    if (T == []const Index) {
        for (v) |x| if (self.has_vars(x)) return true;
        return false;
    }
    if (@typeInfo(T) != .@"struct") return false;
    inline for (@typeInfo(T).@"struct".fields) |f| if (self.any_vars(@field(v, f.name))) return true;
    return false;
}

fn encode(self: *StaticPool, key: Key, str_ty: Index) Item {
    return switch (key) {
        .ptr_type => |p| .{ .tag = if (p.mutable) .ptr_mut_type else .ptr_type, .data = @intFromEnum(p.child) },
        .string => |s| blk: {
            const at = self.extra.head;
            self.extra.append(&.{ self.bytes.head, @intCast(s.len), @intFromEnum(str_ty) });
            if (s.len > 0) self.bytes.append(s);
            break :blk .{ .tag = .string_value, .data = at };
        },
        inline else => |payload, t| .{ .tag = comptime item_tag(t), .data = self.put(payload) },
    };
}

pub fn init(alloc: std.mem.Allocator) StaticPool {
    var self = StaticPool{
        .alloc = alloc,
        .items = .init(alloc, 1024),
        .extra = .init(alloc, 4096),
        .bytes = .init(alloc, 1024),
        .var_bits = .init(alloc, 16),
        .map = .empty,
        .layouts = .init(alloc, 1024),
        .realized_abstracts = .empty,
    };
    for ([_]u16{ 8, 16, 32, 64, 8, 16, 32, 64 }, 0..) |bits, i| _ = self.intern(.{ .int_type = .{ .signedness = if (i < 4) .unsigned else .signed, .bits = bits } });
    for ([_]u16{ 16, 32, 64 }) |bits| _ = self.intern(.{ .float_type = .{ .bits = bits } });
    inline for (@typeInfo(SimpleType).@"enum".fields) |f| _ = self.intern(.{ .simple_type = @enumFromInt(f.value) });
    inline for (@typeInfo(TypeType).@"enum".fields) |f| _ = self.intern(.{ .meta_type = @enumFromInt(f.value) });
    inline for (@typeInfo(SimpleValue).@"enum".fields) |f| _ = self.intern(.{ .simple_value = @enumFromInt(f.value) });
    std.debug.assert(self.items.len() == Index.first_dynamic);
    return self;
}

pub fn deinit(self: *StaticPool) void {
    self.items.deinit();
    self.extra.deinit();
    self.bytes.deinit();
    self.var_bits.deinit();
    self.map.deinit(self.alloc);
    self.layouts.deinit();
    self.realized_abstracts.deinit(self.alloc);
}

pub fn intern(self: *StaticPool, key: Key) Index {
    // a string knows its own `[n]u8` type, interned before the map is touched
    const str_ty = if (key == .string) self.intern(.{ .array_type = .{
        .len = self.intern(.{ .int = .{ .ty = .u64_type, .bits = key.string.len } }),
        .elem = .u8_type,
    } }) else .none;
    const gop = self.map.getOrPutContextAdapted(self.alloc, key, KeyAdapter{ .pool = self }, IndexContext{ .pool = self }) catch @panic("OOM");
    if (gop.found_existing) return gop.key_ptr.*;
    const vars = switch (key) {
        .abstract_type => true,
        .custom_type, .variant_type, .trait_type => false,
        inline else => |payload| self.any_vars(payload),
    };
    const index = self.push_item(self.encode(key, str_ty), vars);
    gop.key_ptr.* = index;
    return index;
}

pub fn reserve_nominal(self: *StaticPool, decl: Resolver.Decl.Index) Index {
    _ = decl; // the decl is written by complete_nominal, until then the entry reads as poison
    return self.push_item(.{ .tag = .simple_type, .data = @intFromEnum(SimpleType.poison) }, false);
}

pub fn complete_nominal(self: *StaticPool, reserved: Index, key: Key) void {
    const item = self.encode(key, .none);
    self.items.pool.tag.buf[@intFromEnum(reserved)] = item.tag;
    self.items.pool.data.buf[@intFromEnum(reserved)] = item.data;
    self.map.putContext(self.alloc, reserved, {}, IndexContext{ .pool = self }) catch @panic("OOM");
}

pub fn get(self: *const StaticPool, index: Index) Key {
    const t = self.tag(index);
    const data = self.items.pool.data.buf[@intFromEnum(index)];
    return switch (t) {
        .ptr_type, .ptr_mut_type => .{ .ptr_type = .{ .child = @enumFromInt(data), .mutable = t == .ptr_mut_type } },
        .string_value => .{ .string = self.bytes.buf[self.extra.buf[data]..][0..self.extra.buf[data + 1]] },
        inline else => |tt| @unionInit(Key, key_field(tt), self.take(@FieldType(Key, key_field(tt)), data)),
    };
}

pub fn tag(self: *const StaticPool, index: Index) Item.Tag {
    return self.items.pool.tag.buf[@intFromEnum(index)];
}

pub fn is_ptr(self: *const StaticPool, t: Index) bool {
    return t != .none and (self.tag(t) == .ptr_type or self.tag(t) == .ptr_mut_type);
}

pub fn pointee(self: *const StaticPool, t: Index) Index {
    return if (self.is_ptr(t)) @enumFromInt(self.items.pool.data.buf[@intFromEnum(t)]) else t;
}

pub fn array_elem(self: *const StaticPool, t: Index) Index {
    return if (t != .none and self.tag(t) == .array_type) self.get(t).array_type.elem else .none;
}

pub fn method_decl(self: *const StaticPool, m: @FieldType(Member, "trait_method")) Resolver.Decl.Index {
    return self.get(m.trait).trait_type.decl.member(m.index);
}

pub fn has_vars(self: *const StaticPool, index: Index) bool {
    const i = @intFromEnum(index);
    return (self.var_bits.buf[i / 64] >> @intCast(i % 64)) & 1 != 0;
}

pub fn type_of(self: *const StaticPool, value: Index) Index {
    const data = self.items.pool.data.buf[@intFromEnum(value)];
    return switch (self.tag(value)) {
        .int_value, .float_value, .aggregate_value, .variant_value => @enumFromInt(self.extra.buf[data]),
        .string_value => @enumFromInt(self.extra.buf[data + 2]),
        .simple_value => if (data == @intFromEnum(SimpleValue.unit)) .unit_type else .bool_type,
        .function_value => .fun_type,
        .generic => .stcfun_type,
        .trait_type => .trait_type,
        .variant_type, .variant_union_type => .variant_type,
        else => .type_type,
    };
}

// ------------------------------------------------------------------------------------------ //
// 5. questions about a type
// ------------------------------------------------------------------------------------------ //

const class_table = blk: {
    var t: [@typeInfo(Item.Tag).@"enum".fields.len]Class = undefined;
    for (&t, 0..) |*c, i| c.* = switch (@as(Item.Tag, @enumFromInt(i))) {
        .int_type => .{ .is_type = true, .is_integer = true, .has_layout = true },
        .float_type => .{ .is_type = true, .is_float = true, .has_layout = true },
        .simple_type => .{ .is_type = true, .has_layout = true },
        .meta_type => .{ .is_type = true, .is_static_only = true },
        .array_type => .{ .is_type = true, .is_aggregate = true, .has_layout = true },
        .ptr_type, .ptr_mut_type => .{ .is_type = true, .is_pointer = true, .has_layout = true },
        .function_type => .{ .is_type = true, .is_callable = true, .has_layout = true },
        .record_type => .{ .is_type = true, .is_aggregate = true, .is_nominal = true, .has_layout = true },
        .variant_type => .{ .is_type = true, .is_nominal = true, .is_variant = true, .has_layout = true },
        .variant_case_type, .variant_union_type => .{ .is_type = true, .is_variant = true, .has_layout = true },
        .trait_type => .{ .is_type = true, .is_nominal = true, .is_trait = true, .is_static_only = true },
        .generic => .{ .is_value = true, .is_callable = true, .is_static_only = true },
        .template_type => .{ .is_type = true, .is_static_only = true },
        .type_var => .{ .is_type = true },
        .function_value => .{ .is_value = true, .is_callable = true },
        else => .{ .is_value = true },
    };
    break :blk t;
};

pub fn class(self: *const StaticPool, index: Index) Class {
    return class_table[@intFromEnum(self.tag(index))];
}

pub fn implements(self: *const StaticPool, ty: Index, trait: Index) bool {
    if (ty == trait) return true;
    const list = switch (self.get(ty)) {
        .custom_type => |c| c.traits,
        .variant_type => |v| v.traits,
        .trait_type => |t| t.supers,
        .variant_case_type => |c| return self.implements(c.variant, trait),
        .ptr_type => |p| return self.implements(p.child, trait),
        else => return false,
    };
    for (list) |t| if (self.implements(t, trait)) return true;
    return false;
}

// depth first through traits and their supers; every trait member has a decl row right after
// the trait body's own row, so member i of a body with decl d is decl d + 1 + i
fn trait_member(self: *const StaticPool, traits: []const Index, name: NamePool.Index, dynamic: bool) Member {
    for (traits) |t| {
        if (self.tag(t) != .trait_type) continue;
        const tt = self.get(t).trait_type;
        for (tt.member_names, 0..) |n, i| if (n == name) return if (dynamic)
            .{ .trait_method = .{ .trait = t, .index = @intCast(i) } }
        else
            .{ .method = tt.decl.member(i) };
        const m = self.trait_member(tt.supers, name, dynamic);
        if (m != .none) return m;
    }
    return .none;
}

pub fn tag_type_of(self: *const StaticPool, t: Index) Index {
    return switch (self.get(t)) {
        .variant_type => |v| if (v.tag_mode == .self) .none else if (v.tag_type == .none or v.tag_type == .poison_type) .u8_type else v.tag_type,
        .variant_case_type => |c| self.tag_type_of(c.variant),
        .variant_union_type => self.union_tag_type(t),
        .ptr_type => |p| self.tag_type_of(p.child),
        else => .none,
    };
}

pub fn lookup_member(self: *StaticPool, ty: Index, name: NamePool.Index) Member {
    const t = if (self.get(ty) == .ptr_type) self.get(ty).ptr_type.child else ty;
    const found: Member = switch (self.get(t)) {
        .array_type => if (name == .len) .builtin_len else .none,
        .custom_type => |c| for (c.field_names, 0..) |n, i| {
            if (n == name) break .{ .field = .{ .index = @intCast(i), .ty = c.field_types[i] } };
        } else self.trait_member(c.traits, name, false),
        .variant_type => |v| for (v.cases) |cs| {
            if (self.get(cs).variant_case_type.name == name) break .{ .case = cs };
        } else self.trait_member(v.traits, name, false),
        .variant_case_type => |c| blk: {
            const m = if (c.payload == .none) Member.none else self.lookup_member(c.payload, name);
            break :blk if (m == .none) self.lookup_member(c.variant, name) else m;
        },
        .variant_union_type => |u| for (u) |v| {
            const m = self.lookup_member(v, name);
            if (m != .none) break m;
        } else .none,
        .trait_type => self.trait_member(&.{t}, name, true),
        else => .none,
    };
    if (found != .none) return found;
    if (name == .tag and self.tag_type_of(t) != .none) return .builtin_tag;
    const nominal = self.tag(t) == .record_type or self.tag(t) == .variant_type;
    return if (nominal and name == .init) .builtin_init else if (nominal and name == .deinit) .builtin_deinit else .none;
}

pub const dyn_len: Index = .unit_value;

fn is_reserved(self: *const StaticPool, ty: Index) bool {
    return ty != .poison_type and self.tag(ty) == .simple_type and self.items.pool.data.buf[@intFromEnum(ty)] == @intFromEnum(SimpleType.poison);
}

pub fn tag_range(self: *const StaticPool, v: Index) u64 {
    const vt = self.get(v).variant_type;
    var hi: u64 = vt.cases.len;
    if (vt.tag_mode == .int) for (vt.cases) |c| {
        const t = self.get(c).variant_case_type.tag;
        if (self.tag(t) == .int_value) hi = @max(hi, self.get(t).int.bits + 1);
    };
    return hi;
}

pub fn union_offset(self: *const StaticPool, u: Index, member: Index) u64 {
    var off: u64 = 0;
    for (self.get(u).variant_union_type) |m| {
        if (m == member) return off;
        off += self.tag_range(m);
    }
    return off;
}

pub fn union_tag_type(self: *const StaticPool, u: Index) Index {
    const members = self.get(u).variant_union_type;
    return smallest_tag_type(if (members.len == 0) 1 else self.union_offset(u, .none));
}

fn payloads(self: *StaticPool, v: Index, size: *u64, al: *u8) Layout.State {
    var state: Layout.State = .done;
    for (self.get(v).variant_type.cases) |cs| {
        const p = self.get(cs).variant_case_type.payload;
        if (p == .none) continue;
        const pl = self.layout(p);
        if (pl.state != .done) state = pl.state;
        size.* = @max(size.*, pl.size);
        al.* = @max(al.*, pl.align_log2);
    }
    return state;
}

// c layout in declaration order (fields are never reordered), pointer size from `target` in main.zig
pub fn layout(self: *StaticPool, ty: Index) Layout {
    if (self.is_reserved(ty)) return std.mem.zeroes(Layout);
    const i = @intFromEnum(ty);
    const state = &self.layouts.pool.state.buf[i];
    switch (state.*) {
        .done, .infinite => return self.layouts.get(i).?,
        .in_progress => {
            state.* = .infinite;
            return self.layouts.get(i).?;
        },
        .unknown => state.* = .in_progress,
    }
    var size: u64 = 0;
    var al: u8 = 0;
    var niche = std.mem.zeroes(Layout.Niche);
    var infinite = false;
    var incomplete = false;
    switch (self.get(ty)) {
        .int_type => |t| {
            size = t.bits / 8;
            al = std.math.log2_int(u64, size);
        },
        .float_type => |t| {
            size = t.bits / 8;
            al = std.math.log2_int(u64, size);
        },
        .simple_type => |s| if (s == .bool) {
            size = 1;
            niche = .{ .offset = 0, .bits = 8, .start = 2, .count = 254 };
        },
        .ptr_type, .function_type => {
            const dyn = self.get(ty) == .ptr_type and self.get(self.get(ty).ptr_type.child) == .array_type and self.get(self.get(ty).ptr_type.child).array_type.len == dyn_len;
            size = target.pointer_bits / 8 * @as(u64, if (dyn) 2 else 1);
            al = std.math.log2_int(u64, target.pointer_bits / 8);
            niche = .{ .offset = 0, .bits = target.pointer_bits, .start = 0, .count = 1 };
        },
        .array_type => |a| if (a.len == dyn_len) {
            size = target.pointer_bits / 8 * 2;
            al = std.math.log2_int(u64, target.pointer_bits / 8);
        } else if (self.tag(a.len) == .int_value) {
            const e = self.layout(a.elem);
            infinite = e.state == .infinite;
            incomplete = e.state == .unknown;
            size = self.get(a.len).int.bits * e.size;
            al = e.align_log2;
        },
        .custom_type => |c| {
            for (c.field_types) |f| {
                const fl = self.layout(f);
                infinite = infinite or fl.state == .infinite;
                incomplete = incomplete or fl.state == .unknown;
                if (!c.is_packed) al = @max(al, fl.align_log2);
            }
            size = self.field_offset(ty, @intCast(c.field_types.len));
        },
        .variant_type => |v| {
            var payload_al: u8 = 0;
            var payload: u64 = 0;
            const ps = self.payloads(ty, &payload, &payload_al);
            infinite = ps == .infinite;
            incomplete = ps == .unknown;
            const tag_l = if (v.tag_mode == .int) self.layout(v.tag_type) else std.mem.zeroes(Layout);
            al = @max(payload_al, tag_l.align_log2);
            size = if (v.tag_mode == .self and payload == 0) self.layout(v.tag_type).size else std.mem.alignForward(u64, tag_l.size, @as(u64, 1) << @intCast(payload_al)) + payload;
        },
        .variant_case_type => |c| return self.layout(c.variant),
        .variant_union_type => |u| {
            var payload_al: u8 = 0;
            var payload: u64 = 0;
            for (u) |v| {
                const ps = self.payloads(v, &payload, &payload_al);
                infinite = infinite or ps == .infinite;
                incomplete = incomplete or ps == .unknown;
            }
            const tag_l = self.layout(self.union_tag_type(ty));
            al = @max(payload_al, tag_l.align_log2);
            size = std.mem.alignForward(u64, tag_l.size, @as(u64, 1) << @intCast(payload_al)) + payload;
        },
        else => {},
    }
    size = std.mem.alignForward(u64, size, @as(u64, 1) << @intCast(al));
    const result = Layout{ .size = size, .align_log2 = al, .state = if (infinite or state.* == .infinite) .infinite else if (incomplete) .unknown else .done, .niche = niche };
    self.layouts.pool.size.buf[i] = result.size;
    self.layouts.pool.align_log2.buf[i] = result.align_log2;
    self.layouts.pool.niche.buf[i] = result.niche;
    self.layouts.pool.state.buf[i] = result.state;
    return result;
}

pub fn field_offset(self: *StaticPool, record: Index, field: u32) u64 {
    const c = self.get(record).custom_type;
    var off: u64 = 0;
    for (c.field_types[0..field]) |f| {
        const fl = self.layout(f);
        if (!c.is_packed) off = std.mem.alignForward(u64, off, @as(u64, 1) << @intCast(fl.align_log2));
        off += fl.size;
    }
    if (field == c.field_types.len or c.is_packed) return off;
    return std.mem.alignForward(u64, off, @as(u64, 1) << @intCast(self.layout(c.field_types[field]).align_log2));
}

pub fn smallest_tag_type(case_count: u64) Index {
    return if (case_count <= 1 << 8) .u8_type else if (case_count <= 1 << 16) .u16_type else if (case_count <= 1 << 32) .u32_type else .u64_type;
}

pub fn fits(self: *const StaticPool, value: Index, ty: Index) bool {
    const v = self.get(value);
    const t = self.get(ty);
    if (t == .float_type) return v == .int or v == .float;
    if (t != .int_type or v != .int) return false;
    const signed_v = self.get(v.int.ty) == .int_type and self.get(v.int.ty).int_type.signedness == .signed;
    const x: i128 = if (signed_v) @as(i64, @bitCast(v.int.bits)) else v.int.bits;
    const one: i128 = 1;
    const bits: u7 = @intCast(t.int_type.bits);
    return if (t.int_type.signedness == .signed) x >= -(one << (bits - 1)) and x < one << (bits - 1) else x >= 0 and x < one << bits;
}

pub fn format(self: *const StaticPool, names: *const NamePool, vars: *const AbstractPool, index: Index, writer: *std.Io.Writer) !void {
    return self.fmt(names, vars, index, writer, 0);
}

fn fmt(self: *const StaticPool, names: *const NamePool, vars: *const AbstractPool, index: Index, w: *std.Io.Writer, depth: u8) std.Io.Writer.Error!void {
    if (index == .none) return w.writeAll("none");
    // nominal types can contain themselves: one inside another prints by its declaration
    if (depth > 0 and self.class(index).is_nominal) return w.print("type#{d}", .{word64(switch (self.get(index)) {
        .custom_type => |c| c.decl,
        .variant_type => |v| v.decl,
        .trait_type => |t| t.decl,
        else => unreachable,
    })});
    switch (self.get(index)) {
        .int_type => |t| try w.print("{c}{d}", .{ @as(u8, if (t.signedness == .signed) 'i' else 'u'), t.bits }),
        .float_type => |t| try w.print("f{d}", .{t.bits}),
        .simple_type => |s| try w.writeAll(if (s == .unit) "()" else @tagName(s)),
        .meta_type => |m| try w.writeAll(@tagName(m)),
        .array_type => |a| {
            try w.writeAll("[");
            if (self.tag(a.len) == .int_value) try self.fmt(names, vars, a.len, w, depth);
            try w.writeAll("]");
            try self.fmt(names, vars, a.elem, w, depth);
        },
        .ptr_type => |p| {
            try w.writeAll(if (p.mutable) "*" else "&");
            try self.fmt(names, vars, p.child, w, depth);
        },
        .function_type => |f| {
            try w.writeAll("(");
            for (f.params, 0..) |p, i| {
                if (i > 0) try w.writeAll(", ");
                try self.fmt(names, vars, p, w, depth);
            }
            try w.writeAll(") -> ");
            try self.fmt(names, vars, f.ret, w, depth);
        },
        .custom_type => |c| {
            try w.writeAll(if (c.is_packed) "**(" else "*(");
            for (c.field_types, c.field_names, 0..) |t, n, i| {
                if (i > 0) try w.writeAll(", ");
                try self.fmt(names, vars, t, w, depth + 1);
                try w.print(" {s}", .{names.get(n)});
            }
            try w.writeAll(")");
        },
        .variant_type => |v| {
            try w.writeAll(if (v.is_unionsized) "++(" else "+(");
            for (v.cases, 0..) |cs, i| try w.print("{s}{s}", .{ if (i > 0) ", " else "", names.get(self.get(cs).variant_case_type.name) });
            try w.writeAll(")");
        },
        .variant_case_type => |c| {
            try self.fmt(names, vars, c.variant, w, depth);
            try w.print(".{s}", .{names.get(c.name)});
        },
        .variant_union_type => |u| for (u, 0..) |v, i| {
            if (i > 0) try w.writeAll(" || ");
            try self.fmt(names, vars, v, w, depth);
        },
        .trait_type => |t| {
            try w.writeAll("!{");
            for (t.member_names, 0..) |n, i| try w.print("{s}{s}", .{ if (i > 0) "; " else "", names.get(n) });
            try w.writeAll("}");
        },
        .static_fun => |s| try w.print("stcfun#{d}", .{@intFromEnum(s.decl)}),
        .template_type => |d| try w.print("abstract#{d}", .{@intFromEnum(d)}),
        .abstract_type => |v| {
            const parents = vars.pool.sliced_field(.parent);
            var root = v;
            while (parents[@intFromEnum(root)] != root) root = parents[@intFromEnum(root)];
            const b = vars.pool.sliced_field(.binding)[@intFromEnum(root)];
            if (b != .none) return self.fmt(names, vars, b, w, depth);
            try w.print("?{d}", .{@intFromEnum(root) + 1});
        },
        .int => |v| if (self.get(v.ty) == .int_type and self.get(v.ty).int_type.signedness == .signed)
            try w.print("{d}", .{@as(i64, @bitCast(v.bits))})
        else
            try w.print("{d}", .{v.bits}),
        .float => |v| try w.print("{d}", .{v.value}),
        .simple_value => |s| try w.writeAll(switch (s) {
            .bool_true => "true",
            .bool_false => "false",
            .unit => "()",
        }),
        .string => |s| try w.print("\"{s}\"", .{s}),
        .aggregate => |a| {
            try w.writeAll("[");
            for (a.elems, 0..) |e, i| {
                if (i > 0) try w.writeAll(", ");
                try self.fmt(names, vars, e, w, depth);
            }
            try w.writeAll("]");
        },
        .variant_value => |v| {
            try self.fmt(names, vars, v.case, w, depth);
            if (v.payload != .none) try self.fmt(names, vars, v.payload, w, depth);
        },
        .function => |d| try w.print("fun#{d}", .{@intFromEnum(d)}),
    }
}

// ------------------------------------------------------------------------------------------ //
// 6. relations between two types
// ------------------------------------------------------------------------------------------ //

// follow bound vars until a concrete type or an unbound var
fn shallow(self: *const StaticPool, vars: *AbstractPool, index: Index) Index {
    var cur = index;
    while (cur != .none and self.tag(cur) == .type_var) {
        const b = vars.binding(@enumFromInt(self.items.pool.data.buf[@intFromEnum(cur)]));
        if (b == .none) return cur;
        cur = b;
    }
    return cur;
}

fn unify_all(self: *StaticPool, vars: *AbstractPool, a: []const Index, b: []const Index) UnifyResult {
    if (a.len != b.len) return .mismatch;
    for (a, b) |x, y| {
        const r = self.unify(vars, x, y);
        if (r != .ok) return r;
    }
    return .ok;
}

pub fn unify(self: *StaticPool, vars: *AbstractPool, a: Index, b: Index) UnifyResult {
    const x = self.shallow(vars, a);
    const y = self.shallow(vars, b);
    if (x == y) return .ok;
    const tx = self.tag(x);
    const ty = self.tag(y);
    if (tx == .type_var and ty == .type_var) {
        vars.link(self.get(x).abstract_type, self.get(y).abstract_type);
        return .ok;
    }
    if (tx == .type_var or ty == .type_var) {
        const v, const t = if (tx == .type_var) .{ self.get(x).abstract_type, y } else .{ self.get(y).abstract_type, x };
        if (self.occurs(vars, v, t)) return .infinite;
        vars.bind(v, t);
        return .ok;
    }
    if (x == .poison_type or y == .poison_type) return .ok;
    if (tx != ty) return .mismatch;
    return switch (self.get(x)) {
        .array_type => |l| if (self.unify(vars, l.len, self.get(y).array_type.len) != .ok) .mismatch else self.unify(vars, l.elem, self.get(y).array_type.elem),
        .ptr_type => |l| self.unify(vars, l.child, self.get(y).ptr_type.child),
        .function_type => |l| blk: {
            const r = self.get(y).function_type;
            if (l.category != r.category) break :blk .mismatch;
            const p = self.unify_all(vars, l.params, r.params);
            break :blk if (p != .ok) p else self.unify(vars, l.ret, r.ret);
        },
        .variant_union_type => |l| self.unify_all(vars, l, self.get(y).variant_union_type),
        else => .mismatch,
    };
}

pub fn payload_case(self: *const StaticPool, variant: Index) Index {
    for (self.get(variant).variant_type.cases) |c| if (self.get(c).variant_case_type.payload != .none) return c;
    return .none;
}

// the single payload field of a variant with exactly one payload case (`Opt8.Some(u8)`), or none
pub fn single_payload(self: *const StaticPool, variant: Index) Index {
    if (self.tag(variant) != .variant_type) return .none;
    var found: Index = .none;
    for (self.get(variant).variant_type.cases) |cs| {
        const p = self.get(cs).variant_case_type.payload;
        if (p == .none) continue;
        if (found != .none) return .none;
        const fields = self.get(p).custom_type.field_types;
        found = if (fields.len == 1) fields[0] else p;
    }
    return found;
}

pub fn coerce(self: *StaticPool, vars: *AbstractPool, from0: Index, to0: Index) CoercionKind {
    const from = self.apply_vars(vars, from0);
    const to = self.apply_vars(vars, to0);
    if (from == to) return .identity;
    if (from == .poison_type or to == .poison_type) return .poison;
    if (from == .never_type) return .never_to_any;
    if (from == .unit_type and to == .runit_type) return .unit_to_runit;
    if (self.has_vars(from) or self.has_vars(to)) {
        const ptrs = self.is_ptr(from) and self.is_ptr(to) and (self.tag(from) == .ptr_mut_type or self.tag(to) == .ptr_type);
        return if (self.unify(vars, if (ptrs) self.pointee(from) else from, if (ptrs) self.pointee(to) else to) == .ok) .unified else .incompatible;
    }
    const f = self.get(from);
    const t = self.get(to);
    if (f == .int_type and t == .int_type) {
        const same = f.int_type.signedness == t.int_type.signedness;
        const to_signed = f.int_type.signedness == .unsigned and t.int_type.signedness == .signed;
        return if ((same and t.int_type.bits >= f.int_type.bits) or (to_signed and t.int_type.bits > f.int_type.bits)) .int_widen else .incompatible;
    }
    if (f == .float_type and t == .float_type) return if (t.float_type.bits >= f.float_type.bits) .float_widen else .incompatible;
    if (f == .ptr_type and t == .ptr_type and f.ptr_type.mutable and !t.ptr_type.mutable and f.ptr_type.child == t.ptr_type.child) return .ptr_mut_to_ptr;
    if (f == .ptr_type and t == .ptr_type and (f.ptr_type.mutable or !t.ptr_type.mutable)) {
        const fc = self.get(f.ptr_type.child);
        const tc = self.get(t.ptr_type.child);
        if (fc == .array_type and fc.array_type.elem == t.ptr_type.child) return .array_ptr_to_elem_ptr;
        if (fc == .array_type and tc == .array_type and tc.array_type.len == dyn_len and fc.array_type.elem == tc.array_type.elem) return .to_dyn;
    }
    if (f == .array_type and t == .array_type and t.array_type.len == dyn_len and f.array_type.elem == t.array_type.elem) return .to_dyn;
    if (f == .variant_case_type) return if (f.variant_case_type.variant == to or self.coerce(vars, f.variant_case_type.variant, to) != .incompatible) .case_to_variant else .incompatible;
    if (t == .variant_union_type) {
        for (t.variant_union_type) |v| if (v == from) return .variant_to_union;
        return .incompatible;
    }
    if (t == .trait_type and self.implements(from, to)) return .impl_to_trait;
    const payload = self.single_payload(to);
    if (payload != .none and f != .variant_type and self.coerce(vars, from, payload) != .incompatible) return .payload_to_self_tagged;
    return .incompatible;
}

pub fn join(self: *StaticPool, vars: *AbstractPool, a: Index, b: Index) JoinResult {
    if (a == b) return .{ .ty = a, .left = .identity, .right = .identity };
    if (a == .poison_type or b == .poison_type) return .{ .ty = .poison_type, .left = .poison, .right = .poison };
    if (a == .never_type or a == .runit_type) return .{ .ty = b, .left = if (a == .never_type) .never_to_any else .unit_to_runit, .right = .identity };
    if (b == .never_type or b == .runit_type) return .{ .ty = a, .left = .identity, .right = if (b == .never_type) .never_to_any else .unit_to_runit };
    if (self.tag(a) == .variant_case_type and self.tag(b) == .variant_case_type) {
        const v = self.get(a).variant_case_type.variant;
        if (v == self.get(b).variant_case_type.variant) return .{ .ty = v, .left = .case_to_variant, .right = .case_to_variant };
    }
    const r = self.coerce(vars, b, a);
    if (r != .incompatible) return .{ .ty = a, .left = .identity, .right = r };
    const l = self.coerce(vars, a, b);
    if (l != .incompatible) return .{ .ty = b, .left = l, .right = .identity };
    return .{ .ty = .none, .left = .incompatible, .right = .incompatible };
}

pub fn cast(self: *StaticPool, from: Index, to: Index) CastKind {
    if (from == to or from == .poison_type or to == .poison_type) return .identity;
    const f = self.get(from);
    const t = self.get(to);
    const f_int = f == .int_type or from == .bool_type;
    return switch (t) {
        .int_type => if (f_int) .int_resize else if (f == .float_type) .float_to_int else if (f == .variant_type or f == .variant_case_type) .bit_reinterpret else .invalid,
        .float_type => if (f_int) .int_to_float else if (f == .float_type) .float_resize else .invalid,
        .variant_case_type => |c| if (from == c.variant or (f == .variant_case_type and f.variant_case_type.variant == c.variant))
            .variant_retag
        else if (c.payload != .none and self.get(c.payload).custom_type.field_types.len == 1 and self.cast(from, self.get(c.payload).custom_type.field_types[0]) == .identity)
            .payload_wrap
        else
            .invalid,
        .ptr_type => |p| if (f != .ptr_type or p.mutable and !f.ptr_type.mutable)
            .invalid
        else if (self.get(p.child) == .array_type and self.elem_of(f.ptr_type.child) == self.get(p.child).array_type.elem)
            (if (self.longer(p.child, f.ptr_type.child) or self.tag(self.get(p.child).array_type.len) != .int_value and self.get(f.ptr_type.child) != .array_type) .invalid else .pointer_relength)
        else
            .bit_reinterpret,
        .array_type => |a| blk: {
            const src = if (f == .ptr_type) f.ptr_type.child else from;
            const sized = self.get(src) == .array_type and self.tag(self.get(src).array_type.len) == .int_value;
            break :blk if (self.elem_of(src) != a.elem or self.tag(a.len) != .int_value or f != .ptr_type and !sized or self.longer(to, src)) .invalid else .array_narrow;
        },
        else => .invalid,
    };
}

fn longer(self: *const StaticPool, to: Index, from: Index) bool {
    if (self.get(from) != .array_type or self.tag(self.get(from).array_type.len) != .int_value or self.tag(self.get(to).array_type.len) != .int_value) return false;
    return self.get(self.get(to).array_type.len).int.bits > self.get(self.get(from).array_type.len).int.bits;
}

fn elem_of(self: *const StaticPool, t: Index) Index {
    return if (self.get(t) == .array_type) self.get(t).array_type.elem else t;
}

pub fn apply_vars(self: *StaticPool, vars: *AbstractPool, index: Index) Index {
    if (index == .none or !self.has_vars(index)) return index;
    const s = self.shallow(vars, index);
    if (s != index) return self.apply_vars(vars, s);
    var buf: [64]Index = undefined;
    return switch (self.get(index)) {
        .array_type => |a| self.intern(.{ .array_type = .{ .len = self.apply_vars(vars, a.len), .elem = self.apply_vars(vars, a.elem) } }),
        .ptr_type => |p| self.intern(.{ .ptr_type = .{ .child = self.apply_vars(vars, p.child), .mutable = p.mutable } }),
        .function_type => |f| blk: {
            const params = buf[0..f.params.len];
            @memcpy(params, f.params);
            for (params) |*p| p.* = self.apply_vars(vars, p.*);
            break :blk self.intern(.{ .function_type = .{ .category = f.category, .params = params, .ret = self.apply_vars(vars, f.ret) } });
        },
        .variant_union_type => |u| blk: {
            const members = buf[0..u.len];
            @memcpy(members, u);
            for (members) |*m| m.* = self.apply_vars(vars, m.*);
            break :blk self.intern(.{ .variant_union_type = members });
        },
        else => index,
    };
}

pub fn occurs(self: *const StaticPool, vars: *AbstractPool, v: AbstractPool.Index, index: Index) bool {
    if (index == .none or !self.has_vars(index)) return false;
    const s = self.shallow(vars, index);
    return switch (self.get(s)) {
        .abstract_type => |w| vars.find(w) == vars.find(v),
        .array_type => |a| self.occurs(vars, v, a.len) or self.occurs(vars, v, a.elem),
        .ptr_type => |p| self.occurs(vars, v, p.child),
        .function_type => |f| for (f.params) |p| {
            if (self.occurs(vars, v, p)) break true;
        } else self.occurs(vars, v, f.ret),
        .variant_union_type => |u| for (u) |m| {
            if (self.occurs(vars, v, m)) break true;
        } else false,
        else => false,
    };
}
