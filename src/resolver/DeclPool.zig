const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const SoD = @import("../ds/dynbuf.zig").SoD;
const NamePool = @import("./NamePool.zig");
const StaticPool = @import("./StaticPool.zig");

const DeclPool = @This();

// one row per declaration: globals, locals, params, fields, binders.
// stored as struct-of-arrays, so every access pattern touches only the columns it needs:
// looking a name up reads `name` only, checking a use reads `kind`, `flags`, `ty`.
pub const Entry = struct {
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: Kind,
    flags: Flags,
    state: State,
    ty: StaticPool.Index,
    value: StaticPool.Index,
    next_overload: Index,

    pub const Kind = enum(u8) {
        variable,
        parameter,
        static_parameter,
        field,
        function,
        static_function,
        inlined_function,
        type_alias,
        record,
        variant,
        variant_case,
        trait,
        trait_member,
        pattern_binder,
        arrow_binder,
        loop_variable,
        self,
        autoins_arg,
        autoins_it,

        pub fn is_fn(kind: Kind) bool {
            return switch (kind) {
                .function, .static_function, .inlined_function, .trait_member => true,
                else => false,
            };
        }

        // the type of a type declared with this kind
        pub fn meta(kind: Kind, other: StaticPool.Index) StaticPool.Index {
            return switch (kind) {
                .record => .type_type,
                .variant => .variant_type,
                .trait => .trait_type,
                else => other,
            };
        }

        pub fn is_type_decl(kind: Kind) bool {
            return kind == .type_alias or kind == .record or kind == .variant or kind == .trait;
        }
    };

    pub const Flags = packed struct(u8) {
        is_pub: bool = false,
        is_mut: bool = false,
        is_stc: bool = false,
        is_global: bool = false,
        is_view: bool = false,
        // methods: the body writes through `self`, the `self` local: something writes through it
        writes: bool = false,
        _pad: u2 = 0,

        pub fn any(f: Flags) bool {
            return @as(u8, @bitCast(f)) != 0;
        }
    };

    //   unresolved -> resolving_signature -> signature_ready -> checking_body -> done   (or failed)
    // signature_ready is published before the body is checked, so a function can call itself or a
    // mutually recursive partner: an induced return type is a type var until the bodies fix it.
    // meeting a declaration in resolving_signature again is a real cycle (a type containing itself
    // by value, a static value defined through itself) and an error.
    pub const State = enum(u8) {
        unresolved,
        resolving_signature,
        signature_ready,
        checking_body,
        done,
        failed,
    };
};

pub const Index = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn member(d: Index, i: usize) Index {
        return @enumFromInt(@intFromEnum(d) + 1 + i);
    }
};

alloc: std.mem.Allocator,
entries: SoD(Entry),

pub inline fn init(alloc: std.mem.Allocator, initial_cap: usize) DeclPool {
    return .{ .alloc = alloc, .entries = SoD(Entry).init(alloc, initial_cap) };
}

pub inline fn deinit(self: *DeclPool) void {
    self.entries.deinit();
}

pub fn push_decl(
    self: *DeclPool,
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: DeclPool.Entry.Kind,
    ty: StaticPool.Index,
    flagss: DeclPool.Entry.Flags,
) DeclPool.Index {
    const d: DeclPool.Index = @enumFromInt(self.entries.len());
    const lazy = flagss.is_global or kind.is_fn() or kind.is_type_decl();

    self.entries.push(.{
        .name = name,
        .node = node,
        .kind = kind,
        .flags = flagss,
        .state = if (lazy) .unresolved else .done,
        .ty = ty,
        .value = .none,
        .next_overload = .none,
    });

    return d;
}

pub inline fn get_name(self: *const DeclPool, d: Index) NamePool.Index {
    return self.entries.pool.name.buf[@intFromEnum(d)];
}

pub inline fn get_node(self: *const DeclPool, d: Index) ParseTree.NodeId {
    return self.entries.pool.node.buf[@intFromEnum(d)];
}

pub inline fn get_kind(self: *const DeclPool, d: Index) Entry.Kind {
    return self.entries.pool.kind.buf[@intFromEnum(d)];
}

pub inline fn get_flags(self: *const DeclPool, d: Index) Entry.Flags {
    return self.entries.pool.flags.buf[@intFromEnum(d)];
}

pub inline fn set_flags(self: *DeclPool, d: Index, v: Entry.Flags) void {
    self.entries.pool.flags.buf[@intFromEnum(d)] = v;
}

pub inline fn flags_ptr(self: *DeclPool, d: Index) *Entry.Flags {
    return &self.entries.pool.flags.buf[@intFromEnum(d)];
}

pub inline fn get_state(self: *const DeclPool, d: Index) Entry.State {
    return self.entries.pool.state.buf[@intFromEnum(d)];
}

pub inline fn set_state(self: *DeclPool, d: Index, v: Entry.State) void {
    self.entries.pool.state.buf[@intFromEnum(d)] = v;
}

pub inline fn state_ptr(self: *DeclPool, d: Index) *Entry.State {
    return &self.entries.pool.state.buf[@intFromEnum(d)];
}

pub inline fn get_ty(self: *const DeclPool, d: Index) StaticPool.Index {
    return self.entries.pool.ty.buf[@intFromEnum(d)];
}

pub inline fn set_ty(self: *DeclPool, d: Index, v: StaticPool.Index) void {
    self.entries.pool.ty.buf[@intFromEnum(d)] = v;
}

pub inline fn get_value(self: *const DeclPool, d: Index) StaticPool.Index {
    return self.entries.pool.value.buf[@intFromEnum(d)];
}

pub inline fn set_value(self: *DeclPool, d: Index, v: StaticPool.Index) void {
    self.entries.pool.value.buf[@intFromEnum(d)] = v;
}

pub inline fn get_next_overload(self: *const DeclPool, d: Index) Index {
    return self.entries.pool.next_overload.buf[@intFromEnum(d)];
}

pub inline fn set_next_overload(self: *DeclPool, d: Index, v: Index) void {
    self.entries.pool.next_overload.buf[@intFromEnum(d)] = v;
}

pub inline fn next_overload_ptr(self: *DeclPool, d: Index) *Index {
    return &self.entries.pool.next_overload.buf[@intFromEnum(d)];
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
pub fn self_off(self: *const DeclPool, d: Index) usize {
    return @intFromBool(self.get_kind(d) == .trait_member and self.get_name(d) != .init);
}
