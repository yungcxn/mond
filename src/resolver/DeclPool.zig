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
// realizations: the template a declaration was realized from and the static arguments it was realized with
template_of: std.AutoHashMapUnmanaged(Index, Index) = .empty,
realized_args: std.AutoHashMapUnmanaged(Index, StaticPool.Index) = .empty,
// functions produced by a stcfun: the realization whose static parameters they see
static_scope: std.AutoHashMapUnmanaged(Index, StaticPool.AbstractKey) = .empty,

pub inline fn init(alloc: std.mem.Allocator, initial_cap: usize) DeclPool {
    return .{ .alloc = alloc, .entries = SoD(Entry).init(alloc, initial_cap) };
}

pub inline fn deinit(self: *DeclPool) void {
    self.entries.deinit();
    self.template_of.deinit(self.alloc);
    self.realized_args.deinit(self.alloc);
    self.static_scope.deinit(self.alloc);
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

pub inline fn names(self: *const DeclPool) []NamePool.Index {
    return self.entries.pool.name.buf;
}

pub inline fn nodes(self: *const DeclPool) []ParseTree.NodeId {
    return self.entries.pool.node.buf;
}

pub inline fn kinds(self: *const DeclPool) []Entry.Kind {
    return self.entries.pool.kind.buf;
}

pub inline fn flags(self: *const DeclPool) []Entry.Flags {
    return self.entries.pool.flags.buf;
}

pub inline fn states(self: *const DeclPool) []Entry.State {
    return self.entries.pool.state.buf;
}

pub inline fn tys(self: *const DeclPool) []StaticPool.Index {
    return self.entries.pool.ty.buf;
}

pub inline fn values(self: *const DeclPool) []StaticPool.Index {
    return self.entries.pool.value.buf;
}

pub inline fn next_overloads(self: *const DeclPool) []Index {
    return self.entries.pool.next_overload.buf;
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
pub fn self_off(self: *const DeclPool, d: Index) usize {
    return @intFromBool(self.kinds()[@intFromEnum(d)] == .trait_member and self.names()[@intFromEnum(d)] != .init);
}

// methods: the owning type is the value of the trait body row right before its members; realizations ask their template
pub fn owner_of(self: *const DeclPool, decl: Index) StaticPool.Index {
    if (self.template_of.get(decl)) |t| return self.owner_of(t);
    if (self.kinds()[@intFromEnum(decl)] != .trait_member) return .none;
    var d = @intFromEnum(decl);
    while (self.kinds()[d] != .trait) d -= 1;
    return self.values()[d];
}
