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

pub inline fn names(self: *DeclPool) []NamePool.Index {
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
