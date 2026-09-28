const std = @import("std");
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const SoD = @import("../ds/dynbuf.zig").SoD;
const Resolver = @import("../Resolver.zig");
const StaticPool = @import("StaticPool.zig");

// a type var is a placeholder for a type the resolver does not know yet, for example:
//   - the return type of `fun f = (i32 x): ret if x == 0: 0 else: f(x - 1)` while its own body is checked
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
const AbstractPool = @This();

const AbstractType = struct {
    parent: Index,
    binding: StaticPool.Index,
    origin: u32,
};

pub const Index = enum(u32) { none = std.math.maxInt(u32), _ };

pool: SoD(AbstractType),

pub fn init(alloc: std.mem.Allocator) AbstractPool {
    return .{ .pool = .init(alloc, 64) };
}

pub fn deinit(self: *AbstractPool) void {
    self.pool.deinit();
}

pub fn fresh(self: *AbstractPool, origin: u32) Index {
    const v: Index = @enumFromInt(self.pool.len());
    self.pool.push(.{ .parent = v, .binding = .none, .origin = origin });
    return v;
}

pub fn find(self: *AbstractPool, v: Index) Index {
    const parents = self.pool.sliced_field(.parent);
    var cur = v;
    while (parents[@intFromEnum(cur)] != cur) {
        const grand = parents[@intFromEnum(parents[@intFromEnum(cur)])];
        parents[@intFromEnum(cur)] = grand;
        cur = grand;
    }
    return cur;
}

pub fn bind(self: *AbstractPool, v: Index, ty: StaticPool.Index) void {
    self.pool.sliced_field(.binding)[@intFromEnum(self.find(v))] = ty;
}

pub fn link(self: *AbstractPool, a: Index, b: Index) void {
    const ra = self.find(a);
    const rb = self.find(b);
    if (ra != rb) self.pool.sliced_field(.parent)[@intFromEnum(ra)] = rb;
}

pub fn binding(self: *AbstractPool, v: Index) StaticPool.Index {
    return self.pool.sliced_field(.binding)[@intFromEnum(self.find(v))];
}

pub fn count(self: *const AbstractPool) u32 {
    return self.pool.len();
}
