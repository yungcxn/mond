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
    _ = alloc;
    @panic("unimplemented");
}

pub fn deinit(self: *AbstractPool) void {
    _ = self;
    @panic("unimplemented");
}

pub fn fresh(self: *AbstractPool, origin: u32) Index {
    // new var that is its own root, binding none, origin = the node that needed it (for error messages)
    _ = .{ self, origin };
    @panic("unimplemented");
}

pub fn find(self: *AbstractPool, v: Index) Index {
    // walk to the root, pointing every visited var at its grandparent (path halving)
    // only through parents
    _ = .{ self, v };
    @panic("unimplemented");
}

pub fn bind(self: *AbstractPool, v: Index, ty: Resolver.StaticPool.Index) void {
    // set the binding of the root of v, the occurs check is done by Pool.unify before
    _ = .{ self, v, ty };
    @panic("unimplemented");
}

pub fn link(self: *AbstractPool, a: Index, b: Index) void {
    // join two unbound groups by pointing one root at the other
    _ = .{ self, a, b };
    @panic("unimplemented");
}

pub fn binding(self: *AbstractPool, v: Index) Resolver.StaticPool.Index {
    // binding of the root of v, or none
    _ = .{ self, v };
    @panic("unimplemented");
}

pub fn count(self: *const AbstractPool) u32 {
    // zero means no inference happened at all, so the final fix-up pass can be skipped
    _ = self;
    @panic("unimplemented");
}
