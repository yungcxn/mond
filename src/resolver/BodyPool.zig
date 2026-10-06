const std = @import("std");
const SoD = @import("../ds/dynbuf.zig").SoD;
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../ParseTree.zig");
const StaticPool = @import("StaticPool.zig");
const DeclPool = @import("DeclPool.zig");

// the node tables of checked bodies and type definitions, kept as realizations share their nodes,
// the interpreter runs them and the lowerer lowers them
const BodyPool = @This();

// the nodes lo..lo+len, their tables at start, the declarations first..first+locals are its locals
pub const Body = struct {
    decl: DeclPool.Index = .none,
    lo: ParseTree.NodeId = 0,
    len: u32 = 0,
    start: u32 = 0,
    first: u32 = 0,
    locals: u32 = 0,
};

pub const NodeInfo = struct {
    ty: StaticPool.Index,
    decl: DeclPool.Index,
    value: StaticPool.Index,
};

alloc: std.mem.Allocator,
list: SoD(Body),
nodes: SoD(NodeInfo),
of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,

pub fn init(alloc: std.mem.Allocator) BodyPool {
    return .{ .alloc = alloc, .list = .init(alloc, 256), .nodes = .init(alloc, 4096) };
}

pub fn deinit(self: *BodyPool) void {
    self.list.deinit();
    self.nodes.deinit();
    self.of.deinit(self.alloc);
}

// `b` with copies of its slice of the node tables
pub fn capture(self: *BodyPool, b: Body, ty: []const StaticPool.Index, decl: []const DeclPool.Index, value: []const StaticPool.Index) Body {
    var c = b;
    c.start = self.nodes.len();
    self.nodes.pool.ty.append(ty[b.lo..][0..b.len]);
    self.nodes.pool.decl.append(decl[b.lo..][0..b.len]);
    self.nodes.pool.value.append(value[b.lo..][0..b.len]);
    return c;
}

pub fn put(self: *BodyPool, b: Body) void {
    self.of.put(self.alloc, b.decl, self.list.len()) catch @panic("OOM");
    self.list.push(b);
}

pub fn get(self: *BodyPool, d: DeclPool.Index) ?Body {
    return self.list.get(self.of.get(d) orelse return null);
}

// the locals a function body reads from the bodies around it, its environment as a closure
pub fn captures(self: *BodyPool, decls: *const DeclPool, d: DeclPool.Index, out: *DynBuf(DeclPool.Index)) void {
    const start = out.head;
    const b = self.get(d) orelse return;
    for (self.nodes.sliced_field(.decl)[b.start..][0..b.len]) |x| {
        if (x == .none or std.mem.indexOfScalar(DeclPool.Index, out.buf[start..out.head], x) != null) continue;
        const flags = decls.flags()[@intFromEnum(x)];
        const node = decls.nodes()[@intFromEnum(x)];
        const local = switch (decls.kinds()[@intFromEnum(x)]) {
            .variable, .parameter, .loop_variable, .pattern_binder, .arrow_binder, .autoins_it, .autoins_arg, .self => true,
            else => false,
        };
        if (local and !flags.is_global and !(flags.is_stc and decls.values()[@intFromEnum(x)] != .none) and (node < b.lo or node >= b.lo + b.len)) out.push(x);
    }
}
