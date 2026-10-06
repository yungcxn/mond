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
// the captures of each closure, computed once its body is checked
caps: std.AutoHashMapUnmanaged(DeclPool.Index, [2]u32) = .empty,
cap_list: DynBuf(DeclPool.Index),

pub fn init(alloc: std.mem.Allocator) BodyPool {
    return .{ .alloc = alloc, .list = .init(alloc, 256), .nodes = .init(alloc, 4096), .cap_list = .init(alloc, 64) };
}

pub fn deinit(self: *BodyPool) void {
    self.list.deinit();
    self.nodes.deinit();
    self.of.deinit(self.alloc);
    self.caps.deinit(self.alloc);
    self.cap_list.deinit();
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
pub fn captures(self: *BodyPool, decls: *const DeclPool, d: DeclPool.Index) []const DeclPool.Index {
    if (self.caps.get(d)) |c| return self.cap_list.buf[c[0]..][0..c[1]];
    const b = self.get(d) orelse return &.{};
    const start = self.cap_list.head;
    for (self.nodes.sliced_field(.decl)[b.start..][0..b.len]) |x| {
        if (x == .none or std.mem.indexOfScalar(DeclPool.Index, self.cap_list.buf[start..self.cap_list.head], x) != null) continue;
        const flags = decls.get_flags(x);
        const node = decls.get_node(x);
        const local = switch (decls.get_kind(x)) {
            .variable, .parameter, .loop_variable, .pattern_binder, .arrow_binder, .autoins_it, .autoins_arg, .self => true,
            else => false,
        };
        if (local and !flags.is_global and !(flags.is_stc and decls.get_value(x) != .none) and (node < b.lo or node >= b.lo + b.len)) self.cap_list.push(x);
    }
    self.caps.put(self.alloc, d, .{ start, self.cap_list.head - start }) catch @panic("OOM");
    return self.cap_list.buf[start..self.cap_list.head];
}
