const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const exprs = @import("exprs.zig");
const types = @import("types.zig");
const generics = @import("generics.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// places written to: whether a write is allowed, which methods write `self`

const Access = enum {
    ok,
    immutable,
    through_ptr,
};

pub fn h18_check_place(self: *Resolver, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    // self is mutable in methods; stc locals are compile-time variables and writable too
    const t = exprs.h09_check_expr(self, ctx, node, .none);
    if (t == .poison_type and self.doc.errors_since(self.tree, 0, node)) return t;
    write_access(self, node, writable(self, node));
    return t;
}

pub fn write_access(self: *Resolver, node: NodeId, a: Access) void {
    switch (a) {
        .ok => wrote(self, node),
        .immutable => self.doc.h21_report(.assign_to_immutable, node, 0, 0),
        .through_ptr => self.doc.h21_report(.write_through_immutable_pointer, node, 0, 0),
    }
}

// a write into a place rooted at `self` (not through a pointer it holds) makes its method one that writes self
pub fn wrote(self: *Resolver, place: NodeId) void {
    var n = place;
    while (self.tree.kind(n) != .identifier_self) switch (self.tree.kind(n)) {
        .capture => n = self.tree.arg(n, 0),
        .member, .array_index, .dereference => {
            const p = self.tree.arg(n, 0);
            if (self.tree.kind(p) != .identifier_self and (self.tree.kind(n) == .dereference or self.static_pool.is_ptr(self.node_type[p]))) return;
            n = p;
        },
        else => return,
    };
    const d = self.node_decl[n];
    if (d != .none and self.decl_pool.kinds()[@intFromEnum(d)] == .self) self.decl_pool.flags()[@intFromEnum(d)].writes = true;
}

pub fn writable(self: *Resolver, node: NodeId) Access {
    return switch (self.tree.kind(node)) {
        .capture => writable(self, self.tree.arg(node, 0)),
        .identifier, .identifier_self => blk: {
            const d = self.node_decl[node];
            if (d == .none) break :blk .ok;
            const f = self.decl_pool.flags()[@intFromEnum(d)];
            break :blk if (f.is_mut or f.is_stc or self.decl_pool.kinds()[@intFromEnum(d)] == .self) .ok else .immutable;
        },
        .member => blk: {
            const base = through(self, self.tree.arg(node, 0), true);
            break :blk if (base != .ok) base else if (field_mut(self, self.node_type[self.tree.arg(node, 0)], self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(node, 1)))) .ok else .immutable;
        },
        .array_index => through(self, self.tree.arg(node, 0), true),
        .dereference => through(self, self.tree.arg(node, 0), false),
        else => .immutable,
    };
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent itself is writable
fn through(self: *Resolver, parent: NodeId, or_place: bool) Access {
    const sp = &self.static_pool;
    const pt = self.node_type[parent];
    if (pt == .none or pt == .poison_type) return .ok;
    const t = sp.apply_vars(&self.abstract_pool, pt);
    if (sp.get(t) == .ptr_type) return if (sp.get(t).ptr_type.mutable) .ok else .through_ptr;
    return if (or_place) writable(self, parent) else .immutable;
}

fn field_mut(self: *Resolver, pt: StaticPool.Index, name: NamePool.Index) bool {
    const sp = &self.static_pool;
    if (pt == .none or pt == .poison_type) return true;
    var t = sp.apply_vars(&self.abstract_pool, pt);
    t = sp.pointee(t);
    if (sp.tag(t) == .variant_case_type) t = sp.get(t).variant_case_type.payload;
    if (t != .none and sp.tag(t) == .template_type) if (generics.template_field(self, sp.get(t).template_type, name)) |f| return syntax.Param.from_node(self.tree, f).is_mut;
    if (t == .none or sp.tag(t) != .record_type) return false;
    for (sp.get(t).custom_type.field_names, 0..) |n, i| if (n == name) return syntax.Param.from_node(self.tree, types.fields_of(self, t)[i]).is_mut;
    return false;
}
