const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// mutability: whether an assignable may be written, which methods write `self`
const Mutability = @This();

const Access = enum {
    ok,
    immutable,
    through_ptr,
};

pub fn res(self: *Mutability) *Resolver {
    return @alignCast(@fieldParentPtr("mutability", self));
}

pub fn check_assignable(self: *Mutability, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    // self is mutable in methods; stc locals are compile-time variables and writable too
    const t = r.exprs.infer(ctx, node, .none);
    if (t == .poison_type and r.doc.errors_since(r.tree, 0, node)) return t;
    self.write_access(node, self.writable(node));
    return t;
}

pub fn write_access(self: *Mutability, node: NodeId, a: Access) void {
    const r = self.res();
    switch (a) {
        .ok => self.wrote(node),
        .immutable => r.doc.report(.assign_to_immutable, node, 0, 0),
        .through_ptr => r.doc.report(.write_through_immutable_pointer, node, 0, 0),
    }
}

// a write into an assignable rooted at `self` (not through a pointer it holds) makes its method one that writes self
pub fn wrote(self: *Mutability, assignable: NodeId) void {
    const r = self.res();
    var n = assignable;
    while (r.tree.kind(n) != .identifier_self) switch (r.tree.kind(n)) {
        .capture => n = r.tree.arg(n, 0),
        .member, .array_index, .dereference => {
            const p = r.tree.arg(n, 0);
            if (r.tree.kind(p) != .identifier_self and (r.tree.kind(n) == .dereference or r.static_pool.is_ptr(r.node_type[p]))) return;
            n = p;
        },
        else => return,
    };
    const d = r.node_decl[n];
    if (d != .none and r.decl_pool.get_kind(d) == .self) r.decl_pool.flags_ptr(d).writes = true;
}

pub fn writable(self: *Mutability, node: NodeId) Access {
    const r = self.res();
    return switch (r.tree.kind(node)) {
        .capture => self.writable(r.tree.arg(node, 0)),
        .identifier, .identifier_self => blk: {
            const d = r.node_decl[node];
            if (d == .none) break :blk .ok;
            const f = r.decl_pool.get_flags(d);
            break :blk if (f.is_mut or f.is_stc or r.decl_pool.get_kind(d) == .self) .ok else .immutable;
        },
        .member => blk: {
            const base = self.through(r.tree.arg(node, 0), true);
            break :blk if (base != .ok) base else if (self.field_mut(r.node_type[r.tree.arg(node, 0)], r.name_pool.name_of(r.tree.arg(node, 1)))) .ok else .immutable;
        },
        .array_index => self.through(r.tree.arg(node, 0), true),
        .dereference => self.through(r.tree.arg(node, 0), false),
        else => .immutable,
    };
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent itself is writable
fn through(self: *Mutability, parent: NodeId, or_assignable: bool) Access {
    const r = self.res();
    const sp = &r.static_pool;
    const pt = r.node_type[parent];
    if (pt == .none or pt == .poison_type) return .ok;
    const t = sp.apply_vars(&r.abstract_pool, pt);
    if (sp.get(t) == .ptr_type) return if (sp.get(t).ptr_type.mutable) .ok else .through_ptr;
    return if (or_assignable) self.writable(parent) else .immutable;
}

fn field_mut(self: *Mutability, pt: StaticPool.Index, name: NamePool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    if (pt == .none or pt == .poison_type) return true;
    var t = sp.apply_vars(&r.abstract_pool, pt);
    t = sp.pointee(t);
    if (sp.tag(t) == .variant_case_type) t = sp.get(t).variant_case_type.payload;
    if (t != .none and sp.tag(t) == .template_type) if (r.generics.template_field(sp.get(t).template_type, name)) |f| return ParseTree.Param.from_node(r.tree, f).is_mut;
    if (t == .none or sp.tag(t) != .record_type) return false;
    for (sp.get(t).custom_type.field_names, 0..) |n, i| if (n == name) return ParseTree.Param.from_node(r.tree, r.types.fields_of(t)[i]).is_mut;
    return false;
}

fn calls_writer(self: *Mutability, m: DeclPool.Index) bool {
    const r = self.res();
    const s = r.tree.subtree(r.decls.value_node(m));
    for (s[0]..s[1]) |x| {
        const d = r.node_decl[x];
        if (r.tree.kind(@intCast(x)) != .fun_call or d == .none or r.tree.kind(r.tree.arg(@intCast(x), 0)) != .member) continue;
        if (r.tree.kind(r.tree.arg(r.tree.arg(@intCast(x), 0), 0)) == .identifier_self and r.decl_pool.get_flags(r.decls.real(d)).writes) return true;
    }
    return false;
}

// a method calling one that writes self writes self too, over the `n` members of a trait body until nothing changes
pub fn propagate_writes(self: *Mutability, body: DeclPool.Index, n: usize) void {
    const r = self.res();
    var grew = true;
    while (grew) {
        grew = false;
        for (0..n) |i| if (!r.decl_pool.get_flags(body.member(i)).writes and self.calls_writer(body.member(i))) {
            r.decl_pool.flags_ptr(body.member(i)).writes = true;
            grew = true;
        };
    }
}
