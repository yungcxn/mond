const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// mutability: whether an assignable may be written, which methods write `self`
const Mutability = @This();

const Access = enum {
    ok,
    immutable,
    through_ptr,
};

pub fn owning_resolver(self: *Mutability) *Resolver {
    return @alignCast(@fieldParentPtr("mutability", self));
}

pub fn check_assignable(
    self: *Mutability,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const mark = resolver.doctor.diagnostics.len();
    const assignable_type = resolver.expressions.infer(context, node, .none);
    // a target that failed to check is already reported, its mutability would only add noise
    const failed = assignable_type == .poison_type and
        resolver.doctor.errors_since(resolver.tree, mark, node);
    if (failed) return assignable_type;

    self.record_write_access(node, self.writable(node));
    resolver.slices.writes_into(node);
    return assignable_type;
}

pub fn record_write_access(self: *Mutability, node: NodeId, access: Access) void {
    const resolver = self.owning_resolver();
    switch (access) {
        .ok => self.mark_written_through(node),
        .immutable => resolver.doctor.report(.assign_to_immutable, node, 0, 0),
        .through_ptr => resolver.doctor.report(.write_through_immutable_pointer, node, 0, 0),
    }
}

// a write into an assignable rooted at `self` (not through a pointer it holds) writes self
pub fn mark_written_through(self: *Mutability, assignable: NodeId) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;

    var node = assignable;
    while (tree.kind(node) != .identifier_self) switch (tree.kind(node)) {
        .capture => node = tree.arg(node, 0),
        .member, .array_index, .dereference => {
            const parent = tree.arg(node, 0);
            // a dereference or a step through a pointer member writes the pointee, not `self`
            const leaves_self = tree.kind(parent) != .identifier_self and
                (tree.kind(node) == .dereference or
                    resolver.static_pool.is_pointer(resolver.node_types[parent]));
            if (leaves_self) return;
            node = parent;
        },
        else => return,
    };

    const declaration = resolver.node_declarations[node];
    if (declaration == .none) return;
    if (resolver.decl_pool.get(declaration, .kind) != .self) return;
    resolver.decl_pool.pointer(declaration, .flags).writes = true;
}

pub fn writable(self: *Mutability, node: NodeId) Access {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    return switch (tree.kind(node)) {
        .capture => self.writable(tree.arg(node, 0)),
        .identifier, .identifier_self => self.identifier_access(node),
        .member => self.member_access(node),
        .array_index => self.access_through_parent(tree.arg(node, 0), true),
        .dereference => self.access_through_parent(tree.arg(node, 0), false),
        else => .immutable,
    };
}

// self is mutable in methods; stc locals are compile-time variables and writable too
fn identifier_access(self: *Mutability, node: NodeId) Access {
    const resolver = self.owning_resolver();
    const declaration = resolver.node_declarations[node];
    if (declaration == .none) return .ok;

    const flags = resolver.decl_pool.get(declaration, .flags);
    const is_self = resolver.decl_pool.get(declaration, .kind) == .self;
    return if (flags.is_mut or flags.is_stc or is_self) .ok else .immutable;
}

fn member_access(self: *Mutability, node: NodeId) Access {
    const resolver = self.owning_resolver();
    const owner = resolver.tree.arg(node, 0);
    const owner_access = self.access_through_parent(owner, true);
    if (owner_access != .ok) return owner_access;

    const name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));
    const owner_type = resolver.node_types[owner];
    const static_pool = &resolver.static_pool;
    if (owner_type == .none or owner_type == .poison_type) return .ok;

    var record_type = static_pool.substitute_type_variables(owner_type);
    record_type = static_pool.pointee(record_type);
    if (resolver.tree.macros and static_pool.tag(record_type) == .ast_type) return .ok;
    if (static_pool.tag(record_type) == .variant_case_type) {
        record_type = static_pool.get(record_type).variant_case_type.payload;
    }

    if (record_type != .none and static_pool.tag(record_type) == .template_type) {
        const template = static_pool.get(record_type).template_type;
        if (resolver.generics.template_field(template, name)) |field_node| {
            const is_mut = ParseTree.Param.from_node(resolver.tree, field_node).is_mut;
            return if (is_mut) .ok else .immutable;
        }
    }

    if (record_type == .none or static_pool.tag(record_type) != .record_type) return .immutable;
    const field_names = static_pool.get(record_type).record_type.field_names;
    for (field_names, 0..) |field_name, i| if (field_name == name) {
        const field_node = resolver.types.field_nodes_of(record_type)[i];
        const is_mut = ParseTree.Param.from_node(resolver.tree, field_node).is_mut;
        return if (is_mut) .ok else .immutable;
    };
    return .immutable;
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent is writable
fn access_through_parent(self: *Mutability, parent: NodeId, or_assignable: bool) Access {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const parent_type = resolver.node_types[parent];
    if (parent_type == .none or parent_type == .poison_type) return .ok;

    const resolved_type = static_pool.substitute_type_variables(parent_type);
    // a slice refers to elements it does not hold, whether they may be written is a question of
    // where it came from (see `Slices`)
    if (static_pool.tag(resolved_type) == .slice_type) return .ok;
    if (static_pool.get(resolved_type) == .pointer_type) {
        const is_mutable = static_pool.get(resolved_type).pointer_type.is_mutable;
        return if (is_mutable) .ok else .through_ptr;
    }
    return if (or_assignable) self.writable(parent) else .immutable;
}

// a method calling one that writes self writes self too, over the `member_count` members of a
// trait body until nothing changes
pub fn propagate_writes(self: *Mutability, body: DeclPool.Index, member_count: usize) void {
    const resolver = self.owning_resolver();
    var grew = true;
    while (grew) {
        grew = false;
        for (0..member_count) |i| {
            const member = body.member(i);
            if (resolver.decl_pool.get(member, .flags).writes) continue;
            // whether `member` calls a method on `self` that writes self
            const calls_self_writer = blk: {
                const tree = resolver.tree;
                const subtree = tree.subtree(resolver.declarations.value_node(member));
                for (subtree[0]..subtree[1]) |index| {
                    const node: NodeId = @intCast(index);
                    const callee_declaration = resolver.node_declarations[index];
                    if (tree.kind(node) != .fun_call or callee_declaration == .none) continue;

                    const callee = tree.arg(node, 0);
                    if (tree.kind(callee) != .member) continue;
                    if (tree.kind(tree.arg(callee, 0)) != .identifier_self) continue;

                    const realized = resolver.declarations.realized(callee_declaration);
                    if (resolver.decl_pool.get(realized, .flags).writes) break :blk true;
                }
                break :blk false;
            };
            if (!calls_self_writer) continue;
            resolver.decl_pool.pointer(member, .flags).writes = true;
            grew = true;
        }
    }
}
