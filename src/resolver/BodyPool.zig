const std = @import("std");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const ParseTree = @import("../ParseTree.zig");
const StaticPool = @import("StaticPool.zig");
const DeclPool = @import("DeclPool.zig");

// copies of the node tables of checked bodies and type definitions for the interpreter and lowerer
// kept because realizations of a template share its nodes, the live tables hold only the last one
const BodyPool = @This();

// the nodes from `first_node` with table rows from `first_row`, its locals from `first_local` on
pub const Body = struct {
    declaration: DeclPool.Index = .none,
    first_node: ParseTree.NodeId = 0,
    node_count: u32 = 0,
    first_row: u32 = 0,
    first_local: u32 = 0,
    local_count: u32 = 0,
};

pub const NodeInfo = struct {
    node_type: StaticPool.Index,
    declaration: DeclPool.Index,
    static_value: StaticPool.Index,
};

allocator: std.mem.Allocator,
bodies: StructOfArrays(Body),
node_rows: StructOfArrays(NodeInfo),
// declaration -> its row in `list`
body_index_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
// the captures of each closure as (start, count) in `cap_list`, computed once its body is checked
capture_ranges: std.AutoHashMapUnmanaged(DeclPool.Index, [2]u32) = .empty,
captured_declarations: DynamicBuffer(DeclPool.Index),

pub fn init(alloc: std.mem.Allocator) BodyPool {
    return .{
        .allocator = alloc,
        .bodies = .init(alloc, 256),
        .node_rows = .init(alloc, 4096),
        .captured_declarations = .init(alloc, 64),
    };
}

pub fn deinit(self: *BodyPool) void {
    self.bodies.deinit();
    self.node_rows.deinit();
    self.body_index_of.deinit(self.allocator);
    self.capture_ranges.deinit(self.allocator);
    self.captured_declarations.deinit();
}

// `body` with copies of its slice of the node tables
pub fn copy_node_tables(
    self: *BodyPool,
    body: Body,
    node_types: []const StaticPool.Index,
    node_declarations: []const DeclPool.Index,
    node_static_values: []const StaticPool.Index,
) Body {
    const first = body.first_node;
    const count = body.node_count;

    var copied = body;
    copied.first_row = self.node_rows.len();
    self.node_rows.buffers.node_type.append(node_types[first..][0..count]);
    self.node_rows.buffers.declaration.append(node_declarations[first..][0..count]);
    self.node_rows.buffers.static_value.append(node_static_values[first..][0..count]);
    return copied;
}

pub fn register(self: *BodyPool, body: Body) void {
    self.body_index_of.put(self.allocator, body.declaration, self.bodies.len()) catch @panic("OOM");
    self.bodies.push(body);
}

pub fn body_of(self: *BodyPool, declaration: DeclPool.Index) ?Body {
    const row = self.body_index_of.get(declaration) orelse return null;
    return self.bodies.get(row);
}

// the locals a function body reads from the bodies around it, its environment as a closure
pub fn captures_of(
    self: *BodyPool,
    decl_pool: *const DeclPool,
    function: DeclPool.Index,
) []const DeclPool.Index {
    if (self.capture_ranges.get(function)) |range| {
        return self.captured_declarations.buffer[range[0]..][0..range[1]];
    }
    const body = self.body_of(function) orelse return &.{};

    const start = self.captured_declarations.len;
    const used = self.node_rows.column(.declaration)[body.first_row..][0..body.node_count];
    for (used) |declaration| {
        if (declaration == .none) continue;

        const captured_so_far = self.captured_declarations.items()[start..];
        const seen = std.mem.indexOfScalar(DeclPool.Index, captured_so_far, declaration) != null;
        if (seen) continue;

        if (is_captured(decl_pool, body, declaration)) self.captured_declarations.push(declaration);
    }

    const count = self.captured_declarations.len - start;
    self.capture_ranges.put(self.allocator, function, .{ start, count }) catch @panic("OOM");
    return self.captured_declarations.buffer[start..self.captured_declarations.len];
}

fn is_captured(decl_pool: *const DeclPool, body: Body, declaration: DeclPool.Index) bool {
    if (!decl_pool.get(declaration, .kind).is_runtime_local()) return false;

    const flags = decl_pool.get(declaration, .flags);
    if (flags.is_global) return false;
    // a static local whose value is known is read as that value, not from the environment
    if (flags.is_stc and decl_pool.get(declaration, .static_value) != .none) return false;

    const node = decl_pool.get(declaration, .node);
    const declared_inside = node >= body.first_node and node < body.first_node + body.node_count;
    return !declared_inside;
}
