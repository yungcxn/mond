const std = @import("std");
const DynamicBuffer = @import("../../containers.zig").DynamicBuffer;
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const NodeId = ParseTree.NodeId;
const Index = StaticPool.Index;

// where the elements of a slice may be written. every place holding a slice is a slot: a
// declaration, a field of a record, a parameter or the result of a function. a slice flows from
// slot to slot, a write through one marks its slot. a slice of something read-only (a string
// literal, an immutable array, a `&` pointer) must reach no written slot; that is checked once
// everything is, so the order of the declarations does not matter
const Slices = @This();

// the kind in the top bits, below it a declaration, a record and its field, a function and its
// parameter, or a function type and a parameter (`indirect`: of every function of that type)
pub const Slot = u64;
const Kind = enum(u3) { declaration, field, parameter, result, indirect, indirect_result };

// where the elements of a slice come from: a slot, elements that may be written, elements that may
// not (at the node making the slice)
pub const Root = union(enum) { none, writable, read_only: NodeId, slot: Slot };

const Edge = struct { from: Slot, to: Slot };
const Source = struct { node: NodeId, slot: Slot };
const Function = struct { declaration: DeclPool.Index, function_type: Index };

edges: DynamicBuffer(Edge),
sources: DynamicBuffer(Source),
written: DynamicBuffer(Slot),
// the parameters holding slices of the functions checked, by their declaration
parameters: std.AutoHashMapUnmanaged(DeclPool.Index, Slot) = .empty,
functions: DynamicBuffer(Function),

pub fn init(allocator: std.mem.Allocator) Slices {
    return .{
        .edges = .init(allocator, 64),
        .sources = .init(allocator, 16),
        .written = .init(allocator, 16),
        .functions = .init(allocator, 16),
    };
}

pub fn deinit(self: *Slices) void {
    const allocator = self.edges.allocator;
    self.edges.deinit();
    self.sources.deinit();
    self.written.deinit();
    self.parameters.deinit(allocator);
    self.functions.deinit();
}

pub fn owning_resolver(self: *Slices) *Resolver {
    return @alignCast(@fieldParentPtr("slices", self));
}

pub fn slot(kind: Kind, owner: u32, part: u32) Slot {
    return @as(u64, @backingInt(kind)) << 61 | @as(u64, owner) << 24 | part;
}

pub fn declaration_slot(declaration: DeclPool.Index) Slot {
    return slot(.declaration, @backingInt(declaration), 0);
}

// whether values of the type hold slices themselves: a slice, behind pointers, as elements. a
// record or variant holds them in its field slots
pub fn holds_slices(pool: *const StaticPool, type_index: Index) bool {
    if (type_index == .none or type_index == .poison_type) return false;
    return switch (pool.get(type_index)) {
        .slice_type => true,
        .pointer_type => |pointer| holds_slices(pool, pointer.pointee),
        .array_type => |array| holds_slices(pool, array.element),
        else => false,
    };
}

// a function's parameters holding slices are slots of it, so a call reaches them before its body
// is checked; a function type's calls through function values reach those of each function of it
pub fn register_parameter(
    self: *Slices,
    function: DeclPool.Index,
    position: usize,
    declaration: DeclPool.Index,
) void {
    const allocator = self.edges.allocator;
    const parameter_slot = slot(.parameter, @backingInt(function), @intCast(position));
    self.parameters.put(allocator, declaration, parameter_slot) catch @panic("OOM");
}

pub fn register_function(self: *Slices, function: DeclPool.Index, function_type: Index) void {
    self.functions.push(.{ .declaration = function, .function_type = function_type });
}

pub fn connects(self: *Slices, from: Slot, to: Slot) void {
    if (from != to) self.edges.push(.{ .from = from, .to = to });
}

// the slot of the one field of the payload `??` and `?<-` unwrap of a value of the type
pub fn payload_slot(self: *Slices, variant: Index) ?Slot {
    const pool = &self.owning_resolver().static_pool;
    const case = pool.first_payload_case(pool.through_pointer(variant));
    if (case == .none) return null;
    const payload = pool.get(case).variant_case_type.payload;
    if (pool.get(payload).record_type.field_types.len != 1) return null;
    return slot(.field, @backingInt(payload), 0);
}

// `node` flows into the slot `into`: from the slot it is held in, or from where its elements are
pub fn flows(self: *Slices, node: NodeId, into: Slot) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    const pool = &resolver.static_pool;
    if (node == 0) return;
    // code not checked (a branch not taken) holds nothing
    const node_type = self.type_of(node);
    if (node_type == .none or node_type == .poison_type) return;
    // an array may be taken as a slice where it goes
    const is_array = pool.tag(pool.pointee(node_type)) == .array_type;
    if (!is_array and !holds_slices(pool, node_type)) return;
    // a choice flows each of its values
    switch (tree.kind(node)) {
        .if_else, .stcif_else => {
            const branch = ParseTree.Branch.from_node(tree, node);
            self.flows(branch.then, into);
            return self.flows(branch.@"else", into);
        },
        .match, .stcmatch => {
            for (tree.manychildren(tree.arg(node, 1))) |arm| self.flows(tree.arg(arm, 1), into);
            return;
        },
        .block => {
            const statements = tree.manychildren(node);
            if (statements.len > 0) self.flows(statements[statements.len - 1], into);
            return;
        },
        // the payload or the fallback
        .selftag_unwrap_fallback => {
            const variant = self.type_of(tree.arg(node, 0));
            if (self.payload_slot(variant)) |payload| self.connects(payload, into);
            return self.flows(tree.arg(node, 1), into);
        },
        else => {},
    }
    switch (self.root(node)) {
        .none, .writable => {},
        .read_only => |source| self.sources.push(.{ .node = source, .slot = into }),
        .slot => |from| if (from != into) self.edges.push(.{ .from = from, .to = into }),
    }
}

// the elements of the slice `node` are written: its slot is, a read-only source is reported
pub fn writes(self: *Slices, node: NodeId) void {
    switch (self.root(node)) {
        .none, .writable => {},
        .read_only => |source| {
            self.owning_resolver().doctor.report(.write_through_immutable_pointer, source, 0, 0);
        },
        .slot => |written| self.written.push(written),
    }
}

// a write into `target` (`s[i] = ..`, `s[i].x += ..`) writes the elements of the slices it goes
// through, not through a pointer
pub fn writes_into(self: *Slices, target: NodeId) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    var node = target;
    while (true) switch (tree.kind(node)) {
        .capture, .member => node = tree.arg(node, 0),
        .array_index => {
            const base = tree.arg(node, 0);
            const base_type = resolver.static_pool.pointee(self.type_of(base));
            if (resolver.static_pool.tag(base_type) == .slice_type) return self.writes(base);
            node = base;
        },
        else => return,
    };
}

fn type_of(self: *Slices, node: NodeId) Index {
    const resolver = self.owning_resolver();
    return resolver.static_pool.substitute_type_variables(resolver.node_types[node]);
}

// where the elements of the slice (or of the slices behind) `node` come from
pub fn root(self: *Slices, node: NodeId) Root {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    const pool = &resolver.static_pool;
    const node_type = self.type_of(node);
    if (node_type == .none or node_type == .poison_type) return .none;
    // an array or a pointer to one is seen as a slice of its own elements, a part of an array as
    // the array
    const array: ?NodeId = array: {
        if (pool.tag(pool.pointee(node_type)) == .array_type and !holds_slices(pool, node_type)) {
            break :array node;
        }
        const is_part = tree.kind(node) == .array_index and tree.props(tree.arg(node, 1)).range;
        if (!is_part) break :array null;
        const base = tree.arg(node, 0);
        if (pool.tag(pool.pointee(self.type_of(base))) == .slice_type) break :array null;
        break :array base;
    };
    // its elements may be written when it is a writable place (not a static one, which is
    // read-only data at run time) or behind a `*` pointer
    if (array) |place| {
        const place_type = self.type_of(place);
        if (pool.is_pointer(place_type)) {
            const is_mutable = pool.get(place_type).pointer_type.is_mutable;
            return if (is_mutable) .writable else .{ .read_only = place };
        }
        if (!tree.props(place).assignable) {
            // a static array is read-only data, any other value a copy of its own
            const is_static = resolver.node_static_values[place] != .none or tree.is_literal(place);
            return if (is_static) .{ .read_only = place } else .writable;
        }
        var named = place;
        while (tree.kind(named) == .capture) named = tree.arg(named, 0);
        const declaration = resolver.node_declarations[named];
        const is_static = declaration != .none and
            resolver.decl_pool.get(declaration, .flags).is_stc;
        if (is_static) return .{ .read_only = place };
        const writable = resolver.mutability.writable(place) == .ok;
        return if (writable) .writable else .{ .read_only = place };
    }
    return switch (tree.kind(node)) {
        .capture, .dereference, .address_of => self.root(tree.arg(node, 0)),
        .identifier, .identifier_self => {
            const declaration = resolver.node_declarations[node];
            if (declaration == .none) return .none;
            if (self.parameters.get(declaration)) |parameter| return .{ .slot = parameter };
            return .{ .slot = declaration_slot(declaration) };
        },
        // a field holding slices of a record, or of the payload of a case, is a slot of that
        // record
        .member => {
            var record = pool.through_pointer(self.type_of(tree.arg(node, 0)));
            if (pool.tag(record) == .variant_case_type) {
                record = pool.get(record).variant_case_type.payload;
            }
            if (record == .none or pool.tag(record) != .record_type) return .{ .read_only = node };
            const name = resolver.name_pool.name_of_node(tree.arg(node, 1));
            return switch (pool.lookup_member(record, name)) {
                .field => |field| .{ .slot = slot(.field, @backingInt(record), field.index) },
                else => .{ .read_only = node },
            };
        },
        // a part of a slice is of its slice
        .array_index => self.root(tree.arg(node, 0)),
        .fun_call => {
            const callee = resolver.node_declarations[node];
            if (callee != .none) return .{ .slot = slot(.result, @backingInt(callee), 0) };
            // a function value: the results of every function of its type
            const callee_type = self.type_of(tree.arg(node, 0));
            return .{ .slot = slot(.indirect_result, @backingInt(callee_type), 0) };
        },
        .as => self.root(tree.arg(node, 0)),
        .selftag_unwrap => if (self.payload_slot(self.type_of(tree.arg(node, 0)))) |payload|
            .{ .slot = payload }
        else
            .{ .read_only = node },
        // anything else making a slice is taken as read-only
        else => .{ .read_only = node },
    };
}

// every read-only source reaching a written slot is reported where it is made
pub fn finish(self: *Slices) void {
    const resolver = self.owning_resolver();
    const allocator = self.edges.allocator;
    if (self.sources.len == 0 or self.written.len == 0) return;

    // calls through a function value reach the parameters and results of each function of its type
    // (its result inferred by now)
    for (self.functions.items()) |function| {
        const pool = &resolver.static_pool;
        const function_type = pool.substitute_type_variables(function.function_type);
        const parameters = pool.get(function_type).function_type.parameters;
        for (0..parameters.len) |i| self.edges.push(.{
            .from = slot(.indirect, @backingInt(function_type), @intCast(i)),
            .to = slot(.parameter, @backingInt(function.declaration), @intCast(i)),
        });
        self.edges.push(.{
            .from = slot(.result, @backingInt(function.declaration), 0),
            .to = slot(.indirect_result, @backingInt(function_type), 0),
        });
    }

    var written: std.AutoHashMapUnmanaged(Slot, void) = .empty;
    defer written.deinit(allocator);
    for (self.written.items()) |slot_written| {
        written.put(allocator, slot_written, {}) catch @panic("OOM");
    }

    var reached: std.AutoHashMapUnmanaged(Slot, void) = .empty;
    defer reached.deinit(allocator);
    var pending: std.ArrayList(Slot) = .empty;
    defer pending.deinit(allocator);
    for (self.sources.items()) |source| {
        reached.clearRetainingCapacity();
        pending.clearRetainingCapacity();
        pending.append(allocator, source.slot) catch @panic("OOM");
        reached.put(allocator, source.slot, {}) catch @panic("OOM");
        const is_written = while (pending.pop()) |current| {
            if (written.contains(current)) break true;
            for (self.edges.items()) |edge| {
                if (edge.from != current or reached.contains(edge.to)) continue;
                reached.put(allocator, edge.to, {}) catch @panic("OOM");
                pending.append(allocator, edge.to) catch @panic("OOM");
            }
        } else false;
        if (is_written) resolver.doctor.report(.write_through_immutable_pointer, source.node, 0, 0);
    }
}
