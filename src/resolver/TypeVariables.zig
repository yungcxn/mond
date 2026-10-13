const std = @import("std");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const StaticPool = @import("StaticPool.zig");

// a type not known yet: a recursive induced return type, the element type of `x = []`, a length
// interned like any type (tag type_variable), so it can sit inside other types (`[?2]?1`)
const TypeVariables = @This();

pub const Index = enum(u32) { none = std.math.maxInt(u32), _ };

// unified variables form a union-find tree, its root carries the binding of the group
const Variable = struct {
    parent: Index,
    binding: StaticPool.Index,
    // the node the variable was created for, decides how an unbound one is reported
    origin: u32,
};

variables: StructOfArrays(Variable),

pub fn init(allocator: std.mem.Allocator) TypeVariables {
    return .{ .variables = .init(allocator, 64) };
}

pub fn deinit(self: *TypeVariables) void {
    self.variables.deinit();
}

pub fn count(self: *const TypeVariables) u32 {
    return self.variables.len();
}

pub fn create(self: *TypeVariables, origin: u32) Index {
    const variable: Index = @enumFromInt(self.variables.len());
    self.variables.push(.{ .parent = variable, .binding = .none, .origin = origin });
    return variable;
}

// the root of the variable's group, every visited variable is hooked to its grandparent on the way
pub fn root_of(self: *TypeVariables, variable: Index) Index {
    const parents = self.variables.column(.parent);
    var current = variable;
    while (parents[@intFromEnum(current)] != current) {
        const parent = parents[@intFromEnum(current)];
        const grandparent = parents[@intFromEnum(parent)];
        parents[@intFromEnum(current)] = grandparent;
        current = grandparent;
    }
    return current;
}

// the root without shortening any path, for readers that must not write
pub fn root_of_const(self: *const TypeVariables, variable: Index) Index {
    const parents = self.variables.column(.parent);
    var current = variable;
    while (parents[@intFromEnum(current)] != current) current = parents[@intFromEnum(current)];
    return current;
}

pub fn bind(self: *TypeVariables, variable: Index, binding: StaticPool.Index) void {
    self.variables.column(.binding)[@intFromEnum(self.root_of(variable))] = binding;
}

pub fn unite(self: *TypeVariables, first: Index, second: Index) void {
    const first_root = self.root_of(first);
    const second_root = self.root_of(second);
    if (first_root == second_root) return;
    self.variables.column(.parent)[@intFromEnum(first_root)] = second_root;
    // the united group keeps a binding either side had
    const bindings = self.variables.column(.binding);
    if (bindings[@intFromEnum(second_root)] == .none) {
        bindings[@intFromEnum(second_root)] = bindings[@intFromEnum(first_root)];
    }
}

pub fn binding_of(self: *TypeVariables, variable: Index) StaticPool.Index {
    return self.variables.column(.binding)[@intFromEnum(self.root_of(variable))];
}

pub fn binding_of_const(self: *const TypeVariables, variable: Index) StaticPool.Index {
    return self.variables.column(.binding)[@intFromEnum(self.root_of_const(variable))];
}

pub fn origin_of(self: *const TypeVariables, variable: Index) u32 {
    return self.variables.column(.origin)[@intFromEnum(variable)];
}
