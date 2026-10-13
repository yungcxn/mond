const std = @import("std");
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const NamePool = @import("NamePool.zig");
const DeclPool = @import("DeclPool.zig");

// which declaration a name means: globals by name, the locals of the scopes open around the node
const Scopes = @This();

// the first declaration of every global name, its overloads follow `next_overload`
// filled before any body is checked, so a global can be used above its declaration
globals: std.AutoHashMapUnmanaged(NamePool.Index, DeclPool.Index) = .empty,

// the local stack: a lookup scans it backwards, so the innermost declaration shadows the others
// names apart from declarations: the scan reads dense u32s, beating a map for a few dozen locals
local_names: DynamicBuffer(NamePool.Index),
local_declarations: DynamicBuffer(DeclPool.Index),
// where each open scope starts in the local stack, closing one frees its locals in one store
scope_starts: DynamicBuffer(u32),

pub fn init(alloc: std.mem.Allocator) Scopes {
    return .{
        .local_names = .init(alloc, 256),
        .local_declarations = .init(alloc, 256),
        .scope_starts = .init(alloc, 16),
    };
}

pub fn deinit(self: *Scopes, alloc: std.mem.Allocator) void {
    self.globals.deinit(alloc);
    self.local_names.deinit();
    self.local_declarations.deinit();
    self.scope_starts.deinit();
}

pub fn lookup(
    self: *const Scopes,
    decl_pool: *const DeclPool,
    name: NamePool.Index,
) DeclPool.Index {
    const names = self.local_names.items();
    var i = names.len;
    var walled = false;
    while (i > 0) {
        i -= 1;
        if (names[i] == name) {
            const declaration = self.local_declarations.buffer[i];
            const kind = decl_pool.get(declaration, .kind);
            const seen = kind.is_type_declaration() or kind == .static_function;
            if (!walled or seen) return declaration;
        }
        // a declaration body never sees the locals of its user
        if (names[i] == .none) break;
        // a local type sees only the types and stcfuns of its function
        walled = walled or names[i] == .wall;
    }
    return self.globals.get(name) orelse .none;
}

pub fn bind(self: *Scopes, name: NamePool.Index, declaration: DeclPool.Index) void {
    self.local_names.push(name);
    self.local_declarations.push(declaration);
}

pub fn open(self: *Scopes) void {
    self.scope_starts.push(self.local_names.len);
}

pub fn close(self: *Scopes) void {
    self.scope_starts.len -= 1;
    self.local_names.len = self.scope_starts.buffer[self.scope_starts.len];
    self.local_declarations.len = self.local_names.len;
}

// the declaration of a name in the innermost scope
pub fn in_innermost_scope(self: *const Scopes, name: NamePool.Index) DeclPool.Index {
    const scope_start = self.scope_starts.buffer[self.scope_starts.len - 1];
    const scope_names = self.local_names.buffer[scope_start..self.local_names.len];
    const offset = std.mem.indexOfScalar(NamePool.Index, scope_names, name) orelse return .none;
    // `_` may be bound any number of times in one scope
    if (name == .underscore) return .none;
    return self.local_declarations.buffer[scope_start + offset];
}
