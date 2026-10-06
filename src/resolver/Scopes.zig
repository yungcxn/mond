const std = @import("std");
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const NamePool = @import("NamePool.zig");
const DeclPool = @import("DeclPool.zig");

// which declaration a name means: the globals by name and the locals of the scopes open around the checked node
const Scopes = @This();

// global names -> first declaration with that name
// - overloads of the same name handled by `DeclPool.next_overloads` for single per-name entry
// - solves: using global before declaring it in a file
globals: std.AutoHashMapUnmanaged(NamePool.Index, DeclPool.Index) = .empty,

// the local scope stack. declaring a local pushes (name, decl); a lookup scans `names`
// backwards, so the innermost declaration wins and shadowing works for free.
// names and decls are two parallel arrays so the scan reads only a dense run of u32 names -
// for the few dozen locals a body has, that beats any hash map and vectorizes well.
names: DynBuf(NamePool.Index),
decls: DynBuf(DeclPool.Index),
// where each open scope starts in the local stack. leaving a scope just truncates the stack
// back to its mark - freeing all its locals at once costs one store.
marks: DynBuf(u32),

pub fn init(alloc: std.mem.Allocator) Scopes {
    return .{ .names = .init(alloc, 256), .decls = .init(alloc, 256), .marks = .init(alloc, 16) };
}

pub fn deinit(self: *Scopes, alloc: std.mem.Allocator) void {
    self.globals.deinit(alloc);
    self.names.deinit();
    self.decls.deinit();
    self.marks.deinit();
}

pub fn h01_lookup(self: *const Scopes, kinds: []const DeclPool.Entry.Kind, name: NamePool.Index) DeclPool.Index {
    const names = self.names.sliced();
    var i = names.len;
    var walled = false;
    while (i > 0) {
        i -= 1;
        if (names[i] == name and (!walled or kinds[@intFromEnum(self.decls.buf[i])].is_type_decl() or kinds[@intFromEnum(self.decls.buf[i])] == .static_function)) return self.decls.buf[i];
        if (names[i] == .none) break; // barrier: a declaration body never sees its user's locals
        walled = walled or names[i] == .wall; // a local type sees only the types and stcfuns of its function
    }
    return self.globals.get(name) orelse .none;
}

pub fn bind(self: *Scopes, name: NamePool.Index, d: DeclPool.Index) void {
    self.names.push(name);
    self.decls.push(d);
}

pub fn h03_push_scope(self: *Scopes) void {
    self.marks.push(self.names.head);
}

pub fn h04_pop_scope(self: *Scopes) void {
    self.marks.head -= 1;
    self.names.head = self.marks.buf[self.marks.head];
    self.decls.head = self.names.head;
}

// the declaration of a name in the innermost scope
pub fn in_scope(self: *const Scopes, name: NamePool.Index) DeclPool.Index {
    const from = self.marks.buf[self.marks.head - 1];
    const i = std.mem.indexOfScalar(NamePool.Index, self.names.buf[from..self.names.head], name) orelse return .none;
    return if (name == .underscore) .none else self.decls.buf[from + i];
}
