const std = @import("std");
const ParseTree = @import("../ParseTree.zig");

// interns identifiers to ids (`Index`), the text of most names is a view into the source
const NamePool = @This();

// predefined names have fixed ids, so the resolver can test `name == .self`
pub const Index = enum(u32) {
    empty,
    underscore,
    it,
    self,
    init,
    deinit,
    main,
    len,
    has_next,
    next,
    tag,
    // what macros ask of trees and the compiler: `$fresh(..)`, `$error(..)`, `refl $file`, `x.$src`
    fresh,
    @"error",
    file,
    src,
    children,
    name,
    params,
    ret,
    body,
    fields,
    cases,
    implof,
    methods,
    type,
    default,
    where,
    mut,
    decls,
    value,
    wall,
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(Index.wall) + 1;
};

allocator: std.mem.Allocator,
// the source the names are read from
tree: *const ParseTree,
src_bytes: []const u8,
text_to_name: std.StringArrayHashMapUnmanaged(void),
// names that are not in the source (`$64`, ...)
owned_texts: std.heap.ArenaAllocator,

pub fn init(alloc: std.mem.Allocator, tree: *const ParseTree, src_bytes: []const u8) NamePool {
    var self = NamePool{
        .allocator = alloc,
        .tree = tree,
        .src_bytes = src_bytes,
        .text_to_name = .{},
        .owned_texts = .init(alloc),
    };
    self.intern_predefineds();
    return self;
}

pub fn deinit(self: *NamePool) void {
    self.text_to_name.deinit(self.allocator);
    self.owned_texts.deinit();
}

pub inline fn name_of_node(self: *NamePool, node: ParseTree.NodeId) Index {
    switch (self.tree.kind(node)) {
        .identifier => {
            // a name with a text of its own (made by a macro) lives in a buffer that may move
            const has_own_text = self.tree.arg(node, 1) != 0;
            if (has_own_text) return self.intern_copy(self.tree.text(node, self.src_bytes));

            const span = self.tree.span(node);
            return self.intern(self.src_bytes[span[0]..span[1]]);
        },
        .identifier_self => return .self,
        else => return .none,
    }
}

// the predefined names in `Index` order, so each lands at its own index. `none` names nothing
inline fn intern_predefineds(self: *NamePool) void {
    inline for (@typeInfo(Index).@"enum".fields) |field| {
        if (comptime @field(Index, field.name) == .none) continue;
        _ = self.intern(comptime predefined_text(field.name));
    }
    std.debug.assert(self.text_to_name.count() == Index.first_dynamic);
}

fn predefined_text(comptime field_name: []const u8) []const u8 {
    return switch (@field(Index, field_name)) {
        .empty => "",
        .underscore => "_",
        .self => "self",
        else => "$" ++ field_name,
    };
}

pub inline fn intern(self: *NamePool, str: []const u8) Index {
    const entry = self.text_to_name.getOrPut(self.allocator, str) catch @panic("OOM");
    // the index is stable, entries are never removed
    return @enumFromInt(entry.index);
}

pub inline fn text_of(self: *const NamePool, name: Index) []const u8 {
    return self.text_to_name.keys()[@intFromEnum(name)];
}

// unnamed parameters and fields are `$0`, `$1`, ...
pub fn positional_name(self: *NamePool, i: usize) Index {
    // the common ones are comptime strings, which live as long as the pool and are never copied
    const dollars = comptime blk: {
        @setEvalBranchQuota(100_000);
        var names: [64][]const u8 = undefined;
        for (&names, 0..) |*name, j| name.* = std.fmt.comptimePrint("${d}", .{j});
        break :blk names;
    };
    if (i < dollars.len) return self.intern(dollars[i]);

    var buffer: [24]u8 = undefined;
    const text = std.fmt.bufPrint(&buffer, "${d}", .{i}) catch unreachable;
    return self.intern_copy(text);
}

// a name from a buffer that does not live as long as the pool, copied when it is new
pub fn intern_copy(self: *NamePool, str: []const u8) Index {
    if (self.text_to_name.getIndex(str)) |index| return @enumFromInt(index);
    return self.intern(self.owned_texts.allocator().dupe(u8, str) catch @panic("OOM"));
}
