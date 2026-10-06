const std = @import("std");
const ParseTree = @import("../ParseTree.zig");

// views into source-file-strings -> mapped to identifier ids (`Index`)
const NamePool = @This();

// - predefined fixed names get fixed ids so the resolver can test `name == .self`
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
    wall,
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(Index.wall) + 1;
};

alloc: std.mem.Allocator,
// the source the names are read from
tree: *const ParseTree,
src_bytes: []const u8,
map: std.StringArrayHashMapUnmanaged(void),
// names that are not in the source (`$64`, ...)
owned: std.heap.ArenaAllocator,

pub fn init(alloc: std.mem.Allocator, tree: *const ParseTree, src_bytes: []const u8) NamePool {
    var self = NamePool{ .alloc = alloc, .tree = tree, .src_bytes = src_bytes, .map = .{}, .owned = .init(alloc) };
    self.intern_predefineds();
    return self;
}

pub fn deinit(self: *NamePool) void {
    self.map.deinit(self.alloc);
    self.owned.deinit();
}

pub inline fn name_of(self: *NamePool, n: ParseTree.NodeId) Index {
    switch (self.tree.kind(n)) {
        .identifier => {
            const s = self.tree.span(n);
            return self.intern_string(self.src_bytes[s[0]..s[1]]);
        },
        .identifier_self => return .self,
        else => return .none,
    }
}

inline fn intern_predefineds(self: *NamePool) void {
    inline for (@typeInfo(Index).@"enum".fields) |f| {
        if (@field(Index, f.name) == Index.empty) {
            _ = self.intern_string("");
        } else if (@field(Index, f.name) == Index.underscore) {
            _ = self.intern_string("_");
        } else if (@field(Index, f.name) == Index.self) {
            _ = self.intern_string("self");
        } else {
            _ = self.intern_string("$" ++ f.name);
        }
    }
}

pub inline fn intern_string(self: *NamePool, str: []const u8) Index {
    const gop = self.map.getOrPut(self.alloc, str) catch @panic("OOM");
    return @enumFromInt(gop.index); // stable since we never remove entries
}

pub inline fn get(self: *const NamePool, name: Index) []const u8 {
    return self.map.keys()[@intFromEnum(name)];
}

// unnamed parameters and fields are `$0`, `$1`, ...
pub fn indexed(self: *NamePool, i: usize) Index {
    const dollars = comptime blk: {
        @setEvalBranchQuota(100_000);
        var t: [64][]const u8 = undefined;
        for (&t, 0..) |*s, j| s.* = std.fmt.comptimePrint("${d}", .{j});
        break :blk t;
    };
    if (i < dollars.len) return self.intern_string(dollars[i]);
    var buf: [24]u8 = undefined;
    const str = std.fmt.bufPrint(&buf, "${d}", .{i}) catch unreachable;
    if (self.map.getIndex(str)) |x| return @enumFromInt(x);
    return self.intern_string(self.owned.allocator().dupe(u8, str) catch @panic("OOM"));
}
