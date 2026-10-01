const std = @import("std");
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;

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
    none = std.math.maxInt(u32),
    _,

    pub const first_dynamic: u32 = @intFromEnum(Index.tag) + 1;
};

alloc: std.mem.Allocator,
map: std.StringArrayHashMapUnmanaged(void),

pub fn init(alloc: std.mem.Allocator) NamePool {
    return .{ .alloc = alloc, .map = .{} };
}

pub fn deinit(self: *NamePool) void {
    self.map.deinit(self.alloc);
}

pub fn intern_predefineds(self: *NamePool) void {
    inline for (@typeInfo(Index).@"enum".fields) |f| {
        if (@field(Index, f.name) == Index.empty) {
            _ = self.intern("");
        } else if (@field(Index, f.name) == Index.underscore) {
            _ = self.intern("_");
        } else if (@field(Index, f.name) == Index.self) {
            _ = self.intern("self");
        } else {
            _ = self.intern("$" ++ f.name);
        }
    }
}

pub fn intern(self: *NamePool, text: []const u8) Index {
    const gop = self.map.getOrPut(self.alloc, text) catch @panic("OOM");
    return @enumFromInt(gop.index); // stable since we never remove entries
}

pub fn get(self: *const NamePool, name: Index) []const u8 {
    return self.map.keys()[@intFromEnum(name)];
}
