const std = @import("std");
const DynBuf = @import("../../ds/dynbuf.zig").DynBuf;
const DeclPool = @import("../DeclPool.zig");

// definite initialization: one bit per local not written yet, in sets of equal width on a stack,
// sets are addressed by index so the width can grow under them; a session owns the sets above its base,
// set 0 of the open session is the current state
const Inits = @This();

// the locals with a bit, in bit order
tracked: DynBuf(DeclPool.Index),
words: DynBuf(u64),
base: u32 = 0,
width: u32 = 1,
count: u32 = 0,
// per open loop the set its exits merge into
exits: DynBuf(u32),

pub const Session = struct { tracked: u32, base: u32, width: u32, count: u32 };

pub fn init(alloc: std.mem.Allocator) Inits {
    return .{ .tracked = .init(alloc, 64), .words = .init(alloc, 64), .exits = .init(alloc, 16) };
}

pub fn deinit(self: *Inits) void {
    self.tracked.deinit();
    self.words.deinit();
    self.exits.deinit();
}

pub fn enter(self: *Inits) Session {
    const s = Session{ .tracked = self.tracked.head, .base = self.base, .width = self.width, .count = self.count };
    self.base = self.words.head;
    self.count = 0;
    _ = self.new();
    return s;
}

pub fn leave(self: *Inits, s: Session) void {
    self.tracked.head = s.tracked;
    self.words.head = self.base;
    self.base = s.base;
    self.width = s.width;
    self.count = s.count;
}

pub fn new(self: *Inits) u32 {
    self.words.extend(self.width, 0);
    self.count += 1;
    return self.count - 1;
}

pub fn release(self: *Inits, count: u32) void {
    self.count = count;
    self.words.head = self.base + count * self.width;
}

fn at(self: *const Inits, i: u32) []u64 {
    return self.words.buf[self.base + i * self.width ..][0..self.width];
}

pub fn copy(self: *Inits, dst: u32, src: u32) void {
    @memcpy(self.at(dst), self.at(src));
}

pub fn save(self: *Inits, src: u32) u32 {
    const d = self.new();
    self.copy(d, src);
    return d;
}

pub fn merge(self: *Inits, dst: u32, src: u32) void {
    for (self.at(dst), self.at(src)) |*a, b| a.* |= b;
}

pub fn clear(self: *Inits, i: u32) void {
    @memset(self.at(i), 0);
}

pub fn empty(self: *const Inits, i: u32) bool {
    for (self.at(i)) |w| if (w != 0) return false;
    return true;
}

pub fn get(self: *const Inits, i: u32, bit: u32) bool {
    return bit / 64 < self.width and self.at(i)[bit / 64] >> @intCast(bit % 64) & 1 != 0;
}

pub fn put(self: *Inits, i: u32, bit: u32, on: bool) void {
    if (bit / 64 >= self.width) {
        if (!on) return;
        self.grow(bit / 64 + 1);
    }
    const m = @as(u64, 1) << @intCast(bit % 64);
    const w = &self.at(i)[bit / 64];
    w.* = if (on) w.* | m else w.* & ~m;
}

// a set of the session `s` around the open one, zero-extended to this width
pub fn import(self: *Inits, dst: u32, s: Session, src: u32) void {
    self.clear(dst);
    @memcpy(self.at(dst)[0..s.width], self.words.buf[s.base + src * s.width ..][0..s.width]);
}

fn grow(self: *Inits, width: u32) void {
    const old = self.width;
    self.words.extend((width - old) * self.count, 0);
    self.width = width;
    var i = self.count;
    while (i > 0) {
        i -= 1;
        const from = self.base + i * old;
        const to = self.base + i * width;
        var j = old;
        while (j > 0) {
            j -= 1;
            self.words.buf[to + j] = self.words.buf[from + j];
        }
        @memset(self.words.buf[to + old .. to + width], 0);
    }
}

pub fn track(self: *Inits, d: DeclPool.Index) void {
    self.put(0, self.tracked.head, true);
    self.tracked.push(d);
}

pub fn tracked_at(self: *const Inits, d: DeclPool.Index) ?u32 {
    return @intCast(std.mem.indexOfScalar(DeclPool.Index, self.tracked.sliced(), d) orelse return null);
}

pub fn written(self: *Inits, d: DeclPool.Index) void {
    if (self.tracked_at(d)) |i| self.put(0, i, false);
}

// a read of `d` before it is written, reported once
pub fn unwritten(self: *Inits, d: DeclPool.Index) bool {
    if (self.empty(0)) return false;
    const i = self.tracked_at(d) orelse return false;
    if (!self.get(0, i)) return false;
    self.put(0, i, false);
    return true;
}
