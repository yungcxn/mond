const Resolver = @import("../../Resolver.zig");

// definite initialization: one bit per local not written yet, in sets of equal width on a stack,
// sets are addressed by index so the width can grow under them; a session owns the sets above its base

pub const Session = struct { base: u32, width: u32, count: u32 };

pub fn enter(self: *Resolver) Session {
    defer {
        self.init_base = self.init_words.head;
        self.init_count = 0;
    }
    return .{ .base = self.init_base, .width = self.init_width, .count = self.init_count };
}

pub fn leave(self: *Resolver, s: Session) void {
    self.init_words.head = self.init_base;
    self.init_base = s.base;
    self.init_width = s.width;
    self.init_count = s.count;
}

pub fn new(self: *Resolver) u32 {
    self.init_words.extend(self.init_width, 0);
    self.init_count += 1;
    return self.init_count - 1;
}

pub fn release(self: *Resolver, count: u32) void {
    self.init_count = count;
    self.init_words.head = self.init_base + count * self.init_width;
}

fn at(self: *const Resolver, i: u32) []u64 {
    return self.init_words.buf[self.init_base + i * self.init_width ..][0..self.init_width];
}

pub fn copy(self: *Resolver, dst: u32, src: u32) void {
    @memcpy(at(self, dst), at(self, src));
}

pub fn save(self: *Resolver, src: u32) u32 {
    const d = new(self);
    copy(self, d, src);
    return d;
}

pub fn merge(self: *Resolver, dst: u32, src: u32) void {
    for (at(self, dst), at(self, src)) |*a, b| a.* |= b;
}

pub fn clear(self: *Resolver, i: u32) void {
    @memset(at(self, i), 0);
}

pub fn empty(self: *const Resolver, i: u32) bool {
    for (at(self, i)) |w| if (w != 0) return false;
    return true;
}

pub fn get(self: *const Resolver, i: u32, bit: u32) bool {
    return bit / 64 < self.init_width and at(self, i)[bit / 64] >> @intCast(bit % 64) & 1 != 0;
}

pub fn put(self: *Resolver, i: u32, bit: u32, on: bool) void {
    if (bit / 64 >= self.init_width) {
        if (!on) return;
        grow(self, bit / 64 + 1);
    }
    const m = @as(u64, 1) << @intCast(bit % 64);
    const w = &at(self, i)[bit / 64];
    w.* = if (on) w.* | m else w.* & ~m;
}

// a set of the session `s` around the open one, zero-extended to this width
pub fn import(self: *Resolver, dst: u32, s: Session, src: u32) void {
    clear(self, dst);
    @memcpy(at(self, dst)[0..s.width], self.init_words.buf[s.base + src * s.width ..][0..s.width]);
}

fn grow(self: *Resolver, width: u32) void {
    const old = self.init_width;
    self.init_words.extend((width - old) * self.init_count, 0);
    self.init_width = width;
    var i = self.init_count;
    while (i > 0) {
        i -= 1;
        const from = self.init_base + i * old;
        const to = self.init_base + i * width;
        var j = old;
        while (j > 0) {
            j -= 1;
            self.init_words.buf[to + j] = self.init_words.buf[from + j];
        }
        @memset(self.init_words.buf[to + old .. to + width], 0);
    }
}
