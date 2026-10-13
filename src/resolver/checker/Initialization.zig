const std = @import("std");
const DynamicBuffer = @import("../../containers.zig").DynamicBuffer;
const DeclPool = @import("../DeclPool.zig");

// definite initialization: one bit per local not written yet, in sets of equal width on a stack
// sets are addressed by index so the width can grow under them; set 0 is the current state
const Initialization = @This();

// the locals with a bit, in bit order
tracked: DynamicBuffer(DeclPool.Index),
words: DynamicBuffer(u64),
base: u32 = 0,
width: u32 = 1,
count: u32 = 0,

pub const Session = struct { tracked: u32, base: u32, width: u32, count: u32 };

pub fn init(alloc: std.mem.Allocator) Initialization {
    var self = Initialization{ .tracked = .init(alloc, 64), .words = .init(alloc, 64) };
    _ = self.new_set();
    return self;
}

pub fn deinit(self: *Initialization) void {
    self.tracked.deinit();
    self.words.deinit();
}

// a session owns the sets above its base, so leaving drops them all at once
pub fn enter(self: *Initialization) Session {
    const outer_session = Session{
        .tracked = self.tracked.len,
        .base = self.base,
        .width = self.width,
        .count = self.count,
    };
    self.base = self.words.len;
    self.count = 0;
    _ = self.new_set();
    return outer_session;
}

pub fn leave(self: *Initialization, outer_session: Session) void {
    self.tracked.len = outer_session.tracked;
    self.words.len = self.base;
    self.base = outer_session.base;
    self.width = outer_session.width;
    self.count = outer_session.count;
}

pub fn new_set(self: *Initialization) u32 {
    self.words.push_repeated(self.width, 0);
    self.count += 1;
    return self.count - 1;
}

pub fn release(self: *Initialization, count: u32) void {
    self.count = count;
    self.words.len = self.base + count * self.width;
}

fn set_words(self: *const Initialization, set: u32) []u64 {
    return self.words.buffer[self.base + set * self.width ..][0..self.width];
}

pub fn copy(self: *Initialization, destination: u32, source: u32) void {
    @memcpy(self.set_words(destination), self.set_words(source));
}

pub fn save(self: *Initialization, source: u32) u32 {
    const saved = self.new_set();
    self.copy(saved, source);
    return saved;
}

pub fn merge(self: *Initialization, destination: u32, source: u32) void {
    for (self.set_words(destination), self.set_words(source)) |*into, from| into.* |= from;
}

pub fn clear(self: *Initialization, set: u32) void {
    @memset(self.set_words(set), 0);
}

pub fn get(self: *const Initialization, set: u32, bit: u32) bool {
    const word_index = bit / 64;
    if (word_index >= self.width) return false;
    return self.set_words(set)[word_index] >> @intCast(bit % 64) & 1 != 0;
}

pub fn put(self: *Initialization, set: u32, bit: u32, on: bool) void {
    const word_index = bit / 64;
    if (word_index >= self.width) {
        // bits past the width read as off, so only switching one on needs room
        if (!on) return;

        // the open session's sets widen in place, back to front so none overwrites an unmoved one
        const old_width = self.width;
        const width = word_index + 1;
        self.words.push_repeated((width - old_width) * self.count, 0);
        self.width = width;

        var set_index = self.count;
        while (set_index > 0) {
            set_index -= 1;
            const from = self.base + set_index * old_width;
            const to = self.base + set_index * width;

            var word = old_width;
            while (word > 0) {
                word -= 1;
                self.words.buffer[to + word] = self.words.buffer[from + word];
            }
            @memset(self.words.buffer[to + old_width .. to + width], 0);
        }
    }

    const mask = @as(u64, 1) << @intCast(bit % 64);
    const word = &self.set_words(set)[word_index];
    word.* = if (on) word.* | mask else word.* & ~mask;
}

// a set of the session `outer_session` around the open one, zero-extended to this width
pub fn import_outer(
    self: *Initialization,
    destination: u32,
    outer_session: Session,
    source: u32,
) void {
    self.clear(destination);
    const outer_start = outer_session.base + source * outer_session.width;
    const outer_words = self.words.buffer[outer_start..][0..outer_session.width];
    @memcpy(self.set_words(destination)[0..outer_session.width], outer_words);
}

pub fn track(self: *Initialization, declaration: DeclPool.Index) void {
    self.put(0, self.tracked.len, true);
    self.tracked.push(declaration);
}

pub fn bit_of(self: *const Initialization, declaration: DeclPool.Index) ?u32 {
    const tracked = self.tracked.items();
    const bit = std.mem.indexOfScalar(DeclPool.Index, tracked, declaration) orelse return null;
    return @intCast(bit);
}

pub fn mark_written(self: *Initialization, declaration: DeclPool.Index) void {
    if (self.bit_of(declaration)) |bit| self.put(0, bit, false);
}

// a read of `declaration` before it is written, reported once
pub fn is_unwritten(self: *Initialization, declaration: DeclPool.Index) bool {
    const is_empty = blk: {
        for (self.set_words(0)) |word| if (word != 0) break :blk false;
        break :blk true;
    };
    if (is_empty) return false;
    const bit = self.bit_of(declaration) orelse return false;
    if (!self.get(0, bit)) return false;
    self.put(0, bit, false);
    return true;
}
