const std = @import("std");

pub fn DynBuf(T: type) type {
    return struct {
        alloc: std.mem.Allocator,
        buf: []T,
        head: usize = 0,
        cap: usize,

        pub fn init(alloc: std.mem.Allocator, initial_cap: usize) @This() {
            if (initial_cap == 0) @panic("Zero cap'd dynbuf");
            return @This(){
                .alloc = alloc,
                .buf = alloc.alloc(T, initial_cap) catch @panic("OOM"),
                .cap = initial_cap,
            };
        }

        pub fn deinit(self: *@This()) void {
            self.alloc.free(self.buf);
        }

        inline fn grow(self: *@This()) void {
            self.cap *= 2;
            self.buf = self.alloc.realloc(self.buf, self.cap) catch @panic("OOM");
        }

        pub fn push(self: @This(), value: T) void {
            if (self.head >= self.cap) self.grow();

            self.buf[self.head] = value;
            self.head += 1;
        }

        pub inline fn sliced(self: *const @This()) []T {
            return self.buf[0..self.head];
        }
    };
}
