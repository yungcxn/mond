pub fn FixedStack(len: usize) type {
    return struct {
        buf: [len]u32 = undefined,
        cursor: usize = 0,

        pub inline fn push(self: *@This(), val: u32) !void {
            if (self.cursor >= len) return error.StackOverflow;
            self.buf[self.cursor] = val;
            self.cursor += 1;
        }

        pub inline fn view(self: *@This()) []const u32 {
            return self.buf[0..self.cursor];
        }
    };
}
