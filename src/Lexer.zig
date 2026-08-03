const std = @import("std");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;

const vertwspace = [_]u8{ ' ', '\t' };
const TextSpan = @Vector(2, u32);

const Token = enum(u8) {
    // keywords
    kw_main,
    kw_u32,
    kw_mut,

    lit_name,

    @"$",
    @"(",
    @")",
    @"{",
    @"}",
    @"\"",
    @"'",

    val_string,
    val_int,
    val_float,
    val_char,
    val_true,
    val_false,
};

const RefingToken = struct {
    token: Token,
    span_idx: u32,
};

const LexState = enum(u8) {
    // TODO
};

src_code: []u8,
cursor: usize = 0,
state: LexState,

token_buf: DynBuf(RefingToken),
extra_spans: DynBuf(TextSpan),

pub fn gen_tokens(self: *@This(), alloc: std.mem.Allocator) void {
    _ = .{ self, alloc };
}
