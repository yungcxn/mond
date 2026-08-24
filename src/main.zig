const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");

inline fn alloc_file_bytes(alloc: std.mem.Allocator, io: std.Io, file: std.Io.File) []u8 {
    const max_file_size = 50 * 1024 * 1024;

    var reader_buf: [4096]u8 = undefined;
    var freader = file.reader(io, &reader_buf);
    const reader: *std.Io.Reader = &freader.interface;
    const result = reader.allocRemaining(
        alloc,
        std.Io.Limit.limited(max_file_size),
    ) catch |e| @panic(@errorName(e));
    return result;
}

const debug = true;

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;

    const in_f = std.Io.Dir.cwd().openFile(io, "./examples/parsetest.mn", .{}) catch @panic("File not found");
    const in_bytes = alloc_file_bytes(alloc, io, in_f);
    defer alloc.free(in_bytes);

    var lexer: Lexer = .{
        .src_bytes = in_bytes,
        .tokens = .init(alloc, 10000),
    };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch |e| return lexer.handle_err(io, e);

    var parser: Parser = .init(alloc, lexer.tokens, in_bytes, lexer.tokens.sliced_field(.span));
    defer parser.deinit();
    parser.build_ast() catch |e| parser.handle_err(io, e);

    if (debug) parser.tree.debug_print_tree(io, in_bytes, parser.func_store.sliced()) catch |e| @panic(@errorName(e));
}
