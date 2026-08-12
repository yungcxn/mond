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

    const in_f = std.Io.Dir.cwd().openFile(io, "./examples/vars.mn", .{}) catch @panic("File not found");
    const in_bytes = alloc_file_bytes(alloc, io, in_f);
    defer alloc.free(in_bytes);

    var lexer: Lexer = .{
        .src_bytes = in_bytes,
        .tokens = .init(alloc, 10000),
    };

    defer {
        lexer.tokens.deinit();
    }

    lexer.gen_tokens() catch |e| {
        var buf: [100]u8 = undefined;
        const err_msg = std.fmt.bufPrint(
            &buf,
            "{s}, on token: '{c}' (pos={d})",
            .{ @errorName(e), lexer.src_bytes[lexer.cursor - 1], lexer.cursor - 1 },
        ) catch @panic("OOM, could not print error");
        @panic(err_msg);
    };

    if (debug) lexer.dbg_print_tokens(io);

    var parser: Parser = .init(alloc, lexer.tokens, in_bytes);

    parser.build_ast() catch |e| @panic(@errorName(e));
}
