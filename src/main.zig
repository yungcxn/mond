const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const Resolver = @import("Resolver.zig");
const HighLowerer = @import("HighLowerer.zig");
const dbg = @import("debug.zig");

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

// the architecture the resolver lays types out for
pub const target: struct { pointer_bits: u8 } = .{ .pointer_bits = 64 };

var stage: union(enum) { none, parsed: struct { std.Io, *Parser } } = .none;

pub const panic = std.debug.FullPanic(struct {
    fn f(msg: []const u8, first_trace_addr: ?usize) noreturn {
        switch (stage) {
            .none => {},
            .parsed => |p| dbg.Parser.print_tree(p[0], &p[1].tree, p[1].src_bytes, p[1].global_store.sliced()) catch {},
        }
        std.debug.defaultPanic(msg, first_trace_addr);
    }
}.f);

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;

    const in_f = std.Io.Dir.cwd().openFile(
        io,
        "./examples/huge.mn",
        .{},
    ) catch @panic("File not found");
    const in_bytes = alloc_file_bytes(alloc, io, in_f);
    defer alloc.free(in_bytes);

    var lexer = Lexer{ .src_bytes = in_bytes, .tokens = .init(alloc, 10000) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch |e| return lexer.handle_err(io, e);

    var parser = Parser.init(alloc, lexer.tokens, in_bytes, lexer.tokens.sliced_field(.span));
    defer parser.deinit();
    parser.build_ast() catch |e| parser.handle_err(io, e);

    var dbg_less = false;
    var inspect = false;
    var args = init.minimal.args.iterate();
    while (args.next()) |a| {
        dbg_less = dbg_less or std.mem.eql(u8, a, "--dbg-less");
        inspect = inspect or std.mem.eql(u8, a, "--dbg-inspect");
    }

    if (debug) stage = .{ .parsed = .{ io, &parser } };

    var resolver = Resolver.init(alloc, &parser.tree, in_bytes, parser.global_store.sliced());
    defer resolver.deinit();
    const resolved = if (resolver.resolve()) |_| true else |_| false;
    stage = .none;
    if (inspect and !resolved) return dbg.Inspector.run(io, &resolver, null) catch |e| @panic(@errorName(e));
    if (debug and !inspect) (if (dbg_less) dbg.Resolver.print(io, &resolver) else dbg.Resolver.print_tree(io, &resolver)) catch |e| @panic(@errorName(e));
    if (!resolved) return;

    var lowerer = HighLowerer.init(alloc, &resolver);
    defer lowerer.deinit();
    lowerer.lower();

    if (inspect) return dbg.Inspector.run(io, &resolver, &lowerer) catch |e| @panic(@errorName(e));
    if (debug) dbg.HighLowerer.print(io, &lowerer) catch |e| @panic(@errorName(e));
}
