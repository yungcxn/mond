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
pub const target: struct { pointer_bits: u8 } = .{ .pointer_bits = 64 }; // arch
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

// command line flags,
// - example: the field `dbg_less` is `--dbg-less`
// - just a number: positional arg after execname
// bool: set when present, string: takes the next arg, slice: takes all following args
const Args = struct {
    build: [:0]const u8,
    dbg_less: bool = false,
    inspect: ?[]const [:0]const u8 = null,

    const fields = @typeInfo(Args).@"struct".fields;
    const usage = blk: {
        var u: []const u8 = "usage: mond";
        for (fields) |f| u = u ++ switch (f.type) {
            bool => " [" ++ Args.arg(f.name) ++ "/" ++ Args.short_arg(f.name) ++ "]",
            [:0]const u8 => " " ++ Args.arg(f.name) ++ "/" ++ Args.short_arg(f.name) ++ " <arg>",
            ?[:0]const u8 => " [" ++ Args.arg(f.name) ++ "/" ++ Args.short_arg(f.name) ++ " <arg>]",
            ?[]const [:0]const u8 => " [" ++ Args.arg(f.name) ++ "/" ++ Args.short_arg(f.name) ++ " <args...>]",
            else => @compileError("unsupported flag type " ++ @typeName(f.type)),
        };
        break :blk u ++ "\n";
    };

    fn arg(comptime name: []const u8) []const u8 {
        comptime var f = ("--" ++ name).*;
        std.mem.replaceScalar(u8, &f, '_', '-');
        const out = f;
        return &out;
    }

    fn short_arg(comptime name: []const u8) []const u8 {
        return ("-" ++ name[0..1]);
    }

    fn parse(args: []const [:0]const u8) ?Args {
        var flags: Args = undefined;
        var i: usize = 1;
        next: while (i < args.len) : (i += 1) {
            inline for (fields) |f| if (std.mem.eql(u8, args[i], comptime arg(f.name)) or
                std.mem.eql(u8, args[i], comptime short_arg(f.name)))
            {
                switch (f.type) {
                    bool => @field(flags, f.name) = true,
                    ?[:0]const u8 => {
                        i += 1;
                        @field(flags, f.name) = if (i < args.len) args[i] else null;
                    },
                    [:0]const u8 => {
                        i += 1;
                        @field(flags, f.name) = if (i < args.len) args[i] else return null;
                    },
                    ?[]const [:0]const u8 => {
                        @field(flags, f.name) = args[i + 1 ..];
                        i = args.len;
                    },
                    else => @compileError("unsupported flag type " ++ @typeName(f.type)),
                }
                continue :next;
            };
            return null;
        }
        return flags;
    }
};

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;
    const initargs = init.minimal.args.toSlice(init.arena.allocator()) catch |e| @panic(@errorName(e));
    const args = Args.parse(initargs) orelse return std.debug.print(Args.usage, .{});

    const in_f = std.Io.Dir.cwd().openFile(io, args.build, .{}) catch {
        std.debug.print("Error opening file: {s}\n", .{args.build});
        return;
    };

    const in_bytes = alloc_file_bytes(alloc, io, in_f);
    defer alloc.free(in_bytes);

    var lexer = Lexer{ .src_bytes = in_bytes, .tokens = .init(alloc, 10000) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch |e| return lexer.handle_err(io, e);

    var parser = Parser.init(alloc, lexer.tokens, in_bytes, lexer.tokens.sliced_field(.span));
    defer parser.deinit();
    parser.build_ast() catch |e| parser.handle_err(io, e);

    if (debug) stage = .{ .parsed = .{ io, &parser } };

    var resolver = Resolver.init(alloc, &parser.tree, in_bytes, parser.global_store.sliced());
    defer resolver.deinit();
    const resolved = resolver.resolve() != error.ResolveFailed;

    stage = .none;

    if (args.inspect) |q| if (!resolved) {
        return dbg.Inspector.run(io, &resolver, null, q) catch |e| {
            @panic(@errorName(e));
        };
    };

    if (debug and args.inspect == null) {
        if (args.dbg_less) {
            dbg.Resolver.print(io, &resolver) catch |e| @panic(@errorName(e));
        } else {
            dbg.Resolver.print_tree(io, &resolver) catch |e| @panic(@errorName(e));
        }
    }

    if (!resolved) return;

    var lowerer = HighLowerer.init(alloc, &resolver);
    defer lowerer.deinit();
    lowerer.lower();

    if (args.inspect) |q| {
        return dbg.Inspector.run(io, &resolver, &lowerer, q) catch |e| @panic(@errorName(e));
    }

    if (debug) dbg.HighLowerer.print(io, &lowerer) catch |e| @panic(@errorName(e));
}
