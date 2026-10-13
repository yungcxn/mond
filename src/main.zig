const std = @import("std");

// the compiler is also the module `mond` for the tools in lsp/ and stats/
pub const Lexer = @import("Lexer.zig");
pub const Parser = @import("Parser.zig");
pub const ParseTree = @import("ParseTree.zig");
pub const Resolver = @import("Resolver.zig");
pub const HighLowerer = @import("HighLowerer.zig");
pub const DeclPool = @import("resolver/DeclPool.zig");
pub const Doctor = @import("resolver/Doctor.zig");
pub const DynamicBuffer = @import("containers.zig").DynamicBuffer;
pub const dbg = @import("debug.zig");

const debug = true;
pub const target: struct { pointer_bits: u8 } = .{ .pointer_bits = 64 };
// a panic after parsing prints the tree first, the context a compiler bug needs
var stage: union(enum) { none, parsed: struct { std.Io, *Parser } } = .none;

pub const panic = std.debug.FullPanic(struct {
    fn on_panic(message: []const u8, first_trace_address: ?usize) noreturn {
        switch (stage) {
            .none => {},
            .parsed => |parsed| {
                const io, const parser = parsed;
                const roots = parser.global_store.items();
                dbg.Parser.print_tree(io, &parser.tree, parser.src_bytes, roots) catch {};
            },
        }
        std.debug.defaultPanic(message, first_trace_address);
    }
}.on_panic);

// command line flags: the field `dbg_less` is `--dbg-less` or `-d`
// bool: set when present, string: takes the next argument, slice: takes all following arguments
// a field without a default is required
const Args = struct {
    build: [:0]const u8,
    dbg_less: bool = false,
    inspect: ?[]const [:0]const u8 = null,

    const fields = @typeInfo(Args).@"struct".fields;
    const usage = blk: {
        var text: []const u8 = "usage: mond";
        for (fields, 0..) |field, i| {
            for (fields[0..i]) |other| {
                if (other.name[0] != field.name[0]) continue;
                @compileError(short_arg(field.name) ++ " is taken by " ++ arg(other.name));
            }

            const flag = arg(field.name) ++ "/" ++ short_arg(field.name) ++ switch (field.type) {
                bool => "",
                [:0]const u8, ?[:0]const u8 => " <arg>",
                ?[]const [:0]const u8 => " <args...>",
                else => @compileError("unsupported flag type " ++ @typeName(field.type)),
            };
            const is_required = field.default_value_ptr == null;
            text = text ++ if (is_required) " " ++ flag else " [" ++ flag ++ "]";
        }
        break :blk text ++ "\n";
    };

    fn arg(comptime name: []const u8) []const u8 {
        comptime var flag = ("--" ++ name).*;
        std.mem.replaceScalar(u8, &flag, '_', '-');
        const out = flag;
        return &out;
    }

    fn short_arg(comptime name: []const u8) []const u8 {
        return ("-" ++ name[0..1]);
    }

    fn parse(arguments: []const [:0]const u8) ?Args {
        var flags = std.mem.zeroInit(Args, .{});
        var i: usize = 1;
        next: while (i < arguments.len) : (i += 1) {
            inline for (fields) |field| {
                const is_flag = std.mem.eql(u8, arguments[i], comptime arg(field.name)) or
                    std.mem.eql(u8, arguments[i], comptime short_arg(field.name));
                if (is_flag) {
                    switch (field.type) {
                        bool => @field(flags, field.name) = true,
                        ?[:0]const u8 => {
                            i += 1;
                            @field(flags, field.name) = if (i < arguments.len)
                                arguments[i]
                            else
                                null;
                        },
                        [:0]const u8 => {
                            i += 1;
                            @field(flags, field.name) = if (i < arguments.len)
                                arguments[i]
                            else
                                return null;
                        },
                        ?[]const [:0]const u8 => {
                            @field(flags, field.name) = arguments[i + 1 ..];
                            i = arguments.len;
                        },
                        else => @compileError("unsupported flag type " ++ @typeName(field.type)),
                    }
                    continue :next;
                }
            }
            return null;
        }

        inline for (fields) |field| {
            const is_required = field.default_value_ptr == null;
            if (is_required and @field(flags, field.name).len == 0) return null;
        }
        return flags;
    }
};

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;
    const arguments = init.minimal.args.toSlice(init.arena.allocator()) catch |err| {
        @panic(@errorName(err));
    };
    const args = Args.parse(arguments) orelse return std.debug.print(Args.usage, .{});

    const input_file = std.Io.Dir.cwd().openFile(io, args.build, .{}) catch {
        std.debug.print("Error opening file: {s}\n", .{args.build});
        return;
    };

    const max_file_size = 50 * 1024 * 1024;

    var reader_buffer: [4096]u8 = undefined;
    var file_reader = input_file.reader(io, &reader_buffer);
    const reader: *std.Io.Reader = &file_reader.interface;
    const source_bytes = reader.allocRemaining(
        alloc,
        std.Io.Limit.limited(max_file_size),
    ) catch |err| @panic(@errorName(err));
    defer alloc.free(source_bytes);

    var lexer = Lexer{ .src_bytes = source_bytes, .tokens = .init(alloc, 10000) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch |err| return lexer.handle_err(io, err);

    var parser = Parser.init(alloc, lexer.tokens, source_bytes, lexer.tokens.column(.span));
    defer parser.deinit();
    parser.build_ast() catch |err| parser.handle_err(io, err);

    if (debug) stage = .{ .parsed = .{ io, &parser } };

    var resolver = Resolver.init(alloc, &parser.tree, source_bytes, parser.global_store.items());
    defer resolver.deinit();
    resolver.session.io, resolver.session.path = .{ io, args.build };
    const resolved = resolver.resolve() != error.ResolveFailed;

    stage = .none;

    if (args.inspect) |queries| if (!resolved) {
        return dbg.Inspector.run(io, &resolver, null, queries) catch |err| {
            @panic(@errorName(err));
        };
    };

    if (debug and args.inspect == null) {
        if (args.dbg_less) {
            dbg.Resolver.print(io, &resolver) catch |err| @panic(@errorName(err));
        } else {
            dbg.Resolver.print_tree(io, &resolver) catch |err| @panic(@errorName(err));
        }
    }

    if (!resolved) return;

    var lowerer = HighLowerer.init(alloc, &resolver);
    defer lowerer.deinit();
    lowerer.lower();

    if (args.inspect) |queries| {
        return dbg.Inspector.run(io, &resolver, &lowerer, queries) catch |err| {
            @panic(@errorName(err));
        };
    }

    if (debug) dbg.HighLowerer.print(io, &lowerer) catch |err| @panic(@errorName(err));
}
