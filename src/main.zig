const std = @import("std");
const mond = @import("mond");
const LLVMLowerer = @import("LLVMLowerer.zig");
const emit = @import("llvm_lowerer/emit.zig");
const link = @import("llvm_lowerer/link.zig");
const Lexer = mond.Lexer;
const Parser = mond.Parser;
const Resolver = mond.Resolver;
const HighLowerer = mond.HighLowerer;
const dbg = mond.dbg;

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

// command line flags: the field `out` is `--out` or `-o`, an underscore in a name becomes a dash
// bool: set when present, string: takes the next argument, slice: takes all following arguments
// a field without a default is required
const Args = struct {
    build: [:0]const u8,
    // the executable, the source's name without `.mn` when not given
    out: ?[:0]const u8 = null,
    // the optimization level, see `emit.Level`
    level: ?[:0]const u8 = null,
    // the stages to print, comma separated, see `Stages`
    print: ?[:0]const u8 = null,
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

// what `--print` shows: the resolved tree, the declarations, `HighIr`, the optimized llvm ir
const Stages = struct {
    tree: bool = false,
    decls: bool = false,
    ir: bool = false,
    llvm: bool = false,

    const usage = "stages: tree, decls, ir, llvm (comma separated)\n";

    fn parse(list: ?[]const u8) ?Stages {
        var stages: Stages = .{};
        var names = std.mem.tokenizeScalar(u8, list orelse return stages, ',');
        next: while (names.next()) |name| {
            inline for (@typeInfo(Stages).@"struct".fields) |field| {
                if (std.mem.eql(u8, name, field.name)) {
                    @field(stages, field.name) = true;
                    continue :next;
                }
            }
            return null;
        }
        return stages;
    }
};

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;
    const arena = init.arena.allocator();
    const arguments = init.minimal.args.toSlice(arena) catch |err| @panic(@errorName(err));
    const args = Args.parse(arguments) orelse return std.debug.print(Args.usage, .{});
    const stages = Stages.parse(args.print) orelse return std.debug.print(Stages.usage, .{});
    const level = emit.Level.parse(args.level orelse "0") orelse {
        return std.debug.print(emit.Level.usage, .{});
    };

    const input_file = std.Io.Dir.cwd().openFile(io, args.build, .{}) catch {
        std.debug.print("Error opening file: {s}\n", .{args.build});
        std.process.exit(1);
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

    stage = .{ .parsed = .{ io, &parser } };

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

    if (stages.tree) dbg.Resolver.print_tree(io, &resolver) catch |err| @panic(@errorName(err));
    if (stages.decls) dbg.Resolver.print(io, &resolver) catch |err| @panic(@errorName(err));
    dbg.Resolver.print_diagnostics(io, &resolver, args.build) catch |err| {
        @panic(@errorName(err));
    };
    if (!resolved) std.process.exit(1);

    var lowerer = HighLowerer.init(alloc, &resolver);
    defer lowerer.deinit();
    lowerer.lower();

    if (args.inspect) |queries| {
        return dbg.Inspector.run(io, &resolver, &lowerer, queries) catch |err| {
            @panic(@errorName(err));
        };
    }

    if (stages.ir) dbg.HighLowerer.print(io, &lowerer) catch |err| @panic(@errorName(err));

    var backend = LLVMLowerer.init(alloc, &lowerer, args.build, .{ .checks = level == .@"0" });
    defer backend.deinit();
    backend.lower();

    const machine = emit.Machine.init(level);
    defer machine.deinit();
    machine.optimize(backend.module);
    if (stages.llvm) emit.print(io, backend.module) catch |err| @panic(@errorName(err));

    const executable = args.out orelse default_executable(arena, args.build);
    const object = std.fmt.allocPrintSentinel(arena, "{s}.o", .{executable}, 0) catch {
        @panic("OOM");
    };
    machine.write_object(backend.module, object);
    const linked = link.executable(arena, object, executable);
    std.Io.Dir.cwd().deleteFile(io, object) catch {};
    if (!linked) std.process.exit(1);
}

// `dir/app.mn` builds `app` in the working directory
fn default_executable(arena: std.mem.Allocator, source_path: []const u8) [:0]const u8 {
    const name = std.fs.path.basename(source_path);
    const stem = if (std.mem.endsWith(u8, name, ".mn")) name[0 .. name.len - ".mn".len] else name;
    const executable = if (stem.len == name.len) "a.out" else stem;
    return arena.dupeSentinel(u8, executable, 0) catch @panic("OOM");
}
