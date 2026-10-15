const std = @import("std");
const builtin = @import("builtin");
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
// bool: set when present, string: takes the next argument, slice: takes the following arguments up
// to the next flag. a field without a default is required
const Args = struct {
    build: []const [:0]const u8,
    out: ?[:0]const u8 = null,
    mode: ?[:0]const u8 = null,
    debug: bool = false,
    cc: ?[:0]const u8 = null,
    with: ?[:0]const u8 = null,
    print: ?[:0]const u8 = null,
    inspect: ?[]const [:0]const u8 = null,
    help: bool = false,

    // per flag: what it takes, what it does (a line each), and the heading of the section it opens
    const Help = struct {
        takes: []const u8 = "",
        does: []const []const u8,
        opens: []const u8 = "",
    };
    const helps = .{
        .build = Help{
            .takes = " <source> [files...]",
            .does = &.{
                "the program, then files to link with it: objects and libraries",
                "as they are, c, c++ and assembly compiled first",
            },
            .opens = "Build",
        },
        .out = Help{
            .takes = " <path>",
            .does = &.{"the executable, by default the source's name without .mn"},
        },
        .mode = Help{ .takes = " <mode>", .does = &.{"how to optimize, see Modes"} },
        .debug = Help{ .does = &.{"debug symbols, so lldb and gdb show functions and lines"} },
        .cc = Help{
            .takes = " <command>",
            .does = &.{"the c compiler and its flags, by default $CC, else cc"},
        },
        .with = Help{
            .takes = " <inputs>",
            .does = &.{"more linker inputs, comma separated: -lm,-L/opt/lib"},
        },
        .print = Help{
            .takes = " <stages>",
            .does = &.{"also print the stages tree, decls, ir or llvm, comma separated"},
            .opens = "Look inside",
        },
        .inspect = Help{
            .takes = " <queries...>",
            .does = &.{"declarations by name, #index or :line, builds nothing"},
        },
        .help = Help{ .does = &.{"this text"} },
    };

    const fields = @typeInfo(Args).@"struct".fields;
    // the help, with its headings in bold or plain
    const help_text: [2][]const u8 = .{ write_help(false), write_help(true) };

    fn write_help(comptime bold: bool) []const u8 {
        @setEvalBranchQuota(100_000);
        const heading_start = if (bold) "\x1b[1m" else "";
        const heading_end = if (bold) "\x1b[0m" else "";
        var column = 0;
        for (fields) |field| {
            const left = "  " ++ short_arg(field.name) ++ ", " ++ arg(field.name);
            column = @max(column, left.len + @field(helps, field.name).takes.len + 2);
        }
        var text: []const u8 = "mond, the compiler of the mond language\n\n" ++
            heading_start ++ "Usage" ++ heading_end ++ "\n" ++
            "  mond -b <source.mn> [files...] [options]\n";
        for (fields, 0..) |field, i| {
            for (fields[0..i]) |other| {
                if (other.name[0] != field.name[0]) continue;
                @compileError(short_arg(field.name) ++ " is taken by " ++ arg(other.name));
            }
            const help: Help = @field(helps, field.name);
            if (help.opens.len > 0) text = text ++ "\n" ++ heading_start ++ help.opens ++
                heading_end ++ "\n";
            const left = "  " ++ short_arg(field.name) ++ ", " ++ arg(field.name) ++ help.takes;
            for (help.does, 0..) |line, k| {
                const start = if (k == 0) left else "";
                text = text ++ start ++ padding(column - start.len) ++ line ++ "\n";
            }
        }
        text = text ++ "\n" ++ heading_start ++ "Modes" ++ heading_end ++ "\n";
        const modes = std.enums.values(emit.Mode);
        var mode_column = 0;
        for (modes) |mode| mode_column = @max(mode_column, "  ".len + @tagName(mode).len + 3);
        for (modes) |mode| {
            const name = "  " ++ @tagName(mode);
            text = text ++ name ++ padding(mode_column - name.len) ++ mode.description() ++ "\n";
        }
        return text;
    }

    fn padding(comptime width: usize) []const u8 {
        const spaces: [width]u8 = @splat(' ');
        return &spaces;
    }

    fn arg(comptime name: []const u8) []const u8 {
        comptime var flag = ("--" ++ name).*;
        std.mem.replaceScalar(u8, &flag, '_', '-');
        const out = flag;
        return &out;
    }

    fn short_arg(comptime name: []const u8) []const u8 {
        return ("-" ++ name[0..1]);
    }

    // why the arguments make no command
    const Problem = union(enum) {
        // an argument that is no flag
        unknown: []const u8,
        // a flag without the value it takes
        needs_value: []const u8,
        // a required flag that is missing
        needs_flag: []const u8,
    };

    fn parse(arguments: []const [:0]const u8, problem: *Problem) ?Args {
        var flags = std.mem.zeroInit(Args, .{});
        var i: usize = 1;
        next: while (i < arguments.len) : (i += 1) {
            inline for (fields) |field| {
                const is_flag = std.mem.eql(u8, arguments[i], comptime arg(field.name)) or
                    std.mem.eql(u8, arguments[i], comptime short_arg(field.name));
                if (is_flag) {
                    switch (field.type) {
                        bool => @field(flags, field.name) = true,
                        [:0]const u8, ?[:0]const u8 => {
                            i += 1;
                            if (i == arguments.len) {
                                problem.* = .{ .needs_value = comptime arg(field.name) };
                                return null;
                            }
                            @field(flags, field.name) = arguments[i];
                        },
                        []const [:0]const u8, ?[]const [:0]const u8 => {
                            var end = i + 1;
                            while (end < arguments.len) : (end += 1) {
                                if (std.mem.startsWith(u8, arguments[end], "-")) break;
                            }
                            @field(flags, field.name) = arguments[i + 1 .. end];
                            i = end - 1;
                        },
                        else => @compileError("unsupported flag type " ++ @typeName(field.type)),
                    }
                    continue :next;
                }
            }
            problem.* = .{ .unknown = arguments[i] };
            return null;
        }
        if (flags.help) return flags;

        inline for (fields) |field| {
            const is_required = field.default_value_ptr == null;
            if (is_required and @field(flags, field.name).len == 0) {
                problem.* = .{ .needs_flag = comptime arg(field.name) };
                return null;
            }
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

    // `unknown` gets a name that is no stage
    fn parse(list: ?[]const u8, unknown: *[]const u8) ?Stages {
        var stages: Stages = .{};
        var names = std.mem.tokenizeScalar(u8, list orelse return stages, ',');
        next: while (names.next()) |name| {
            inline for (@typeInfo(Stages).@"struct".fields) |field| {
                if (std.mem.eql(u8, name, field.name)) {
                    @field(stages, field.name) = true;
                    continue :next;
                }
            }
            unknown.* = name;
            return null;
        }
        return stages;
    }
};

// `a, b or c` of the names of a struct's fields or an enum's tags
fn spelled_out(comptime Type: type) []const u8 {
    const names = std.meta.fieldNames(Type);
    var text: []const u8 = names[0];
    for (names[1..], 1..) |name, i| {
        text = text ++ (if (i + 1 == names.len) " or " else ", ") ++ name;
    }
    return text;
}

// a message on stderr, `mond:` in bold on a terminal
fn complain(io: std.Io, comptime format: []const u8, arguments: anytype) void {
    const is_terminal = std.Io.File.stderr().isTty(io) catch false;
    const prefix = if (is_terminal) "\x1b[1mmond:\x1b[0m " else "mond: ";
    std.debug.print("{s}" ++ format ++ "\n", .{prefix} ++ arguments);
}

fn fail(io: std.Io, comptime format: []const u8, arguments: anytype) noreturn {
    complain(io, format, arguments);
    std.process.exit(1);
}

pub fn main(init: std.process.Init) void {
    const io = init.io;
    const alloc = init.gpa;
    const arena = init.arena.allocator();
    const arguments = init.minimal.args.toSlice(arena) catch |err| @panic(@errorName(err));
    var problem: Args.Problem = undefined;
    const args = if (arguments.len == 1) Args{ .build = &.{}, .help = true } else Args.parse(
        arguments,
        &problem,
    ) orelse switch (problem) {
        .unknown => |argument| fail(io, "'{s}' is no flag, see mond --help", .{argument}),
        .needs_value => |flag| fail(io, "{s} needs a value, see mond --help", .{flag}),
        .needs_flag => |flag| fail(io, "{s} is missing or empty, see mond --help", .{flag}),
    };
    if (args.help) {
        const stdout = std.Io.File.stdout();
        const is_terminal = stdout.isTty(io) catch false;
        stdout.writeStreamingAll(io, Args.help_text[@intFromBool(is_terminal)]) catch {};
        return;
    }
    var unknown_stage: []const u8 = undefined;
    const stages = Stages.parse(args.print, &unknown_stage) orelse fail(
        io,
        "'{s}' is no stage, expected " ++ comptime spelled_out(Stages),
        .{unknown_stage},
    );
    const mode_name = args.mode orelse "none";
    const mode = std.meta.stringToEnum(emit.Mode, mode_name) orelse fail(
        io,
        "'{s}' is no mode, expected " ++ comptime spelled_out(emit.Mode),
        .{mode_name},
    );
    const source_path = args.build[0];

    const input_file = std.Io.Dir.cwd().openFile(io, source_path, .{}) catch |err| {
        fail(io, "cannot read {s}: {t}", .{ source_path, err });
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
    resolver.session.io, resolver.session.path = .{ io, source_path };
    const resolved = resolver.resolve() != error.ResolveFailed;

    stage = .none;

    if (args.inspect) |queries| if (!resolved) {
        return dbg.Inspector.run(io, &resolver, null, queries) catch |err| {
            @panic(@errorName(err));
        };
    };

    if (stages.tree) dbg.Resolver.print_tree(io, &resolver) catch |err| @panic(@errorName(err));
    if (stages.decls) dbg.Resolver.print(io, &resolver) catch |err| @panic(@errorName(err));
    dbg.Resolver.print_diagnostics(io, &resolver, source_path) catch |err| {
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

    const debug_source = if (!args.debug) null else std.Io.Dir.cwd().realPathFileAlloc(
        io,
        source_path,
        arena,
    ) catch |err| @panic(@errorName(err));
    var backend = LLVMLowerer.init(alloc, &lowerer, source_path, .{
        .checks = mode.has_checks(),
        .debug_source = debug_source,
        .optimized = mode != .none,
    });
    defer backend.deinit();
    backend.lower();

    const machine = emit.Machine.init(mode);
    defer machine.deinit();
    machine.optimize(backend.module);
    if (stages.llvm) emit.print(io, backend.module) catch |err| @panic(@errorName(err));

    const executable = args.out orelse default_executable(arena, source_path);
    const object = std.fmt.allocPrintSentinel(arena, "{s}.o", .{executable}, 0) catch {
        @panic("OOM");
    };
    machine.write_object(backend.module, object);
    // the objects built here, `object` first, deleted after linking
    var objects: std.ArrayList([:0]const u8) = .empty;
    objects.append(arena, object) catch @panic("OOM");
    var inputs: std.ArrayList([:0]const u8) = .empty;
    const linkable = [_][]const u8{ ".o", ".a", ".so", ".dylib" };
    const compiled = for (args.build[1..]) |input| {
        const extension = std.fs.path.extension(input);
        for (linkable) |kind| {
            if (std.mem.eql(u8, extension, kind)) break;
        } else {
            // `app` builds `io.c` into `app.io.c.o`, next to it
            const name = std.fs.path.basename(input);
            const compiled_object = std.fmt.allocPrintSentinel(arena, "{s}.{s}.o", .{
                executable,
                name,
            }, 0) catch @panic("OOM");
            objects.append(arena, compiled_object) catch @panic("OOM");
            inputs.append(arena, compiled_object) catch @panic("OOM");
            var command: std.ArrayList([]const u8) = .empty;
            const compiler = args.cc orelse init.environ_map.get("CC") orelse "cc";
            var words = std.mem.tokenizeScalar(u8, compiler, ' ');
            while (words.next()) |word| command.append(arena, word) catch @panic("OOM");
            const level_flag = std.fmt.allocPrint(arena, "-{s}", .{mode.optimization()}) catch {
                @panic("OOM");
            };
            command.appendSlice(arena, &.{ "-c", input, "-o", compiled_object, level_flag }) catch {
                @panic("OOM");
            };
            if (args.debug) command.append(arena, "-g") catch @panic("OOM");
            var child = std.process.spawn(io, .{ .argv = command.items }) catch |err| {
                complain(io, "cannot run {s}: {t}", .{ command.items[0], err });
                break false;
            };
            const term = child.wait(io) catch |err| @panic(@errorName(err));
            if (term != .exited or term.exited != 0) break false;
            continue;
        }
        inputs.append(arena, input) catch @panic("OOM");
    } else true;
    var listed = std.mem.tokenizeScalar(u8, args.with orelse "", ',');
    while (listed.next()) |input| {
        const terminated = arena.dupeSentinel(u8, input, 0) catch @panic("OOM");
        inputs.append(arena, terminated) catch @panic("OOM");
    }
    const linked = compiled and link.executable(arena, object, executable, inputs.items);
    // on macos the debugger reads the dwarf from the object files the executable names
    const keeps_objects = linked and args.debug and builtin.os.tag.isDarwin();
    if (!keeps_objects) for (objects.items) |built| std.Io.Dir.cwd().deleteFile(io, built) catch {};
    if (!linked) std.process.exit(1);
}

// `dir/app.mn` builds `app` in the working directory
fn default_executable(arena: std.mem.Allocator, source_path: []const u8) [:0]const u8 {
    const name = std.fs.path.basename(source_path);
    const stem = if (std.mem.endsWith(u8, name, ".mn")) name[0 .. name.len - ".mn".len] else name;
    const executable = if (stem.len == name.len) "a.out" else stem;
    return arena.dupeSentinel(u8, executable, 0) catch @panic("OOM");
}
