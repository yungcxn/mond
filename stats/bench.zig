const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;
const Parser = mond.Parser;
const Resolver = mond.Resolver;
const HighLowerer = mond.HighLowerer;

// each compiling program runs through the whole pipeline once per round, the fastest round counts
const example_directories = [_][]const u8{
    "examples",
    "examples/positive",
    "examples/general-purpose",
};
const default_round_count = 30;

const Program = struct { path: []const u8, source: []u8 };

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const arena = init.arena.allocator();
    const arguments = try init.minimal.args.toSlice(arena);
    const round_count = if (arguments.len > 1)
        try std.fmt.parseInt(u32, arguments[1], 10)
    else
        default_round_count;

    const programs = blk: {
        var programs: std.ArrayList(Program) = .empty;
        for (example_directories) |directory_path| {
            var directory = try std.Io.Dir.cwd().openDir(io, directory_path, .{ .iterate = true });
            defer directory.close(io);
            var entries = directory.iterate();
            while (try entries.next(io)) |entry| {
                if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".mn")) continue;
                const source =
                    try directory.readFileAlloc(io, entry.name, arena, .limited(50 << 20));
                const path = try std.fs.path.join(arena, &.{ directory_path, entry.name });
                try programs.append(arena, .{ .path = path, .source = source });
            }
        }
        break :blk programs.items;
    };
    const per_program_ns = try arena.alloc(i96, programs.len);
    @memset(per_program_ns, std.math.maxInt(i96));
    var fastest_round_ns: i96 = std.math.maxInt(i96);
    var total_ns: i96 = 0;
    for (0..round_count) |_| {
        const started = std.Io.Timestamp.now(io, .awake);
        for (programs, per_program_ns) |program, *fastest_ns| {
            const program_started = std.Io.Timestamp.now(io, .awake);
            compile(io, program);
            const program_finished = std.Io.Timestamp.now(io, .awake);
            const program_ns = program_started.durationTo(program_finished).nanoseconds;
            fastest_ns.* = @min(fastest_ns.*, program_ns);
        }
        const round_ns = started.durationTo(std.Io.Timestamp.now(io, .awake)).nanoseconds;
        fastest_round_ns = @min(fastest_round_ns, round_ns);
        total_ns += round_ns;
    }

    var output_buffer: [256]u8 = undefined;
    var stdout = std.Io.File.stdout().writerStreaming(io, &output_buffer);
    try stdout.interface.print("{d} programs, {d} rounds: fastest {d} us, mean {d} us\n", .{
        programs.len,
        round_count,
        @divTrunc(fastest_round_ns, std.time.ns_per_us),
        @divTrunc(@divTrunc(total_ns, round_count), std.time.ns_per_us),
    });
    if (arguments.len > 2 and std.mem.eql(u8, arguments[2], "--slowest")) {
        const order = try arena.alloc(usize, programs.len);
        for (order, 0..) |*slot, i| slot.* = i;
        std.mem.sort(usize, order, per_program_ns, struct {
            fn slower(times: []const i96, a: usize, b: usize) bool {
                return times[a] > times[b];
            }
        }.slower);
        for (order[0..@min(10, order.len)]) |i| {
            const microseconds: i64 = @intCast(@divTrunc(per_program_ns[i], std.time.ns_per_us));
            try stdout.interface.print("  {d:>8} us  {s}\n", .{ microseconds, programs[i].path });
        }
    }
    try stdout.interface.flush();
}

fn compile(io: std.Io, program: Program) void {
    const allocator = std.heap.smp_allocator;
    var lexer = Lexer{ .src_bytes = program.source, .tokens = .init(allocator, 1024) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch return;

    const spans = lexer.tokens.column(.span);
    var parser = Parser.init(allocator, lexer.tokens, program.source, spans);
    defer parser.deinit();
    parser.build_ast() catch return;

    const roots = parser.global_store.items();
    var resolver = Resolver.init(allocator, &parser.tree, program.source, roots);
    defer resolver.deinit();
    resolver.session.io, resolver.session.path = .{ io, program.path };
    resolver.resolve() catch return;

    var lowerer = HighLowerer.init(allocator, &resolver);
    defer lowerer.deinit();
    lowerer.lower();
}
