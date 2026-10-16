// the backend tests: every program in examples/backend is built by `mond` in the modes below and
// run, and must print exactly its `#> line` markers, in order, and exit as its `#?` markers say:
// `#? exit N` with N (else 0), `#? trap` stopped by a runtime check where the mode keeps them (in
// the other modes it is undefined behavior and not run), `#? args a b` runs it with arguments
const std = @import("std");

const reset = "\x1b[0m";
const dim = "\x1b[90m";
const green = "\x1b[32m";
const red = "\x1b[1;31m";
const bold = "\x1b[1m";

const Writer = std.Io.Writer;

const directory_path = "examples/backend";
const output_path = ".zig-cache/backend-tests";
// what a program is built with unless a `#+` marker names it: the c library, and the c functions
// of c_interop.mn, compiled by `mond` with the c compiler
const default_arguments = [_][]const u8{ "-lc", "examples/backend/lib/clib.c" };
// unoptimized and optimized with the runtime checks, and optimized without them: for speed at
// -O2 and -O3, and for size at -Oz
const modes = [_][]const u8{ "none", "safe", "default", "aggressive", "minsize" };
// the modes keeping the runtime checks
const checked_modes = [_][]const u8{ "none", "safe" };

// how a program has to end, and what it is run with
const Ending = struct {
    exit_code: u8 = 0,
    traps: bool = false,
    arguments: []const []const u8 = &.{},
};
const time_limit: std.Io.Timeout = .{ .duration = .{
    .raw = .fromSeconds(60),
    .clock = .awake,
} };

// `mond-test-backend <mond> [filters..]`
pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const arena = init.arena.allocator();
    const arguments = try init.minimal.args.toSlice(arena);
    const mond = arguments[1];
    const filters = arguments[2..];

    var buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const writer = &file_writer.interface;

    var directory = try std.Io.Dir.cwd().openDir(io, directory_path, .{ .iterate = true });
    defer directory.close(io);
    try std.Io.Dir.cwd().createDirPath(io, output_path);
    // the executables are built anew each run, none of them is kept
    defer std.Io.Dir.cwd().deleteTree(io, output_path) catch {};

    // sorted, so the output does not depend on the file system
    var names: std.ArrayList([]const u8) = .empty;
    var iterator = directory.iterate();
    while (try iterator.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".mn")) continue;
        try names.append(arena, try arena.dupe(u8, entry.name));
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less_than(_: void, left: []const u8, right: []const u8) bool {
            return std.mem.order(u8, left, right) == .lt;
        }
    }.less_than);

    const rule = "\n{s} (built in modes none, safe, default, aggressive and minsize, " ++
        "must print its `#>` lines and end as its `#?` lines say)\n";
    try writer.print(bold ++ rule ++ reset, .{directory_path});
    var counts: [2]usize = .{ 0, 0 };
    for (names.items) |name| {
        const matches_filters = for (filters) |filter| {
            if (std.mem.indexOf(u8, name, filter) != null) break true;
        } else filters.len == 0;
        if (!matches_filters) continue;

        const source = try directory.readFileAlloc(io, name, arena, .limited(50 << 20));
        const expected = try expected_output(arena, source);
        const build_with = try build_arguments(arena, source);
        const ending = try expected_ending(arena, source);
        for (modes) |mode| {
            const passed =
                try check(writer, arena, io, mond, name, mode, expected, build_with, ending);
            counts[@intFromBool(!passed)] += 1;
        }
    }

    const failed = counts[1];
    const summary_format = bold ++ "\n{s}{d} passed, {d} failed" ++ reset ++
        dim ++ "  (backend builds)\n" ++ reset;
    try writer.print(summary_format, .{ if (failed == 0) green else red, counts[0], failed });
    try writer.flush();
    if (failed > 0) std.process.exit(1);
}

// the text after each `#> `, a line of output each
fn expected_output(arena: std.mem.Allocator, source: []const u8) ![]const u8 {
    var output: std.ArrayList(u8) = .empty;
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        const at = std.mem.indexOf(u8, line, "#> ") orelse continue;
        try output.appendSlice(arena, std.mem.trimEnd(u8, line[at + "#> ".len ..], " \r"));
        try output.append(arena, '\n');
    }
    return output.items;
}

// the `#? exit N`, `#? trap` and `#? args ..` markers
fn expected_ending(arena: std.mem.Allocator, source: []const u8) !Ending {
    var ending: Ending = .{};
    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |line| {
        const at = std.mem.indexOf(u8, line, "#? ") orelse continue;
        var words = std.mem.tokenizeAny(u8, line[at + "#? ".len ..], " \r");
        const kind = words.next() orelse continue;
        if (std.mem.eql(u8, kind, "exit")) {
            ending.exit_code = try std.fmt.parseInt(u8, words.next() orelse "0", 10);
        } else if (std.mem.eql(u8, kind, "trap")) {
            ending.traps = true;
        } else if (std.mem.eql(u8, kind, "args")) {
            var arguments: std.ArrayList([]const u8) = .empty;
            while (words.next()) |word| try arguments.append(arena, word);
            ending.arguments = arguments.items;
        }
    }
    return ending;
}

// the arguments after `#+ `, files relative to examples/backend, else `default_arguments`
fn build_arguments(arena: std.mem.Allocator, source: []const u8) ![]const []const u8 {
    var lines = std.mem.splitScalar(u8, source, '\n');
    const marked = while (lines.next()) |line| {
        const at = std.mem.indexOf(u8, line, "#+") orelse continue;
        break line[at + "#+".len ..];
    } else return &default_arguments;
    var arguments: std.ArrayList([]const u8) = .empty;
    var words = std.mem.tokenizeAny(u8, marked, " \r");
    while (words.next()) |word| {
        const argument = if (word[0] == '-') word else try std.fs.path.join(arena, &.{
            directory_path,
            word,
        });
        try arguments.append(arena, argument);
    }
    return arguments.items;
}

fn check(
    writer: *Writer,
    arena: std.mem.Allocator,
    io: std.Io,
    mond: []const u8,
    name: []const u8,
    mode: []const u8,
    expected: []const u8,
    arguments: []const []const u8,
    ending: Ending,
) !bool {
    const stem = name[0 .. name.len - ".mn".len];
    const source_path = try std.fs.path.join(arena, &.{ directory_path, name });
    const executable = try std.fmt.allocPrint(arena, "{s}/{s}-{s}", .{ output_path, stem, mode });

    var argv: std.ArrayList([]const u8) = .empty;
    try argv.appendSlice(arena, &.{ mond, "-b", source_path });
    try argv.appendSlice(arena, arguments);
    try argv.appendSlice(arena, &.{ "-o", executable, "-m", mode });
    const built = try std.process.run(arena, io, .{ .argv = argv.items, .timeout = time_limit });
    if (!exited_cleanly(built.term)) {
        try report(writer, name, mode, "does not build", built.stderr);
        return false;
    }

    defer std.Io.Dir.cwd().deleteFile(io, executable) catch {};
    const is_checked = for (checked_modes) |checked| {
        if (std.mem.eql(u8, checked, mode)) break true;
    } else false;
    // a failing check without the checks is undefined behavior: built, not run
    if (ending.traps and !is_checked) {
        const skipped_format = "  " ++ green ++ "✓" ++ reset ++ " {s} -m {s}  " ++
            dim ++ "built, traps only with checks" ++ reset ++ "\n";
        try writer.print(skipped_format, .{ name, mode });
        return true;
    }
    var run_argv: std.ArrayList([]const u8) = .empty;
    try run_argv.append(arena, executable);
    try run_argv.appendSlice(arena, ending.arguments);
    const ran = try std.process.run(arena, io, .{ .argv = run_argv.items, .timeout = time_limit });
    const ended_as_expected = switch (ran.term) {
        .exited => |code| !ending.traps and code == ending.exit_code,
        .signal => ending.traps,
        else => false,
    };
    if (!ended_as_expected) {
        const status = try std.fmt.allocPrint(arena, "ended with {any}", .{ran.term});
        try report(writer, name, mode, status, ran.stdout);
        return false;
    }
    if (!std.mem.eql(u8, ran.stdout, expected)) {
        try report(
            writer,
            name,
            mode,
            "printed other lines",
            try difference(arena, expected, ran.stdout),
        );
        return false;
    }
    const line_count = std.mem.count(u8, expected, "\n");
    const passed_format = "  " ++ green ++ "✓" ++ reset ++ " {s} -m {s}  " ++
        dim ++ "{d} lines" ++ reset ++ "\n";
    try writer.print(passed_format, .{ name, mode, line_count });
    return true;
}

fn exited_cleanly(term: std.process.Child.Term) bool {
    return switch (term) {
        .exited => |code| code == 0,
        else => false,
    };
}

fn report(
    writer: *Writer,
    name: []const u8,
    mode: []const u8,
    problem: []const u8,
    details: []const u8,
) !void {
    const failed_format = "  " ++ red ++ "✗" ++ reset ++ " {s} -m {s}  {s}\n";
    try writer.print(failed_format, .{ name, mode, problem });
    var lines = std.mem.splitScalar(u8, std.mem.trimEnd(u8, details, "\n"), '\n');
    while (lines.next()) |line| try writer.print(dim ++ "      {s}\n" ++ reset, .{line});
}

// the expected and the printed lines side by side, from the first that differs
fn difference(arena: std.mem.Allocator, expected: []const u8, printed: []const u8) ![]const u8 {
    var text: std.ArrayList(u8) = .empty;
    var expected_lines = std.mem.splitScalar(u8, expected, '\n');
    var printed_lines = std.mem.splitScalar(u8, printed, '\n');
    var line_number: usize = 1;
    var differs = false;
    while (true) : (line_number += 1) {
        const expected_line = expected_lines.next();
        const printed_line = printed_lines.next();
        if (expected_line == null and printed_line == null) break;
        const same = expected_line != null and printed_line != null and
            std.mem.eql(u8, expected_line.?, printed_line.?);
        if (same and !differs) continue;
        differs = true;
        try text.print(arena, "line {d}: expected `{s}`, printed `{s}`\n", .{
            line_number,
            expected_line orelse "",
            printed_line orelse "",
        });
    }
    return text.items;
}
