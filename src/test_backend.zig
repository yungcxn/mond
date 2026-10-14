// the backend tests: every program in examples/backend is built by `mond` at the levels below and
// run, and must exit with 0 and print exactly its `#> line` markers, in order
const std = @import("std");

const reset = "\x1b[0m";
const dim = "\x1b[90m";
const green = "\x1b[32m";
const red = "\x1b[1;31m";
const bold = "\x1b[1m";

const Writer = std.Io.Writer;

const directory_path = "examples/backend";
const output_path = ".zig-cache/backend-tests";
// unoptimized with the runtime checks, and optimized
const levels = [_][]const u8{ "0", "2" };
const time_limit: std.Io.Timeout = .{ .duration = .{
    .raw = .fromSeconds(60),
    .clock = .awake,
} };

// `mond-test-backend <mond> <c library> [filters..]`
pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const arena = init.arena.allocator();
    const arguments = try init.minimal.args.toSlice(arena);
    const mond = arguments[1];
    const c_library = arguments[2];
    const filters = arguments[3..];

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

    const rule = "\n{s} (built at levels 0 and 2, must print its `#>` lines)\n";
    try writer.print(bold ++ rule ++ reset, .{directory_path});
    var counts: [2]usize = .{ 0, 0 };
    for (names.items) |name| {
        const matches_filters = for (filters) |filter| {
            if (std.mem.indexOf(u8, name, filter) != null) break true;
        } else filters.len == 0;
        if (!matches_filters) continue;

        const source = try directory.readFileAlloc(io, name, arena, .limited(50 << 20));
        const expected = try expected_output(arena, source);
        for (levels) |level| {
            const passed = try check(writer, arena, io, mond, c_library, name, level, expected);
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

fn check(
    writer: *Writer,
    arena: std.mem.Allocator,
    io: std.Io,
    mond: []const u8,
    c_library: []const u8,
    name: []const u8,
    level: []const u8,
    expected: []const u8,
) !bool {
    const stem = name[0 .. name.len - ".mn".len];
    const source_path = try std.fs.path.join(arena, &.{ directory_path, name });
    const executable = try std.fmt.allocPrint(arena, "{s}/{s}-{s}", .{ output_path, stem, level });

    const built = try std.process.run(arena, io, .{
        .argv = &.{ mond, "-b", source_path, "-o", executable, "-l", level, "-w", c_library },
        .timeout = time_limit,
    });
    if (!exited_cleanly(built.term)) {
        try report(writer, name, level, "does not build", built.stderr);
        return false;
    }

    defer std.Io.Dir.cwd().deleteFile(io, executable) catch {};
    const ran = try std.process.run(arena, io, .{ .argv = &.{executable}, .timeout = time_limit });
    if (!exited_cleanly(ran.term)) {
        const status = try std.fmt.allocPrint(arena, "ended with {any}", .{ran.term});
        try report(writer, name, level, status, ran.stdout);
        return false;
    }
    if (!std.mem.eql(u8, ran.stdout, expected)) {
        try report(
            writer,
            name,
            level,
            "printed other lines",
            try difference(arena, expected, ran.stdout),
        );
        return false;
    }
    const line_count = std.mem.count(u8, expected, "\n");
    const passed_format = "  " ++ green ++ "✓" ++ reset ++ " {s} -l {s}  " ++
        dim ++ "{d} lines" ++ reset ++ "\n";
    try writer.print(passed_format, .{ name, level, line_count });
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
    level: []const u8,
    problem: []const u8,
    details: []const u8,
) !void {
    const failed_format = "  " ++ red ++ "✗" ++ reset ++ " {s} -l {s}  {s}\n";
    try writer.print(failed_format, .{ name, level, problem });
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
