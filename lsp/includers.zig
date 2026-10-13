const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;

// whether another mond file of the workspace includes the file at `path`. such a file is a library,
// meant to be included, so the editor does not ask it for a `$main` (compiling it still does).
// the workspace is the nearest directory above `path` holding a `.git` or a `build.zig`
pub fn is_included(io: std.Io, allocator: std.mem.Allocator, path: []const u8) bool {
    if (path.len == 0) return false;
    const target = absolute_path(io, allocator, path) orelse return false;
    const root = workspace_root(io, allocator, target);

    const cwd = std.Io.Dir.cwd();
    var root_directory = cwd.openDir(io, root, .{ .iterate = true }) catch return false;
    defer root_directory.close(io);
    var walker = root_directory.walkSelectively(allocator) catch return false;
    defer walker.deinit();

    while (walker.next(io) catch null) |entry| switch (entry.kind) {
        .directory => if (!is_skipped(entry.basename)) walker.enter(io, entry) catch {},
        .file => {
            if (!std.mem.endsWith(u8, entry.basename, ".mn")) continue;
            const includer = std.fs.path.join(allocator, &.{ root, entry.path }) catch continue;
            if (std.mem.eql(u8, includer, target)) continue;
            if (includes(io, allocator, includer, target)) return true;
        },
        else => {},
    };
    return false;
}

// hidden directories (`.git`, `.zig-cache`) and build outputs hold no sources
fn is_skipped(directory_name: []const u8) bool {
    if (directory_name.len > 0 and directory_name[0] == '.') return true;
    return std.mem.eql(u8, directory_name, "zig-out") or
        std.mem.eql(u8, directory_name, "node_modules");
}

fn absolute_path(io: std.Io, allocator: std.mem.Allocator, path: []const u8) ?[]const u8 {
    if (std.fs.path.isAbsolute(path)) return std.fs.path.resolve(allocator, &.{path}) catch null;
    const current = std.process.currentPathAlloc(io, allocator) catch return null;
    return std.fs.path.resolve(allocator, &.{ current, path }) catch null;
}

// without a marker the directory above the file's own, where a program sits next to its `lib/`
fn workspace_root(io: std.Io, allocator: std.mem.Allocator, file: []const u8) []const u8 {
    const own_directory = std.fs.path.dirname(file) orelse return file;
    var directory: ?[]const u8 = own_directory;
    while (directory) |candidate| : (directory = std.fs.path.dirname(candidate)) {
        for ([_][]const u8{ ".git", "build.zig" }) |marker| {
            const marker_path = std.fs.path.join(allocator, &.{ candidate, marker }) catch continue;
            std.Io.Dir.cwd().access(io, marker_path, .{}) catch continue;
            return candidate;
        }
    }
    return std.fs.path.dirname(own_directory) orelse own_directory;
}

// whether `includer` has an `include "..."` naming `target`, a path relative to the includer as
// the compiler reads it. lexed, so an include in a comment does not count
fn includes(
    io: std.Io,
    allocator: std.mem.Allocator,
    includer: []const u8,
    target: []const u8,
) bool {
    const limit: std.Io.Limit = .limited(50 << 20);
    const cwd = std.Io.Dir.cwd();
    const source = cwd.readFileAlloc(io, includer, allocator, limit) catch return false;
    if (std.mem.indexOf(u8, source, "include") == null) return false;

    var lexer = Lexer{ .src_bytes = source, .tokens = .init(allocator, 1024) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch {};

    const kinds = lexer.tokens.column(.tk);
    const spans = lexer.tokens.column(.span);
    const includer_directory = std.fs.path.dirname(includer) orelse ".";
    for (kinds, 0..) |kind, i| {
        if (kind != .kw_include or i + 1 >= kinds.len or kinds[i + 1] != .val_string) continue;
        const written = std.mem.trim(u8, source[spans[i + 1][0]..spans[i + 1][1]], "\"");
        const parts = [_][]const u8{ includer_directory, written };
        const included = std.fs.path.resolve(allocator, &parts) catch continue;
        if (std.mem.eql(u8, included, target)) return true;
    }
    return false;
}

test "a file another file includes is a library, one only named in a comment is not" {
    const io = std.testing.io;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var workspace = std.testing.tmpDir(.{});
    defer workspace.cleanup();
    try workspace.dir.createDirPath(io, ".git");
    try workspace.dir.createDirPath(io, "lib");
    const library_source = "# include \"b.mn\"\npub fun f = () {}\n";
    const program_source = "<include \"lib/a.mn\">;\n$main = () {}\n";
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/a.mn", .data = library_source });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/b.mn", .data = "pub fun g = () {}\n" });
    try workspace.dir.writeFile(io, .{ .sub_path = "main.mn", .data = program_source });

    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root_buffer[0..try workspace.dir.realPath(io, &root_buffer)];
    const library = try std.fs.path.join(allocator, &.{ root, "lib", "a.mn" });
    const mentioned = try std.fs.path.join(allocator, &.{ root, "lib", "b.mn" });
    const program = try std.fs.path.join(allocator, &.{ root, "main.mn" });

    try std.testing.expect(is_included(io, allocator, library));
    try std.testing.expect(!is_included(io, allocator, mentioned));
    try std.testing.expect(!is_included(io, allocator, program));
}
