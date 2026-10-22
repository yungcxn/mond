const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;

// whether another mond file of the workspace includes the file at `path`. such a file is a library,
// meant to be included, so the editor does not ask it for a `main` (compiling it still does).
// the workspace is the nearest directory above `path` holding a `.git` or a `build.zig`
pub fn is_included(io: std.Io, allocator: std.mem.Allocator, path: []const u8) bool {
    if (path.len == 0) return false;
    const target = if (std.fs.path.isAbsolute(path))
        std.fs.path.resolve(allocator, &.{path}) catch return false
    else blk: {
        const current = std.process.currentPathAlloc(io, allocator) catch return false;
        break :blk std.fs.path.resolve(allocator, &.{ current, path }) catch return false;
    };
    // without a marker the directory above the file's own, where a program sits next to its `lib/`
    const root = blk: {
        const own_directory = std.fs.path.dirname(target) orelse break :blk target;
        var directory: ?[]const u8 = own_directory;
        while (directory) |candidate| : (directory = std.fs.path.dirname(candidate)) {
            for ([_][]const u8{ ".git", "build.zig" }) |marker| {
                const marker_path = std.fs.path.join(allocator, &.{ candidate, marker }) catch
                    continue;
                std.Io.Dir.cwd().access(io, marker_path, .{}) catch continue;
                break :blk candidate;
            }
        }
        break :blk std.fs.path.dirname(own_directory) orelse own_directory;
    };

    const cwd = std.Io.Dir.cwd();
    var root_directory = cwd.openDir(io, root, .{ .iterate = true }) catch return false;
    defer root_directory.close(io);
    var walker = root_directory.walkSelectively(allocator) catch return false;
    defer walker.deinit();

    while (walker.next(io) catch null) |entry| switch (entry.kind) {
        .directory => {
            // hidden directories (`.git`, `.zig-cache`) and build outputs hold no sources
            const name = entry.basename;
            const is_skipped = (name.len > 0 and name[0] == '.') or
                std.mem.eql(u8, name, "zig-out") or
                std.mem.eql(u8, name, "node_modules");
            if (!is_skipped) walker.enter(io, entry) catch {};
        },
        .file => {
            if (!std.mem.endsWith(u8, entry.basename, ".mn")) continue;
            const includer = std.fs.path.join(allocator, &.{ root, entry.path }) catch continue;
            if (std.mem.eql(u8, includer, target)) continue;

            // an `include "..."` naming `target`, a path relative to the includer as the compiler
            // reads it. lexed, so an include in a comment does not count
            const limit: std.Io.Limit = .limited(50 << 20);
            const source = cwd.readFileAlloc(io, includer, allocator, limit) catch continue;
            if (std.mem.indexOf(u8, source, "include") == null) continue;

            var lexer = Lexer{ .src_bytes = source, .tokens = .init(allocator, 1024) };
            defer lexer.tokens.deinit();
            lexer.gen_tokens() catch {};

            const kinds = lexer.tokens.column(.tk);
            const spans = lexer.tokens.column(.span);
            const includer_directory = std.fs.path.dirname(includer) orelse ".";
            for (kinds, 0..) |kind, i| {
                if (kind != .kw_include and kind != .kw_includeraw or i + 1 >= kinds.len) continue;
                if (kinds[i + 1] != .val_string) continue;
                const written = std.mem.trim(u8, source[spans[i + 1][0]..spans[i + 1][1]], "\"");
                const parts = [_][]const u8{ includer_directory, written };
                const included = std.fs.path.resolve(allocator, &parts) catch continue;
                if (std.mem.eql(u8, included, target)) return true;
            }
        },
        else => {},
    };
    return false;
}

test "an included file (raw, via a library or a namespace) is a library, one in a comment is not" {
    const io = std.testing.io;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var workspace = std.testing.tmpDir(.{});
    defer workspace.cleanup();
    try workspace.dir.createDirPath(io, ".git");
    try workspace.dir.createDirPath(io, "lib/sub");
    const library_source = "# include \"b.mn\"\n<include \"sub/d.mn\">;\npub fun f = () {}\n";
    const program_source = "<include \"lib/a.mn\">;\n<includeraw \"lib/c.mn\">;\n" ++
        "space = <include \"lib/e.mn\">;\nmain = () {}\n";
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/a.mn", .data = library_source });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/b.mn", .data = "pub fun g = () {}\n" });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/c.mn", .data = "fun h = () {}\n" });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/sub/d.mn", .data = "pub fun i = () {}\n" });
    try workspace.dir.writeFile(io, .{ .sub_path = "lib/e.mn", .data = "pub fun j = () {}\n" });
    try workspace.dir.writeFile(io, .{ .sub_path = "main.mn", .data = program_source });

    var root_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const root = root_buffer[0..try workspace.dir.realPath(io, &root_buffer)];
    const library = try std.fs.path.join(allocator, &.{ root, "lib", "a.mn" });
    const mentioned = try std.fs.path.join(allocator, &.{ root, "lib", "b.mn" });
    const raw = try std.fs.path.join(allocator, &.{ root, "lib", "c.mn" });
    const program = try std.fs.path.join(allocator, &.{ root, "main.mn" });
    const nested = try std.fs.path.join(allocator, &.{ root, "lib", "sub", "d.mn" });
    const namespaced = try std.fs.path.join(allocator, &.{ root, "lib", "e.mn" });

    try std.testing.expect(is_included(io, allocator, library));
    try std.testing.expect(!is_included(io, allocator, mentioned));
    try std.testing.expect(is_included(io, allocator, raw));
    try std.testing.expect(!is_included(io, allocator, program));
    try std.testing.expect(is_included(io, allocator, nested));
    try std.testing.expect(is_included(io, allocator, namespaced));
}
