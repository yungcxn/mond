const std = @import("std");
const Server = @import("Server.zig");
const Analysis = @import("Analysis.zig");

// `mond-lsp` serves the editor, `mond-lsp analyze` is its worker
pub fn main(init: std.process.Init) !void {
    const allocator = init.arena.allocator();
    const arguments = try init.minimal.args.toSlice(allocator);
    if (arguments.len > 1 and std.mem.eql(u8, arguments[1], "analyze")) {
        const path = if (arguments.len > 2) arguments[2] else "";
        return Analysis.run(init.io, allocator, path);
    }
    try Server.run(init.io, init.gpa, try std.process.executablePathAlloc(init.io, allocator));
}
