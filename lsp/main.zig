const std = @import("std");
const Server = @import("Server.zig");
const Analysis = @import("Analysis.zig");

// `mond-lsp` serves the editor, `mond-lsp analyze` is its worker
pub fn main(init: std.process.Init) !void {
    const a = init.arena.allocator();
    const args = try init.minimal.args.toSlice(a);
    if (args.len > 1 and std.mem.eql(u8, args[1], "analyze")) return Analysis.run(init.io, a);
    try Server.run(init.io, init.gpa, try std.process.executablePathAlloc(init.io, a));
}
