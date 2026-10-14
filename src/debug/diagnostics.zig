// the diagnostics of a resolved file as `path:line:column: code operands`, one per line
const std = @import("std");
const Resolver = @import("../Resolver.zig");
const Doctor = @import("../resolver/Doctor.zig");
const source = @import("source.zig");
const style = @import("style.zig");
const print_operands = @import("operands.zig").print_operands;

pub fn print(io: std.Io, resolver: *Resolver, path: []const u8) !void {
    var buffer: [4096]u8 = undefined;
    var file_writer = std.Io.File.stderr().writerStreaming(io, &buffer);
    const writer = &file_writer.interface;

    var starts = source.line_starts(resolver);
    defer starts.deinit();
    const diagnostics = resolver.doctor.diagnostics.columns();
    for (
        diagnostics.node,
        diagnostics.code,
        diagnostics.first_operand,
        diagnostics.second_operand,
    ) |node, code, first_operand, second_operand| {
        const span = source.node_span(resolver.tree, resolver.src_bytes, node);
        const at: u32 = if (span) |known| known[0] else 0;
        const line_starts = starts.buffer[0..starts.len];
        const line = source.line_of(line_starts, at);
        const column = at - line_starts[line];
        const color = if (Doctor.severity_of(code) == .@"error")
            style.error_color
        else
            style.warning_color;
        try writer.print("{s}:{d}:{d}: {s}{s}" ++ style.reset, .{
            path,
            line + 1,
            column + 1,
            color,
            @tagName(code),
        });
        try print_operands(writer, resolver, code, first_operand, second_operand, true);
        try writer.writeAll("\n");
    }
    try writer.flush();
}
