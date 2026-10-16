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
    const is_terminal = std.Io.File.stderr().isTty(io) catch false;
    const reset = if (is_terminal) style.reset else "";
    const dim = if (is_terminal) style.dim else "";
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
        const color = if (!is_terminal)
            ""
        else if (Doctor.severity_of(code) == .@"error")
            style.error_color
        else
            style.warning_color;

        var leaf = node;
        while (resolver.tree.token(leaf) == null) {
            const children = resolver.tree.children(leaf);
            if (children.len == 0 or children[0] == 0) break;
            leaf = children[0];
        }
        const word = if (resolver.tree.token(leaf) == null) 0 else resolver.tree.arg(leaf, 1);
        const word_at = if (word == 0) 0 else resolver.tree.words.column(.at)[word - 1];
        const file = for (resolver.session.files.items) |included| {
            if (word != 0 and word_at >= included.at and word_at - included.at < included.len) {
                break included;
            }
        } else null;
        if (file == null) {
            try writer.print("{s}:{d}:{d}: ", .{ path, line + 1, column + 1 });
        } else {
            const included = file.?;
            const offset = word_at - included.at;
            const text = resolver.tree.text_bytes.buffer[included.at..][0..included.len];
            const before = text[0..offset];
            const included_line = std.mem.count(u8, before, "\n") + 1;
            const line_start = if (std.mem.lastIndexOfScalar(u8, before, '\n')) |i| i + 1 else 0;
            const included_column = offset - line_start + 1;
            try writer.print("{s}:{d}:{d}: ", .{ included.path, included_line, included_column });
        }
        try writer.print("{s}{s}{s}", .{ color, @tagName(code), reset });
        if (is_terminal) {
            try print_operands(writer, resolver, code, first_operand, second_operand, true);
        } else {
            try print_operands(writer, resolver, code, first_operand, second_operand, false);
        }
        try writer.writeAll("\n");
        if (file != null) {
            const note_format = "{s}:{d}:{d}: {s}included here{s}\n";
            try writer.print(note_format, .{ path, line + 1, column + 1, dim, reset });
        }
    }
    try writer.flush();
}
