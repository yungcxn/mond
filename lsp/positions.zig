const std = @import("std");
const Analysis = @import("Analysis.zig");
const Position = Analysis.Position;
const Range = Analysis.Range;

// byte offsets of the source as lsp positions: a line and a column in utf-16 code units

pub fn range(analysis: *const Analysis, start_offset: u32, end_offset: u32) Range {
    return .{ .start = position(analysis, start_offset), .end = position(analysis, end_offset) };
}

pub fn position(analysis: *const Analysis, offset: u32) Position {
    const line_starts = analysis.line_starts.items();
    const line = std.sort.partitionPoint(u32, line_starts, offset, starts_at_or_before) - 1;
    const text_before = analysis.source[line_starts[line]..offset];
    return .{ .line = @intCast(line), .character = utf16_length(text_before) };
}

fn starts_at_or_before(offset: u32, line_start: u32) bool {
    return line_start <= offset;
}

pub fn before(earlier: Position, later: Position) bool {
    if (earlier.line != later.line) return earlier.line < later.line;
    return earlier.character < later.character;
}

// lsp counts columns in utf-16 code units
pub fn utf16_length(text: []const u8) u32 {
    var units: u32 = 0;
    for (text) |byte| units += switch (byte) {
        // a continuation byte adds nothing, a four byte sequence is a surrogate pair,
        // an invalid lead byte is one replacement character
        0x80...0xbf => 0,
        0xf0...0xf7 => 2,
        else => 1,
    };
    return units;
}
