// the operands of a diagnostic, shared by the terminal printers, the test harness and the lsp
const std = @import("std");
const Resolver = @import("../Resolver.zig");
const Doctor = @import("../resolver/Doctor.zig");
const style = @import("style.zig");

const Ink = struct {
    dim: []const u8 = "",
    reset: []const u8 = "",
    bold: []const u8 = "",
    type_color: []const u8 = "",
};

const terminal_ink: Ink = .{
    .dim = style.dim,
    .reset = style.reset,
    .bold = style.bold,
    .type_color = style.type_color,
};

// `paint`: ansi colors for a terminal, plain text for editors
pub fn print_operands(
    writer: *std.Io.Writer,
    resolver: *Resolver,
    code: Doctor.Disorder,
    first: u32,
    second: u32,
    comptime paint: bool,
) !void {
    const ink: Ink = if (paint) terminal_ink else .{};
    const operands = Doctor.operands_of(code);

    for (operands, [2]u32{ first, second }) |operand, value| {
        if (operand.kind == .none) continue;
        // a count may be any number, the other kinds use the maximum as absent
        if (operand.kind != .count and value == std.math.maxInt(u32)) continue;

        try writer.print("  " ++ ink.dim ++ "{s}" ++ ink.reset ++ " ", .{operand.label});
        switch (operand.kind) {
            .name => {
                const known = value < resolver.name_pool.text_to_name.count();
                const text = if (known) resolver.name_pool.text_of(@enumFromInt(value)) else "?";
                try writer.print(ink.bold ++ "`{s}`" ++ ink.reset, .{text});
            },
            .type => {
                try writer.writeAll(ink.type_color);
                const pool = &resolver.static_pool;
                if (value < pool.items.len()) {
                    try pool.format(&resolver.name_pool, @enumFromInt(value), writer);
                } else {
                    try writer.writeAll("?");
                }
                try writer.writeAll(ink.reset);
            },
            .count => try writer.print(ink.bold ++ "{d}" ++ ink.reset, .{value}),
            .declaration => try writer.print(ink.bold ++ "#{d}" ++ ink.reset, .{value}),
            .none => unreachable,
        }
    }
}
