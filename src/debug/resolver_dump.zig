// the resolver dump: one row per declaration, then every diagnostic under its source line
const std = @import("std");
const Resolver = @import("../Resolver.zig");
const Doctor = @import("../resolver/Doctor.zig");
const source_positions = @import("source.zig");
const print_operands = @import("operands.zig").print_operands;
const style = @import("style.zig");

const reset = style.reset;
const dim = style.dim;
const bold = style.bold;

pub fn print(io: std.Io, resolver: *Resolver) !void {
    var buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const writer = &file_writer.interface;

    var line_starts = source_positions.line_starts(resolver);
    defer line_starts.deinit();
    const starts = line_starts.items();

    const header = dim ++ "[DEBUG RESOLVER DUMP]\n" ++ reset;
    try writer.writeAll(header ++ style.function_color ++ "declarations\n" ++ reset);

    const declarations = resolver.decl_pool.entries.columns();
    var global_count: usize = 0;
    for (0..declarations.name.len) |i| {
        global_count += @intFromBool(declarations.flags[i].is_global);
        try declaration_row(writer, resolver, starts, i);
    }

    const diagnostics = resolver.doctor.diagnostics.columns();
    if (diagnostics.code.len > 0) {
        try writer.writeAll(style.function_color ++ "\ndiagnostics\n" ++ reset);
    }

    var error_count: usize = 0;
    for (
        diagnostics.code,
        diagnostics.node,
        diagnostics.first_operand,
        diagnostics.second_operand,
    ) |code, node, first_operand, second_operand| {
        const severity = Doctor.severity_of(code);
        error_count += @intFromBool(severity == .@"error");

        const severity_color = if (severity == .@"error")
            style.error_color
        else
            style.warning_color;
        const title_format = "{s}{s}" ++ reset ++ " " ++ bold ++ "{s}" ++ reset;
        try writer.print(title_format, .{ severity_color, @tagName(severity), @tagName(code) });

        const span = source_positions.node_span(resolver.tree, resolver.src_bytes, node);
        const line = if (span) |known| source_positions.line_of(starts, known[0]) else 0;
        if (span) |known| {
            const column = known[0] - starts[line] + 1;
            try writer.print(dim ++ ", :{d}:{d}" ++ reset, .{ line + 1, column });
        }

        try print_operands(writer, resolver, code, first_operand, second_operand, true);
        try writer.writeAll("\n");

        if (span) |known| {
            const line_start = starts[line];
            const line_end = source_positions.line_end(starts, line, resolver.src_bytes.len);
            const indent = style.spaces[0..@min(style.spaces.len, known[0] - line_start)];
            const source_line = resolver.src_bytes[line_start..line_end];
            try writer.print(
                "    {s}\n    " ++ style.kind_color ++ "{s}",
                .{ source_line, indent },
            );

            const underline_length = @max(1, @min(known[1], line_end) -| known[0]);
            for (0..underline_length) |_| try writer.writeAll("~");
            try writer.writeAll(reset ++ "\n");
        }
    }

    const diagnostic_count = resolver.doctor.diagnostics.columns().code.len;
    const summary_format = dim ++ "\n{d} declarations ({d} global), {d} pool entries, " ++
        "{d} type vars, {d} diagnostics ({d} errors, {d} warnings)\n" ++ reset;
    try writer.print(summary_format, .{
        declarations.name.len,
        global_count,
        resolver.static_pool.items.len(),
        resolver.static_pool.type_variables.count(),
        diagnostic_count,
        error_count,
        diagnostic_count - error_count,
    });
    try writer.flush();
}

pub fn declaration_row(
    writer: *std.Io.Writer,
    resolver: *Resolver,
    starts: []const u32,
    index: usize,
) !void {
    const declarations = resolver.decl_pool.entries.columns();
    const pool = &resolver.static_pool;
    const kind = declarations.kind[index];
    const flags = declarations.flags[index];

    const name_color = if (flags.is_global) style.function_color else switch (kind) {
        .function,
        .static_function,
        .inlined_function,
        .trait_member,
        .type_alias,
        .record,
        .variant,
        .trait,
        => style.kind_color,
        .field => style.field_color,
        .variable,
        .parameter,
        .static_parameter,
        .variant_case,
        .pattern_binder,
        .arrow_binder,
        .loop_variable,
        .self,
        .autoins_arg,
        .autoins_it,
        => style.variable_color,
    };
    const node = declarations.node[index];
    const span = source_positions.node_span(resolver.tree, resolver.src_bytes, node);
    const line = if (span) |known| source_positions.line_of(starts, known[0]) + 1 else 0;
    const name = source_positions.declaration_name(resolver, @enumFromInt(index));

    // the modifiers ("pub ", 4 columns each) share the padded name column
    const modifier_count = @as(usize, @intFromBool(flags.is_pub)) +
        @intFromBool(flags.is_mut) +
        @intFromBool(flags.is_stc);
    const padding = style.spaces[0..24 -| (name.len + 4 * modifier_count)];

    const name_format = dim ++ "  #{d:<5}" ++ reset ++ " " ++
        style.field_color ++ "{s}{s}{s}{s}{s}" ++ reset ++ "{s}";
    try writer.print(name_format, .{
        index,
        if (flags.is_pub) "pub " else "",
        if (flags.is_mut) "mut " else "",
        if (flags.is_stc) "stc " else "",
        name_color,
        name,
        padding,
    });
    try writer.print(dim ++ "{s:<16} :{d:<5}" ++ reset ++ " ", .{ @tagName(kind), line });

    if (declarations.state[index] == .failed) {
        try writer.writeAll(style.error_color ++ "failed " ++ reset);
    }
    try writer.writeAll(style.type_color);
    try pool.format(&resolver.name_pool, declarations.value_type[index], writer);
    try writer.writeAll(reset);

    const static_value = declarations.static_value[index];
    // a function's own value, a trait and a static function would only repeat the type
    const shows_static_value = static_value != .none and
        !(pool.tag(static_value) == .function_value and
            @intFromEnum(pool.get(static_value).function_value) == index) and
        kind != .trait and
        pool.tag(static_value) != .static_function;
    if (shows_static_value) {
        try writer.writeAll(dim ++ " = " ++ reset);
        try pool.format(&resolver.name_pool, static_value, writer);
    }

    const next_overload = declarations.next_overload[index];
    if (next_overload != .none) {
        const overload_format = dim ++ "  next overload #{d}" ++ reset;
        try writer.print(overload_format, .{@intFromEnum(next_overload)});
    }
    try writer.writeAll("\n");
}
