const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;
const ParseTree = mond.ParseTree;
const Resolver = mond.Resolver;
const Analysis = @import("Analysis.zig");
const linking = @import("linking.zig");
const positions = @import("positions.zig");
const StaticIndex = std.meta.Child(@FieldType(Resolver, "node_types"));
const DeclPool = mond.DeclPool;
const Writer = std.Io.Writer;
const outside = "outside a function: static_eval_failed";

// the hover of an unwrap without fallback (`x??`): what a failure returns, by the compiler's rules
// (`StaticPool.fallback_case`, `Flow.missing_fallback`) for the result of each function holding it

pub fn link(analysis: *Analysis, lexer: *Lexer, resolver: *Resolver) void {
    const tree = resolver.tree;
    const tokens = lexer.tokens.columns();
    // the `??` of an unwrap follows its operand, past brackets, postfix operators and the `??` of
    // unwraps inside the operand, which come first
    const taken = analysis.allocator.alloc(bool, tokens.tk.len) catch @panic("OOM");
    @memset(taken, false);
    for (1..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const kind = tree.kind(node);
        if (kind != .selftag_unwrap and kind != .selftag_unwrap_fallback) continue;
        const operand_extent = tree.extent(tree.arg(node, 0)) orelse continue;
        const end = operand_extent[1];
        const after_operand = std.sort.partitionPoint(Lexer.TextSpan, tokens.span, end, struct {
            fn before(operand_end: u32, span: Lexer.TextSpan) bool {
                return span[0] < operand_end;
            }
        }.before);
        const token = for (after_operand..tokens.tk.len) |candidate| switch (tokens.tk[candidate]) {
            .@"pct_(", .@"pct_)", .@"pct_[", .@"pct_]", .@"xpct_.*", .@"xpct_.&" => {},
            .@"xpct_++", .@"xpct_--" => {},
            .@"xpct_??" => if (!taken[candidate]) break candidate,
            else => break null,
        } else null;
        const unwrap_token = token orelse continue;
        taken[unwrap_token] = true;
        if (kind != .selftag_unwrap or is_quoted(analysis, tree, node)) continue;

        const span = tokens.span[unwrap_token];
        analysis.declaration_sites.push(.{
            .token = Analysis.none,
            .global = false,
            .class = .operator,
            .modifiers = 0,
        });
        analysis.declarations.push(.{
            .name = "??",
            .detail = describe(analysis, resolver, node) catch @panic("OOM"),
            .kind = 0,
            .range = positions.range(analysis, span[0], span[1]),
            .selectionRange = null,
        });
        analysis.token_meaning[unwrap_token] = @intCast(analysis.declarations.items().len - 1);
    }
}

// per innermost function holding `node` (one, or a realization per argument type) what it returns
fn describe(analysis: *Analysis, resolver: *Resolver, node: u32) ![]const u8 {
    const bodies = resolver.bodies.bodies.columns();
    const node_types = resolver.bodies.node_rows.column(.node_type);
    var innermost: u32 = std.math.maxInt(u32);
    for (bodies.declaration, bodies.first_node, bodies.node_count) |declaration, first, count| {
        if (!resolver.decl_pool.get(declaration, .kind).is_function()) continue;
        if (node -% first < count) innermost = @min(innermost, count);
    }
    if (innermost == std.math.maxInt(u32)) return outside;

    var text: Writer.Allocating = .init(analysis.allocator);
    var described: Writer.Allocating = .init(analysis.allocator);
    for (
        bodies.declaration,
        bodies.first_node,
        bodies.node_count,
        bodies.first_row,
    ) |declaration, first, count, first_row| {
        if (count != innermost or node -% first >= count) continue;
        if (!resolver.decl_pool.get(declaration, .kind).is_function()) continue;
        if (is_in_default(resolver, declaration, node)) return outside;
        const pool = &resolver.static_pool;
        const operand_type = node_types[first_row + resolver.tree.arg(node, 0) - first];
        const declared = resolver.types.signature(declaration).return_type;
        // a stcfun without a declared result returns what its body makes
        const produced = resolver.declarations.produced_node(declaration);
        const result = if (pool.substitute_type_variables(declared) == .poison_type)
            node_types[first_row + produced - first]
        else
            declared;
        described.clearRetainingCapacity();
        try describe_return(
            analysis,
            resolver,
            &described.writer,
            pool.substitute_type_variables(result),
            pool.substitute_type_variables(operand_type),
        );
        // realizations returning the same are told once
        const one = described.written();
        var lines = std.mem.splitSequence(u8, text.written(), " | ");
        const is_told = while (lines.next()) |line| {
            if (std.mem.eql(u8, line, one)) break true;
        } else false;
        if (is_told) continue;
        if (text.written().len > 0) try text.writer.writeAll(" | ");
        try text.writer.writeAll(one);
    }
    return text.written();
}

// quoted code returns from the function it lands in, not from the one it is written in
fn is_quoted(analysis: *Analysis, tree: *ParseTree, node: u32) bool {
    var ancestor = analysis.node_parent[node];
    while (ancestor != Analysis.none) : (ancestor = analysis.node_parent[ancestor]) {
        switch (tree.kind(ancestor)) {
            .quote => return true,
            .unquote, .unquote_list => return false,
            else => {},
        }
    }
    return false;
}

// a parameter's default runs where the function is called, it is no part of the function's body
fn is_in_default(resolver: *Resolver, declaration: DeclPool.Index, node: u32) bool {
    const tree = resolver.tree;
    for (tree.params_of(resolver.declarations.value_node(declaration))) |parameter| {
        const default = ParseTree.Param.from_node(tree, parameter).default;
        if (default == 0) continue;
        const first, const end = tree.subtree(default);
        if (node >= first and node < end) return true;
    }
    return false;
}

fn describe_return(
    analysis: *Analysis,
    resolver: *Resolver,
    writer: *Writer,
    result: StaticIndex,
    operand_type: StaticIndex,
) !void {
    const pool = &resolver.static_pool;
    if (pool.tag(operand_type) != .variant_type) return writer.writeAll("never fails");
    const missing = resolver.flow.missing_fallback(result, operand_type);
    if (missing != .none) {
        return writer.print("no fallback: {s}", .{linking.type_text(analysis, resolver, missing)});
    }
    try writer.writeAll("ret");
    if (result == .unit_type or result == .runit_type or result == .poison_type) return;

    // each failing case that picks itself, then what the others pick
    try writer.writeByte(' ');
    const unwrapped = pool.first_payload_case(operand_type);
    var told: u32 = 0;
    var others = false;
    for (pool.get(operand_type).variant_type.cases) |failing| {
        if (failing == unwrapped) continue;
        if (pool.fallback_case(result, failing) != failing) {
            others = true;
            continue;
        }
        if (told > 0) try writer.writeAll(" or ");
        try write_value(analysis, resolver, writer, result, failing);
        told += 1;
    }
    if (others) {
        if (told > 0) try writer.writeAll(" or ");
        try write_value(analysis, resolver, writer, result, .none);
    }
    try writer.print("  # {s}", .{name_of(analysis, resolver, result)});
}

fn write_value(
    analysis: *Analysis,
    resolver: *Resolver,
    writer: *Writer,
    value_type: StaticIndex,
    failing: StaticIndex,
) Writer.Error!void {
    const pool = &resolver.static_pool;
    const properties = pool.properties(value_type);
    if (properties.is_integer) return writer.writeAll("0");
    if (properties.is_float) return writer.writeAll("0.0");
    if (value_type == .bool_type) return writer.writeAll("false");
    switch (pool.tag(value_type)) {
        .array_type => {
            const element = pool.get(value_type).array_type.element;
            const length = pool.static_length(value_type) orelse 0;
            try writer.writeByte('[');
            for (0..@min(length, 4)) |i| {
                if (i > 0) try writer.writeAll(", ");
                try write_value(analysis, resolver, writer, element, .none);
            }
            if (length > 4) try writer.writeAll(", ..");
            try writer.writeByte(']');
        },
        .record_type => {
            try writer.writeAll(name_of(analysis, resolver, value_type));
            try write_fields(analysis, resolver, writer, value_type);
        },
        .variant_type, .unified_variant_type, .variant_case_type => {
            const case = pool.fallback_case(value_type, failing);
            if (pool.tag(case) != .variant_case_type) {
                return write_value(analysis, resolver, writer, case, .none);
            }
            const case_type = pool.get(case).variant_case_type;
            const case_name = resolver.name_pool.text_of(case_type.name);
            const variant_name = name_of(analysis, resolver, case_type.variant);
            try writer.print("{s}.{s}", .{ variant_name, case_name });
            if (case_type.payload != .none) {
                try write_fields(analysis, resolver, writer, case_type.payload);
            }
        },
        else => {},
    }
}

// `(name = value, ..)`, a default as written, a positional field without its name
fn write_fields(
    analysis: *Analysis,
    resolver: *Resolver,
    writer: *Writer,
    record: StaticIndex,
) Writer.Error!void {
    const pool = &resolver.static_pool;
    try writer.writeByte('(');
    for (resolver.types.field_nodes_of(record), 0..) |field_node, i| {
        if (i > 0) try writer.writeAll(", ");
        const name = resolver.name_pool.text_of(pool.get(record).record_type.field_names[i]);
        if (name.len > 0 and name[0] != '$') try writer.print("{s} = ", .{name});
        const default = ParseTree.Param.from_node(resolver.tree, field_node).default;
        if (default != 0) {
            try writer.writeAll(source_of(analysis, resolver, default));
        } else {
            try write_value(analysis, resolver, writer, pool.field_type(record, i), .none);
        }
    }
    try writer.writeByte(')');
}

// a record or variant by its declared name
fn name_of(analysis: *Analysis, resolver: *Resolver, type_index: StaticIndex) []const u8 {
    const pool = &resolver.static_pool;
    const declaration = switch (pool.get(type_index)) {
        .record_type => |record| record.declaration,
        .variant_type => |variant| variant.declaration,
        else => return linking.type_text(analysis, resolver, type_index),
    };
    const name = resolver.name_pool.text_of(resolver.decl_pool.get(declaration, .name));
    return if (name.len > 0) name else linking.type_text(analysis, resolver, type_index);
}

// the source of an expression: its tokens, the brackets and quotes closing it
fn source_of(analysis: *Analysis, resolver: *Resolver, node: u32) []const u8 {
    const source = analysis.source;
    const extent = resolver.tree.extent(node) orelse return "..";
    if (extent[1] > source.len) return "..";
    var start = extent[0];
    var end = extent[1];
    if (start > 0 and source[start - 1] == '"' and end < source.len) {
        start -= 1;
        end += 1;
    }
    var depth: i32 = 0;
    for (source[start..end]) |byte| depth += bracket_depth(byte);
    while (depth > 0 and end < source.len) : (end += 1) depth += bracket_depth(source[end]);
    return source[start..end];
}

fn bracket_depth(byte: u8) i32 {
    return switch (byte) {
        '(', '[', '{' => 1,
        ')', ']', '}' => -1,
        else => 0,
    };
}
