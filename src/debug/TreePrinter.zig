// the parse tree as an indented outline
// once resolved, annotated with types, declarations and diagnostics
const TreePrinter = @This();
const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const Doctor = @import("../resolver/Doctor.zig");
const source_positions = @import("source.zig");
const print_operands = @import("operands.zig").print_operands;
const style = @import("style.zig");
const Node = ParseTree.Node;
const NodeId = ParseTree.NodeId;

const reset = style.reset;
const dim = style.dim;
const bold = style.bold;

writer: *std.Io.Writer,
tree: *ParseTree,
source: []const u8,
// null for the bare parse tree, which has nothing to annotate
resolver: ?*Resolver,
// indexed by node, empty without a resolver
diagnosed: []bool,

pub fn print(
    io: std.Io,
    tree: *ParseTree,
    source: []const u8,
    roots: []const NodeId,
    resolver: ?*Resolver,
) !void {
    var buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &buffer);

    const diagnosed = try diagnosed_nodes(tree, resolver);
    defer std.heap.smp_allocator.free(diagnosed);

    const printer: TreePrinter = .{
        .writer = &file_writer.interface,
        .tree = tree,
        .source = source,
        .resolver = resolver,
        .diagnosed = diagnosed,
    };
    const writer = printer.writer;

    const parser_header = dim ++ "[DEBUG PARSER AST DUMP]\n" ++ reset;
    const resolver_header = dim ++ "[DEBUG RESOLVER TREE]\n" ++ reset;
    try writer.writeAll(if (resolver == null) parser_header else resolver_header);

    for (roots, 0..) |root, i| {
        const root_kind = tree.ast_nodes.column(.nk)[root];
        const root_format = style.function_color ++ "{s} (#{d})" ++ reset;
        try writer.print(root_format, .{ @tagName(root_kind), i });
        try printer.annotate(root);
        try writer.writeAll("\n");

        try printer.print_node(root, "", true, true, "", 0);
        try writer.writeAll("\n");
    }

    const node_count = tree.ast_nodes.len();
    try writer.print(dim ++ "{d} functions, {d} nodes total" ++ reset, .{ roots.len, node_count });
    if (resolver) |resolved| {
        const declaration_count = resolved.decl_pool.entries.len();
        const diagnostic_count = resolved.doctor.diagnostics.len();
        const counts_format = dim ++ ", {d} declarations, {d} diagnostics" ++ reset;
        try writer.print(counts_format, .{ declaration_count, diagnostic_count });
    }
    try writer.writeAll("\n");
    try writer.flush();
}

// owned by `std.heap.smp_allocator`
pub fn diagnosed_nodes(tree: *ParseTree, resolver: ?*Resolver) ![]bool {
    const length = if (resolver == null) 0 else tree.ast_nodes.len();
    const diagnosed = try std.heap.smp_allocator.alloc(bool, length);
    @memset(diagnosed, false);

    const resolved = resolver orelse return diagnosed;
    for (resolved.doctor.diagnostics.column(.node)) |node| diagnosed[node] = true;
    return diagnosed;
}

// a root prints no line of its own, its caller has written the header
pub fn print_node(
    printer: TreePrinter,
    node: NodeId,
    prefix: []const u8,
    is_root: bool,
    is_last: bool,
    label: []const u8,
    label_width: usize,
) std.Io.Writer.Error!void {
    if (node >= printer.tree.ast_nodes.len()) {
        const missing_format = "{s}" ++ style.error_color ++ "<missing node #{d}>\n" ++ reset;
        return printer.writer.print(missing_format, .{ prefix, node });
    }

    const kind = printer.tree.ast_nodes.column(.nk)[node];
    const slots: [2]NodeId = printer.tree.ast_nodes.column(.args)[node];
    const child_count = Node.nk_childc[@intFromEnum(kind)];
    const is_leaf = child_count == .none or child_count == .data;

    if (!is_root) try printer.print_node_line(node, prefix, is_last, label, label_width);
    if (is_leaf) return;

    var prefix_buffer: [1024]u8 = undefined;
    const continuation = prefix_continuation(is_root, is_last);
    const child_prefix = std.fmt.bufPrint(
        &prefix_buffer,
        "{s}{s}",
        .{ prefix, continuation },
    ) catch prefix;

    if (child_count == .many) return printer.print_list_children(slots, child_prefix);

    const field_names = Node.nk_field_names[@intFromEnum(kind)];
    const field_count: usize = if (child_count == .two) 2 else 1;
    const second_name_length = if (field_count == 2) field_names[1].len else 0;
    const field_label_width = @max(field_names[0].len, second_name_length);
    for (0..field_count) |i| {
        const is_last_field = i + 1 == field_count;
        try printer.print_node(
            slots[i],
            child_prefix,
            false,
            is_last_field,
            field_names[i],
            field_label_width,
        );
    }
}

fn print_node_line(
    printer: TreePrinter,
    node: NodeId,
    prefix: []const u8,
    is_last: bool,
    label: []const u8,
    label_width: usize,
) !void {
    const writer = printer.writer;
    const kind = printer.tree.ast_nodes.column(.nk)[node];
    const child_count = Node.nk_childc[@intFromEnum(kind)];
    const is_leaf = child_count == .none or child_count == .data;

    const branch = if (is_last) "└── " else "├── ";
    try writer.print("{s}{s}", .{ prefix, branch });

    if (label.len > 0) {
        const padding_length = @min(style.spaces.len - 1, label_width -| label.len) + 1;
        const label_format = style.field_color ++ "{s}" ++ dim ++ ":" ++ reset ++ "{s}";
        try writer.print(label_format, .{ label, style.spaces[0..padding_length] });
    }

    const kind_color = if (is_leaf) style.leaf_color else style.kind_color;
    try writer.print("{s}{s}" ++ reset, .{ kind_color, @tagName(kind) });

    if (child_count == .data) {
        const text = printer.tree.text(node, printer.source);
        if (text.len > 0) try writer.print(dim ++ "  \"{s}\"" ++ reset, .{text});
    }

    try printer.annotate(node);
    try writer.writeAll("\n");
}

fn prefix_continuation(is_root: bool, is_last: bool) []const u8 {
    if (is_root) return "";
    if (is_last) return "    ";
    return "│   ";
}

fn print_list_children(
    printer: TreePrinter,
    slots: [2]NodeId,
    child_prefix: []const u8,
) std.Io.Writer.Error!void {
    const first_reference = slots[0];
    const length = slots[1];
    const children = printer.tree.extra_childrefs.buffer[first_reference..][0..length];

    var label_buffer: [16]u8 = undefined;
    const widest_label = std.fmt.bufPrint(&label_buffer, "[{d}]", .{length -| 1}) catch unreachable;
    const label_width = widest_label.len;

    for (children, 0..) |child, i| {
        const label = std.fmt.bufPrint(&label_buffer, "[{d}]", .{i}) catch unreachable;
        const is_last = i + 1 == children.len;
        try printer.print_node(child, child_prefix, false, is_last, label, label_width);
    }
}

pub fn annotate(printer: TreePrinter, node: NodeId) !void {
    const resolver = printer.resolver orelse return;

    try printer.annotate_type(resolver, node);
    try printer.annotate_declaration(resolver, node);

    if (!printer.diagnosed[node]) return;
    try printer.annotate_diagnostics(resolver, node);
}

fn annotate_type(printer: TreePrinter, resolver: *Resolver, node: NodeId) !void {
    const node_type = resolver.node_types[node];
    if (node_type == .none) return;

    const poison_prefix = style.error_color ++ "  : ";
    const type_prefix = style.type_color ++ "  : ";
    try printer.writer.writeAll(if (node_type == .poison_type) poison_prefix else type_prefix);
    try resolver.static_pool.format(&resolver.name_pool, node_type, printer.writer);
    try printer.writer.writeAll(reset);
}

fn annotate_declaration(printer: TreePrinter, resolver: *Resolver, node: NodeId) !void {
    const declaration = resolver.node_declarations[node];
    if (declaration == .none) return;

    const declaration_format = dim ++ "  → " ++ reset ++ bold ++ "#{d} {s}" ++ reset ++
        dim ++ " {s}" ++ reset;
    try printer.writer.print(declaration_format, .{
        @intFromEnum(declaration),
        source_positions.declaration_name(resolver, declaration),
        @tagName(resolver.decl_pool.get(declaration, .kind)),
    });
}

fn annotate_diagnostics(printer: TreePrinter, resolver: *Resolver, node: NodeId) !void {
    const diagnostics = resolver.doctor.diagnostics.columns();
    for (
        diagnostics.node,
        diagnostics.code,
        diagnostics.first_operand,
        diagnostics.second_operand,
    ) |diagnosed_node, code, first_operand, second_operand| {
        if (diagnosed_node != node) continue;

        const is_error = Doctor.severity_of(code) == .@"error";
        const color = if (is_error) style.error_color else style.warning_color;
        try printer.writer.print("{s}  ✗ {s}" ++ reset, .{ color, @tagName(code) });
        try print_operands(printer.writer, resolver, code, first_operand, second_operand, true);
    }
}
