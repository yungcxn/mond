// `mond --inspect`: the resolved tree and the lowered code of declarations
// queried by name, `#index` or `:line`
const Inspector = @This();
const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const HighLowerer = @import("../HighLowerer.zig");
const DeclPool = @import("../resolver/DeclPool.zig");
const TreePrinter = @import("TreePrinter.zig");
const ir_printer = @import("ir_printer.zig");
const resolver_dump = @import("resolver_dump.zig");
const source_positions = @import("source.zig");
const style = @import("style.zig");
const Node = ParseTree.Node;
const NodeId = ParseTree.NodeId;

const reset = style.reset;
const dim = style.dim;
const bold = style.bold;

const no_node = std.math.maxInt(NodeId);

writer: *std.Io.Writer,
resolver: *Resolver,
// null when resolution failed and nothing was lowered
lowerer: ?*HighLowerer,
tree_printer: TreePrinter,
line_starts: []const u32,
// indexed by node, `no_node` for a root
parent: []NodeId,
// indexed by node, the function or type declared by it, else `.none`
owner: []DeclPool.Index,

pub fn run(
    io: std.Io,
    resolver: *Resolver,
    lowerer: ?*HighLowerer,
    queries: []const [:0]const u8,
) !void {
    const allocator = std.heap.smp_allocator;
    var output_buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &output_buffer);

    var line_starts = source_positions.line_starts(resolver);
    defer line_starts.deinit();

    const node_count = resolver.tree.ast_nodes.len();
    const diagnosed = try TreePrinter.diagnosed_nodes(resolver.tree, resolver);
    defer allocator.free(diagnosed);

    const parent = try allocator.alloc(NodeId, node_count);
    defer allocator.free(parent);
    const owner = try allocator.alloc(DeclPool.Index, node_count);
    defer allocator.free(owner);
    fill_parents(resolver.tree, parent);
    fill_owners(resolver, owner);

    const inspector: Inspector = .{
        .writer = &file_writer.interface,
        .resolver = resolver,
        .lowerer = lowerer,
        .tree_printer = .{
            .writer = &file_writer.interface,
            .tree = resolver.tree,
            .source = resolver.src_bytes,
            .resolver = resolver,
            .diagnosed = diagnosed,
        },
        .line_starts = line_starts.items(),
        .parent = parent,
        .owner = owner,
    };

    if (queries.len == 0) {
        const usage = dim ++ "usage: mond --inspect (name | #decl | :line)...\n" ++ reset;
        try inspector.writer.writeAll(usage);
    }
    for (queries) |query| {
        if (query.len > 0) try inspector.answer(query);
    }
    try inspector.writer.flush();
}

fn fill_parents(tree: *ParseTree, parent: []NodeId) void {
    @memset(parent, no_node);
    for (0..parent.len) |node| {
        for (tree.children(@intCast(node))) |child| {
            if (child < parent.len) parent[child] = @intCast(node);
        }
    }
}

fn fill_owners(resolver: *Resolver, owner: []DeclPool.Index) void {
    @memset(owner, .none);
    const declarations = resolver.decl_pool.entries.columns();
    for (declarations.node, declarations.kind, 0..) |node, kind, i| {
        const owns_code = kind.is_function() or is_type_kind(kind);
        if (owns_code and node < owner.len) owner[node] = @enumFromInt(i);
    }
}

fn answer(inspector: Inspector, query: []const u8) !void {
    try inspector.writer.print(bold ++ "\n▸ {s}\n" ++ reset, .{query});

    const matched = if (query[0] == ':')
        try inspector.inspect_line(query[1..])
    else
        try inspector.inspect_declarations(query);
    if (!matched) try inspector.writer.writeAll(style.error_color ++ "  no match\n" ++ reset);
}

fn inspect_declarations(inspector: Inspector, query: []const u8) !bool {
    const resolver = inspector.resolver;
    const wanted_index: ?usize = if (query[0] == '#')
        std.fmt.parseInt(usize, query[1..], 10) catch return false
    else
        null;

    var matched = false;
    for (0..resolver.decl_pool.entries.len()) |i| {
        if (!inspector.matches(i, wanted_index, query)) continue;
        matched = true;
        const declaration: DeclPool.Index = @enumFromInt(i);

        try inspector.writer.writeAll(style.function_color ++ "resolved\n" ++ reset);
        try resolver_dump.declaration_row(inspector.writer, resolver, inspector.line_starts, i);
        try inspector.print_subtree(resolver.decl_pool.get(declaration, .node));

        const by_index = wanted_index != null;
        if (by_index or !inspector.shares_later_function(declaration)) {
            try inspector.print_lowered(declaration);
        }
    }
    if (matched) return true;
    return std.mem.eql(u8, query, "$init") and try inspector.print_functions(.none) > 0;
}

// overloads of equal parameters share one function, by name it is printed at the last one
fn shares_later_function(inspector: Inspector, declaration: DeclPool.Index) bool {
    const lowerer = inspector.lowerer orelse return false;
    return lowerer.next_overload_of.contains(declaration);
}

fn matches(inspector: Inspector, index: usize, wanted_index: ?usize, query: []const u8) bool {
    if (wanted_index) |wanted| return wanted == index;
    const name = source_positions.declaration_name(inspector.resolver, @enumFromInt(index));
    return std.mem.eql(u8, name, query);
}

fn inspect_line(inspector: Inspector, line_text: []const u8) !bool {
    const wanted_line = (std.fmt.parseInt(usize, line_text, 10) catch return false) -| 1;

    var last_declaration: ?DeclPool.Index = null;
    for (1..inspector.parent.len) |i| {
        const node: NodeId = @intCast(i);
        if (!inspector.is_outermost_on_line(node, wanted_line)) continue;

        try inspector.writer.writeAll(style.function_color ++ "resolved\n" ++ reset);
        try inspector.print_subtree(node);

        const declaration = inspector.enclosing_declaration(node);
        if (declaration != last_declaration) try inspector.print_lowered(declaration);
        last_declaration = declaration;

        try inspector.print_nested_functions(node, declaration);
    }
    return last_declaration != null;
}

// a node whose parent also lies within the line is printed as part of that parent
fn is_outermost_on_line(inspector: Inspector, node: NodeId, line: usize) bool {
    if (inspector.line_of_node(node) != line) return false;
    if (inspector.continues_past_line(node, line)) return false;

    const parent = inspector.parent[node];
    if (parent == no_node) return true;
    if (inspector.line_of_node(parent) != line) return true;
    return inspector.continues_past_line(parent, line);
}

// functions declared inside the node (closures) are lowered on their own
fn print_nested_functions(
    inspector: Inspector,
    node: NodeId,
    declaration: DeclPool.Index,
) !void {
    for (inspector.owner, 0..) |owned, owner_node| {
        if (owned == .none or owned == declaration) continue;
        if (inspector.enclosing_declaration(@intCast(owner_node)) != owned) continue;
        if (!inspector.is_within(@intCast(owner_node), node)) continue;
        _ = try inspector.print_functions(owned);
    }
}

fn line_of_node(inspector: Inspector, node: NodeId) ?usize {
    const resolver = inspector.resolver;
    const span = source_positions.node_span(resolver.tree, resolver.src_bytes, node) orelse
        return null;
    return source_positions.line_of(inspector.line_starts, span[0]);
}

fn print_subtree(inspector: Inspector, node: NodeId) !void {
    if (node == 0 or node >= inspector.parent.len) return;
    const writer = inspector.writer;
    const resolver = inspector.resolver;

    if (inspector.line_of_node(node)) |line| {
        const starts = inspector.line_starts;
        const line_end = source_positions.line_end(starts, line, resolver.src_bytes.len);
        const source_line = resolver.src_bytes[starts[line]..line_end];
        try writer.print(dim ++ "  {d:>5} │ " ++ reset ++ "{s}\n", .{ line + 1, source_line });
    }

    const kind = resolver.tree.ast_nodes.column(.nk)[node];
    try writer.print(style.kind_color ++ "{s}" ++ reset, .{@tagName(kind)});
    try inspector.tree_printer.annotate(node);
    try writer.writeAll("\n");
    try inspector.tree_printer.print_node(node, "", true, true, "", 0);
}

fn enclosing_declaration(inspector: Inspector, node: NodeId) DeclPool.Index {
    var current = node;
    while (current != no_node and inspector.owner[current] == .none) {
        current = inspector.parent[current];
    }
    if (current == no_node) return .none;
    return inspector.owner[current];
}

// walks outwards until a declaration has code of its own, the rest lives in `$init`
fn print_lowered(inspector: Inspector, declaration: DeclPool.Index) !void {
    const writer = inspector.writer;
    const lowerer = inspector.lowerer orelse {
        const failed = style.error_color ++ "lowered\n  not lowered, resolution failed\n" ++ reset;
        return writer.writeAll(failed);
    };
    try writer.writeAll(style.function_color ++ "lowered\n" ++ reset);

    var current = declaration;
    while (current != .none) : (current = inspector.outer_declaration(current)) {
        if (lowerer.global_index_of.get(current)) |global_index| {
            try ir_printer.print_global(writer, lowerer, global_index);
            // a global without a constant initial value is computed in `$init`
            if (lowerer.ir.globals.column(.init)[global_index] != .none) return;
        }

        if (try inspector.print_types(current)) return;
        if (try inspector.print_functions(current) > 0) return;

        if (inspector.resolver.decl_pool.get(current, .kind).is_function()) {
            return writer.writeAll(dim ++ "  no code: unused or static only\n" ++ reset);
        }
    }
    _ = try inspector.print_functions(.none);
}

// a list node whose last descendant lies on a later line, a block opened on this line
fn continues_past_line(inspector: Inspector, node: NodeId, line: usize) bool {
    const tree = inspector.resolver.tree;
    const kind = tree.ast_nodes.column(.nk)[node];
    if (Node.nk_childc[@intFromEnum(kind)] != .many) return false;

    var last_descendant = node;
    while (tree.children(last_descendant).len > 0) {
        const children = tree.children(last_descendant);
        const last_child = children[children.len - 1];
        if (last_child == 0 or last_child >= inspector.parent.len) break;
        last_descendant = last_child;
    }
    return inspector.line_of_node(last_descendant) != line;
}

fn is_within(inspector: Inspector, node: NodeId, ancestor: NodeId) bool {
    var current = node;
    while (current != no_node and current != ancestor) current = inspector.parent[current];
    return current == ancestor;
}

fn outer_declaration(inspector: Inspector, declaration: DeclPool.Index) DeclPool.Index {
    const node = inspector.resolver.decl_pool.get(declaration, .node);
    if (node >= inspector.parent.len) return .none;
    if (inspector.parent[node] == no_node) return .none;
    return inspector.enclosing_declaration(inspector.parent[node]);
}

fn is_type_kind(kind: DeclPool.Entry.Kind) bool {
    return kind == .record or kind == .variant or kind == .type_alias;
}

// with the instances of a generic function and the overloads grouped into it
fn print_functions(inspector: Inspector, declaration: DeclPool.Index) !usize {
    // a program that did not resolve was never lowered, there is no ir to show
    const lowerer = inspector.lowerer orelse return 0;
    const head = lowerer.overload_group_head_of.get(declaration) orelse declaration;

    var count: usize = 0;
    const function_declarations = lowerer.ir.functions.column(.decl);
    for (function_declarations, 0..) |function_declaration, function_index| {
        const is_head = function_declaration == head;
        if (!is_head and !inspector.is_instance_of(function_declaration, head)) continue;

        try ir_printer.print_function(inspector.writer, lowerer, function_index);
        count += 1;
    }
    return count;
}

fn is_instance_of(
    inspector: Inspector,
    declaration: DeclPool.Index,
    template: DeclPool.Index,
) bool {
    if (declaration == .none) return false;
    return inspector.resolver.generics.template_of.get(declaration) == template;
}

// with the instances of a generic type
fn print_types(inspector: Inspector, declaration: DeclPool.Index) !bool {
    const resolver = inspector.resolver;
    if (!is_type_kind(resolver.decl_pool.get(declaration, .kind))) return false;
    const lowerer = inspector.lowerer orelse return true;

    const static_values = resolver.decl_pool.entries.column(.static_value);
    for (static_values, 0..) |static_value, i| {
        const candidate: DeclPool.Index = @enumFromInt(i);
        if (static_value == .none) continue;
        const is_wanted = candidate == declaration or
            inspector.is_instance_of(candidate, declaration);
        if (!is_wanted) continue;
        try ir_printer.print_type_definition(inspector.writer, lowerer, static_value);
    }
    return true;
}
