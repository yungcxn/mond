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
    @memset(parent, no_node);
    for (0..parent.len) |node| {
        for (resolver.tree.children(@intCast(node))) |child| {
            if (child < parent.len) parent[child] = @intCast(node);
        }
    }
    @memset(owner, .none);
    const declarations = resolver.decl_pool.entries.columns();
    for (declarations.node, declarations.kind, 0..) |node, kind, i| {
        const owns_code = kind.is_function() or
            kind == .record or kind == .variant or kind == .type_alias;
        if (owns_code and node < owner.len) owner[node] = @fromBackingInt(@intCast(i));
    }

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
        if (query.len == 0) continue;
        try inspector.writer.print(bold ++ "\n▸ {s}\n" ++ reset, .{query});

        const matched = if (query[0] == ':') blk: {
            const wanted_line = (std.fmt.parseInt(usize, query[1..], 10) catch
                break :blk false) -| 1;

            var last_declaration: ?DeclPool.Index = null;
            for (1..inspector.parent.len) |i| {
                const node: NodeId = @intCast(i);
                // a node whose parent also lies within the line is printed as part of that parent
                if (inspector.line_of_node(node) != wanted_line) continue;
                if (inspector.continues_past_line(node, wanted_line)) continue;
                if (parent[node] != no_node and
                    inspector.line_of_node(parent[node]) == wanted_line and
                    !inspector.continues_past_line(parent[node], wanted_line)) continue;

                try inspector.writer.writeAll(style.function_color ++ "resolved\n" ++ reset);
                try inspector.print_subtree(node);

                const declaration = inspector.enclosing_declaration(node);
                if (declaration != last_declaration) try inspector.print_lowered(declaration);
                last_declaration = declaration;

                // functions declared inside the node (closures) are lowered on their own
                for (inspector.owner, 0..) |owned, owner_node| {
                    if (owned == .none or owned == declaration) continue;
                    if (inspector.enclosing_declaration(@intCast(owner_node)) != owned) continue;
                    var current: NodeId = @intCast(owner_node);
                    while (current != no_node and current != node) {
                        current = inspector.parent[current];
                    }
                    if (current != node) continue;
                    _ = try inspector.print_functions(owned);
                }
            }
            break :blk last_declaration != null;
        } else blk: {
            const wanted_index: ?usize = if (query[0] == '#')
                std.fmt.parseInt(usize, query[1..], 10) catch break :blk false
            else
                null;

            var matched = false;
            for (0..resolver.decl_pool.entries.len()) |i| {
                const declaration: DeclPool.Index = @fromBackingInt(@intCast(i));
                if (wanted_index) |wanted| {
                    if (wanted != i) continue;
                } else {
                    const name = source_positions.declaration_name(resolver, declaration);
                    if (!std.mem.eql(u8, name, query)) continue;
                }
                matched = true;

                try inspector.writer.writeAll(style.function_color ++ "resolved\n" ++ reset);
                try resolver_dump.declaration_row(
                    inspector.writer,
                    resolver,
                    inspector.line_starts,
                    i,
                );
                try inspector.print_subtree(resolver.decl_pool.get(declaration, .node));

                const by_index = wanted_index != null;
                // overloads of equal parameters share one function, printed by name at the last one
                if (by_index or inspector.lowerer == null or
                    !inspector.lowerer.?.next_overload_of.contains(declaration))
                {
                    try inspector.print_lowered(declaration);
                }
            }
            if (matched) break :blk true;
            break :blk std.mem.eql(u8, query, "$init") and try inspector.print_functions(.none) > 0;
        };
        if (!matched) try inspector.writer.writeAll(style.error_color ++ "  no match\n" ++ reset);
    }
    try inspector.writer.flush();
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
    while (current != .none) {
        if (lowerer.global_index_of.get(current)) |global_index| {
            try ir_printer.print_global(writer, lowerer, global_index);
            // a global without a constant initial value is computed in `$init`
            if (lowerer.ir.globals.column(.init)[global_index] != .none) return;
        }

        // with the instances of a generic type
        const resolver = inspector.resolver;
        const kind = resolver.decl_pool.get(current, .kind);
        if (kind == .record or kind == .variant or kind == .type_alias) {
            const static_values = resolver.decl_pool.entries.column(.static_value);
            for (static_values, 0..) |static_value, i| {
                const candidate: DeclPool.Index = @fromBackingInt(@intCast(i));
                if (static_value == .none) continue;
                const is_wanted = candidate == current or (candidate != .none and
                    resolver.generics.template_of.get(candidate) == current);
                if (!is_wanted) continue;
                try ir_printer.print_type_definition(writer, lowerer, static_value);
            }
            return;
        }
        if (try inspector.print_functions(current) > 0) return;

        if (resolver.decl_pool.get(current, .kind).is_function()) {
            return writer.writeAll(dim ++ "  no code: unused or static only\n" ++ reset);
        }

        const node = resolver.decl_pool.get(current, .node);
        current = if (node >= inspector.parent.len or inspector.parent[node] == no_node)
            .none
        else
            inspector.enclosing_declaration(inspector.parent[node]);
    }
    _ = try inspector.print_functions(.none);
}

// a list node whose last descendant lies on a later line, a block opened on this line
fn continues_past_line(inspector: Inspector, node: NodeId, line: usize) bool {
    const tree = inspector.resolver.tree;
    const kind = tree.ast_nodes.column(.nk)[node];
    if (Node.nk_childc[@backingInt(kind)] != .many) return false;

    var last_descendant = node;
    while (tree.children(last_descendant).len > 0) {
        const children = tree.children(last_descendant);
        const last_child = children[children.len - 1];
        if (last_child == 0 or last_child >= inspector.parent.len) break;
        last_descendant = last_child;
    }
    return inspector.line_of_node(last_descendant) != line;
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
        if (!is_head and (function_declaration == .none or
            inspector.resolver.generics.template_of.get(function_declaration) != head)) continue;

        try ir_printer.print_function(inspector.writer, lowerer, function_index);
        count += 1;
    }
    return count;
}
