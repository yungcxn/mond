// source positions and names of nodes and declarations, shared by the debug printers
const std = @import("std");
const Lexer = @import("../Lexer.zig");
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const DeclPool = @import("../resolver/DeclPool.zig");
const DynamicBuffer = @import("../containers.zig").DynamicBuffer;
const Node = ParseTree.Node;
const NodeId = ParseTree.NodeId;

pub fn declaration_name(resolver: *Resolver, declaration: DeclPool.Index) []const u8 {
    const name = resolver.decl_pool.get(declaration, .name);
    if (name == .empty or name == .none) return "<anon>";
    return resolver.name_pool.text_of(name);
}

// the byte offset where each line starts, the first line starts at 0
pub fn line_starts(resolver: *Resolver) DynamicBuffer(u32) {
    var starts: DynamicBuffer(u32) = .init(resolver.allocator, 1024);
    starts.push(0);
    for (resolver.src_bytes, 0..) |character, i| {
        if (character == '\n') starts.push(@intCast(i + 1));
    }
    return starts;
}

// the zero-based line holding the byte offset `at`
pub fn line_of(starts: []const u32, at: u32) usize {
    var low: usize = 0;
    var high: usize = starts.len;
    while (high - low > 1) {
        const middle = (low + high) / 2;
        if (starts[middle] <= at) low = middle else high = middle;
    }
    return low;
}

// the byte offset just past the line, without its newline
pub fn line_end(starts: []const u32, line: usize, source_length: usize) u32 {
    if (line + 1 < starts.len) return starts[line + 1] - 1;
    return @intCast(source_length);
}

pub fn node_span(tree: *const ParseTree, source: []const u8, node: NodeId) ?Lexer.TextSpan {
    const kinds = tree.ast_nodes.column(.nk);
    const arguments = tree.ast_nodes.column(.args);
    const spans = tree.span_store;

    var current = node;
    while (child_count_of(kinds[current]) != .data) {
        // 0 when the node has no children
        const child: NodeId = blk: {
            const slots: [2]NodeId = arguments[current];
            if (child_count_of(kinds[current]) != .many) break :blk slots[0];

            const child_count = slots[1];
            if (child_count == 0) break :blk 0;
            break :blk tree.extra_childrefs.buffer[slots[0]];
        };
        if (child == 0 or child >= tree.ast_nodes.len()) break;
        current = child;
    } else return spans[arguments[current][0]];

    // a childless node (`brk`, `true`) has no token, its keyword is searched after the last token
    var token: u32 = 0;
    var preceding = current;
    while (preceding > 0) : (preceding -= 1) {
        if (child_count_of(kinds[preceding]) == .data) {
            token = arguments[preceding][0];
            break;
        }
    }

    const kind = kinds[current];
    // the source text of a childless node, null when it is not written as one word
    const keyword = switch (kind) {
        .brk => "brk",
        .cont => "cont",
        .ret_void => "ret",
        .boolean_true => "true",
        .boolean_false => "false",
        .identifier_self => @tagName(kind)["identifier_".len..],
        else => blk: {
            const is_builtin_type = @intFromEnum(kind) >= @intFromEnum(Node.Kind.type_u8) and
                @intFromEnum(kind) <= @intFromEnum(Node.Kind.type_stcfun);
            if (is_builtin_type) break :blk @tagName(kind)["type_".len..];
            break :blk null;
        },
    } orelse return if (spans.len == 0) null else spans[token];

    // the node is the rank-th of its kind after that token, so it is the rank-th such keyword
    var rank: usize = 0;
    for (preceding + 1..current + 1) |later| rank += @intFromBool(kinds[later] == kind);

    // searched to the end: the keyword may stand far behind the last token (a long run of `brk`s)
    for (spans[token..]) |span| {
        if (!std.mem.eql(u8, source[span[0]..span[1]], keyword)) continue;
        rank -= 1;
        if (rank == 0) return span;
    }
    if (spans.len == 0) return null;
    return spans[token];
}

fn child_count_of(kind: Node.Kind) @TypeOf(Node.nk_childc[0]) {
    return Node.nk_childc[@intFromEnum(kind)];
}
