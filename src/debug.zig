// debug output of every stage, the printers themselves live in debug/
const std = @import("std");
const ParseTree = @import("ParseTree.zig");
const Res = @import("Resolver.zig");
const Low = @import("HighLowerer.zig");
const TreePrinter = @import("debug/TreePrinter.zig");
const resolver_dump = @import("debug/resolver_dump.zig");
const ir_printer = @import("debug/ir_printer.zig");
const diagnostics = @import("debug/diagnostics.zig");
const NodeId = ParseTree.NodeId;

pub const Inspector = @import("debug/Inspector.zig");
pub const CodePrinter = @import("debug/CodePrinter.zig");
pub const print_operands = @import("debug/operands.zig").print_operands;
pub const node_span = @import("debug/source.zig").node_span;

pub const Parser = struct {
    pub fn print_tree(
        io: std.Io,
        tree: *ParseTree,
        source: []const u8,
        roots: []const NodeId,
    ) !void {
        return TreePrinter.print(io, tree, source, roots, null);
    }
};

pub const Resolver = struct {
    // the program as code, as the last macro pass left it, with readable names (see `CodePrinter`)
    pub fn print_code(io: std.Io, resolver: *Res) !void {
        const allocator = std.heap.smp_allocator;
        var code: std.ArrayList(u8) = .empty;
        defer code.deinit(allocator);
        var printer: CodePrinter = .{
            .out = &code,
            .allocator = allocator,
            .tree = resolver.tree,
            .source = resolver.src_bytes,
        };
        for (resolver.roots) |root| try printer.note_names(root);
        try printer.statements(resolver.roots);
        try std.Io.File.stdout().writeStreamingAll(io, code.items);
    }

    pub fn print_tree(io: std.Io, resolver: *Res) !void {
        return TreePrinter.print(io, resolver.tree, resolver.src_bytes, resolver.roots, resolver);
    }

    pub fn print(io: std.Io, resolver: *Res) !void {
        return resolver_dump.print(io, resolver);
    }

    pub fn print_diagnostics(io: std.Io, resolver: *Res, path: []const u8) !void {
        return diagnostics.print(io, resolver, path);
    }
};

pub const HighLowerer = struct {
    pub fn print(io: std.Io, lowerer: *Low) !void {
        return ir_printer.print(io, lowerer);
    }
};
