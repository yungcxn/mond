// debug output of every stage, the printers themselves live in debug/
const std = @import("std");
const ParseTree = @import("ParseTree.zig");
const Res = @import("Resolver.zig");
const Low = @import("HighLowerer.zig");
const TreePrinter = @import("debug/TreePrinter.zig");
const resolver_dump = @import("debug/resolver_dump.zig");
const ir_printer = @import("debug/ir_printer.zig");
const NodeId = ParseTree.NodeId;

pub const Inspector = @import("debug/Inspector.zig");
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
    pub fn print_tree(io: std.Io, resolver: *Res) !void {
        return TreePrinter.print(io, resolver.tree, resolver.src_bytes, resolver.roots, resolver);
    }

    pub fn print(io: std.Io, resolver: *Res) !void {
        return resolver_dump.print(io, resolver);
    }
};

pub const HighLowerer = struct {
    pub fn print(io: std.Io, lowerer: *Low) !void {
        return ir_printer.print(io, lowerer);
    }
};
