const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const ParseTree = @import("../../ParseTree.zig");
const Index = StaticPool.Index;
const Writer = std.Io.Writer;

// types and values written the way a program spells them

pub fn format(
    pool: *const StaticPool,
    names: *const NamePool,
    index: Index,
    writer: *Writer,
) !void {
    return write_entry(pool, names, index, writer, 0);
}

// `depth` counts the records entered, a nominal type inside one prints by its declaration
fn write_entry(
    pool: *const StaticPool,
    names: *const NamePool,
    index: Index,
    writer: *Writer,
    depth: u8,
) Writer.Error!void {
    if (index == .none) return writer.writeAll("none");
    // nominal types can contain themselves
    if (depth > 0 and pool.properties(index).is_nominal) {
        const declaration = switch (pool.get(index)) {
            .record_type => |record| record.declaration,
            .variant_type => |variant| variant.declaration,
            .trait_type => |trait| trait.declaration,
            else => unreachable,
        };
        return writer.print("type#{d}", .{@intFromEnum(declaration)});
    }
    switch (pool.get(index)) {
        .int_type => |int_type| {
            const sign: u8 = if (int_type.signedness == .signed) 'i' else 'u';
            try writer.print("{c}{d}", .{ sign, int_type.bits });
        },
        .float_type => |float_type| try writer.print("f{d}", .{float_type.bits}),
        .simple_type => |simple| {
            try writer.writeAll(if (simple == .unit) "()" else @tagName(simple));
        },
        .meta_type => |meta| try writer.writeAll(@tagName(meta)),
        .array_type => |array| {
            try writer.writeAll("[");
            // a length inferred already is shown, an open or a runtime one is not
            const length = if (pool.tag(array.length) == .type_variable) blk: {
                const variable = pool.get(array.length).type_variable;
                const root = pool.type_variables.root_of_const(variable);
                break :blk pool.type_variables.binding_of_const(root);
            } else array.length;
            const is_known = length != .none and pool.tag(length) == .int_value;
            if (is_known) try write_entry(pool, names, length, writer, depth);
            try writer.writeAll("]");
            try write_entry(pool, names, array.element, writer, depth);
        },
        .pointer_type => |pointer| {
            try writer.writeAll(if (pointer.is_mutable) "*" else "&");
            try write_entry(pool, names, pointer.pointee, writer, depth);
        },
        .function_type => |function| {
            if (function.category == .inlined) try writer.writeAll("inlfun ");
            try writer.writeAll("(");
            try write_list(pool, names, function.parameters, ", ", writer, depth);
            try writer.writeAll(") -> ");
            try write_entry(pool, names, function.return_type, writer, depth);
        },
        .record_type => |record| {
            try writer.writeAll(if (record.is_packed) "**(" else "*(");
            for (record.field_types, record.field_names, 0..) |field_type, field_name, i| {
                if (i > 0) try writer.writeAll(", ");
                try write_entry(pool, names, field_type, writer, depth + 1);
                try writer.print(" {s}", .{names.text_of(field_name)});
            }
            try writer.writeAll(")");
        },
        .variant_type => |variant| {
            try writer.writeAll(if (variant.is_unionsized) "++(" else "+(");
            for (variant.cases, 0..) |case, i| {
                const separator = if (i > 0) ", " else "";
                const case_name = names.text_of(pool.get(case).variant_case_type.name);
                try writer.print("{s}{s}", .{ separator, case_name });
            }
            try writer.writeAll(")");
        },
        .variant_case_type => |case| {
            try write_entry(pool, names, case.variant, writer, depth);
            try writer.print(".{s}", .{names.text_of(case.name)});
        },
        .variant_union_type => |members| {
            try write_list(pool, names, members, " || ", writer, depth);
        },
        .trait_type => |trait| {
            try writer.writeAll("!{");
            for (trait.member_names, 0..) |member_name, i| {
                const separator = if (i > 0) "; " else "";
                try writer.print("{s}{s}", .{ separator, names.text_of(member_name) });
            }
            try writer.writeAll("}");
        },
        .static_function => |function| {
            try writer.print("stcfun#{d}", .{@intFromEnum(function.declaration)});
        },
        .template_type => |declaration| {
            try writer.print("abstract#{d}", .{@intFromEnum(declaration)});
        },
        .type_variable => |variable| {
            const root = pool.type_variables.root_of_const(variable);
            const binding = pool.type_variables.binding_of_const(root);
            if (binding != .none) return write_entry(pool, names, binding, writer, depth);
            try writer.print("?{d}", .{@intFromEnum(root) + 1});
        },
        .int_value => |int_value| {
            const value_type = pool.get(int_value.value_type);
            const signed = value_type == .int_type and value_type.int_type.signedness == .signed;
            if (signed) {
                try writer.print("{d}", .{@as(i64, @bitCast(int_value.bits))});
            } else try writer.print("{d}", .{int_value.bits});
        },
        .float_value => |float_value| try writer.print("{d}", .{float_value.value}),
        .simple_value => |simple| try writer.writeAll(switch (simple) {
            .bool_true => "true",
            .bool_false => "false",
            .unit => "()",
        }),
        .string_value => |bytes| try writer.print("\"{s}\"", .{bytes}),
        .aggregate_value => |aggregate| {
            try writer.writeAll("[");
            try write_list(pool, names, aggregate.elements, ", ", writer, depth);
            try writer.writeAll("]");
        },
        .variant_value => |variant_value| {
            try write_entry(pool, names, variant_value.case, writer, depth);
            if (variant_value.payload != .none) {
                try write_entry(pool, names, variant_value.payload, writer, depth);
            }
        },
        .function_value => |declaration| try writer.print("fun#{d}", .{@intFromEnum(declaration)}),
        .ast_type => |ast| {
            try writer.writeAll("ast");
            if (ast.produces != .none) {
                try writer.writeAll("(");
                try write_entry(pool, names, ast.produces, writer, depth);
                try writer.writeAll(")");
            }
            if (ast.root_kind != 0) {
                try writer.print(".{s}", .{ParseTree.Node.case_names[ast.root_kind - 1]});
            }
        },
        .tree_value => |tree| try writer.print("tree#{d}", .{tree.node}),
    }
}

fn write_list(
    pool: *const StaticPool,
    names: *const NamePool,
    items: []const Index,
    separator: []const u8,
    writer: *Writer,
    depth: u8,
) Writer.Error!void {
    for (items, 0..) |item, i| {
        if (i > 0) try writer.writeAll(separator);
        try write_entry(pool, names, item, writer, depth);
    }
}
