const std = @import("std");
const StaticPool = @import("StaticPool.zig");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const ParseTree = @import("../ParseTree.zig");

// collects what the resolver finds wrong with a program, a report never stops resolving
const Doctor = @This();

pub const Severity = enum(u8) { note, warning, @"error" };

// what a diagnostic operand holds, decides how it is printed
pub const OperandKind = enum { none, name, type, count, declaration };

pub const Operand = struct { label: []const u8 = "", kind: OperandKind = .none };

const no_operand: Operand = .{};

fn operand(comptime kind: OperandKind, comptime label: []const u8) Operand {
    return .{ .label = label, .kind = kind };
}

// one row per diagnostic code: its name, its severity and what its two operands are
// `Disorder` and every lookup below are generated from here, a new diagnostic is one new row
const definition_table = .{
    .{ "undefined_name", .@"error", operand(.name, "name"), no_operand },
    .{
        "duplicate_declaration",
        .@"error",
        operand(.name, "name"),
        operand(.declaration, "first declared as"),
    },
    .{ "unknown_member", .@"error", operand(.name, "member"), operand(.type, "of") },
    .{ "type_mismatch", .@"error", operand(.type, "found"), operand(.type, "expected") },
    .{ "infinite_type", .@"error", operand(.type, "type"), no_operand },
    .{ "uninferable_type", .@"error", operand(.type, "type"), no_operand },
    .{ "not_a_type", .@"error", operand(.type, "type"), no_operand },
    .{ "not_callable", .@"error", operand(.type, "type"), no_operand },
    .{ "invalid_operand", .@"error", operand(.name, "of"), operand(.type, "type") },
    .{ "wrong_arity", .@"error", operand(.count, "arguments"), operand(.count, "parameters") },
    .{ "unknown_named_argument", .@"error", operand(.name, "name"), operand(.type, "of") },
    .{ "no_matching_overload", .@"error", operand(.count, "arguments"), no_operand },
    .{ "ambiguous_overload", .@"error", operand(.declaration, "picked"), no_operand },
    .{ "invalid_cast", .@"error", operand(.type, "found"), operand(.type, "expected") },
    .{ "runit_mixing", .@"error", operand(.type, "found"), operand(.type, "expected") },
    .{ "declaration_cycle", .@"error", operand(.name, "name"), no_operand },
    .{ "recursive_by_value_type", .@"error", operand(.type, "type"), no_operand },
    .{ "assertsize_failed", .@"error", operand(.count, "size"), operand(.count, "asserted") },
    .{ "tag_overflow", .@"error", operand(.type, "tag"), operand(.type, "tag type") },
    .{ "self_tag_without_niche", .@"error", operand(.count, "payload cases"), no_operand },
    .{ "trait_member_missing", .@"error", operand(.name, "member"), operand(.type, "of trait") },
    .{
        "trait_signature_mismatch",
        .@"error",
        operand(.name, "member"),
        operand(.type, "of trait"),
    },
    .{ "no_deinit", .@"error", operand(.type, "type"), no_operand },
    .{ "not_static", .@"error", no_operand, no_operand },
    .{ "static_eval_failed", .@"error", no_operand, no_operand },
    .{ "stcwhere_violated", .@"error", operand(.declaration, "in"), operand(.type, "arguments") },
    .{ "redundant_stc", .@"error", no_operand, no_operand },
    .{ "genexpr_index", .@"error", no_operand, no_operand },
    .{ "generic_member", .@"error", no_operand, no_operand },
    .{ "missing_ret", .@"error", no_operand, no_operand },
    .{ "redundant_ret", .@"error", no_operand, no_operand },
    .{ "redundant_fun", .@"error", no_operand, no_operand },
    .{ "missing_keyword", .@"error", operand(.name, "keyword"), no_operand },
    .{ "unrealized_template", .@"error", no_operand, no_operand },
    .{ "trait_outside_parameter", .@"error", operand(.type, "type"), no_operand },
    .{ "unstorable_dereference", .@"error", operand(.type, "pointer"), no_operand },
    .{ "impure_stcfun", .@"error", no_operand, no_operand },
    .{ "escaping_closure", .@"error", no_operand, no_operand },
    .{ "brk_outside_loop", .@"error", no_operand, no_operand },
    .{ "cont_outside_loop", .@"error", no_operand, no_operand },
    .{ "ret_type_mismatch", .@"error", operand(.type, "found"), operand(.type, "expected") },
    .{ "non_exhaustive_match", .@"error", operand(.type, "type"), no_operand },
    .{ "redundant_match_arm", .warning, no_operand, no_operand },
    .{ "assign_to_immutable", .@"error", no_operand, no_operand },
    .{ "write_through_immutable_pointer", .@"error", no_operand, no_operand },
    .{ "use_before_initialization", .@"error", no_operand, no_operand },
    .{
        "destructure_type_conflict",
        .@"error",
        operand(.type, "found"),
        operand(.type, "expected"),
    },
    .{ "missing_main", .@"error", no_operand, no_operand },
    .{ "invalid_main", .@"error", operand(.type, "type"), no_operand },
    // macros: stray `@`, writes into resolved declarations, includes, endless expansion
    .{ "stray_unquote", .@"error", no_operand, no_operand },
    .{ "frozen_declaration", .@"error", operand(.declaration, "of"), no_operand },
    .{ "crash", .@"error", operand(.name, ""), no_operand },
    .{ "include_failed", .@"error", operand(.name, "file"), operand(.name, "because") },
    .{ "endless_expansion", .@"error", no_operand, no_operand },
};

pub const Disorder = blk: {
    var names: [definition_table.len][]const u8 = undefined;
    var values: [definition_table.len]u16 = undefined;
    for (definition_table, 0..) |row, i| {
        names[i] = row[0];
        values[i] = i;
    }
    break :blk @Enum(u16, .exhaustive, &names, &values);
};

const Definition = struct { severity: Severity, operands: [2]Operand };

const definitions = blk: {
    var table: [definition_table.len]Definition = undefined;
    for (definition_table, 0..) |row, i| {
        table[i] = .{ .severity = row[1], .operands = .{ row[2], row[3] } };
    }
    break :blk table;
};

pub fn severity_of(code: Disorder) Severity {
    return definitions[@intFromEnum(code)].severity;
}

pub fn operands_of(code: Disorder) [2]Operand {
    return definitions[@intFromEnum(code)].operands;
}

// the operands are pool indices, names, declarations or counts, as the code's row says
pub const Diagnosis = struct {
    code: Disorder,
    node: ParseTree.NodeId,
    first_operand: u32,
    second_operand: u32,
    // made by a check that runs once (a signature, a body), a rewind keeps it
    is_settled: bool = false,
};

diagnostics: StructOfArrays(Diagnosis),

pub fn report(
    doctor: *Doctor,
    code: Disorder,
    node: ParseTree.NodeId,
    first: anytype,
    second: anytype,
) void {
    doctor.diagnostics.push(.{
        .code = code,
        .node = node,
        .first_operand = operand_word(first),
        .second_operand = operand_word(second),
    });
}

// warnings are reported but do not stop the program from compiling
pub fn has_errors(doctor: *const Doctor) bool {
    for (doctor.diagnostics.column(.code)) |code| if (severity_of(code) == .@"error") return true;
    return false;
}

pub fn has_report_at(doctor: *const Doctor, node: ParseTree.NodeId) bool {
    return std.mem.indexOfScalar(ParseTree.NodeId, doctor.diagnostics.column(.node), node) != null;
}

// whether an error was reported since `mark` inside the subtree of `root`
pub fn errors_since(
    doctor: *const Doctor,
    tree: *const ParseTree,
    mark: usize,
    root: ParseTree.NodeId,
) bool {
    const reports = doctor.diagnostics.columns();
    // the subtree is only looked up once an error shows up, most calls find none
    var subtree: ?[2]ParseTree.NodeId = null;
    for (reports.code[mark..], reports.node[mark..]) |code, node| {
        if (severity_of(code) != .@"error") continue;

        if (subtree == null) subtree = tree.subtree(root);
        const first_node, const end_node = subtree.?;
        if (node >= first_node and node < end_node) return true;
    }
    return false;
}

// takes back the reports since `mark`, but not the settled ones: the check that made them,
// first run inside an attempt that is taken back, is not run again
pub fn rewind(doctor: *Doctor, mark: u32) void {
    const reports = doctor.diagnostics.columns();
    var kept = mark;
    for (mark..reports.code.len) |i| {
        if (!reports.is_settled[i]) continue;
        inline for (@typeInfo(Diagnosis).@"struct".fields) |field| {
            @field(reports, field.name)[kept] = @field(reports, field.name)[i];
        }
        kept += 1;
    }
    doctor.diagnostics.truncate(kept);
}

// the reports since `mark` come from a check that runs once
pub fn settle(doctor: *Doctor, mark: u32) void {
    for (doctor.diagnostics.column(.is_settled)[mark..]) |*is_settled| is_settled.* = true;
}

fn operand_word(value: anytype) u32 {
    return switch (@typeInfo(@TypeOf(value))) {
        .@"enum" => @intFromEnum(value),
        .enum_literal => @intFromEnum(@as(StaticPool.Index, value)),
        else => @intCast(value),
    };
}
