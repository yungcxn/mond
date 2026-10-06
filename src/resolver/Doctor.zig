const std = @import("std");
const StaticPool = @import("StaticPool.zig");
const SoD = @import("../ds/dynbuf.zig").SoD;
const ParseTree = @import("../ParseTree.zig");

pub const Disorder = enum(u16) {
    undefined_name,
    duplicate_declaration,
    unknown_member,
    type_mismatch,
    infinite_type,
    uninferable_type,
    not_a_type,
    not_callable,
    wrong_arity,
    unknown_named_argument,
    no_matching_overload,
    ambiguous_overload,
    invalid_cast,
    runit_mixing,
    declaration_cycle,
    recursive_by_value_type,
    assertsize_failed,
    tag_overflow,
    self_tag_without_niche,
    trait_member_missing,
    trait_signature_mismatch,
    no_deinit,
    not_static,
    static_eval_failed,
    stcwhere_violated,
    redundant_stc,
    genexpr_index,
    generic_member,
    missing_ret,
    redundant_ret,
    redundant_fun,
    unrealized_template,
    impure_stcfun,
    brk_outside_loop,
    cont_outside_loop,
    ret_type_mismatch,
    non_exhaustive_match,
    redundant_match_arm,
    assign_to_immutable,
    write_through_immutable_pointer,
    use_before_initialization,
    destructure_type_conflict,
    missing_main,

    pub const Severity = enum(u8) { note, warning, @"error" };
};

pub const Diagnosis = struct {
    code: Disorder,
    severity: Disorder.Severity,
    node: ParseTree.NodeId,
    a: u32,
    b: u32,
};

diagnostics: SoD(Diagnosis),

const Doctor = @This();

pub fn report(doc: *Doctor, code: Disorder, node: ParseTree.NodeId, a: anytype, b: anytype) void {
    const severity: Disorder.Severity = if (code == .redundant_match_arm) .warning else .@"error";
    doc.diagnostics.push(.{ .code = code, .severity = severity, .node = node, .a = word(a), .b = word(b) });
}

pub fn has(doc: *const Doctor, n: ParseTree.NodeId) bool {
    return std.mem.indexOfScalar(ParseTree.NodeId, doc.diagnostics.sliced_field(.node), n) != null;
}

// whether an error was reported since `mark` inside the subtree of `v`
pub fn errors_since(doc: *const Doctor, tree: *const ParseTree, mark: usize, v: ParseTree.NodeId) bool {
    const d = doc.diagnostics.sliced();
    var s: ?[2]ParseTree.NodeId = null;
    for (d.severity[mark..], d.node[mark..]) |sev, n| if (sev == .@"error") {
        if (s == null) s = tree.subtree(v);
        if (n >= s.?[0] and n < s.?[1]) return true;
    };
    return false;
}

pub fn rewind(doc: *Doctor, mark: u32) void {
    inline for (@typeInfo(Diagnosis).@"struct".fields) |f| @field(doc.diagnostics.pool, f.name).head = mark;
}

fn word(v: anytype) u32 {
    return switch (@typeInfo(@TypeOf(v))) {
        .@"enum" => @intFromEnum(v),
        .enum_literal => @intFromEnum(@as(StaticPool.Index, v)),
        else => @intCast(v),
    };
}
