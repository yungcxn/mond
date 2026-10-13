// the example tests: every file must report exactly its `#!` diagnostics and pass its checks
const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const ParseTree = @import("ParseTree.zig");
const Resolver = @import("Resolver.zig");
const HighLowerer = @import("HighLowerer.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const HighIr = @import("high_lowerer/HighIr.zig");
const Ref = HighIr.Ref;
const debug = @import("debug.zig");

const reset = "\x1b[0m";
const dim = "\x1b[90m";
const green = "\x1b[32m";
const red = "\x1b[1;31m";
const bold = "\x1b[1m";

const Allocator = std.mem.Allocator;
const Writer = std.Io.Writer;

const Finding = struct {
    line: usize,
    code: []const u8,
    message: []const u8 = "",

    fn less_than(_: void, left: Finding, right: Finding) bool {
        if (left.line != right.line) return left.line < right.line;
        return std.mem.order(u8, left.code, right.code) == .lt;
    }
};

const Result = struct { found: []Finding, resolver: ?*Resolver = null };

// `#: name type` checks the type of a declaration, `#= name value` its static value
const Check = struct { line: usize, is_value: bool, name: []const u8, expected: []const u8 };

const InvalidIr = struct { declaration: DeclPool.Index, message: []const u8 };

pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const arguments = try init.minimal.args.toSlice(init.arena.allocator());
    const filters = arguments[1..];

    var buffer: [1 << 16]u8 = undefined;
    var file_writer = std.Io.File.stdout().writerStreaming(io, &buffer);
    const writer = &file_writer.interface;

    const examples = try check_directory(writer, io, "examples", false, filters);
    const positive = try check_directory(writer, io, "examples/positive", false, filters);
    const general_purpose = try check_directory(
        writer,
        io,
        "examples/general-purpose",
        false,
        filters,
    );
    const positive_counts: [2]usize = .{
        examples[0] + positive[0] + general_purpose[0],
        examples[1] + positive[1] + general_purpose[1],
    };
    const negative_counts = try check_directory(writer, io, "examples/negative", true, filters);

    const failed = positive_counts[1] + negative_counts[1];
    const summary_format = bold ++ "\n{s}{d} passed, {d} failed" ++ reset ++
        dim ++ "  ({d} positive, {d} negative files)\n" ++ reset;
    try writer.print(summary_format, .{
        if (failed == 0) green else red,
        positive_counts[0] + negative_counts[0],
        failed,
        positive_counts[0] + positive_counts[1],
        negative_counts[0] + negative_counts[1],
    });
    try writer.flush();

    if (failed > 0) std.process.exit(1);
}

// returns how many files passed and how many failed
fn check_directory(
    writer: *Writer,
    io: std.Io,
    path: []const u8,
    negative: bool,
    filters: []const [:0]const u8,
) ![2]usize {
    var arena = std.heap.ArenaAllocator.init(std.heap.smp_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var directory = try std.Io.Dir.cwd().openDir(io, path, .{ .iterate = true });
    defer directory.close(io);
    const names = try example_names(allocator, io, directory);

    const rule = if (negative)
        "must report exactly the `#!` diagnostics"
    else
        "must resolve without diagnostics";
    try writer.print(bold ++ "\n{s} ({s})\n" ++ reset, .{ path, rule });

    var counts: [2]usize = .{ 0, 0 };
    for (names) |name| {
        if (!matches_filters(name, filters)) continue;
        const passed = try check_file(writer, io, allocator, directory, path, name, negative);
        counts[@intFromBool(!passed)] += 1;
    }
    return counts;
}

// sorted, so the output does not depend on the file system
fn example_names(allocator: Allocator, io: std.Io, directory: std.Io.Dir) ![]const []const u8 {
    var names: std.ArrayList([]const u8) = .empty;
    var iterator = directory.iterate();
    while (try iterator.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".mn")) continue;
        try names.append(allocator, try allocator.dupe(u8, entry.name));
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less_than(_: void, left: []const u8, right: []const u8) bool {
            return std.mem.order(u8, left, right) == .lt;
        }
    }.less_than);
    return names.items;
}

// without filters every file is checked
fn matches_filters(name: []const u8, filters: []const [:0]const u8) bool {
    if (filters.len == 0) return true;
    for (filters) |filter| {
        if (std.mem.indexOf(u8, name, filter) != null) return true;
    }
    return false;
}

fn check_file(
    writer: *Writer,
    io: std.Io,
    allocator: Allocator,
    directory: std.Io.Dir,
    path: []const u8,
    name: []const u8,
    negative: bool,
) !bool {
    const source = try directory.readFileAlloc(io, name, allocator, .limited(50 << 20));
    const expected = try expected_findings(allocator, source);
    const file_path = try std.fs.path.join(allocator, &.{ path, name });
    const result = try run(allocator, io, file_path, source);
    var details: Writer.Allocating = .init(allocator);

    // a negative example without any `#!` would pass without testing anything
    const has_expectations = !negative or expected.len > 0;
    const findings_match = try compare_findings(&details.writer, source, expected, result.found);
    var passed = has_expectations and findings_match;

    const checks = try collect_checks(allocator, source);
    for (checks) |check| {
        const actual = if (result.resolver) |resolver|
            try actual_text(allocator, resolver, check)
        else
            "<not resolved>";
        const same = std.mem.eql(u8, actual, check.expected);
        passed = passed and same;
        try print_check(&details.writer, source, check, actual, same);
    }

    const declaration_count = if (result.resolver) |resolver|
        resolver.decl_pool.entries.len()
    else
        0;
    const file_format = "  {s}{s}" ++ reset ++ " {s}/{s}  " ++
        dim ++ "{d} expected, {d} found, {d} checks, {d} declarations" ++ reset ++ "\n{s}";
    try writer.print(file_format, .{
        if (passed) green else red,
        if (passed) "✓" else "✗",
        path,
        name,
        expected.len,
        result.found.len,
        checks.len,
        declaration_count,
        details.written(),
    });
    return passed;
}

// both lists are sorted, so one merge pass pairs them up
fn compare_findings(
    writer: *Writer,
    source: []const u8,
    expected: []const Finding,
    found: []const Finding,
) !bool {
    var all_match = true;
    var i: usize = 0;
    var j: usize = 0;
    while (i < expected.len or j < found.len) {
        const both_left = i < expected.len and j < found.len;
        const is_match = both_left and
            expected[i].line == found[j].line and
            std.mem.eql(u8, expected[i].code, found[j].code);
        if (is_match) {
            try print_finding(writer, source, green ++ "✓         ", found[j]);
            i += 1;
            j += 1;
            continue;
        }

        all_match = false;
        const expected_comes_first = j >= found.len or
            (i < expected.len and Finding.less_than({}, expected[i], found[j]));
        if (expected_comes_first) {
            try print_finding(writer, source, red ++ "missing   ", expected[i]);
            i += 1;
        } else {
            try print_finding(writer, source, red ++ "unexpected", found[j]);
            j += 1;
        }
    }
    return all_match;
}

fn print_finding(writer: *Writer, source: []const u8, mark: []const u8, finding: Finding) !void {
    const finding_format = "      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++
        "{s}  " ++ dim ++ "{s}" ++ reset ++ "\n";
    try writer.print(finding_format, .{
        mark,
        dim,
        finding.line,
        bold,
        finding.code,
        finding.message,
        source_line(source, finding.line),
    });
}

fn print_check(
    writer: *Writer,
    source: []const u8,
    check: Check,
    actual: []const u8,
    same: bool,
) !void {
    const check_format = "      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++ "{s}";
    try writer.print(check_format, .{
        if (same) green ++ "✓         " else red ++ "wrong     ",
        dim,
        check.line,
        bold,
        check.name,
        actual,
    });
    if (!same) try writer.print(red ++ "  expected " ++ reset ++ "{s}", .{check.expected});
    try writer.print("  " ++ dim ++ "{s}" ++ reset ++ "\n", .{source_line(source, check.line)});
}

// the one-based line holding the byte offset `at`
fn line_at(source: []const u8, at: usize) usize {
    return std.mem.count(u8, source[0..@min(at, source.len)], "\n") + 1;
}

fn node_line(tree: *const ParseTree, source: []const u8, node: ParseTree.NodeId) usize {
    const span = debug.node_span(tree, source, node) orelse return 1;
    return line_at(source, span[0]);
}

// a lexing or parsing error stops the pipeline as the only finding
fn run(allocator: Allocator, io: std.Io, path: []const u8, source: []u8) !Result {
    var findings: std.ArrayList(Finding) = .empty;
    var lexer = Lexer{ .src_bytes = source, .tokens = .init(allocator, 1024) };
    if (lexer.gen_tokens()) |_| {} else |lexing_error| {
        try findings.append(allocator, .{
            .line = line_at(source, lexer.cursor -| 1),
            .code = @errorName(lexing_error),
        });
        return sorted(findings, null);
    }

    const parser = try allocator.create(Parser);
    parser.* = Parser.init(allocator, lexer.tokens, source, lexer.tokens.column(.span));
    if (parser.build_ast()) |_| {} else |parsing_error| {
        const last_token = lexer.tokens.column(.span)[parser.tok_cursor -| 1];
        try findings.append(allocator, .{
            .line = line_at(source, last_token[0]),
            .code = @errorName(parsing_error),
        });
        return sorted(findings, null);
    }

    const resolver = try allocator.create(Resolver);
    resolver.* = Resolver.init(allocator, &parser.tree, source, parser.global_store.items());
    resolver.session.io, resolver.session.path = .{ io, path };
    const resolved = if (resolver.resolve()) |_| true else |_| false;

    if (resolved) try lower_and_verify(allocator, resolver, &parser.tree, source, &findings);
    try collect_diagnostics(allocator, resolver, &parser.tree, source, &findings);
    return sorted(findings, resolver);
}

fn sorted(findings: std.ArrayList(Finding), resolver: ?*Resolver) Result {
    std.mem.sort(Finding, findings.items, {}, Finding.less_than);
    return .{ .found = findings.items, .resolver = resolver };
}

fn lower_and_verify(
    allocator: Allocator,
    resolver: *Resolver,
    tree: *const ParseTree,
    source: []const u8,
    findings: *std.ArrayList(Finding),
) !void {
    const lowerer = try allocator.create(HighLowerer);
    lowerer.* = HighLowerer.init(allocator, resolver);
    lowerer.lower();

    const invalid_ir = try verify(allocator, lowerer) orelse return;
    const line = if (invalid_ir.declaration == .none)
        1
    else
        node_line(tree, source, resolver.decl_pool.get(invalid_ir.declaration, .node));
    try findings.append(allocator, .{
        .line = line,
        .code = "invalid_ir",
        .message = invalid_ir.message,
    });
}

fn collect_diagnostics(
    allocator: Allocator,
    resolver: *Resolver,
    tree: *const ParseTree,
    source: []const u8,
    findings: *std.ArrayList(Finding),
) !void {
    const diagnostics = resolver.doctor.diagnostics.columns();
    for (
        diagnostics.code,
        diagnostics.node,
        diagnostics.first_operand,
        diagnostics.second_operand,
    ) |code, node, first, second| {
        var message: Writer.Allocating = .init(allocator);
        try debug.print_operands(&message.writer, resolver, code, first, second, true);
        try findings.append(allocator, .{
            .line = node_line(tree, source, node),
            .code = @tagName(code),
            .message = message.written(),
        });
    }
}

// the first broken invariant of the lowered ir, null when it is well formed
fn verify(allocator: Allocator, lowerer: *HighLowerer) !?InvalidIr {
    const functions = lowerer.ir.functions.columns();
    for (0..functions.decl.len) |function_index| {
        // an extern function has no blocks to check
        if (functions.blocks[function_index] == 0) continue;
        const invalid_ir = try verify_function(allocator, &lowerer.ir, function_index);
        if (invalid_ir != null) return invalid_ir;
    }
    return null;
}

fn verify_function(allocator: Allocator, ir: *HighIr, function_index: usize) !?InvalidIr {
    const functions = ir.functions.columns();
    const block_count = functions.blocks[function_index];
    const instruction_count = functions.insts[function_index];

    const check: FunctionCheck = .{
        .allocator = allocator,
        .ir = ir,
        .function_index = function_index,
        .declaration = functions.decl[function_index],
        .block_count = block_count,
        .first_block = functions.first_block[function_index],
        .first_instruction = functions.first_inst[function_index],
        .instruction_count = instruction_count,
        .owner = try allocator.alloc(u32, instruction_count),
        .successors = try allocator.alloc(std.ArrayList(u32), block_count),
        .dominators = try allocator.alloc(std.DynamicBitSetUnmanaged, block_count),
    };

    if (try check.verify_blocks()) |invalid_ir| return invalid_ir;
    if (try check.verify_predecessors()) |invalid_ir| return invalid_ir;
    try check.compute_dominators();
    return check.verify_operands();
}

// one function of the ir under verification, block and instruction indices are function-local
const FunctionCheck = struct {
    allocator: Allocator,
    ir: *HighIr,
    function_index: usize,
    declaration: DeclPool.Index,
    block_count: u32,
    first_block: u32,
    first_instruction: u32,
    instruction_count: u32,
    // the block of each instruction
    owner: []u32,
    successors: []std.ArrayList(u32),
    // per block, the blocks dominating it
    dominators: []std.DynamicBitSetUnmanaged,

    const Use = struct { index: usize, op: HighIr.Op, block: u32, predecessors: []const u32 };

    fn invalid(check: FunctionCheck, comptime format: []const u8, arguments: anytype) !?InvalidIr {
        const message = try std.fmt.allocPrint(check.allocator, format, arguments);
        return .{ .declaration = check.declaration, .message = message };
    }

    // blocks must tile the instructions in order, each ending in its only terminator
    fn verify_blocks(check: FunctionCheck) !?InvalidIr {
        const blocks = check.ir.blocks.columns();
        const instructions = check.ir.insts.columns();
        const function_index = check.function_index;

        var next_start: u32 = 0;
        for (0..check.block_count) |block| {
            const start = blocks.start[check.first_block + block];
            const length = blocks.len[check.first_block + block];
            if (start != next_start) {
                return check.invalid("fn #{d} b{d} not contiguous", .{ function_index, block });
            }
            next_start += length;
            if (length == 0) return check.invalid("fn #{d} b{d} empty", .{ function_index, block });

            check.successors[block] = .empty;
            for (start..start + length) |i| {
                check.owner[i] = @intCast(block);
                const instruction_index = check.first_instruction + i;
                const op = instructions.op[instruction_index];

                const is_last = i + 1 == start + length;
                if (op.is_terminator() != is_last) {
                    const misplaced_format = "fn #{d} b{d} terminator misplaced at %{d}";
                    return check.invalid(misplaced_format, .{ function_index, block, i });
                }

                const first_operand = instructions.a[instruction_index];
                const second_operand = instructions.b[instruction_index];
                try check.append_successors(block, op, first_operand, second_operand);
            }

            for (check.successors[block].items) |successor| {
                if (successor >= check.block_count) {
                    const out_of_range_format = "fn #{d} b{d} jumps out of range";
                    return check.invalid(out_of_range_format, .{ function_index, block });
                }
            }
        }

        if (next_start != check.instruction_count) {
            return check.invalid("fn #{d} instruction count mismatch", .{function_index});
        }
        return null;
    }

    fn append_successors(
        check: FunctionCheck,
        block: usize,
        op: HighIr.Op,
        first_operand: u32,
        second_operand: u32,
    ) !void {
        // jump targets are the operands the op table shapes as blocks: new ops need no edit here
        const shape = op.shape();
        const operands = [2]u32{ first_operand, second_operand };
        const successors = &check.successors[block];
        for (shape, operands) |operand_kind, operand| switch (operand_kind) {
            .block => try successors.append(check.allocator, operand),
            .blocks => try successors.appendSlice(check.allocator, check.ir.list(operand)),
            // a case list is the default block, then (value, block) pairs
            .cases => for (check.ir.list(operand), 0..) |entry, i| {
                if (i % 2 == 0) try successors.append(check.allocator, entry);
            },
            .none, .ref, .imm, .refs => {},
        };
    }

    // every jump must be listed once among the predecessors of its target
    fn verify_predecessors(check: FunctionCheck) !?InvalidIr {
        const predecessor_lists = check.ir.blocks.column(.preds);
        for (0..check.block_count) |block| {
            const predecessors = check.ir.list(predecessor_lists[check.first_block + block]);
            for (0..check.block_count) |source_block| {
                var jumps: usize = 0;
                for (check.successors[source_block].items) |successor| {
                    jumps += @intFromBool(successor == block);
                }

                var listed: usize = 0;
                for (predecessors) |predecessor| {
                    listed += @intFromBool(predecessor == source_block);
                }

                if (jumps != listed) {
                    const disagree_format = "fn #{d} b{d} preds disagree with b{d}";
                    const disagree_arguments = .{ check.function_index, block, source_block };
                    return check.invalid(disagree_format, disagree_arguments);
                }
            }
        }
        return null;
    }

    // iterated to a fixed point: a block is dominated by itself and what dominates all predecessors
    fn compute_dominators(check: FunctionCheck) !void {
        for (check.dominators, 0..) |*dominator_set, block| {
            dominator_set.* = try .initFull(check.allocator, check.block_count);
            if (block == 0) {
                dominator_set.unsetAll();
                dominator_set.set(0);
            }
        }

        const predecessor_lists = check.ir.blocks.column(.preds);
        var changed = true;
        while (changed) {
            changed = false;
            for (1..check.block_count) |block| {
                var narrowed = try check.dominators[block].clone(check.allocator);
                const predecessors = check.ir.list(predecessor_lists[check.first_block + block]);
                for (predecessors) |predecessor| {
                    narrowed.setIntersection(check.dominators[predecessor]);
                }
                narrowed.set(block);

                if (!narrowed.eql(check.dominators[block])) {
                    check.dominators[block] = narrowed;
                    changed = true;
                }
            }
        }
    }

    fn verify_operands(check: FunctionCheck) !?InvalidIr {
        const instructions = check.ir.insts.columns();
        const predecessor_lists = check.ir.blocks.column(.preds);

        for (0..check.instruction_count) |i| {
            const instruction_index = check.first_instruction + i;
            const op = instructions.op[instruction_index];
            const block = check.owner[i];
            const predecessors = check.ir.list(predecessor_lists[check.first_block + block]);
            const first_operand = instructions.a[instruction_index];
            const second_operand = instructions.b[instruction_index];

            if (op == .phi and check.ir.list(second_operand).len != predecessors.len) {
                const phi_format = "fn #{d} phi %{d} has {d} operands for {d} preds";
                const operand_count = check.ir.list(second_operand).len;
                const phi_arguments = .{ check.function_index, i, operand_count, predecessors.len };
                return check.invalid(phi_format, phi_arguments);
            }

            const use: Use = .{
                .index = i,
                .op = op,
                .block = block,
                .predecessors = predecessors,
            };
            const shape = op.shape();
            for (shape, [2]u32{ first_operand, second_operand }) |kind, operand| {
                if (try check.verify_operand(use, kind, operand)) |invalid_ir| return invalid_ir;
            }
        }
        return null;
    }

    fn verify_operand(
        check: FunctionCheck,
        use: Use,
        kind: HighIr.Op.Operand,
        operand: u32,
    ) !?InvalidIr {
        const single = [1]u32{operand};
        const items: []const u32 = switch (kind) {
            .ref => &single,
            .refs, .cases => check.ir.list(operand),
            .none, .imm, .block, .blocks => &.{},
        };
        const function_index = check.function_index;

        for (items, 0..) |item, k| {
            const reference: Ref = @enumFromInt(item);
            // a case list alternates blocks and values, only the values are operands
            if ((kind == .cases and k % 2 == 0) or reference == .none) continue;
            if (reference.is_const()) continue;
            if (reference.is_global()) {
                if (reference.index() >= check.ir.globals.len()) {
                    return check.invalid("fn #{d} %{d} bad global", .{ function_index, use.index });
                }
                continue;
            }

            if (kind == .cases) {
                const case_format = "fn #{d} %{d} non-constant case";
                return check.invalid(case_format, .{ function_index, use.index });
            }
            if (item >= check.instruction_count) {
                const range_format = "fn #{d} %{d} uses out of range %{d}";
                return check.invalid(range_format, .{ function_index, use.index, item });
            }
            if (!check.dominates(item, use, k)) {
                const dominance_format = "fn #{d} %{d} uses %{d} not dominating";
                return check.invalid(dominance_format, .{ function_index, use.index, item });
            }
        }
        return null;
    }

    // a phi operand must dominate the end of its predecessor, any other operand the use itself
    fn dominates(check: FunctionCheck, definition: u32, use: Use, operand_position: usize) bool {
        const definition_block = check.owner[definition];
        if (use.op == .phi) {
            const predecessor = use.predecessors[operand_position];
            return check.dominators[predecessor].isSet(definition_block);
        }
        if (definition_block == use.block) return definition < use.index;
        return check.dominators[use.block].isSet(definition_block);
    }
};

// the trimmed text after `marker_text` up to a following comment, null without the marker
fn marker(line: []const u8, marker_text: []const u8) ?[]const u8 {
    const at = std.mem.indexOf(u8, line, marker_text) orelse return null;
    const rest = line[at + marker_text.len ..];
    const comment_start = std.mem.indexOfScalar(u8, rest, '#') orelse rest.len;
    return std.mem.trim(u8, rest[0..comment_start], " \t");
}

fn collect_checks(allocator: Allocator, source: []const u8) ![]Check {
    var checks: std.ArrayList(Check) = .empty;
    var lines = std.mem.splitScalar(u8, source, '\n');
    var line_number: usize = 0;
    while (lines.next()) |line| {
        line_number += 1;
        for ([_][]const u8{ "#:", "#=" }) |marker_text| {
            const content = marker(line, marker_text) orelse continue;
            const name_end = std.mem.indexOfScalar(u8, content, ' ') orelse content.len;
            try checks.append(allocator, .{
                .line = line_number,
                .is_value = marker_text[1] == '=',
                .name = content[0..name_end],
                .expected = std.mem.trim(u8, content[name_end..], " "),
            });
        }
    }
    return checks.items;
}

// the formatted type or static value of the checked declaration
fn actual_text(allocator: Allocator, resolver: *Resolver, check: Check) ![]const u8 {
    const declarations = resolver.decl_pool.entries.columns();
    for (0..declarations.name.len) |i| {
        const name = declarations.name[i];
        if (name == .empty or name == .none) continue;
        if (!std.mem.eql(u8, resolver.name_pool.text_of(name), check.name)) continue;

        const node = declarations.node[i];
        const span = debug.node_span(resolver.tree, resolver.src_bytes, node) orelse continue;
        if (line_at(resolver.src_bytes, span[0]) != check.line) continue;

        var text: Writer.Allocating = .init(allocator);
        const shown = if (check.is_value)
            declarations.static_value[i]
        else
            resolver.static_pool.substitute_type_variables(declarations.value_type[i]);
        try resolver.static_pool.format(&resolver.name_pool, shown, &text.writer);
        return text.written();
    }
    return "<no such declaration on this line>";
}

fn expected_findings(allocator: Allocator, source: []const u8) ![]Finding {
    var findings: std.ArrayList(Finding) = .empty;
    var lines = std.mem.splitScalar(u8, source, '\n');
    var line_number: usize = 0;
    while (lines.next()) |line| {
        line_number += 1;
        const codes_text = marker(line, "#!") orelse continue;
        var codes = std.mem.tokenizeScalar(u8, codes_text, ' ');
        while (codes.next()) |code| {
            try findings.append(allocator, .{ .line = line_number, .code = code });
        }
    }
    std.mem.sort(Finding, findings.items, {}, Finding.less_than);
    return findings.items;
}

// the code of a line without its markers
fn source_line(source: []const u8, line_number: usize) []const u8 {
    var lines = std.mem.splitScalar(u8, source, '\n');
    for (1..line_number) |_| _ = lines.next();
    const line = lines.next() orelse "";
    const comment_start = std.mem.indexOfScalar(u8, line, '#') orelse line.len;
    return std.mem.trim(u8, line[0..comment_start], " \t");
}
