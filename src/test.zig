// the example tests: every file must report exactly its `#!` diagnostics and pass its checks
const std = @import("std");
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const Resolver = @import("Resolver.zig");
const HighLowerer = @import("HighLowerer.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const HighIr = @import("high_lowerer/HighIr.zig");
const ParseTree = @import("ParseTree.zig");
const Doctor = @import("resolver/Doctor.zig");
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

    // every file of every directory is a task on the cores of the machine, reported in order
    var group: std.Io.Group = .init;
    const process_arena = init.arena.allocator();
    // the negative examples start first, the evaluation budget tests among them run longest
    const queued = [_]Directory{
        try queue_directory(process_arena, io, &group, "examples/negative", true, filters),
        try queue_directory(process_arena, io, &group, "examples", false, filters),
        try queue_directory(process_arena, io, &group, "examples/positive", false, filters),
        try queue_directory(process_arena, io, &group, "examples/general-purpose", false, filters),
        // the docs show the language as it is: their code is checked like the examples
        try queue_directory(process_arena, io, &group, "docs", false, filters),
    };
    try group.await(io);

    const examples = try report_directory(writer, queued[1]);
    const positive = try report_directory(writer, queued[2]);
    const general_purpose = try report_directory(writer, queued[3]);
    const positive_counts: [2]usize = .{
        examples[0] + positive[0] + general_purpose[0],
        examples[1] + positive[1] + general_purpose[1],
    };
    const negative_counts = try report_directory(writer, queued[0]);
    const docs = try report_directory(writer, queued[4]);

    // and they name every keyword, tree kind and diagnostic, so no feature goes undocumented
    const unnamed = blk: {
        if (filters.len > 0) break :blk 0;
        var arena = std.heap.ArenaAllocator.init(std.heap.smp_allocator);
        defer arena.deinit();
        const allocator = arena.allocator();
        var text: std.ArrayList(u8) = .empty;
        var directory = try std.Io.Dir.cwd().openDir(io, "docs", .{ .iterate = true });
        defer directory.close(io);
        var iterator = directory.iterate();
        while (try iterator.next(io)) |entry| {
            if (entry.kind != .file or !std.mem.endsWith(u8, entry.name, ".md")) continue;
            const limit: std.Io.Limit = .limited(50 << 20);
            const page = try directory.readFileAlloc(io, entry.name, allocator, limit);
            try text.appendSlice(allocator, page);
        }

        var names: std.ArrayList([]const u8) = .empty;
        for (std.meta.fieldNames(Lexer.Token.Kind)) |name| {
            if (std.mem.startsWith(u8, name, "kw_")) try names.append(allocator, name["kw_".len..]);
        }
        for (ParseTree.Node.case_names) |name| try names.append(allocator, name);
        for (std.meta.fieldNames(Doctor.Disorder)) |name| try names.append(allocator, name);

        const rule = "\ndocs (must name every keyword, tree kind and diagnostic)\n";
        try writer.print(bold ++ rule ++ reset, .{});
        var count: usize = 0;
        for (names.items) |name| {
            const quoted = try std.fmt.allocPrint(allocator, "`{s}`", .{name});
            if (std.mem.indexOf(u8, text.items, quoted) != null) continue;
            try writer.print("  " ++ red ++ "✗" ++ reset ++ " {s} is not in docs/\n", .{name});
            count += 1;
        }
        break :blk count;
    };

    const failed = positive_counts[1] + negative_counts[1] + docs[1] + unnamed;
    const summary_format = bold ++ "\n{s}{d} passed, {d} failed" ++ reset ++
        dim ++ "  ({d} positive, {d} negative files, {d} doc examples)\n" ++ reset;
    try writer.print(summary_format, .{
        if (failed == 0) green else red,
        positive_counts[0] + negative_counts[0] + docs[0],
        failed,
        positive_counts[0] + positive_counts[1],
        negative_counts[0] + negative_counts[1],
        docs[0] + docs[1],
    });
    try writer.flush();

    if (failed > 0) std.process.exit(1);
}

// the files of a directory (or blocks of its docs), each checked by a task of `group`
const Directory = struct { path: []const u8, negative: bool, jobs: []Job };

fn queue_directory(
    allocator: Allocator,
    io: std.Io,
    group: *std.Io.Group,
    path: []const u8,
    negative: bool,
    filters: []const [:0]const u8,
) !Directory {
    var directory = try std.Io.Dir.cwd().openDir(io, path, .{ .iterate = true });
    defer directory.close(io);
    // sorted, so the output does not depend on the file system
    var names: std.ArrayList([]const u8) = .empty;
    var iterator = directory.iterate();
    while (try iterator.next(io)) |entry| {
        const is_checked = std.mem.endsWith(u8, entry.name, ".mn") or
            std.mem.endsWith(u8, entry.name, ".md");
        if (entry.kind != .file or !is_checked) continue;
        try names.append(allocator, try allocator.dupe(u8, entry.name));
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less_than(_: void, left: []const u8, right: []const u8) bool {
            return std.mem.order(u8, left, right) == .lt;
        }
    }.less_than);

    var jobs: std.ArrayList(Job) = .empty;
    for (names.items) |name| {
        // without filters every file is checked
        const matches_filters = blk: {
            if (filters.len == 0) break :blk true;
            for (filters) |filter| {
                if (std.mem.indexOf(u8, name, filter) != null) break :blk true;
            }
            break :blk false;
        };
        if (!matches_filters) continue;

        const source = try directory.readFileAlloc(io, name, allocator, .limited(50 << 20));
        if (!std.mem.endsWith(u8, name, ".md")) {
            try jobs.append(allocator, .{ .label = name, .source = source });
            continue;
        }

        // a doc checks each of its ```mond blocks as a file, with an empty `main` when it has none
        var lines = std.mem.splitScalar(u8, source, '\n');
        var line_number: usize = 0;
        var block: ?std.ArrayList(u8) = null;
        var block_line: usize = 0;
        while (lines.next()) |line| {
            line_number += 1;
            if (block == null) {
                if (std.mem.eql(u8, std.mem.trimEnd(u8, line, " "), "```mond")) {
                    block = .empty;
                    block_line = line_number + 1;
                }
                continue;
            }
            if (!std.mem.startsWith(u8, line, "```")) {
                try block.?.appendSlice(allocator, line);
                try block.?.append(allocator, '\n');
                continue;
            }
            if (std.mem.indexOf(u8, block.?.items, "main = (") == null) {
                try block.?.appendSlice(allocator, "main = () {}\n");
            }
            const label = try std.fmt.allocPrint(allocator, "{s}:{d}", .{ name, block_line });
            try jobs.append(allocator, .{ .label = label, .source = block.?.items });
            block = null;
        }
    }

    for (jobs.items) |*job| group.async(io, Job.run, .{ job, io, path, negative });
    return .{ .path = path, .negative = negative, .jobs = jobs.items };
}

// prints what the tasks of a directory reported, returns how many files passed and how many failed
fn report_directory(writer: *Writer, directory: Directory) ![2]usize {
    const rule = if (directory.negative)
        "must report exactly the `#!` diagnostics"
    else
        "must resolve without diagnostics";
    try writer.print(bold ++ "\n{s} ({s})\n" ++ reset, .{ directory.path, rule });
    var counts: [2]usize = .{ 0, 0 };
    for (directory.jobs) |job| {
        try writer.writeAll(job.output);
        std.heap.smp_allocator.free(job.output);
        counts[@intFromBool(!job.passed)] += 1;
    }
    return counts;
}

// a file or doc block checked as a task of its own, keeping only what it reports
const Job = struct {
    label: []const u8,
    source: []u8,
    output: []const u8 = "",
    passed: bool = false,

    fn run(job: *Job, io: std.Io, path: []const u8, negative: bool) void {
        var arena = std.heap.ArenaAllocator.init(std.heap.smp_allocator);
        defer arena.deinit();
        const allocator = arena.allocator();
        var output: Writer.Allocating = .init(allocator);
        const writer = &output.writer;
        const checked = check_source(writer, allocator, io, path, job.label, job.source, negative);
        job.passed = checked catch |failure| blk: {
            const failed_format = "  " ++ red ++ "✗" ++ reset ++ " {s}/{s}  {s}\n";
            writer.print(failed_format, .{ path, job.label, @errorName(failure) }) catch {};
            break :blk false;
        };
        job.output = std.heap.smp_allocator.dupe(u8, output.written()) catch "";
    }
};

// whether `source` reports exactly its `#!` diagnostics and passes its checks, shown as `path/name`
fn check_source(
    writer: *Writer,
    allocator: Allocator,
    io: std.Io,
    path: []const u8,
    name: []const u8,
    source: []u8,
    negative: bool,
) !bool {
    const expected = blk: {
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
        break :blk findings.items;
    };
    const file_path = try std.fs.path.join(allocator, &.{ path, name });
    const result = try run(allocator, io, file_path, source);
    var details: Writer.Allocating = .init(allocator);

    // a negative example without any `#!` would pass without testing anything
    const has_expectations = !negative or expected.len > 0;
    // both lists are sorted, so one merge pass pairs them up
    const findings_match = blk: {
        const found = result.found;
        var all_match = true;
        var i: usize = 0;
        var j: usize = 0;
        while (i < expected.len or j < found.len) {
            const both_left = i < expected.len and j < found.len;
            const is_match = both_left and
                expected[i].line == found[j].line and
                std.mem.eql(u8, expected[i].code, found[j].code);
            if (is_match) {
                try print_finding(&details.writer, source, green ++ "✓         ", found[j]);
                i += 1;
                j += 1;
                continue;
            }

            all_match = false;
            const expected_comes_first = j >= found.len or
                (i < expected.len and Finding.less_than({}, expected[i], found[j]));
            if (expected_comes_first) {
                try print_finding(&details.writer, source, red ++ "missing   ", expected[i]);
                i += 1;
            } else {
                try print_finding(&details.writer, source, red ++ "unexpected", found[j]);
                j += 1;
            }
        }
        break :blk all_match;
    };
    var passed = has_expectations and findings_match;

    const checks = blk: {
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
        break :blk checks.items;
    };
    for (checks) |check| {
        const actual = if (result.resolver) |resolver|
            try actual_text(allocator, resolver, check)
        else
            "<not resolved>";
        const same = std.mem.eql(u8, actual, check.expected);
        passed = passed and same;

        const check_format = "      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++ "{s}";
        try details.writer.print(check_format, .{
            if (same) green ++ "✓         " else red ++ "wrong     ",
            dim,
            check.line,
            bold,
            check.name,
            actual,
        });
        if (!same) {
            try details.writer.print(red ++ "  expected " ++ reset ++ "{s}", .{check.expected});
        }
        // the code of a line without its markers
        var lines = std.mem.splitScalar(u8, source, '\n');
        for (1..check.line) |_| _ = lines.next();
        const line = lines.next() orelse "";
        const comment_start = std.mem.indexOfScalar(u8, line, '#') orelse line.len;
        const source_line = std.mem.trim(u8, line[0..comment_start], " \t");
        try details.writer.print("  " ++ dim ++ "{s}" ++ reset ++ "\n", .{source_line});
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

fn print_finding(writer: *Writer, source: []const u8, mark: []const u8, finding: Finding) !void {
    const finding_format = "      {s} {s}:{d:<4}" ++ reset ++ " {s}{s:<30}" ++ reset ++
        "{s}  " ++ dim ++ "{s}" ++ reset ++ "\n";
    // the code of a line without its markers
    var lines = std.mem.splitScalar(u8, source, '\n');
    for (1..finding.line) |_| _ = lines.next();
    const line = lines.next() orelse "";
    const comment_start = std.mem.indexOfScalar(u8, line, '#') orelse line.len;
    try writer.print(finding_format, .{
        mark,
        dim,
        finding.line,
        bold,
        finding.code,
        finding.message,
        std.mem.trim(u8, line[0..comment_start], " \t"),
    });
}

// the one-based line holding the byte offset `at`
fn line_at(source: []const u8, at: usize) usize {
    return std.mem.count(u8, source[0..@min(at, source.len)], "\n") + 1;
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

    if (resolved) {
        const lowerer = try allocator.create(HighLowerer);
        lowerer.* = HighLowerer.init(allocator, resolver);
        lowerer.lower();

        if (try verify(allocator, lowerer)) |invalid_ir| {
            const line = if (invalid_ir.declaration == .none) 1 else blk: {
                const node = resolver.decl_pool.get(invalid_ir.declaration, .node);
                const span = debug.node_span(&parser.tree, source, node) orelse break :blk 1;
                break :blk line_at(source, span[0]);
            };
            try findings.append(allocator, .{
                .line = line,
                .code = "invalid_ir",
                .message = invalid_ir.message,
            });
        }
    }

    const diagnostics = resolver.doctor.diagnostics.columns();
    for (
        diagnostics.code,
        diagnostics.node,
        diagnostics.first_operand,
        diagnostics.second_operand,
    ) |code, node, first, second| {
        var message: Writer.Allocating = .init(allocator);
        try debug.print_operands(&message.writer, resolver, code, first, second, true);
        const line = if (debug.node_span(&parser.tree, source, node)) |span|
            line_at(source, span[0])
        else
            1;
        try findings.append(allocator, .{
            .line = line,
            .code = @tagName(code),
            .message = message.written(),
        });
    }
    return sorted(findings, resolver);
}

fn sorted(findings: std.ArrayList(Finding), resolver: ?*Resolver) Result {
    std.mem.sort(Finding, findings.items, {}, Finding.less_than);
    return .{ .found = findings.items, .resolver = resolver };
}

// the first broken invariant of the lowered ir, null when it is well formed
fn verify(allocator: Allocator, lowerer: *HighLowerer) !?InvalidIr {
    const functions = lowerer.ir.functions.columns();
    for (0..functions.decl.len) |function_index| {
        // an extern function has no blocks to check
        if (functions.blocks[function_index] == 0) continue;
        const block_count = functions.blocks[function_index];
        const instruction_count = functions.insts[function_index];

        const check: FunctionCheck = .{
            .allocator = allocator,
            .ir = &lowerer.ir,
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

        // blocks must tile the instructions in order, each ending in its only terminator
        const blocks = check.ir.blocks.columns();
        const instructions = check.ir.insts.columns();

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

        // every jump must be listed once among the predecessors of its target
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

        // iterated to a fixed point: dominated by itself and what dominates all predecessors
        for (check.dominators, 0..) |*dominator_set, block| {
            dominator_set.* = try .initFull(check.allocator, check.block_count);
            if (block == 0) {
                dominator_set.unsetAll();
                dominator_set.set(0);
            }
        }

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

            const use: FunctionCheck.Use = .{
                .index = i,
                .op = op,
                .block = block,
                .predecessors = predecessors,
            };
            const shape = op.shape();
            for (shape, [2]u32{ first_operand, second_operand }) |kind, operand| {
                const single = [1]u32{operand};
                const items: []const u32 = switch (kind) {
                    .ref => &single,
                    .refs, .cases => check.ir.list(operand),
                    .none, .imm, .block, .blocks => &.{},
                };

                for (items, 0..) |item, k| {
                    const reference: Ref = @enumFromInt(item);
                    // a case list alternates blocks and values, only the values are operands
                    if ((kind == .cases and k % 2 == 0) or reference == .none) continue;
                    if (reference.is_const()) continue;
                    if (reference.is_global()) {
                        if (reference.index() >= check.ir.globals.len()) {
                            return check.invalid(
                                "fn #{d} %{d} bad global",
                                .{ function_index, use.index },
                            );
                        }
                        continue;
                    }

                    if (kind == .cases) {
                        const case_format = "fn #{d} %{d} non-constant case";
                        return check.invalid(case_format, .{ function_index, use.index });
                    }
                    if (item >= check.instruction_count) {
                        const range_format = "fn #{d} %{d} uses out of range %{d}";
                        return check.invalid(
                            range_format,
                            .{ function_index, use.index, item },
                        );
                    }
                    // a phi operand must dominate the end of its predecessor, others the use itself
                    const definition_block = check.owner[item];
                    const dominated = if (use.op == .phi)
                        check.dominators[use.predecessors[k]].isSet(definition_block)
                    else if (definition_block == use.block)
                        item < use.index
                    else
                        check.dominators[use.block].isSet(definition_block);
                    if (!dominated) {
                        const dominance_format = "fn #{d} %{d} uses %{d} not dominating";
                        return check.invalid(
                            dominance_format,
                            .{ function_index, use.index, item },
                        );
                    }
                }
            }
        }
    }
    return null;
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
};

// the trimmed text after `marker_text` up to a following comment, null without the marker
fn marker(line: []const u8, marker_text: []const u8) ?[]const u8 {
    const at = std.mem.indexOf(u8, line, marker_text) orelse return null;
    const rest = line[at + marker_text.len ..];
    const comment_start = std.mem.indexOfScalar(u8, rest, '#') orelse rest.len;
    return std.mem.trim(u8, rest[0..comment_start], " \t");
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
