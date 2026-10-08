const std = @import("std");
const Analysis = @import("Analysis.zig");

// the language server: json-rpc on stdin and stdout. documents are analyzed by a worker, a child process
// running the compiler, so a compiler crash costs that analysis but never the server

const Server = @This();

io: std.Io,
gpa: std.mem.Allocator,
// this executable, it is its own worker
exe: []const u8,
out: *std.Io.Writer,
// uri -> its document
docs: std.StringHashMapUnmanaged(Doc) = .empty,
// the lifecycle: requests come after `initialize`, after `shutdown` only `exit`
phase: enum { new, running, shut } = .new,

// `text` waits for its analysis, `result` is the last one and lives in `arena`
const Doc = struct { text: ?[]u8 = null, result: Analysis.Result = .{}, arena: std.heap.ArenaAllocator.State = .{} };

const Method = enum {
    initialize,
    shutdown,
    exit,
    @"textDocument/didOpen",
    @"textDocument/didChange",
    @"textDocument/didClose",
    @"textDocument/semanticTokens/full",
    @"textDocument/definition",
    @"textDocument/references",
    @"textDocument/documentSymbol",
    @"textDocument/hover",
};

const Message = struct {
    id: ?std.json.Value = null,
    method: []const u8 = "",
    params: ?Params = null,
};

const Params = struct {
    textDocument: struct { uri: []const u8 = "", text: []const u8 = "" } = .{},
    // the whole text, the server asks for full sync
    contentChanges: []const struct { text: []const u8 } = &.{},
    position: Analysis.Position = .{ .line = 0, .character = 0 },
    context: struct { includeDeclaration: bool = true } = .{},
};

const timeout: std.Io.Timeout = .{ .duration = .{ .raw = .fromSeconds(5), .clock = .awake } };

const crashed = Analysis.Diagnostic{
    .range = .{ .start = .{ .line = 0, .character = 0 }, .end = .{ .line = 0, .character = 0 } },
    .severity = 1,
    .message = "mond crashed or hung on this file",
};

pub fn run(io: std.Io, gpa: std.mem.Allocator, exe: []const u8) !void {
    var in_buf: [1 << 16]u8 = undefined;
    var out_buf: [1 << 16]u8 = undefined;
    var in = std.Io.File.stdin().readerStreaming(io, &in_buf);
    var out = std.Io.File.stdout().writerStreaming(io, &out_buf);
    var s = Server{ .io = io, .gpa = gpa, .exe = exe, .out = &out.interface };
    var arena = std.heap.ArenaAllocator.init(gpa);
    while (true) : (_ = arena.reset(.retain_capacity)) {
        const a = arena.allocator();
        // the client closing stdin ends the server
        const body = read(&in.interface, a) catch return;
        if (std.json.parseFromSliceLeaky(Message, a, body, .{ .ignore_unknown_fields = true })) |m| {
            try s.handle(a, m);
        } else |_| try s.fail(a, .null, -32700, "parse error");
        // the client is quiet, what it changed gets analyzed
        if (in.interface.bufferedLen() == 0) {
            var docs = s.docs.iterator();
            while (docs.next()) |d| try s.analyze(a, d.key_ptr.*, d.value_ptr);
        }
        try out.interface.flush();
    }
}

fn read(in: *std.Io.Reader, a: std.mem.Allocator) ![]u8 {
    var len: usize = 0;
    while (true) {
        const line = std.mem.trimEnd(u8, try in.takeDelimiterInclusive('\n'), "\r\n");
        if (line.len == 0) return in.readAlloc(a, len);
        if (std.ascii.startsWithIgnoreCase(line, "content-length:")) len = try std.fmt.parseInt(usize, std.mem.trim(u8, line[15..], " "), 10);
    }
}

fn handle(s: *Server, a: std.mem.Allocator, m: Message) !void {
    const p = m.params orelse Params{};
    const uri = p.textDocument.uri;
    const method = std.meta.stringToEnum(Method, m.method) orelse return s.fail(a, m.id, -32601, "unknown method");
    if (method != .exit and (s.phase == .shut or (s.phase == .new) != (method == .initialize))) {
        return if (s.phase == .new) s.fail(a, m.id, -32002, "not initialized") else s.fail(a, m.id, -32600, "invalid request");
    }
    switch (method) {
        .initialize => {
            s.phase = .running;
            try s.respond(a, m.id, .{
                .capabilities = .{
                    .positionEncoding = "utf-16",
                    .textDocumentSync = 1,
                    .semanticTokensProvider = .{
                        .legend = .{ .tokenTypes = std.meta.fieldNames(Analysis.Type), .tokenModifiers = std.meta.fieldNames(Analysis.Modifier) },
                        .full = true,
                    },
                    .definitionProvider = true,
                    .referencesProvider = true,
                    .documentSymbolProvider = true,
                    .hoverProvider = true,
                },
                .serverInfo = .{ .name = "mond-lsp" },
            });
        },
        .shutdown => {
            s.phase = .shut;
            try s.respond(a, m.id, null);
        },
        .exit => std.process.exit(@intFromBool(s.phase != .shut)),
        .@"textDocument/didOpen" => try s.change(uri, p.textDocument.text),
        .@"textDocument/didChange" => if (p.contentChanges.len > 0) try s.change(uri, p.contentChanges[p.contentChanges.len - 1].text),
        .@"textDocument/didClose" => {
            if (s.docs.fetchRemove(uri)) |d| {
                s.gpa.free(d.key);
                if (d.value.text) |text| s.gpa.free(text);
                d.value.arena.promote(s.gpa).deinit();
            }
            try s.notify(a, "textDocument/publishDiagnostics", .{ .uri = uri, .diagnostics = &[_]Analysis.Diagnostic{} });
        },
        // the questions about a document are answered by its analysis of the current text
        else => {
            const d = s.docs.getPtr(uri) orelse return s.respond(a, m.id, null);
            try s.analyze(a, uri, d);
            const r = d.result;
            const link = at(r.links, p.position);
            switch (method) {
                .@"textDocument/semanticTokens/full" => try s.respond(a, m.id, .{ .data = r.data }),
                .@"textDocument/documentSymbol" => try s.respond(a, m.id, try symbols(a, r.decls, r.outline)),
                .@"textDocument/definition" => try s.respond(a, m.id, if (link) |l| if (r.decls[l[3]].selectionRange) |sel| Location{ .uri = uri, .range = sel } else null else null),
                .@"textDocument/hover" => try s.respond(a, m.id, if (link) |l| .{
                    .contents = .{ .kind = "markdown", .value = try hover(a, r.decls[l[3]]) },
                    .range = range(l),
                } else null),
                .@"textDocument/references" => {
                    var refs: std.ArrayList(Location) = .empty;
                    if (link) |l| for (r.links) |x| if (x[3] == l[3] and (p.context.includeDeclaration or !std.meta.eql(@as(?Analysis.Range, range(x)), r.decls[l[3]].selectionRange))) {
                        try refs.append(a, .{ .uri = uri, .range = range(x) });
                    };
                    try s.respond(a, m.id, refs.items);
                },
                else => unreachable,
            }
        },
    }
}

const Location = struct { uri: []const u8, range: Analysis.Range };

// the name at `p`, a cursor right behind a name is on it too
fn at(links: []const Analysis.Link, p: Analysis.Position) ?Analysis.Link {
    const i = std.sort.partitionPoint(Analysis.Link, links, p, struct {
        fn ends_before(q: Analysis.Position, l: Analysis.Link) bool {
            return Analysis.before(range(l).end, q);
        }
    }.ends_before);
    return if (i < links.len and !Analysis.before(p, range(links[i]).start)) links[i] else null;
}

fn range(l: Analysis.Link) Analysis.Range {
    return .{ .start = .{ .line = l[0], .character = l[1] }, .end = .{ .line = l[0], .character = l[2] } };
}

fn symbols(a: std.mem.Allocator, decls: []const Analysis.Symbol, outline: []const Analysis.Outline) ![]const Analysis.Symbol {
    const out = try a.alloc(Analysis.Symbol, outline.len);
    for (out, outline) |*s, o| {
        s.* = decls[o.decl];
        s.children = try symbols(a, decls, o.children);
    }
    return out;
}

fn hover(a: std.mem.Allocator, d: Analysis.Symbol) ![]const u8 {
    return std.fmt.allocPrint(a, "```mond\n{s}{s}{s}\n```", .{ d.name, if (d.detail.len > 0) ": " else "", d.detail });
}

// a change only keeps the text, typing does not wait for analyses
fn change(s: *Server, uri: []const u8, text: []const u8) !void {
    const gop = try s.docs.getOrPut(s.gpa, uri);
    if (!gop.found_existing) {
        gop.key_ptr.* = try s.gpa.dupe(u8, uri);
        gop.value_ptr.* = .{};
    }
    if (gop.value_ptr.text) |old| s.gpa.free(old);
    gop.value_ptr.text = try s.gpa.dupe(u8, text);
}

// publishes the diagnostics and keeps the result until the editor asks, a crash keeps the last result
fn analyze(s: *Server, a: std.mem.Allocator, uri: []const u8, d: *Doc) !void {
    const text = d.text orelse return;
    defer {
        s.gpa.free(text);
        d.text = null;
    }
    var arena = std.heap.ArenaAllocator.init(s.gpa);
    const r = s.work(arena.allocator(), text) orelse {
        arena.deinit();
        return s.notify(a, "textDocument/publishDiagnostics", .{ .uri = uri, .diagnostics = &[_]Analysis.Diagnostic{crashed} });
    };
    d.arena.promote(s.gpa).deinit();
    d.* = .{ .result = r, .arena = arena.state };
    try s.notify(a, "textDocument/publishDiagnostics", .{ .uri = uri, .diagnostics = r.diagnostics });
}

// the worker reads the source on stdin and answers on stdout, its panics go to stderr (the editor's log),
// a worker that hangs is killed after `timeout`
fn work(s: *Server, a: std.mem.Allocator, text: []const u8) ?Analysis.Result {
    var child = std.process.spawn(s.io, .{ .argv = &.{ s.exe, "analyze" }, .stdin = .pipe, .stdout = .pipe }) catch return null;
    defer child.kill(s.io);
    child.stdin.?.writeStreamingAll(s.io, text) catch return null;
    child.stdin.?.close(s.io);
    child.stdin = null;
    var streams: std.Io.File.MultiReader.Buffer(1) = undefined;
    var out: std.Io.File.MultiReader = undefined;
    out.init(a, s.io, streams.toStreams(), &.{child.stdout.?});
    defer out.deinit();
    out.fillRemaining(timeout.toDeadline(s.io)) catch return null;
    const term = child.wait(s.io) catch return null;
    if (term != .exited or term.exited != 0) return null;
    return std.json.parseFromSliceLeaky(Analysis.Result, a, out.reader(0).buffered(), .{ .allocate = .alloc_always }) catch null;
}

fn respond(s: *Server, a: std.mem.Allocator, id: ?std.json.Value, result: anytype) !void {
    try s.send(a, .{ .jsonrpc = "2.0", .id = id, .result = result });
}

// notifications get no answer, not even an error
fn fail(s: *Server, a: std.mem.Allocator, id: ?std.json.Value, code: i32, message: []const u8) !void {
    if (id) |i| try s.send(a, .{ .jsonrpc = "2.0", .id = i, .@"error" = .{ .code = code, .message = message } });
}

fn notify(s: *Server, a: std.mem.Allocator, comptime method: []const u8, params: anytype) !void {
    try s.send(a, .{ .jsonrpc = "2.0", .method = method, .params = params });
}

fn send(s: *Server, a: std.mem.Allocator, msg: anytype) !void {
    const body = try std.json.Stringify.valueAlloc(a, msg, .{});
    try s.out.print("Content-Length: {d}\r\n\r\n{s}", .{ body.len, body });
}
