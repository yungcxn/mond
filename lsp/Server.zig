const std = @import("std");
const Analysis = @import("Analysis.zig");
const Completion = @import("Completion.zig");

// the language server: json-rpc on stdin and stdout, documents are analyzed by a worker, a child
// process running the compiler, so a compiler crash costs that analysis but never the server

const Server = @This();

io: std.Io,
gpa: std.mem.Allocator,
// this executable, it is its own worker
executable_path: []const u8,
output: *std.Io.Writer,
// uri -> its document
documents: std.StringHashMapUnmanaged(Document) = .empty,
// the lifecycle: requests come after `initialize`, after `shutdown` only `exit`
phase: enum { new, running, shut } = .new,

// `result` is the last analysis of `source` and lives in `arena`
// completion goes by the last names known, the text being typed rarely parses
// older known names than the result's live in `known_names_arena`
const Document = struct {
    // the text waiting for its analysis
    pending_text: ?[]u8 = null,
    source: []const u8 = "",
    result: Analysis.Result = .{},
    arena: std.heap.ArenaAllocator.State = .{},
    known_names: []const Analysis.Symbol = &.{},
    known_names_arena: ?std.heap.ArenaAllocator.State = null,
};

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
    @"textDocument/completion",
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

const Location = struct { uri: []const u8, range: Analysis.Range };

const worker_timeout: std.Io.Timeout = .{
    .duration = .{ .raw = .fromSeconds(5), .clock = .awake },
};

const crash_diagnostic = Analysis.Diagnostic{
    .range = .{ .start = .{ .line = 0, .character = 0 }, .end = .{ .line = 0, .character = 0 } },
    .severity = 1,
    .message = "mond crashed or hung on this file",
};

pub fn run(io: std.Io, gpa: std.mem.Allocator, executable_path: []const u8) !void {
    var input_buffer: [1 << 16]u8 = undefined;
    var output_buffer: [1 << 16]u8 = undefined;
    var input = std.Io.File.stdin().readerStreaming(io, &input_buffer);
    var output = std.Io.File.stdout().writerStreaming(io, &output_buffer);
    var server = Server{
        .io = io,
        .gpa = gpa,
        .executable_path = executable_path,
        .output = &output.interface,
    };

    var arena = std.heap.ArenaAllocator.init(gpa);
    while (true) : (_ = arena.reset(.retain_capacity)) {
        const allocator = arena.allocator();
        const body = read_message(&input.interface, allocator) catch |err| switch (err) {
            // the header is answered, the next message may still be read
            error.InvalidContentLength => {
                try server.fail(allocator, .null, -32700, "invalid content-length");
                continue;
            },
            // the client closing stdin ends the server
            else => return,
        };
        const options: std.json.ParseOptions = .{ .ignore_unknown_fields = true };
        if (std.json.parseFromSliceLeaky(Message, allocator, body, options)) |message| {
            try server.handle(allocator, message);
        } else |_| try server.fail(allocator, .null, -32700, "parse error");

        // the client is quiet, what it changed gets analyzed
        if (input.interface.bufferedLen() == 0) {
            var documents = server.documents.iterator();
            while (documents.next()) |entry| {
                try server.analyze(allocator, entry.key_ptr.*, entry.value_ptr);
            }
        }
        try output.interface.flush();
    }
}

fn read_message(input: *std.Io.Reader, allocator: std.mem.Allocator) ![]u8 {
    var content_length: usize = 0;
    while (true) {
        const line = std.mem.trimEnd(u8, try input.takeDelimiterInclusive('\n'), "\r\n");
        if (line.len == 0) return input.readAlloc(allocator, content_length);

        const header = "content-length:";
        if (!std.ascii.startsWithIgnoreCase(line, header)) continue;
        const value = std.mem.trim(u8, line[header.len..], " ");
        content_length = std.fmt.parseInt(usize, value, 10) catch return error.InvalidContentLength;
    }
}

fn handle(server: *Server, allocator: std.mem.Allocator, message: Message) !void {
    const params = message.params orelse Params{};
    const uri = params.textDocument.uri;
    const method = std.meta.stringToEnum(Method, message.method) orelse {
        return server.fail(allocator, message.id, -32601, "unknown method");
    };
    if (method != .exit and !server.accepts(method)) {
        if (server.phase == .new) {
            return server.fail(allocator, message.id, -32002, "not initialized");
        }
        return server.fail(allocator, message.id, -32600, "invalid request");
    }

    switch (method) {
        .initialize => {
            server.phase = .running;
            try server.respond(allocator, message.id, capabilities);
        },
        .shutdown => {
            server.phase = .shut;
            try server.respond(allocator, message.id, null);
        },
        .exit => std.process.exit(@intFromBool(server.phase != .shut)),
        .@"textDocument/didOpen" => try server.change(uri, params.textDocument.text),
        .@"textDocument/didChange" => {
            const changes = params.contentChanges;
            if (changes.len > 0) try server.change(uri, changes[changes.len - 1].text);
        },
        .@"textDocument/didClose" => {
            server.close(uri);
            const no_diagnostics = &[_]Analysis.Diagnostic{};
            const closed = .{ .uri = uri, .diagnostics = no_diagnostics };
            try server.notify(allocator, "textDocument/publishDiagnostics", closed);
        },
        .@"textDocument/semanticTokens/full",
        .@"textDocument/documentSymbol",
        .@"textDocument/definition",
        .@"textDocument/hover",
        .@"textDocument/completion",
        .@"textDocument/references",
        => try server.answer(allocator, message, method, params),
    }
}

// only `initialize` before it, nothing after `shutdown`
fn accepts(server: *Server, method: Method) bool {
    if (server.phase == .shut) return false;
    return (server.phase == .new) == (method == .initialize);
}

const capabilities = .{
    .capabilities = .{
        .positionEncoding = "utf-16",
        .textDocumentSync = 1,
        .semanticTokensProvider = .{
            .legend = .{
                .tokenTypes = std.meta.fieldNames(Analysis.Type),
                .tokenModifiers = std.meta.fieldNames(Analysis.Modifier),
            },
            .full = true,
        },
        .definitionProvider = true,
        .referencesProvider = true,
        .documentSymbolProvider = true,
        .hoverProvider = true,
        .completionProvider = .{ .triggerCharacters = &[_][]const u8{ ".", "$" } },
    },
    .serverInfo = .{ .name = "mond-lsp" },
};

fn close(server: *Server, uri: []const u8) void {
    const removed = server.documents.fetchRemove(uri) orelse return;
    server.gpa.free(removed.key);
    if (removed.value.pending_text) |text| server.gpa.free(text);
    removed.value.arena.promote(server.gpa).deinit();
    if (removed.value.known_names_arena) |known| known.promote(server.gpa).deinit();
}

// the questions about a document are answered by its analysis of the current text
fn answer(
    server: *Server,
    allocator: std.mem.Allocator,
    message: Message,
    method: Method,
    params: Params,
) !void {
    const id = message.id;
    const uri = params.textDocument.uri;
    const document = server.documents.getPtr(uri) orelse return server.respond(allocator, id, null);
    try server.analyze(allocator, uri, document);

    const result = document.result;
    const link = link_at(result.links, params.position);
    switch (method) {
        .@"textDocument/semanticTokens/full" => {
            try server.respond(allocator, id, .{ .data = result.data });
        },
        .@"textDocument/documentSymbol" => {
            const symbols = try outline_symbols(allocator, result.decls, result.outline);
            try server.respond(allocator, id, symbols);
        },
        .@"textDocument/definition" => {
            try server.respond(allocator, id, definition(result, link, uri));
        },
        .@"textDocument/hover" => {
            const found = link orelse return server.respond(allocator, id, null);
            const text = try hover_text(allocator, result.decls[found[3]]);
            const hover = .{
                .contents = .{ .kind = "markdown", .value = text },
                .range = link_range(found),
            };
            try server.respond(allocator, id, hover);
        },
        .@"textDocument/completion" => {
            const names = document.known_names;
            const items = try Completion.offer(allocator, document.source, params.position, names);
            try server.respond(allocator, id, items);
        },
        .@"textDocument/references" => {
            const include_declaration = params.context.includeDeclaration;
            const found = try references(allocator, result, link, uri, include_declaration);
            try server.respond(allocator, id, found);
        },
        .initialize,
        .shutdown,
        .exit,
        .@"textDocument/didOpen",
        .@"textDocument/didChange",
        .@"textDocument/didClose",
        => unreachable,
    }
}

// the name at `position`, a cursor right behind a name is on it too
fn link_at(links: []const Analysis.Link, position: Analysis.Position) ?Analysis.Link {
    const index = std.sort.partitionPoint(Analysis.Link, links, position, ends_before);
    if (index >= links.len) return null;
    if (Analysis.before(position, link_range(links[index]).start)) return null;
    return links[index];
}

fn ends_before(position: Analysis.Position, link: Analysis.Link) bool {
    return Analysis.before(link_range(link).end, position);
}

fn link_range(link: Analysis.Link) Analysis.Range {
    const line, const start, const end, _ = link;
    return .{
        .start = .{ .line = line, .character = start },
        .end = .{ .line = line, .character = end },
    };
}

fn definition(result: Analysis.Result, link: ?Analysis.Link, uri: []const u8) ?Location {
    const found = link orelse return null;
    const name_range = result.decls[found[3]].selectionRange orelse return null;
    return .{ .uri = uri, .range = name_range };
}

fn references(
    allocator: std.mem.Allocator,
    result: Analysis.Result,
    link: ?Analysis.Link,
    uri: []const u8,
    include_declaration: bool,
) ![]const Location {
    var found: std.ArrayList(Location) = .empty;
    const target = link orelse return found.items;
    const declared_at = result.decls[target[3]].selectionRange;
    for (result.links) |other| {
        if (other[3] != target[3]) continue;
        const is_declaration = std.meta.eql(@as(?Analysis.Range, link_range(other)), declared_at);
        if (!include_declaration and is_declaration) continue;
        try found.append(allocator, .{ .uri = uri, .range = link_range(other) });
    }
    return found.items;
}

// the declarations of the outline with their children
fn outline_symbols(
    allocator: std.mem.Allocator,
    declarations: []const Analysis.Symbol,
    outline: []const Analysis.Outline,
) ![]const Analysis.Symbol {
    const symbols = try allocator.alloc(Analysis.Symbol, outline.len);
    for (symbols, outline) |*symbol, entry| {
        symbol.* = declarations[entry.decl];
        symbol.children = try outline_symbols(allocator, declarations, entry.children);
    }
    return symbols;
}

fn hover_text(allocator: std.mem.Allocator, declaration: Analysis.Symbol) ![]const u8 {
    const separator = if (declaration.detail.len > 0) ": " else "";
    const parts = .{ declaration.name, separator, declaration.detail };
    return std.fmt.allocPrint(allocator, "```mond\n{s}{s}{s}\n```", parts);
}

// a change only keeps the text, typing does not wait for analyses
fn change(server: *Server, uri: []const u8, text: []const u8) !void {
    const entry = try server.documents.getOrPut(server.gpa, uri);
    if (!entry.found_existing) {
        entry.key_ptr.* = try server.gpa.dupe(u8, uri);
        entry.value_ptr.* = .{};
    }
    if (entry.value_ptr.pending_text) |old| server.gpa.free(old);
    entry.value_ptr.pending_text = try server.gpa.dupe(u8, text);
}

// publishes the diagnostics and keeps the result for the editor, a crash keeps the last result
fn analyze(
    server: *Server,
    allocator: std.mem.Allocator,
    uri: []const u8,
    document: *Document,
) !void {
    const text = document.pending_text orelse return;
    defer {
        server.gpa.free(text);
        document.pending_text = null;
    }

    var arena = std.heap.ArenaAllocator.init(server.gpa);
    const result = server.run_worker(arena.allocator(), uri, text) orelse {
        arena.deinit();
        const crashed = .{ .uri = uri, .diagnostics = &[_]Analysis.Diagnostic{crash_diagnostic} };
        return server.notify(allocator, "textDocument/publishDiagnostics", crashed);
    };

    const source = try arena.allocator().dupe(u8, text);
    if (result.decls.len > 0) {
        if (document.known_names_arena) |known| known.promote(server.gpa).deinit();
        document.arena.promote(server.gpa).deinit();
        document.* = .{
            .source = source,
            .result = result,
            .arena = arena.state,
            .known_names = result.decls,
        };
    } else {
        // the names known stay, with the arena they are in
        if (document.known_names_arena == null) {
            document.known_names_arena = document.arena;
        } else {
            document.arena.promote(server.gpa).deinit();
        }
        document.source = source;
        document.result = result;
        document.arena = arena.state;
    }

    const analyzed = .{ .uri = uri, .diagnostics = result.diagnostics };
    try server.notify(allocator, "textDocument/publishDiagnostics", analyzed);
}

// the worker reads the source on stdin and answers on stdout, its panics go to the editor's log
// a worker that hangs is killed after `worker_timeout`
fn run_worker(
    server: *Server,
    allocator: std.mem.Allocator,
    uri: []const u8,
    text: []const u8,
) ?Analysis.Result {
    const io = server.io;
    // it gets the document's file for `include`
    const path = path_of_uri(allocator, uri) catch return null;
    const argv: []const []const u8 = &.{ server.executable_path, "analyze", path };
    var child = std.process.spawn(io, .{ .argv = argv, .stdin = .pipe, .stdout = .pipe }) catch {
        return null;
    };
    defer child.kill(io);

    child.stdin.?.writeStreamingAll(io, text) catch return null;
    child.stdin.?.close(io);
    child.stdin = null;

    var streams: std.Io.File.MultiReader.Buffer(1) = undefined;
    var output: std.Io.File.MultiReader = undefined;
    output.init(allocator, io, streams.toStreams(), &.{child.stdout.?});
    defer output.deinit();
    output.fillRemaining(worker_timeout.toDeadline(io)) catch return null;

    const termination = child.wait(io) catch return null;
    if (termination != .exited or termination.exited != 0) return null;
    const answer_text = output.reader(0).buffered();
    const options: std.json.ParseOptions = .{ .allocate = .alloc_always };
    const parsed = std.json.parseFromSliceLeaky(Analysis.Result, allocator, answer_text, options);
    return parsed catch null;
}

// also of a remote uri (`vscode-remote://ssh-remote+host/..`): a folder shared under one path
fn path_of_uri(allocator: std.mem.Allocator, uri: []const u8) ![]const u8 {
    const scheme_end = std.mem.indexOf(u8, uri, "://") orelse return "";
    const path_start = std.mem.indexOfScalarPos(u8, uri, scheme_end + 3, '/') orelse return "";
    return std.Uri.percentDecodeInPlace(try allocator.dupe(u8, uri[path_start..]));
}

fn respond(
    server: *Server,
    allocator: std.mem.Allocator,
    id: ?std.json.Value,
    result: anytype,
) !void {
    try server.send(allocator, .{ .jsonrpc = "2.0", .id = id, .result = result });
}

// notifications get no answer, not even an error
fn fail(
    server: *Server,
    allocator: std.mem.Allocator,
    id: ?std.json.Value,
    code: i32,
    message: []const u8,
) !void {
    const request_id = id orelse return;
    const failure = .{ .code = code, .message = message };
    try server.send(allocator, .{ .jsonrpc = "2.0", .id = request_id, .@"error" = failure });
}

fn notify(
    server: *Server,
    allocator: std.mem.Allocator,
    comptime method: []const u8,
    params: anytype,
) !void {
    try server.send(allocator, .{ .jsonrpc = "2.0", .method = method, .params = params });
}

fn send(server: *Server, allocator: std.mem.Allocator, message: anytype) !void {
    const body = try std.json.Stringify.valueAlloc(allocator, message, .{});
    try server.output.print("Content-Length: {d}\r\n\r\n{s}", .{ body.len, body });
}
