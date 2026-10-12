const std = @import("std");
const ParseTree = @import("ParseTree.zig");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const AbstractPool = @import("resolver/AbstractPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const BodyPool = @import("resolver/BodyPool.zig");
const Scopes = @import("resolver/Scopes.zig");
const Doctor = @import("resolver/Doctor.zig");
const Interpreter = @import("resolver/Interpreter.zig");
const Inits = @import("resolver/checker/Inits.zig");
const Decls = @import("resolver/checker/Decls.zig");
const Exprs = @import("resolver/checker/Exprs.zig");
const Mutability = @import("resolver/checker/Mutability.zig");
const Calls = @import("resolver/checker/Calls.zig");
const Flow = @import("resolver/checker/Flow.zig");
const Patterns = @import("resolver/checker/Patterns.zig");
const Types = @import("resolver/checker/Types.zig");
const Generics = @import("resolver/checker/Generics.zig");
const Statics = @import("resolver/checker/Statics.zig");
pub const Macros = @import("resolver/checker/Macros.zig");

const Resolver = @This();

// the resolver answers two questions for every ast node:
//   1. which declaration does this identifier mean?   -> node_decl
//   2. what type does this expression have?           -> node_type
//
// how it works:
//   - one recursive walk per declaration body does everything at once: scoping, name lookup,
//     type checking + inference, mutability, loop context, runit. every node is visited about
//     once while its data is still in cache.
//   - global declarations are resolved lazily: when a body uses a global that is not resolved
//     yet, it is resolved right there and memoized. a state per declaration detects real cycles.
//   - types never have to be written: most are known on the spot (the value's type), and where
//     they are not (induced return types in recursion, `x = []`), a type var stands in and is
//     filled by unification later (see AbstractPool.zig). one final sweep replaces
//     every var by its result, and is skipped entirely when no var was ever created.
//   - nothing the parse tree already has is copied (defaults, where-clauses, field names are
//     read from the tree when needed). side tables only hold what is computed.
//   - macros change the program before it is compiled: a pass that expands a splice (`<x>`) rebuilds the
//     tree and starts over, the last pass compiles what no macro changes anymore (see checker/Macros.zig)
//
// who does what:
//   - the resolver holds the parts below and runs the phases in order, the node tables are its own
//   - data: `ParseTree` decodes its own node layouts, the pools hold names, declarations, static values and types,
//     type vars and checked bodies, `Scopes` maps names to declarations, `Doctor` collects the reports
//   - roles: the checker is one role per part of the language (`decls`, `exprs`, `mutability`, ..) reaching
//     the rest through `res()`, the interpreter evaluates what is static whenever a role asks and is built
//     the same way (`variables`, `flow`, ..) through `interp()`, every role owns the state of its work
//
// future:
//   - multithreading: bodies are independent once signatures are ready - check them on worker
//     threads with their own type vars and diagnostics, decl states become atomics
//   - incremental: hash every top-level declaration's tokens, reuse results of unchanged ones

pub const Watch = struct { ctx: *anyopaque, pass: *const fn (*anyopaque, *Resolver) void };

pub const FnCtx = struct {
    decl: DeclPool.Index = .none,
    ret_type: StaticPool.Index = .none,
    self_type: StaticPool.Index = .none,
    loop_depth: u16 = 0,
    in_static: bool = false,
    interpreted: bool = false,
    abstract: bool = false,
};

alloc: std.mem.Allocator,
tree: *ParseTree,
src_bytes: []const u8,
// emitted by `Parser`, or by the last rebuild of the tree
roots: []const ParseTree.NodeId,
// the roots once a pass rebuilt the tree, kept over passes
rebuilt: ?DynBuf(ParseTree.NodeId) = null,
// where `include` reads, the file of `src_bytes`
io: ?std.Io = null,
path: []const u8 = "",
// sees every pass that expanded something before the tree is rebuilt: the language server, the last pass has no trace of
// what the splices spelled
watch: ?Watch = null,

// identifier string -> NamePool.Index. names are interned when a node is resolved (visited)
name_pool: NamePool,

// where every static (non-runtime) value (from integer values to types) is stored.
static_pool: StaticPool,

// placeholders for types not known yet and what they turned out to be
abstract_pool: AbstractPool,

decl_pool: DeclPool,

// the two results, one slot per parse tree node, indexed by ParseTree.NodeId.
// plain arrays of u32: 8 bytes per node in total, and the lowerer reads them with no indirection.
node_type: []StaticPool.Index,
node_decl: []DeclPool.Index,
node_value: []StaticPool.Index,
// their copies for every checked body, the interpreter and the lowerer read them
bodies: BodyPool,

// which declaration a name means
scopes: Scopes,
// which locals are not written yet
inits: Inits,

// the checker, a role per part of the language
decls: Decls = .{},
exprs: Exprs = .{},
mutability: Mutability = .{},
calls: Calls = .{},
flow: Flow,
patterns: Patterns = .{},
types: Types = .{},
generics: Generics = .{},
statics: Statics = .{},
macros: Macros,

// stores which nodes have something to report (e.g. warning or error)
// - a single report does not stop resolving
doc: Doctor,

// "static" (compiletime) evaluation of what's static
interpreter: Interpreter,

// buffers that live while one top-level declaration is checked
temp: std.heap.ArenaAllocator,

pub inline fn init(alloc: std.mem.Allocator, tree: *ParseTree, src_bytes: []const u8, roots: []const ParseTree.NodeId) Resolver {
    const r = Resolver{
        .alloc = alloc,
        .tree = tree,
        .src_bytes = src_bytes,
        .roots = roots,
        .name_pool = .init(alloc, tree, src_bytes),
        .static_pool = .init(alloc),
        .abstract_pool = .init(alloc),
        .decl_pool = .init(alloc, 4096),
        .node_type = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_decl = alloc.alloc(DeclPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_value = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .bodies = .init(alloc),
        .scopes = .init(alloc),
        .inits = .init(alloc),
        .flow = .init(alloc),
        .macros = .{ .pass_len = tree.ast_nodes.len() },
        .doc = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .init(alloc),
        .temp = .init(alloc),
    };
    @memset(r.node_type, .none);
    @memset(r.node_decl, .none);
    @memset(r.node_value, .none);
    return r;
}

pub inline fn deinit(self: *Resolver) void {
    self.name_pool.deinit();
    self.static_pool.deinit();
    self.abstract_pool.deinit();
    self.decl_pool.deinit();
    self.bodies.deinit();
    self.scopes.deinit(self.alloc);
    self.inits.deinit();
    self.interpreter.deinit();
    self.doc.diagnostics.deinit();
    self.flow.deinit();
    self.generics.deinit(self.alloc);
    self.temp.deinit();
    if (self.rebuilt) |*b| b.deinit();
    self.alloc.free(self.macros.starts);

    self.alloc.free(self.node_type);
    self.alloc.free(self.node_decl);
    self.alloc.free(self.node_value);
}

pub fn resolve(self: *Resolver) !void {
    // the nodes made in the last pass (quotes, `refl $file`) have rows in the node tables too, for whoever walks the tree
    defer self.fit();
    var passes: u32 = 0;
    while (true) : (passes += 1) {
        self.decls.collect_globals();
        // the source has no `@` outside a quote, later passes have only what landed in it too (see `Trees.land`)
        if (self.tree.macros and passes == 0) for (self.roots) |root| self.macros.strays(root, false);
        if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;
        // the splices at the top run first, in order, before anything they could change is resolved. a pass in which a splice
        // failed is the last, everything is checked for its errors
        const top = self.tree.macros and self.macros.expand_roots();
        if (!top or self.macros.expanded == 0 or self.macros.failed) self.check_globals();
        if (self.macros.failed or self.macros.expanded == 0 and !self.macros.edited) break;
        if (passes == Macros.max_passes) {
            _ = self.report(.endless_expansion, self.macros.last, 0, 0);
            return error.ResolveFailed;
        }
        self.restart();
    }
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;

    self.types.apply_inferred();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;

    self.decls.check_main();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;
}

fn check_globals(self: *Resolver) void {
    const count = self.decl_pool.entries.len();
    for (0..count) |i| {
        self.decls.ensure_signature(@enumFromInt(i));
        self.decls.check_body(@enumFromInt(i));
        _ = self.temp.reset(.retain_capacity);
    }
    var ctx = FnCtx{};
    for (self.roots) |root| if (self.node_decl[root] == .none and self.tree.kind(root) != .splice) {
        _ = self.exprs.infer(&ctx, root, .none);
    };
    self.calls.check_groups();
}

// the next pass: the tree rebuilt with what this one expanded, everything resolved anew on it
fn restart(self: *Resolver) void {
    if (self.watch) |w| {
        self.fit();
        w.pass(w.ctx, self);
    }
    var roots = self.rebuilt orelse DynBuf(ParseTree.NodeId).init(self.alloc, @max(16, @as(u32, @intCast(self.roots.len))));
    self.rebuilt = null;
    // the roots a pass ends with: those of `refl $file` when a macro read or wrote them, else the ones it began with
    const from = if (self.macros.file != 0) self.tree.manychildren(self.macros.file) else self.roots;
    if (from.ptr != roots.buf.ptr) {
        roots.head = 0;
        roots.append(from);
    }
    self.tree.rebuild(self.alloc, &roots, self.src_bytes);
    const keep = .{ self.io, self.path, self.watch, self.macros.fresh };
    const alloc, const tree, const src = .{ self.alloc, self.tree, self.src_bytes };
    self.deinit();
    self.* = init(alloc, tree, src, roots.sliced());
    self.rebuilt = roots;
    self.io, self.path, self.watch, self.macros.fresh = keep;
}

// rows in the node tables for the nodes macros added to the tree
pub fn fit(self: *Resolver) void {
    const n = self.tree.ast_nodes.len();
    if (n <= self.node_type.len) return;
    inline for (.{ "node_type", "node_decl", "node_value" }) |f| {
        const old = @field(self, f).len;
        @field(self, f) = self.alloc.realloc(@field(self, f), n) catch @panic("OOM");
        @memset(@field(self, f)[old..], .none);
    }
}

pub fn scratch(self: *Resolver, comptime T: type, n: usize) []T {
    return self.temp.allocator().alloc(T, n) catch @panic("OOM");
}

pub inline fn set(self: *Resolver, n: ParseTree.NodeId, t: StaticPool.Index) StaticPool.Index {
    self.node_type[n] = t;
    return t;
}

pub fn report(self: *Resolver, code: Doctor.Disorder, n: ParseTree.NodeId, a: anytype, b: anytype) StaticPool.Index {
    self.doc.report(code, n, a, b);
    return self.set(n, .poison_type);
}

pub fn mismatch(self: *Resolver, n: ParseTree.NodeId, t: StaticPool.Index, want: StaticPool.Index) StaticPool.Index {
    return if (t == .poison_type) t else self.report(.type_mismatch, n, t, want);
}

// the node tables of `root` as they are now, a body whose locals are the declarations from `first` on
pub fn capture(self: *Resolver, decl: DeclPool.Index, root: ParseTree.NodeId, first: u32) BodyPool.Body {
    const lo, const hi = self.tree.subtree(root);
    return self.bodies.capture(.{ .decl = decl, .lo = lo, .len = hi - lo, .first = first, .locals = self.decl_pool.entries.len() - first }, self.node_type, self.node_decl, self.node_value);
}

pub fn node_info(self: *const Resolver, b: BodyPool.Body, comptime field: @EnumLiteral(), n: ParseTree.NodeId) @FieldType(BodyPool.NodeInfo, @tagName(field)) {
    if (n -% b.lo < b.len) return @field(self.bodies.nodes.pool, @tagName(field)).buf[b.start + n - b.lo];
    return @field(self, if (field == .ty) "node_type" else "node_" ++ @tagName(field))[n];
}
