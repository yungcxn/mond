const std = @import("std");
const ParseTree = @import("ParseTree.zig");
const DynamicBuffer = @import("containers.zig").DynamicBuffer;

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const BodyPool = @import("resolver/BodyPool.zig");
const Scopes = @import("resolver/Scopes.zig");
const Doctor = @import("resolver/Doctor.zig");
const Interpreter = @import("resolver/Interpreter.zig");
const Initialization = @import("resolver/checker/Initialization.zig");
const Declarations = @import("resolver/checker/Declarations.zig");
const Expressions = @import("resolver/checker/Expressions.zig");
const Mutability = @import("resolver/checker/Mutability.zig");
const Calls = @import("resolver/checker/Calls.zig");
const Flow = @import("resolver/checker/Flow.zig");
const Patterns = @import("resolver/checker/Patterns.zig");
const Types = @import("resolver/checker/Types.zig");
const Generics = @import("resolver/checker/Generics.zig");
const StaticValues = @import("resolver/checker/StaticValues.zig");
pub const Macros = @import("resolver/checker/Macros.zig");

const Resolver = @This();

// the resolver answers for every ast node which declaration it means and what type it has
// one recursive walk per body does scoping, lookup, inference and checks while nodes are in cache
// globals resolve lazily on first use and are memoized, a state per declaration detects cycles
// unknown types are type variables filled by unification, the final sweep only runs if any exist
// nothing the parse tree already holds is copied, the side tables only hold what is computed
// a macro pass that expands a splice rebuilds the tree and starts over (see checker/Macros.zig)
// checker roles reach the rest through `owning_resolver()`, interpreter roles through
// `owning_interpreter()`

// lets the language server see every expanding pass, the last pass keeps no trace of the splices
pub const Watch = struct { observer: *anyopaque, pass: *const fn (*anyopaque, *Resolver) void };

// what outlives a macro pass: everything else is built anew on the rebuilt tree (see `restart`)
pub const Session = struct {
    // where `include` reads, the file of `src_bytes`
    io: ?std.Io = null,
    path: []const u8 = "",
    // called before the tree is rebuilt
    watch: ?Watch = null,
    // names `$fresh` and hygiene made so far, so no later pass makes one again
    fresh_name_count: u32 = 0,
};

pub const FunctionContext = struct {
    declaration: DeclPool.Index = .none,
    return_type: StaticPool.Index = .none,
    self_type: StaticPool.Index = .none,
    loop_depth: u16 = 0,
    is_static_context: bool = false,
    is_interpreted: bool = false,
    is_abstract: bool = false,
};

allocator: std.mem.Allocator,
tree: *ParseTree,
src_bytes: []const u8,
// emitted by `Parser`, or by the last rebuild of the tree
roots: []const ParseTree.NodeId,
// owns the roots once a pass rebuilt the tree, kept over passes
rebuilt: ?DynamicBuffer(ParseTree.NodeId) = null,
session: Session = .{},

// names are interned when their node is resolved, not when it is parsed
name_pool: NamePool,
// every static (compile time) value, from integers to types
static_pool: StaticPool,
decl_pool: DeclPool,

// one slot per parse tree node: plain arrays, so the lowerer reads them without indirection
node_types: []StaticPool.Index,
node_declarations: []DeclPool.Index,
node_static_values: []StaticPool.Index,
// copies of the node tables of every checked body, the interpreter and the lowerer read them
bodies: BodyPool,

scopes: Scopes,
// which locals are not written yet
initialization: Initialization,

// the checker, one role per part of the language
declarations: Declarations = .{},
expressions: Expressions = .{},
mutability: Mutability = .{},
calls: Calls = .{},
flow: Flow,
patterns: Patterns = .{},
types: Types = .{},
generics: Generics = .{},
static_values: StaticValues = .{},
macros: Macros,

// a single report never stops resolving
doctor: Doctor,
interpreter: Interpreter,

// buffers that live while one top-level declaration is checked
temporary_arena: std.heap.ArenaAllocator,

pub inline fn init(
    alloc: std.mem.Allocator,
    tree: *ParseTree,
    src_bytes: []const u8,
    roots: []const ParseTree.NodeId,
) Resolver {
    const node_count = tree.ast_nodes.len();
    const resolver = Resolver{
        .allocator = alloc,
        .tree = tree,
        .src_bytes = src_bytes,
        .roots = roots,
        .name_pool = .init(alloc, tree, src_bytes),
        .static_pool = .init(alloc),
        .decl_pool = .init(alloc, 4096),
        .node_types = alloc.alloc(StaticPool.Index, node_count) catch @panic("OOM"),
        .node_declarations = alloc.alloc(DeclPool.Index, node_count) catch @panic("OOM"),
        .node_static_values = alloc.alloc(StaticPool.Index, node_count) catch @panic("OOM"),
        .bodies = .init(alloc),
        .scopes = .init(alloc),
        .initialization = .init(alloc),
        .flow = .init(alloc),
        .macros = .{ .pass_len = node_count },
        .doctor = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .init(alloc),
        .temporary_arena = .init(alloc),
    };

    @memset(resolver.node_types, .none);
    @memset(resolver.node_declarations, .none);
    @memset(resolver.node_static_values, .none);
    return resolver;
}

pub inline fn deinit(self: *Resolver) void {
    self.name_pool.deinit();
    self.static_pool.deinit();
    self.decl_pool.deinit();
    self.bodies.deinit();
    self.scopes.deinit(self.allocator);
    self.initialization.deinit();
    self.interpreter.deinit();
    self.doctor.diagnostics.deinit();
    self.flow.deinit();
    self.generics.deinit(self.allocator);
    self.temporary_arena.deinit();
    if (self.rebuilt) |*rebuilt_roots| rebuilt_roots.deinit();
    self.allocator.free(self.macros.starts);

    self.allocator.free(self.node_types);
    self.allocator.free(self.node_declarations);
    self.allocator.free(self.node_static_values);
}

pub fn resolve(self: *Resolver) !void {
    // nodes made in the last pass (quotes, `refl $file`) need rows too, for whoever walks the tree
    defer self.grow_node_tables();

    var passes: u32 = 0;
    while (true) : (passes += 1) {
        self.declarations.collect_globals();

        // the source has no `@` outside a quote, later passes hold only what landed in it
        // (see `Trees.land`)
        if (self.tree.macros and passes == 0) {
            for (self.roots) |root| self.macros.report_stray_unquotes(root, false);
        }
        try self.fail_on_errors();

        // top-level splices run first, in order, before anything they could change is resolved
        const has_top_splices = self.tree.macros and self.macros.expand_roots();
        // a pass in which a splice failed is the last, so everything is checked for its errors
        const will_rebuild = has_top_splices and
            self.macros.expanded != 0 and
            !self.macros.failed;
        if (!will_rebuild) {
            const declaration_count = self.decl_pool.entries.len();
            for (0..declaration_count) |i| {
                const declaration: DeclPool.Index = @enumFromInt(i);
                self.declarations.ensure_signature(declaration);
                self.declarations.check_body(declaration);
                _ = self.temporary_arena.reset(.retain_capacity);
            }

            var context = FunctionContext{};
            for (self.roots) |root| {
                const declares_nothing = self.node_declarations[root] == .none;
                if (declares_nothing and self.tree.kind(root) != .splice) {
                    // a top-level expression is a scope, what it binds (`x <- y`) ends with it
                    self.scopes.open();
                    _ = self.expressions.infer(&context, root, .none);
                    self.scopes.close();
                }
            }

            self.calls.check_dispatch_groups();
        }

        const nothing_changed = self.macros.expanded == 0 and !self.macros.edited;
        if (self.macros.failed or nothing_changed) break;

        if (passes == Macros.max_passes) {
            _ = self.report(.endless_expansion, self.macros.last, 0, 0);
            return error.ResolveFailed;
        }

        // the next pass resolves everything anew on the tree rebuilt with what this one expanded
        if (self.session.watch) |watch| {
            self.grow_node_tables();
            watch.pass(watch.observer, self);
        }

        // the buffer of the last rebuild is reused, the first rebuild makes one
        const capacity = @max(16, @as(u32, @intCast(self.roots.len)));
        var roots = self.rebuilt orelse
            DynamicBuffer(ParseTree.NodeId).init(self.allocator, capacity);
        self.rebuilt = null;
        // a pass ends with the roots of `refl $file` when a macro read or wrote them
        const final_roots = if (self.macros.file != 0)
            self.tree.manychildren(self.macros.file)
        else
            self.roots;
        // the roots of the last rebuild already live in the buffer, copying would alias
        if (final_roots.ptr != roots.buffer.ptr) {
            roots.len = 0;
            roots.append(final_roots);
        }
        self.tree.rebuild(self.allocator, &roots, self.src_bytes);

        // the session and the fresh name counter outlive the pass, everything else starts anew
        const session = self.session;
        const alloc, const tree, const src_bytes = .{ self.allocator, self.tree, self.src_bytes };
        self.deinit();
        self.* = init(alloc, tree, src_bytes, roots.items());
        self.rebuilt = roots;
        self.session = session;
    }
    try self.fail_on_errors();

    self.types.finish_inference();
    try self.fail_on_errors();

    self.declarations.check_main();
    try self.fail_on_errors();
}

inline fn fail_on_errors(self: *const Resolver) error{ResolveFailed}!void {
    if (self.doctor.has_errors()) return error.ResolveFailed;
}

// macros add nodes to the tree, they need rows in the node tables too
pub fn grow_node_tables(self: *Resolver) void {
    const node_count = self.tree.ast_nodes.len();
    if (node_count <= self.node_types.len) return;

    inline for (.{ "node_types", "node_declarations", "node_static_values" }) |table_name| {
        const table = &@field(self, table_name);
        const old_length = table.len;
        table.* = self.allocator.realloc(table.*, node_count) catch @panic("OOM");
        @memset(table.*[old_length..], .none);
    }
}

pub fn temporary_slice(self: *Resolver, comptime T: type, count: usize) []T {
    return self.temporary_arena.allocator().alloc(T, count) catch @panic("OOM");
}

pub inline fn set_node_type(
    self: *Resolver,
    node: ParseTree.NodeId,
    node_type: StaticPool.Index,
) StaticPool.Index {
    self.node_types[node] = node_type;
    return node_type;
}

pub fn report(
    self: *Resolver,
    code: Doctor.Disorder,
    node: ParseTree.NodeId,
    first_operand: anytype,
    second_operand: anytype,
) StaticPool.Index {
    self.doctor.report(code, node, first_operand, second_operand);
    return self.set_node_type(node, .poison_type);
}

pub fn report_mismatch(
    self: *Resolver,
    node: ParseTree.NodeId,
    found_type: StaticPool.Index,
    expected_type: StaticPool.Index,
) StaticPool.Index {
    // a poisoned type was reported where it came from
    if (found_type == .poison_type) return found_type;
    return self.report(.type_mismatch, node, found_type, expected_type);
}

// the node tables of `root` as they are now, a body whose locals are the declarations from
// `first_local` on
pub fn capture_body(
    self: *Resolver,
    declaration: DeclPool.Index,
    root: ParseTree.NodeId,
    first_local: u32,
) BodyPool.Body {
    const first_node, const end_node = self.tree.subtree(root);
    const body: BodyPool.Body = .{
        .declaration = declaration,
        .first_node = first_node,
        .node_count = end_node - first_node,
        .first_local = first_local,
        .local_count = self.decl_pool.entries.len() - first_local,
    };
    return self.bodies.copy_node_tables(
        body,
        self.node_types,
        self.node_declarations,
        self.node_static_values,
    );
}

// nodes outside the body (globals, its surroundings) are read from the live node tables
pub fn node_info(
    self: *const Resolver,
    body: BodyPool.Body,
    comptime field: @EnumLiteral(),
    node: ParseTree.NodeId,
) @FieldType(BodyPool.NodeInfo, @tagName(field)) {
    if (node -% body.first_node < body.node_count) {
        const row = body.first_row + node - body.first_node;
        return self.bodies.node_rows.column(field)[row];
    }

    return @field(self, switch (field) {
        .node_type => "node_types",
        .declaration => "node_declarations",
        .static_value => "node_static_values",
        else => @compileError("no node table for " ++ @tagName(field)),
    })[node];
}
