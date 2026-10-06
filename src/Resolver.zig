const std = @import("std");
const ParseTree = @import("ParseTree.zig");
const syntax = @import("resolver/syntax.zig");

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const AbstractPool = @import("resolver/AbstractPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const BodyPool = @import("resolver/BodyPool.zig");
const Scopes = @import("resolver/Scopes.zig");
const Doctor = @import("resolver/Doctor.zig");
const Interpreter = @import("resolver/Interpreter.zig");
const Inits = @import("resolver/checker/Inits.zig");
const decls = @import("resolver/checker/decls.zig");
const exprs = @import("resolver/checker/exprs.zig");
const calls = @import("resolver/checker/calls.zig");
const generics = @import("resolver/checker/generics.zig");

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
//
// who does what:
//   - the resolver owns the state, runs the phases s1..s4 and keeps the node tables
//   - every part answers about its own data only: `syntax` reads the tree, `Scopes` maps names to declarations,
//     the pools hold names, declarations, static values and types, type vars and checked bodies, `Doctor` the reports
//   - checker/ holds the rules, a module per part of the language, `exprs.h09_check_expr` walks into them
//   - the interpreter evaluates what is static whenever the checker asks
//
// future:
//   - multithreading: bodies are independent once signatures are ready - check them on worker
//     threads with their own type vars and diagnostics, decl states become atomics
//   - incremental: hash every top-level declaration's tokens, reuse results of unchanged ones

pub const Stmt = struct {
    node: ParseTree.NodeId, // actual parent, e.g. the unwrapper assignment parent node

    // all other of these fields may be fully unset:
    flags: DeclPool.Entry.Flags,
    kind: DeclPool.Entry.Kind,
    type: ParseTree.NodeId,
    assignees: []const ParseTree.NodeId,
    values: []const ParseTree.NodeId,

    pub fn from_node(res: *const Resolver, n0: ParseTree.NodeId) Stmt {
        var flags = DeclPool.Entry.Flags{};

        // assignments are possibly with modifiers, which must be unpacked and put into flags
        const non_assignmoded_root = blk: {
            var n = n0;
            outer: while (true) : (n = res.tree.arg(n, 0)) switch (res.tree.kind(n)) {
                .mod_pub => flags.is_pub = true,
                .mod_mut => flags.is_mut = true,
                .mod_stc => flags.is_stc = true,
                else => break :outer,
            };
            break :blk n;
        };

        var stmt_type: ParseTree.NodeId = 0;
        var stmt_value: ParseTree.NodeId = 0;
        var stmt_ids: []const ParseTree.NodeId = &.{};

        switch (res.tree.kind(non_assignmoded_root)) {
            .def_var => {
                const def_var_ch = res.tree.laidout_children(.def_var, non_assignmoded_root);
                stmt_type = def_var_ch.type;
                stmt_ids = if (res.tree.kind(def_var_ch.identifier) == .partial__destructure) res.tree.manychildren(def_var_ch.identifier) else res.tree.arg_ptr(non_assignmoded_root, 1)[0..1];
            },
            .assign_typed => {
                const assign_typed_ch = res.tree.laidout_children(.assign_typed, non_assignmoded_root);
                const def_var_ch = res.tree.laidout_children(.def_var, assign_typed_ch.def_var);
                stmt_value = assign_typed_ch.assigned;
                stmt_type = res.tree.arg(assign_typed_ch.def_var, 0);
                stmt_ids = if (res.tree.kind(def_var_ch.identifier) == .partial__destructure) res.tree.manychildren(def_var_ch.identifier) else res.tree.arg_ptr(assign_typed_ch.def_var, 1)[0..1];
            },
            .assign => {
                const assign_ch = res.tree.laidout_children(.assign, non_assignmoded_root);
                stmt_value = res.tree.arg(non_assignmoded_root, 1);
                stmt_ids = if (res.tree.kind(assign_ch.assignee) == .partial__destructure) res.tree.manychildren(assign_ch.assignee) else res.tree.arg_ptr(non_assignmoded_root, 0)[0..1];
            },
            else => {},
        }

        const decl_id = if (stmt_ids.len == 1) res.node_decl[stmt_ids[0]] else .none;
        const place = stmt_ids.len == 1 and res.tree.kind(stmt_ids[0]) != .identifier and res.tree.kind(stmt_ids[0]) != .identifier_self;
        const assigns = stmt_type == 0 and (place or decl_id != .none and !res.decl_pool.kinds()[@intFromEnum(decl_id)].is_fn());

        var values: []const ParseTree.NodeId = &.{};
        if (stmt_value != 0) {
            const r_ch = res.tree.arg(non_assignmoded_root, 1);
            values = if (res.tree.kind(r_ch) == .partial__assign_multival) res.tree.manychildren(r_ch) else res.tree.arg_ptr(non_assignmoded_root, 1)[0..1];
        }

        return .{
            .node = non_assignmoded_root,
            .flags = flags,
            .kind = if (assigns) .variable else syntax.decl_kind(res.tree, stmt_type, stmt_value),
            .type = stmt_type,
            .assignees = stmt_ids,
            .values = values,
        };
    }

    pub fn is_member(s: Stmt) bool {
        return s.assignees.len == 1 and s.kind.is_fn();
    }

    pub fn declares(s: Stmt) bool {
        return s.type != 0 or s.flags.any() or s.kind != .variable;
    }
};

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
// emitted by `Parser`
roots: []const ParseTree.NodeId,

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
// brk and cont seen so far: a loop without a brk never ends, one without either yields one element per step
jumps: [2]u32 = .{ 0, 0 },
deferrals: u32 = 0,

// stores which nodes have something to report (e.g. warning or error)
// - a single report does not stop resolving
doc: Doctor,

// "static" (compiletime) evaluation of what's static
interpreter: Interpreter,

// buffers that live while one top-level declaration is checked
temp: std.heap.ArenaAllocator,

pub inline fn init(alloc: std.mem.Allocator, tree: *ParseTree, src_bytes: []const u8, roots: []const ParseTree.NodeId) Resolver {
    return Resolver{
        .alloc = alloc,
        .tree = tree,
        .src_bytes = src_bytes,
        .roots = roots,
        .name_pool = .init(alloc),
        .static_pool = .init(alloc),
        .abstract_pool = .init(alloc),
        .decl_pool = .init(alloc, 4096),
        .node_type = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_decl = alloc.alloc(DeclPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_value = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .bodies = .init(alloc),
        .scopes = .init(alloc),
        .inits = .init(alloc),
        .doc = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .init(alloc),
        .temp = .init(alloc),
    };
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
    self.temp.deinit();

    self.alloc.free(self.node_type);
    self.alloc.free(self.node_decl);
    self.alloc.free(self.node_value);
}

pub inline fn resolve(self: *Resolver) !void {
    self.s1_collect_globals();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;

    self.s2_check_globals();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;

    self.s3_apply_inferred_types();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;

    self.s4_check_entry_point();
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;
}

fn s1_collect_globals(self: *Resolver) void {
    @memset(self.node_type, .none);
    @memset(self.node_decl, .none);
    @memset(self.node_value, .none);

    self.name_pool.intern_predefineds();
    _ = self.inits.new();

    for (self.roots) |root| {

        // every root is assumed to be a "statement", but statements did not exist up until now,
        //   as statements were expressions aswell in the `Parser`
        const s: Stmt = Stmt.from_node(self, root);

        var flags = s.flags;
        flags.is_global = true;
        const declares = s.declares();

        for (s.assignees) |assignee_id| {
            // possibly not an identifier, therefore `continue` for `.none`
            const name = self.name_pool.name_of(self.tree, self.src_bytes, assignee_id);
            if (name == .none) continue;

            const gop = self.scopes.globals.getOrPut(self.alloc, name) catch @panic("OOM");
            const name_has_decl = gop.found_existing;

            // if the name is declared and not a new function overload -> duplicate decl error
            if (name_has_decl and !(s.kind.is_fn() and self.decl_pool.kinds()[@intFromEnum(gop.value_ptr.*)].is_fn())) {
                if (declares) {
                    _ = self.report(.duplicate_declaration, assignee_id, name, gop.value_ptr.*);
                    if (self.node_decl[root] == .none) self.node_decl[root] = gop.value_ptr.*;
                }
                continue;
            }

            const new_decl = self.decl_pool.push_decl(name, s.node, s.kind, .none, flags);

            // overloads with a where clause come before the ones without, so every group of same-typed
            // overloads reads as a runtime dispatch: its where-clauses in order, the where-less fallback last
            if (gop.found_existing) {
                var at = gop.value_ptr;
                while (at.* != .none and (!calls.has_where(self, new_decl) or calls.has_where(self, at.*))) at = &self.decl_pool.next_overloads()[@intFromEnum(at.*)];
                self.decl_pool.next_overloads()[@intFromEnum(new_decl)] = at.*;
                at.* = new_decl;
            } else gop.value_ptr.* = new_decl;
            self.node_decl[assignee_id] = new_decl;
            if (self.node_decl[root] == .none) self.node_decl[root] = new_decl;
        }
    }
}

fn s2_check_globals(self: *Resolver) void {
    const count = self.decl_pool.entries.len();
    for (0..count) |i| {
        decls.h05_ensure_signature(self, @enumFromInt(i));
        decls.h06_check_body(self, @enumFromInt(i));
        _ = self.temp.reset(.retain_capacity);
    }
    var ctx = FnCtx{};
    for (self.roots) |root| if (self.node_decl[root] == .none) {
        _ = exprs.h09_check_expr(self, &ctx, root, .none);
    };
    calls.check_groups(self);
}

fn s3_apply_inferred_types(self: *Resolver) void {
    if (self.abstract_pool.count() == 0) return;
    const sp = &self.static_pool;
    for (self.decl_pool.entries.sliced_field(.ty), 0..) |t, i| if (t != .none and sp.has_vars(t)) {
        const at = sp.apply_vars(&self.abstract_pool, t);
        if (sp.open_type_var(at) and !generics.length_generic(self, at)) _ = self.report(.uninferable_type, self.decl_pool.nodes()[i], at, .none);
    };
    // lengths nothing fixed are only known at runtime; a loop value then needs its element count at loop entry
    const vs = self.abstract_pool.pool.sliced();
    const group = self.alloc.alloc(ParseTree.NodeId, vs.parent.len) catch @panic("OOM");
    defer self.alloc.free(group);
    @memset(group, ParseTree.none_node);
    for (0..vs.parent.len) |i| {
        const root = @intFromEnum(self.abstract_pool.find(@enumFromInt(i)));
        if (vs.binding[root] != .none) continue;
        const origin = vs.origin[i];
        const k = self.tree.kind(origin);
        const counted = switch (k) {
            .for_seq, .for_var_in_seq => blk: {
                const f = if (k == .for_var_in_seq) self.tree.arg(origin, 0) else origin;
                const seq = self.tree.arg(f, 0);
                const st = sp.deref(&self.abstract_pool, sp.apply_vars(&self.abstract_pool, self.node_type[seq]));
                break :blk if (syntax.props(self.tree.kind(seq)).range) self.tree.kind(seq) != .gen_lowerbound else st != .none and sp.tag(sp.pointee(st)) == .array_type;
            },
            .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => false,
            .type_array_unlengthed, .array_index, .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => true,
            else => continue,
        };
        if (group[root] == ParseTree.none_node or !counted) group[root] = if (counted) 0 else origin;
    }
    for (group, 0..) |g, i| if (g != ParseTree.none_node) {
        if (g != 0) _ = self.report(.uninferable_type, g, sp.apply_vars(&self.abstract_pool, self.node_type[g]), .none);
        self.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len);
    };
    for ([_][]StaticPool.Index{ self.node_type, self.decl_pool.entries.sliced_field(.ty) }) |ts| for (ts) |*t| if (t.* != .none and sp.has_vars(t.*)) {
        t.* = sp.apply_vars(&self.abstract_pool, t.*);
    };
}

fn s4_check_entry_point(self: *Resolver) void {
    const main = self.scopes.globals.get(.main) orelse return self.doc.h21_report(.missing_main, 0, 0, 0);
    const node = self.decl_pool.nodes()[@intFromEnum(main)];
    if (self.decl_pool.next_overloads()[@intFromEnum(main)] != .none) return self.doc.h21_report(.duplicate_declaration, self.decl_pool.nodes()[@intFromEnum(self.decl_pool.next_overloads()[@intFromEnum(main)])], NamePool.Index.main, main);
    const ty = self.decl_pool.tys()[@intFromEnum(main)];
    const sp = &self.static_pool;
    const ok = ty != .none and sp.tag(ty) == .function_type and blk: {
        const f = sp.get(ty).function_type;
        const args_ok = f.params.len == 0 or (f.params.len == 2 and sp.get_tag_prop(f.params[0]).is_integer and sp.get_tag_prop(f.params[1]).is_pointer);
        break :blk args_ok and (f.ret == .unit_type or f.ret == .runit_type or f.ret == .never_type or sp.get_tag_prop(f.ret).is_integer);
    };
    if (!ok) _ = self.report(.type_mismatch, node, ty, .none);
}

pub fn scratch(self: *Resolver, comptime T: type, n: usize) []T {
    return self.temp.allocator().alloc(T, n) catch @panic("OOM");
}

pub inline fn set(self: *Resolver, n: ParseTree.NodeId, t: StaticPool.Index) StaticPool.Index {
    self.node_type[n] = t;
    return t;
}

pub fn report(self: *Resolver, code: Doctor.Disorder, n: ParseTree.NodeId, a: anytype, b: anytype) StaticPool.Index {
    self.doc.h21_report(code, n, a, b);
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
