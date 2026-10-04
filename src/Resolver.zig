const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const ParseTree = @import("ParseTree.zig");

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const Doctor = @import("resolver/Doctor.zig");
const Interpreter = @import("resolver/Interpreter.zig");
const AbstractPool = @import("resolver/AbstractPool.zig");

const Resolver = @This();
const calls = @import("resolver/checker/calls.zig");
const control = @import("resolver/checker/control.zig");
const types = @import("resolver/checker/types.zig");
const statics = @import("resolver/checker/statics.zig");

pub const same_params = calls.same_params;
pub const bind_args = calls.bind_args;
pub const payload_of = control.payload_of;
pub const h07_lower_type = types.h07_lower_type;
pub const static_type = types.static_type;
pub const cast_target = types.cast_target;
pub const literal_value = statics.literal_value;
pub const retype = statics.retype;
pub const h20_instantiate = statics.h20_instantiate;
pub const is_template = statics.is_template;
pub const length_generic = statics.length_generic;
pub const generic_slot = statics.generic_slot;
pub const templated = statics.templated;
pub const realizes = statics.realizes;
pub const holds_template = statics.holds_template;

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
//     filled by unification later (see type_system.zig, section 4). one final sweep replaces
//     every var by its result, and is skipped entirely when no var was ever created.
//   - nothing the parse tree already has is copied (defaults, where-clauses, field names are
//     read from the tree when needed). side tables only hold what is computed.
//
// future:
//   - multithreading: bodies are independent once signatures are ready - check them on worker
//     threads with their own type vars and diagnostics, decl states become atomics
//   - incremental: hash every top-level declaration's tokens, reuse results of unchanged ones

pub const Body = struct {
    decl: DeclPool.Index = .none,
    lo: ParseTree.NodeId = 0,
    len: u32 = 0,
    start: u32 = 0,
    first: u32 = 0,
    locals: u32 = 0,
};

pub const Param = struct {
    ty: ParseTree.NodeId = 0,
    name: ParseTree.NodeId = 0,
    default: ParseTree.NodeId = 0,
    where: ParseTree.NodeId = 0,
    @"else": ParseTree.NodeId = 0,
    is_mut: bool = false,
    stc: bool = false,

    // TODO: res should be removed from here, as only tree is needed
    pub fn from_node(res: *const Resolver, n0: ParseTree.NodeId) Param {
        var p = Param{};
        var n = n0;
        while (true) {
            switch (res.tree.kind(n)) {
                .partial__fun_def_param_named, .partial__type_def_param_named => p.name = res.tree.arg(n, 1),
                .partial__fun_def_param_default, .partial__type_def_param_default => p.default = res.tree.arg(n, 1),
                .partial__fun_def_param_where, .partial__type_def_param_where => p.where = res.tree.arg(n, 1),
                .partial__fun_def_param_stcwhere => {
                    p.where = res.tree.arg(n, 1);
                    p.stc = true;
                },
                .partial__fun_def_param_where_else, .partial__type_def_param_where_else => p.@"else" = res.tree.arg(n, 1),
                .partial__type_def_param_mut => p.is_mut = true,
                .partial__fun_def_param, .partial__type_def_param => {
                    p.ty = res.tree.arg(n, 0);
                    return p;
                },
                else => {
                    p.ty = n;
                    return p;
                },
            }
            n = res.tree.arg(n, 0);
        }
    }
};

const Access = enum {
    ok,
    immutable,
    through_ptr,
};

pub const Def = struct {
    core: ParseTree.NodeId,
    body: ParseTree.NodeId = 0,
    size: ParseTree.NodeId = 0,
    tagof: ParseTree.NodeId = 0,
};

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
        const assigns = stmt_type == 0 and decl_id != .none and !res.decl_pool.kinds()[@intFromEnum(decl_id)].is_fn();

        var values: []const ParseTree.NodeId = &.{};
        if (stmt_value != 0) {
            const r_ch = res.tree.arg(non_assignmoded_root, 1);
            values = if (res.tree.kind(r_ch) == .partial__assign_multival) res.tree.manychildren(r_ch) else res.tree.arg_ptr(non_assignmoded_root, 1)[0..1];
        }

        return .{
            .node = non_assignmoded_root,
            .flags = flags,
            .kind = if (assigns) .variable else res.decl_kind(stmt_type, stmt_value),
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

pub const Loop = struct {
    cond: ParseTree.NodeId = 0,
    repeat: ParseTree.NodeId = 0,
    head: ParseTree.NodeId = 0,
    seq: ParseTree.NodeId = 0,
    variable: ParseTree.NodeId = 0,
    body: ParseTree.NodeId,
};

pub const Range = struct {
    lo: ParseTree.NodeId,
    hi: ParseTree.NodeId,
    incl: bool,
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

pub const NodeProperties = packed struct(u8) {
    stc: bool = false,
    loop: bool = false,
    range: bool = false,
    type_expr: bool = false,
    declares: bool = false,
    runit: bool = false,
    literal: bool = false,
    _pad: u1 = 0,
};

// TODO WATCH: sollte in ein eigenes "TreeData" für den Res.

pub const node_props = blk: {
    var t: [256]NodeProperties = @splat(.{});

    for ([_]ParseTree.Node.Kind{
        .stcif_then,
        .stcif_else,
        .stcwhile,
        .stcwhile_with_repeat_stmt,
        .stcfor_seq,
        .stcfor_var_in_seq,
        .stcloop,
        .stcloop_with_repeat_stmt,
        .stcmatch,
    }) |k| t[@intFromEnum(k)].stc = true;

    for ([_]ParseTree.Node.Kind{
        .@"while",
        .while_with_repeat_stmt,
        .stcwhile,
        .stcwhile_with_repeat_stmt,
        .for_seq,
        .for_var_in_seq,
        .stcfor_seq,
        .stcfor_var_in_seq,
        .loop,
        .loop_with_repeat_stmt,
        .stcloop,
        .stcloop_with_repeat_stmt,
    }) |k| t[@intFromEnum(k)].loop = true;

    for ([_]ParseTree.Node.Kind{
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
    }) |k| t[@intFromEnum(k)].range = true;

    for (@intFromEnum(ParseTree.Node.Kind.type_ptrmut)..@intFromEnum(ParseTree.Node.Kind.type_stcfun) + 1) |i| t[i].type_expr = true;

    for ([_]ParseTree.Node.Kind{
        .type_array,
        .type_array_unlengthed,
        .def_fun_declaration,
        .typeof,
    }) |k| t[@intFromEnum(k)].type_expr = true;

    for ([_]ParseTree.Node.Kind{
        .def_var,
        .assign,
        .assign_typed,
        .mod_pub,
        .mod_mut,
        .mod_stc,
    }) |k| t[@intFromEnum(k)].declares = true;

    for ([_]ParseTree.Node.Kind{
        .block,
        .if_then,
        .if_else,
        .stcif_then,
        .stcif_else,
        .match,
        .stcmatch,
    }) |k| t[@intFromEnum(k)].runit = true;

    for ([_]ParseTree.Node.Kind{
        .int,
        .float,
        .char,
        .string,
    }) |k| t[@intFromEnum(k)].literal = true;

    break :blk t;
};

// per-body state that would otherwise be globals. lives on the machine stack while a body is checked
pub const EphemeralNodeInfo = struct {
    ty: StaticPool.Index,
    decl: DeclPool.Index,
    value: StaticPool.Index,
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

// placeholders for types not known yet and what they turned out to be. see type_system.zig.
abstract_pool: AbstractPool,

decl_pool: DeclPool,

// the two results, one slot per parse tree node, indexed by ParseTree.NodeId.
// plain arrays of u32: 8 bytes per node in total, and the lowerer reads them with no indirection.
node_type: []StaticPool.Index,
node_decl: []DeclPool.Index,
node_value: []StaticPool.Index,
bodies: SoD(Body),
body_nodes: SoD(EphemeralNodeInfo),
body_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
template_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
realized_args: std.AutoHashMapUnmanaged(DeclPool.Index, StaticPool.Index) = .empty,
// functions produced by a stcfun: the realization whose static parameters they see
static_scope: std.AutoHashMapUnmanaged(DeclPool.Index, StaticPool.AbstractKey) = .empty,
init_tracked: DynBuf(DeclPool.Index),
uninit: u64 = 0,
deferrals: u32 = 0,
// brk and cont seen so far: a loop without a brk never ends, one without either yields one element per step
jumps: [2]u32 = .{ 0, 0 },
loop_exits: DynBuf(u64),

// global names -> first declaration with that name
// - overloads of the same name handled by `decls.next_overload` for single per-name entry
// - solves: using global before declaring it in a file
global_decls: std.AutoHashMapUnmanaged(NamePool.Index, DeclPool.Index),

// the local scope stack. declaring a local pushes (name, decl); a lookup scans `local_names`
// backwards, so the innermost declaration wins and shadowing works for free.
// names and decls are two parallel arrays so the scan reads only a dense run of u32 names -
// for the few dozen locals a body has, that beats any hash map and vectorizes well.
local_names: DynBuf(NamePool.Index),
local_decls: DynBuf(DeclPool.Index),
// where each open scope starts in the local stack. leaving a scope just truncates the stack
// back to its mark - freeing all its locals at once costs one store.
local_scope_marks: DynBuf(u32),

// stores which nodes have something to report (e.g. warning or error)
// - a single report does not stop resolving
doc: Doctor,

// "static" (compiletime) evaluation of what's static
interpreter: Interpreter,

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
        .bodies = .init(alloc, 256),
        .body_nodes = .init(alloc, 4096),
        .init_tracked = .init(alloc, 64),
        .loop_exits = .init(alloc, 16),
        .global_decls = .empty,
        .local_names = .init(alloc, 256),
        .local_decls = .init(alloc, 256),
        .local_scope_marks = .init(alloc, 16),
        .doc = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .init(alloc),
    };
}

pub inline fn deinit(self: *Resolver) void {
    self.name_pool.deinit();
    self.static_pool.deinit();
    self.abstract_pool.deinit();
    self.decl_pool.deinit();
    self.bodies.deinit();
    self.body_nodes.deinit();
    self.interpreter.deinit();
    self.init_tracked.deinit();
    self.loop_exits.deinit();
    self.local_names.deinit();
    self.local_decls.deinit();
    self.local_scope_marks.deinit();
    self.doc.diagnostics.deinit();

    self.body_of.deinit(self.alloc);
    self.template_of.deinit(self.alloc);
    self.realized_args.deinit(self.alloc);
    self.static_scope.deinit(self.alloc);
    self.global_decls.deinit(self.alloc);

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

            const gop = self.global_decls.getOrPut(self.alloc, name) catch @panic("OOM");
            const name_has_decl = gop.found_existing;

            // if the name is declared and not a new function overload -> duplicate decl error
            if (name_has_decl and !(s.kind.is_fn() and self.decl_pool.kinds()[@intFromEnum(gop.value_ptr.*)].is_fn())) {
                if (declares) {
                    _ = self.report(.duplicate_declaration, assignee_id, name, gop.value_ptr.*);
                    if (self.node_decl[root] == .none) self.node_decl[root] = gop.value_ptr.*;
                }
                continue;
            }

            // TODO NEXT
            const new_decl = self.push_decl(name, s.node, s.kind, .none, flags);

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
        self.h05_ensure_signature(@enumFromInt(i));
        self.h06_check_body(@enumFromInt(i));
    }
    var ctx = FnCtx{};
    for (self.roots) |root| if (self.node_decl[root] == .none) {
        _ = self.h09_check_expr(&ctx, root, .none);
    };
    // overloads that differ only by where clauses dispatch at runtime and need a where-less fallback
    var heads = self.global_decls.valueIterator();
    while (heads.next()) |h| {
        var c = h.*;
        while (c != .none) : (c = self.decl_pool.next_overloads()[@intFromEnum(c)]) {
            if (self.group_head(h.*, c) != c) continue;
            var size: u32 = 0;
            var fallback = false;
            var m = c;
            while (m != .none) : (m = self.decl_pool.next_overloads()[@intFromEnum(m)]) if (calls.same_params(self, m, c)) {
                size += 1;
                fallback = fallback or !calls.dispatches(self, self.real(m));
            };
            if (size > 1 and !fallback) _ = self.report(.no_matching_overload, self.decl_pool.nodes()[@intFromEnum(c)], size, 0);
        }
    }
}

fn s3_apply_inferred_types(self: *Resolver) void {
    if (self.abstract_pool.count() == 0) return;
    const sp = &self.static_pool;
    for (self.decl_pool.entries.sliced_field(.ty), 0..) |t, i| if (t != .none and sp.has_vars(t)) {
        const at = sp.apply_vars(&self.abstract_pool, t);
        if (statics.open_type_var(self, at) and !statics.length_generic(self, at)) _ = self.report(.uninferable_type, self.decl_pool.nodes()[i], at, .none);
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
                const st = self.deref(sp.apply_vars(&self.abstract_pool, self.node_type[seq]));
                break :blk (is_range_kind(self.tree.kind(seq)) and self.tree.kind(seq) != .gen_lowerbound) or (st != .none and sp.tag(st) == .array_type) or control.is_ptr_array(self, self.node_type[seq]);
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
    const main = self.global_decls.get(.main) orelse return self.doc.h21_report(.missing_main, 0, 0, 0);
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

// ------------------------------------------------------------------------------------------ //
// scopes and names
// ------------------------------------------------------------------------------------------ //

pub fn h01_lookup(self: *Resolver, name: NamePool.Index) DeclPool.Index {
    const names = self.local_names.sliced();
    var i = names.len;
    while (i > 0) {
        i -= 1;
        if (names[i] == name) return self.local_decls.buf[i];
        if (names[i] == .none) break; // barrier: a declaration body never sees its user's locals
    }
    return self.global_decls.get(name) orelse .none;
}

pub fn use(self: *Resolver, node: ParseTree.NodeId) DeclPool.Index {
    const name = self.name_pool.name_of(self.tree, self.src_bytes, node);
    const d = self.h01_lookup(name);
    if (d == .none) {
        _ = self.report(.undefined_name, node, name, 0);
        return d;
    }
    self.node_decl[node] = d;
    self.h05_ensure_signature(d);
    return d;
}

pub fn h02_declare_local(self: *Resolver, name: NamePool.Index, node: ParseTree.NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index) DeclPool.Index {
    const d = self.push_decl(name, node, kind, ty, .{});
    self.local_names.push(name);
    self.local_decls.push(d);
    return d;
}

pub fn h03_push_scope(self: *Resolver) void {
    self.local_scope_marks.push(self.local_names.head);
}

pub fn h04_pop_scope(self: *Resolver) void {
    self.local_scope_marks.head -= 1;
    self.local_names.head = self.local_scope_marks.buf[self.local_scope_marks.head];
    self.local_decls.head = self.local_names.head;
}

// ------------------------------------------------------------------------------------------ //
// declarations
// ------------------------------------------------------------------------------------------ //

pub fn h05_ensure_signature(self: *Resolver, decl: DeclPool.Index) void {
    const state = &self.decl_pool.states()[@intFromEnum(decl)];
    switch (state.*) {
        .unresolved => {},
        .resolving_signature => {
            _ = self.report(.declaration_cycle, self.decl_pool.nodes()[@intFromEnum(decl)], self.decl_pool.names()[@intFromEnum(decl)], 0);
            state.* = .failed;
            return;
        },
        else => return,
    }
    state.* = .resolving_signature;
    const sp = &self.static_pool;
    const kind = self.decl_pool.kinds()[@intFromEnum(decl)];
    const s = Stmt.from_node(self, self.decl_pool.nodes()[@intFromEnum(decl)]);
    if (s.type != 0 and self.tree.kind(s.type) == .type_fun and switch (self.decl_pool.names()[@intFromEnum(decl)]) {
        .init, .deinit, .main, .has_next, .next => true,
        else => false,
    }) _ = self.report(.redundant_fun, s.type, 0, 0);
    const flags = self.decl_pool.flags()[@intFromEnum(decl)];
    var ctx = FnCtx{ .decl = decl, .self_type = self.owner_of(decl), .in_static = flags.is_stc };
    const v = self.value_node(decl);
    self.open_scope(flags.is_global, if (self.self_off(decl) == 1) ctx.self_type else .none, v);
    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => if (self.tree.kind(v) == .def_fun or self.tree.kind(v) == .def_fun_declaration) {
            // stcfun: the first tuple is static, whatever the body produces is the result (a second tuple belongs to the produced function)
            const unit = self.tree.arg(v, 1);
            const tk = self.template(decl);
            const uk = self.type_kind(unit);
            if (kind == .static_function and tk == .variable and uk != .variable) _ = self.report(.missing_ret, unit, 0, 0);
            const res = if (self.tree.kind(unit) == .ret) self.tree.arg(unit, 0) else unit;
            const ret: StaticPool.Index = if (kind == .static_function)
                meta(self.type_kind(res), if (self.tree.kind(res) == .def_fun or self.tree.kind(res) == .def_fun_declaration) .fun_type else .poison_type)
            else if (self.tree.kind(v) == .def_fun_declaration or self.tree.kind(self.tree.arg(v, 0)) == .partial__fun_def_header_ret) .unit_type else self.fresh_var(v);
            if (tk != .variable and uk == .variable) {
                _ = self.report(.redundant_ret, unit, 0, 0);
            } else if (tk != .variable and uk != tk) _ = self.report(.type_mismatch, unit, ret, meta(tk, .trait_type));
            const category: StaticPool.FunType.Category = switch (kind) {
                .static_function => .static,
                .inlined_function => .inlined,
                else => .default,
            };
            // a method's first parameter is the induced `*Self`, `init` constructs and has none
            self.decl_pool.tys()[@intFromEnum(decl)] = types.fun_type(self, &ctx, v, category, ret, if (self.self_off(decl) == 1) self.self_ptr(ctx.self_type) else .none);
            if (flags.is_global and self.decl_pool.names()[@intFromEnum(decl)] == .main) self.decl_pool.tys()[@intFromEnum(decl)] = types.dynify(self, self.decl_pool.tys()[@intFromEnum(decl)]);
            self.decl_pool.values()[@intFromEnum(decl)] = if (kind == .static_function)
                sp.intern(.{ .static_fun = .{ .decl = decl, .result_kind = if (sp.tag(ret) == .meta_type) sp.get(ret).meta_type else .stcfun } })
            else
                sp.intern(.{ .function = decl });
        } else {
            // a function produced by a static expression (`fun sub_from_templ = my_templ(i32, false)`)
            const fv = statics.h08_eval_static(self, &ctx, v);
            if (sp.tag(fv) == .function_value) {
                self.decl_pool.values()[@intFromEnum(decl)] = fv;
                self.decl_pool.tys()[@intFromEnum(decl)] = self.decl_pool.tys()[@intFromEnum(sp.get(fv).function)];
            } else if (fv != .poison_type) _ = self.report(.type_mismatch, v, sp.type_of(fv), .fun_type);
        },
        .record, .variant, .trait => _ = types.h19_check_type_def(self, &ctx, decl, v),
        .type_alias => {
            const t = types.h07_lower_type(self, &ctx, v);
            self.decl_pool.values()[@intFromEnum(decl)] = t;
            self.decl_pool.tys()[@intFromEnum(decl)] = sp.type_of(t);
        },
        else => _ = self.h11_check_assign(&ctx, self.decl_pool.nodes()[@intFromEnum(decl)]),
    }
    self.h04_pop_scope();
    if (self.decl_pool.states()[@intFromEnum(decl)] == .resolving_signature) self.decl_pool.states()[@intFromEnum(decl)] = .signature_ready;
}

pub fn h06_check_body(self: *Resolver, decl: DeclPool.Index) void {
    const state = &self.decl_pool.states()[@intFromEnum(decl)];
    if (state.* != .signature_ready) return;
    const sp = &self.static_pool;
    const kind = self.decl_pool.kinds()[@intFromEnum(decl)];
    const v = self.value_node(decl);
    const ty = self.decl_pool.tys()[@intFromEnum(decl)];
    // stcfun bodies are checked per realization, length-generic ones per length (h20); `main` is realized once, by the runtime
    const generic = statics.length_generic(self, ty) and !self.template_of.contains(decl);
    const abstract = generic and statics.only_templates(self, ty);
    if (kind == .static_function or !kind.is_fn() or self.tree.kind(v) != .def_fun or generic and !abstract) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;
    const first = self.decl_pool.entries.len();
    const mark = self.doc.diagnostics.len();
    const outer = self.init_enter();
    defer self.init_leave(outer.tracked, outer.uninit);
    // a local function sees which enclosing locals are not written yet
    if (kind == .function and !self.decl_pool.flags()[@intFromEnum(decl)].is_global) self.uninit = outer.uninit;
    const off = self.self_off(decl);
    var ctx = FnCtx{ .decl = decl, .ret_type = sp.get(ty).function_type.ret, .self_type = self.owner_of(decl), .abstract = abstract };
    self.open_scope(self.decl_pool.flags()[@intFromEnum(decl)].is_global, if (off == 1) ctx.self_type else .none, v);
    const g = self.template_of.get(decl);
    const args = self.realized_args.get(decl);
    const view = if (g) |t| !statics.only_templates(self, self.decl_pool.tys()[@intFromEnum(t)]) else false;
    // a where clause sees its own parameter and the ones before it; realized `type` parameters are static values
    var slot: usize = 0;
    for (self.params_of(v), 0..) |pn, i| {
        const p = Param.from_node(self, pn);
        const pt = sp.get(ty).function_type.params[i + off];
        if (p.default != 0) _ = self.check(&ctx, p.default, pt);
        for (self.params_of(v)[0..i], 0..) |q, j| if (self.param_name(q, j) == self.name_at(p, i)) self.doc.h21_report(.duplicate_declaration, pn, self.name_at(p, i), decl);
        const pd = self.h02_declare_local(self.name_at(p, i), pn, .parameter, pt);
        self.node_decl[pn] = pd;
        const gp = if (g) |t| self.sig(t).params[i + off] else pt;
        self.decl_pool.flags()[@intFromEnum(pd)].is_view = view and statics.templated(self, gp) != .none;
        if (args) |a| if (statics.generic_slot(self, gp)) {
            if (sp.tag(gp) == .meta_type) self.decl_pool.values()[@intFromEnum(pd)] = sp.get(a).aggregate.elems[slot];
            slot += 1;
        };
        calls.link(self, p.name, pd, pt);
        self.check_guards(&ctx, p, pt);
    }
    self.check_unit(&ctx, self.tree.arg(v, 1));
    self.h04_pop_scope();
    if (off == 1 and self.decl_pool.flags()[first].writes) self.decl_pool.flags()[@intFromEnum(decl)].writes = true;
    self.decl_pool.states()[@intFromEnum(decl)] = if (self.errors_since(mark, v)) .failed else .done;
    if (!abstract) statics.snapshot(self, decl, v, first);
}

pub fn errors_since(self: *Resolver, mark: usize, v: ParseTree.NodeId) bool {
    const d = self.doc.diagnostics.sliced();
    var s: ?[2]ParseTree.NodeId = null;
    for (d.severity[mark..], d.node[mark..]) |sev, n| if (sev == .@"error") {
        if (s == null) s = self.tree.subtree(v);
        if (n >= s.?[0] and n < s.?[1]) return true;
    };
    return false;
}

pub fn check_unit(self: *Resolver, ctx: *FnCtx, body: ParseTree.NodeId) void {
    const sp = &self.static_pool;
    if (self.tree.kind(body) != .block) {
        _ = self.check(ctx, body, ctx.ret_type);
        return;
    }
    const t = self.h09_check_expr(ctx, body, .none);
    const r = sp.apply_vars(&self.abstract_pool, ctx.ret_type);
    // a `{}` body that never returns a value returns unit, a body with a result returns it on every path (`$main` falls off with 0)
    if (r != .none and sp.tag(r) == .type_var) _ = sp.unify(&self.abstract_pool, ctx.ret_type, .unit_type) else if (r != .none and (ctx.decl == .none or self.decl_pool.names()[@intFromEnum(ctx.decl)] != .main) and r != .unit_type and r != .runit_type and r != .poison_type and t != .never_type and t != .poison_type and !self.doc.has(body)) _ = self.report(.missing_ret, body, 0, 0);
}

pub const prim_types = blk: {
    var t: [256]StaticPool.Index = @splat(.none);
    for (@typeInfo(StaticPool.Index).@"enum".fields) |f| if (std.mem.endsWith(u8, f.name, "_type") and @hasField(ParseTree.Node.Kind, "type_" ++ f.name[0 .. f.name.len - 5])) {
        t[@intFromEnum(@field(ParseTree.Node.Kind, "type_" ++ f.name[0 .. f.name.len - 5]))] = @enumFromInt(f.value);
    };
    break :blk t;
};

// ------------------------------------------------------------------------------------------ //
// expressions
// ------------------------------------------------------------------------------------------ //

// scalars declared without a value must be written before they are read: `uninit` has one bit per such local,
// branches merge their bits, loops leave with the union of the states at their exits
pub fn h09_check_expr(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const ap = &self.abstract_pool;
    const a0 = self.tree.arg(node, 0);
    const a1 = self.tree.arg(node, 1);
    const k = self.tree.kind(node);
    if (ctx.interpreted and node_props[@intFromEnum(k)].stc and !self.doc.has(node)) _ = self.report(.redundant_stc, node, 0, 0);
    const t: StaticPool.Index = switch (k) {
        .int, .float, .char, .string, .boolean_true, .boolean_false => statics.literal_type(self, node, expected),
        .identifier, .identifier_self => blk: {
            const d = self.use(node);
            if (d == .none) break :blk .poison_type;
            self.check_init(node, d);
            const ty = self.decl_pool.tys()[@intFromEnum(d)];
            break :blk if (ty == .none) .poison_type else ty;
        },
        .capture => self.h09_check_expr(ctx, a0, expected),
        .block => blk: {
            self.h03_push_scope();
            defer self.h04_pop_scope();
            var last: StaticPool.Index = .unit_type;
            const stmts = self.tree.manychildren(node);
            // local functions are visible in their whole block
            for (stmts) |s| {
                const st = Stmt.from_node(self, s);
                if (st.kind != .function or st.assignees.len != 1 or st.type == 0 or self.tree.kind(st.type) != .type_fun) continue;
                const d = self.h02_declare_local(self.name_pool.name_of(self.tree, self.src_bytes, st.assignees[0]), st.node, .function, .none);
                self.decl_pool.flags()[@intFromEnum(d)] = st.flags;
                self.node_decl[st.assignees[0]] = d;
            }
            for (stmts, 0..) |s, i| {
                const declares = node_props[@intFromEnum(self.tree.kind(s))].declares;
                if (!declares) self.h03_push_scope();
                last = self.h09_check_expr(ctx, s, if (i + 1 == stmts.len) expected else .none);
                if (!declares) self.h04_pop_scope();
            }
            break :blk last;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => self.h11_check_assign(ctx, node),
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => blk: {
            const lt = self.h18_check_place(ctx, a0);
            if ((k == .assign_add or k == .assign_sub) and self.elem_ptr(lt)) break :blk if (self.integer(ctx, a1)) .unit_type else .poison_type;
            _ = self.check(ctx, a1, lt);
            break :blk self.numeric(node, lt, .unit_type);
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix => blk: {
            const lt = self.h18_check_place(ctx, a0);
            break :blk if (self.elem_ptr(lt)) lt else self.numeric(node, lt, lt);
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap => blk: {
            const j = self.pair(ctx, node, a0, a1, if (self.is_numeric(expected)) expected else .none);
            const wraps = k == .binary_add_wrap or k == .binary_sub_wrap or k == .binary_mul_wrap;
            const r = if ((k == .binary_add or k == .binary_sub) and self.elem_ptr(j)) j else if (wraps and !sp.get_tag_prop(j).is_integer and sp.tag(j) != .type_var) self.mismatch(node, j, .none) else self.numeric(node, j, j);
            // arithmetic on constants is folded, an overflow is an error as soon as it can be seen
            if (r != .poison_type and !ctx.abstract and self.folded(a0) and self.folded(a1)) {
                _ = self.set(node, r);
                _ = statics.h08_eval_static(self, ctx, node);
            }
            break :blk r;
        },
        .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => blk: {
            const j = self.pair(ctx, node, a0, a1, .none);
            break :blk if (j == .poison_type) j else .bool_type;
        },
        .binary_logic_or, .binary_logic_and => blk: {
            const w = self.condition(ctx, node);
            self.uninit = w[0] | w[1];
            break :blk .bool_type;
        },
        .binary_logic_xor => blk: {
            _ = self.check(ctx, a0, .bool_type);
            _ = self.check(ctx, a1, .bool_type);
            break :blk .bool_type;
        },
        .neg_logic => blk: { // `!` is logical on bools and bitwise on integers
            const st = self.h09_check_expr(ctx, a0, expected);
            break :blk if (st == .bool_type or sp.get_tag_prop(st).is_integer) st else self.mismatch(node, st, .bool_type);
        },
        .neg_num => if (self.is_literal(node)) statics.literal_type(self, node, expected) else self.numeric(node, self.h09_check_expr(ctx, a0, expected), .none),
        .fun_call, .with => calls.h12_check_call(self, ctx, node),
        .member => self.h13_check_member(ctx, node),
        .array_index => blk: {
            var st = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            if (is_range_kind(self.tree.kind(a1))) break :blk self.report(.genexpr_index, a1, 0, 0);
            const it = self.h09_check_expr(ctx, a1, .none);
            if (!sp.get_tag_prop(it).is_integer) _ = self.mismatch(a1, it, .u64_type);
            if (st == .poison_type) break :blk st;
            const through_ptr = sp.is_ptr(st);
            st = sp.pointee(st);
            // pointers index like arrays (`*u8 buf; buf[i]`), arrays auto-deref once
            const elem = if (sp.get(st) == .array_type) sp.get(st).array_type.elem else if (through_ptr) st else break :blk self.report(.type_mismatch, a0, st, .none);
            // lengths of realizations and stcfun bodies are the interpreter's to check, their constant indices may be guarded
            if (!ctx.interpreted and !(ctx.decl != .none and self.template_of.contains(ctx.decl)) and sp.get(st) == .array_type and sp.tag(sp.get(st).array_type.len) == .int_value and self.is_literal(a1)) {
                const i = statics.static_int(self, ctx, a1) orelse break :blk elem;
                if (i < 0 or i >= sp.get(sp.get(st).array_type.len).int.bits) _ = self.report(.static_eval_failed, a1, 0, 0);
            }
            break :blk elem;
        },
        .dereference => blk: {
            const st = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            break :blk if (sp.is_ptr(st)) sp.pointee(st) else self.mismatch(node, st, .none);
        },
        .address_of => blk: {
            if (self.tree.kind(a0) == .identifier) self.uninit &= ~self.init_bit(self.h01_lookup(self.name_pool.name_of(self.tree, self.src_bytes, a0)));
            const exp = sp.apply_vars(ap, expected);
            const st = self.h09_check_expr(ctx, a0, if (sp.is_ptr(exp)) sp.pointee(exp) else .none);
            // write access only to what could be written directly
            const mutable = self.writable(a0) == .ok;
            if (mutable and exp != .none and sp.tag(exp) == .ptr_mut_type) self.wrote(a0);
            break :blk if (st == .poison_type) st else sp.intern(.{ .ptr_type = .{ .child = st, .mutable = mutable } });
        },
        .array, .array_empty => blk: {
            const exp = sp.apply_vars(ap, expected);
            var elem = sp.array_elem(exp);
            const elems = if (k == .array) self.tree.manychildren(node) else &[_]ParseTree.NodeId{};
            for (elems) |e| {
                const et = self.h09_check_expr(ctx, e, elem);
                if (elem == .none) elem = et else _ = self.h10_expect(e, et, elem);
            }
            if (elem == .none) elem = self.fresh_var(node);
            break :blk sp.intern(.{ .array_type = .{ .len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = elems.len } }), .elem = elem } });
        },
        .as => blk: {
            const from = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            const to = types.cast_target(self, ctx, a1, from);
            const lost = to == .poison_type or from == .poison_type or sp.get(to) == .array_type and sp.get(to).array_type.len == .poison_type or sp.get(to) == .ptr_type and sp.get(sp.get(to).ptr_type.child) == .array_type and sp.get(sp.get(to).ptr_type.child).array_type.len == .poison_type;
            break :blk if (lost) .poison_type else if (sp.cast(from, to) == .invalid) self.report(.invalid_cast, node, from, to) else to;
        },
        .asbits => blk: {
            const from = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            const to = types.h07_lower_type(self, ctx, a1);
            if (from == .poison_type or to == .poison_type) break :blk .poison_type;
            break :blk if (!sp.get_tag_prop(from).has_layout or !sp.get_tag_prop(to).has_layout or sp.layout(to).size < sp.layout(from).size) self.report(.invalid_cast, node, from, to) else to;
        },
        .oftype => blk: {
            const vt = self.deref(self.h09_check_expr(ctx, a0, .none));
            const ot0 = if (ctx.interpreted) statics.deferred(self, ctx, a1) orelse .none else types.h07_lower_type(self, ctx, a1);
            const ot = if (ot0 != .none and sp.tag(ot0) == .generic) types.h07_lower_type(self, ctx, a1) else ot0;
            self.node_value[a1] = ot;
            self.node_value[node] = if (ot == .none or (ctx.interpreted and sp.tag(vt) == .meta_type)) .none else if (statics.templated(self, ot) != .none) (if (statics.realizes(self, vt, ot)) .bool_true else .bool_false) else if (statics.templated(self, vt) != .none) .none else if (vt == ot or sp.implements(vt, ot)) .bool_true else if (sp.tag(vt) == .trait_type) .none else .bool_false;
            break :blk .bool_type;
        },
        .typeof, .sizeof => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            if (self.tree.kind(a0) == .identifier and statics.is_template(self, self.node_decl[a0])) break :blk self.report(.unrealized_template, a0, 0, 0);
            _ = statics.try_static(self, ctx, node);
            break :blk if (k == .typeof) .type_type else .u64_type;
        },
        .if_then, .if_else, .stcif_then, .stcif_else => control.h15_check_branching(self, ctx, node, expected),
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => control.h16_check_loop(self, ctx, node, expected),
        // ranges are sequences of their bound type, so `for` and slicing treat them like arrays
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => blk: {
            const exp = sp.apply_vars(ap, expected);
            const e = sp.array_elem(exp);
            var hint = if (e != .none) e else if (self.is_numeric(exp)) exp else .none;
            const g = self.range(node);
            for ([_]ParseTree.NodeId{ g.lo, g.hi }) |x| if (x != 0 and hint != .none and self.is_literal(x) and statics.literal_type(self, x, hint) != hint) {
                hint = .none;
            };
            const b = if (k == .gen_incl or k == .gen_excl) self.pair(ctx, node, a0, a1, hint) else self.operand(ctx, a0, hint);
            if (!sp.get_tag_prop(b).is_integer) break :blk self.mismatch(node, b, .u64_type);
            break :blk sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = b } });
        },
        .match, .stcmatch => control.h14_check_match(self, ctx, node, expected),
        .ret => blk: {
            _ = if (ctx.ret_type == .none) self.h09_check_expr(ctx, a0, .none) else self.check(ctx, a0, ctx.ret_type);
            break :blk .never_type;
        },
        .ret_void => if (ctx.ret_type != .none and sp.coerce(ap, .unit_type, ctx.ret_type) == .incompatible) self.report(.ret_type_mismatch, node, .unit_type, ctx.ret_type) else .never_type,
        .brk, .cont => if (ctx.loop_depth > 0) blk: {
            self.jumps[@intFromBool(k == .cont)] += 1;
            if (k == .brk and self.loop_exits.head > 0) self.loop_exits.buf[self.loop_exits.head - 1] |= self.uninit;
            break :blk .never_type;
        } else self.report(if (k == .brk) .brk_outside_loop else .cont_outside_loop, node, 0, 0),
        .do, .@"defer" => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk if (k == .do) .runit_type else .unit_type;
        },
        .deinit, .inlined_defer_deinit => blk: {
            const st = self.h09_check_expr(ctx, a0, if (k == .deinit) .none else expected);
            self.need_deinit(node, st);
            // a deinitialized local has to be written again before it is read
            if (k == .deinit and self.tree.kind(a0) == .identifier and self.node_decl[a0] != .none and !self.decl_pool.flags()[@intFromEnum(self.node_decl[a0])].is_global) {
                const bit = self.init_bit(self.node_decl[a0]);
                if (bit != 0) self.uninit |= bit else self.track(self.node_decl[a0]);
            }
            break :blk if (k == .deinit) .unit_type else st;
        },
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => control.h17_check_unwrap(self, ctx, node, expected),
        .def_fun => blk: { // lambdas and local functions are checked on the spot and see the enclosing locals
            const d = self.push_decl(.empty, node, .function, .none, .{});
            self.node_decl[node] = d;
            self.h05_ensure_signature(d);
            self.h06_check_body(d);
            break :blk self.decl_pool.tys()[@intFromEnum(d)];
        },
        // type expressions in value position: the value is a type
        else => if (node_props[@intFromEnum(k)].type_expr or k == .unify_variants or self.type_kind(node) != .variable) (if (statics.deferred(self, ctx, node)) |v| sp.type_of(v) else types.meta_of(self, node)) else .unit_type,
    };
    return self.set(node, t);
}

// the locals not written yet when a condition is true and when it is false: `and` runs its right side only after a true left one
pub fn condition(self: *Resolver, ctx: *FnCtx, n: ParseTree.NodeId) [2]u64 {
    const k = self.tree.kind(n);
    if (k == .capture) {
        const w = self.condition(ctx, self.tree.arg(n, 0));
        _ = self.set(n, self.node_type[self.tree.arg(n, 0)]);
        return w;
    }
    if (k != .binary_logic_and and k != .binary_logic_or) {
        _ = self.check(ctx, n, .bool_type);
        return .{ self.uninit, self.uninit };
    }
    const l = self.condition(ctx, self.tree.arg(n, 0));
    self.uninit = l[@intFromBool(k == .binary_logic_or)];
    const r = self.condition(ctx, self.tree.arg(n, 1));
    _ = self.set(n, .bool_type);
    return if (k == .binary_logic_and) .{ r[0], l[1] | r[1] } else .{ l[0] | r[0], r[1] };
}

pub fn h10_expect(self: *Resolver, node: ParseTree.NodeId, actual: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    // a poisoned value settles what it was expected to infer, so the error does not spread
    if (actual == .poison_type and expected != .none and self.static_pool.has_vars(expected)) _ = self.static_pool.unify(&self.abstract_pool, expected, .poison_type);
    if (expected == .none or actual == .poison_type or expected == .poison_type) return actual;
    // literals take the expected type directly (an unbound var: their default, which then binds the var)
    const a = if (self.is_literal(node)) self.set(node, statics.literal_type(self, node, expected)) else actual;
    if (self.static_pool.coerce(&self.abstract_pool, a, expected) != .incompatible) return expected;
    return self.report(if (self.static_pool.unify(&self.abstract_pool, a, expected) == .infinite) .infinite_type else .type_mismatch, node, a, expected);
}

pub fn h11_check_assign(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parts = Stmt.from_node(self, node);
    const n = parts.node;
    const flags = parts.flags;
    const kind = parts.kind;
    if (ctx.interpreted and is_type_decl(kind)) {
        _ = self.h09_check_expr(ctx, parts.values[0], .none);
        const t = statics.deferred(self, ctx, parts.values[0]);
        for (parts.assignees) |id| {
            const d = self.declare(id, n, kind, if (t) |x| sp.type_of(x) else types.meta_of(self, parts.values[0]), flags);
            self.decl_pool.states()[@intFromEnum(d)] = .done;
            self.decl_pool.values()[@intFromEnum(d)] = t orelse .none;
        }
        return .unit_type;
    }
    if (kind == .function and parts.type == 0 and parts.assignees.len == 1) {
        const e = self.h01_lookup(self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]));
        if (e != .none and !self.decl_pool.kinds()[@intFromEnum(e)].is_fn() and self.decl_pool.tys()[@intFromEnum(e)] != .none and sp.tag(sp.apply_vars(&self.abstract_pool, self.decl_pool.tys()[@intFromEnum(e)])) == .function_type) {
            self.node_decl[parts.assignees[0]] = e;
            return self.h11_check_assign(ctx, node);
        }
    }
    if (kind != .variable) { // local function / type / trait
        for (parts.assignees) |id| {
            const d = self.declare(id, n, kind, .none, flags);
            self.h05_ensure_signature(d);
            self.h06_check_body(d);
        }
        return .unit_type;
    }
    const values = parts.values;
    // a write into a place (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    if (parts.assignees.len == 1 and self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]) == .none) {
        const pt = self.h18_check_place(ctx, parts.assignees[0]);
        for (values) |v| _ = self.check(ctx, v, pt);
        return .unit_type;
    }
    const declaring = parts.type != 0 or @as(u8, @bitCast(flags)) != 0;
    var ty: StaticPool.Index = if (parts.type != 0) types.realized_type(self, ctx, parts.type) else .none;
    // untyped: visible names are assigned, their type is shared by the new ones
    var existing: [64]DeclPool.Index = undefined;
    for (parts.assignees, 0..) |id, i| {
        existing[i] = if (declaring or self.pre_declared(self.node_decl[id], n)) .none else self.h01_lookup(self.name_pool.name_of(self.tree, self.src_bytes, id));
        if (existing[i] == .none) continue;
        const outer = self.uninit;
        self.uninit = 0;
        const et = self.h18_check_place(ctx, id);
        self.uninit = outer;
        if (ty == .none) ty = et else if (et != ty and et != .poison_type) _ = self.report(.destructure_type_conflict, id, et, ty);
    }
    self.h03_push_scope();
    if (values.len > 1) {
        var shared = ty;
        for (values, 0..) |v, i| {
            const vt = self.check(ctx, v, if (i < parts.assignees.len and existing[i] != .none) self.decl_pool.tys()[@intFromEnum(existing[i])] else ty);
            if (shared == .none) shared = vt else if (ty == .none) {
                const j = sp.join(&self.abstract_pool, shared, vt);
                shared = if (j.ty == .none) self.report(.destructure_type_conflict, v, shared, vt) else j.ty;
            }
        }
        ty = shared;
    } else if (values.len == 1) {
        // a fresh var as expectation means "a value is wanted" (loops / ifs as values) without fixing its type
        const got = self.check(ctx, values[0], if (ty != .none) ty else self.fresh_var(n));
        if (ty == .none) ty = sp.apply_vars(&self.abstract_pool, got);
        if (ty != .none and sp.tag(ty) == .function_type and statics.holds_template(self, ty)) ty = self.report(.unrealized_template, values[0], ty, 0);
    }
    self.h04_pop_scope();
    for (parts.assignees, 0..) |id, i| {
        const d = if (existing[i] != .none) existing[i] else self.declare(id, n, .variable, if (ty == .none) .poison_type else ty, flags);
        if (existing[i] != .none) self.uninit &= ~self.init_bit(d) else if (values.len == 0 and !self.decl_pool.flags()[@intFromEnum(d)].is_global and self.scalar(self.decl_pool.tys()[@intFromEnum(d)])) self.track(d);
        if (values.len > 0 and self.node_type[values[@min(i, values.len - 1)]] != .poison_type and (existing[i] == .none or (self.interpreter.depth > 0 and !ctx.interpreted)) and (self.decl_pool.flags()[@intFromEnum(d)].is_stc or ctx.in_static)) {
            self.decl_pool.values()[@intFromEnum(d)] = statics.retype(self, statics.static_of(self, ctx, values[@min(i, values.len - 1)]), self.decl_pool.tys()[@intFromEnum(d)]);
            // an unlengthed static takes the length of its value
            const v = self.decl_pool.values()[@intFromEnum(d)];
            if (v != .none and sp.tag(v) == .aggregate_value and sp.has_vars(self.decl_pool.tys()[@intFromEnum(d)])) _ = sp.unify(&self.abstract_pool, self.decl_pool.tys()[@intFromEnum(d)], sp.type_of(v));
            const dt = self.decl_pool.tys()[@intFromEnum(d)];
            if (v != .none and sp.tag(v) == .aggregate_value and sp.tag(dt) == .array_type and sp.tag(sp.get(dt).array_type.len) == .int_value and sp.get(sp.get(dt).array_type.len).int.bits != sp.get(v).aggregate.elems.len)
                _ = self.report(.type_mismatch, values[@min(i, values.len - 1)], sp.type_of(v), dt);
        }
    }
    return .unit_type;
}

fn h13_check_member(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parent = self.tree.arg(node, 0);
    const name = self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(node, 1));
    const pt = self.h09_check_expr(ctx, parent, .none);
    if (pt == .poison_type) return pt;
    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = sp.tag(pt) == .meta_type;
    const base = if (!on_type) sp.apply_vars(&self.abstract_pool, pt) else statics.deferred(self, ctx, parent) orelse return .poison_type;
    if (base == .poison_type) return base;
    if (sp.tag(base) == .type_var) return self.report(.uninferable_type, parent, base, .none);
    if (statics.templated(self, base) != .none) return statics.template_member(self, node, statics.templated(self, base), name);
    const view = if (self.tree.kind(parent) == .identifier and self.node_decl[parent] != .none) self.decl_pool.flags()[@intFromEnum(self.node_decl[parent])].is_view else false;
    if (view and statics.source_of(self, base) != .none and statics.template_member(self, node, sp.intern(.{ .template_type = statics.source_of(self, base) }), name) == .poison_type) return .poison_type;
    return switch (sp.lookup_member(base, name)) {
        .field => |f| if (on_type) self.report(.unknown_member, node, name, base) else f.ty,
        .method => |m| self.method(node, m),
        .trait_method => |m| self.method(node, sp.method_decl(m)),
        .case => |c| c,
        .builtin_len => .u64_type,
        .builtin_tag => if (on_type) self.report(.unknown_member, node, name, base) else sp.tag_type_of(base),
        .builtin_init, .builtin_deinit => sp.intern(.{ .function_type = .{ .category = .default, .params = &.{}, .ret = if (name == .init) base else .unit_type } }),
        .none => self.report(.unknown_member, node, name, base),
    };
}

fn h18_check_place(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // self is mutable in methods; stc locals are compile-time variables and writable too
    const t = self.h09_check_expr(ctx, node, .none);
    if (t == .poison_type and self.errors_since(0, node)) return t;
    self.write_access(node, self.writable(node));
    return t;
}

pub fn write_access(self: *Resolver, node: ParseTree.NodeId, a: Access) void {
    switch (a) {
        .ok => self.wrote(node),
        .immutable => self.doc.h21_report(.assign_to_immutable, node, 0, 0),
        .through_ptr => self.doc.h21_report(.write_through_immutable_pointer, node, 0, 0),
    }
}

// a write into a place rooted at `self` (not through a pointer it holds) makes its method one that writes self
fn wrote(self: *Resolver, place: ParseTree.NodeId) void {
    var n = place;
    while (self.tree.kind(n) != .identifier_self) switch (self.tree.kind(n)) {
        .capture => n = self.tree.arg(n, 0),
        .member, .array_index, .dereference => {
            const p = self.tree.arg(n, 0);
            if (self.tree.kind(p) != .identifier_self and (self.tree.kind(n) == .dereference or self.static_pool.is_ptr(self.node_type[p]))) return;
            n = p;
        },
        else => return,
    };
    const d = self.node_decl[n];
    if (d != .none and self.decl_pool.kinds()[@intFromEnum(d)] == .self) self.decl_pool.flags()[@intFromEnum(d)].writes = true;
}

// HELPERS! must be interned TODO

pub inline fn set(self: *Resolver, n: ParseTree.NodeId, t: StaticPool.Index) StaticPool.Index {
    self.node_type[n] = t;
    return t;
}

pub fn report(self: *Resolver, code: Doctor.Disorder, n: ParseTree.NodeId, a: anytype, b: anytype) StaticPool.Index {
    self.doc.h21_report(code, n, a, b);
    return self.set(n, .poison_type);
}

pub fn check_guards(self: *Resolver, ctx: *FnCtx, p: Param, t: StaticPool.Index) void {
    if (p.where != 0) _ = self.check(ctx, p.where, .bool_type);
    if (p.@"else" != 0) _ = if (self.tree.kind(p.@"else") == .assign) self.h09_check_expr(ctx, p.@"else", .none) else self.check(ctx, p.@"else", t);
}

pub fn init_enter(self: *Resolver) struct { tracked: u32, uninit: u64 } {
    defer self.uninit = 0;
    return .{ .tracked = self.init_tracked.head, .uninit = self.uninit };
}

pub fn init_leave(self: *Resolver, tracked: u32, uninit: u64) void {
    self.init_tracked.head = tracked;
    self.uninit = uninit;
}

pub fn check(self: *Resolver, ctx: *FnCtx, n: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const t = self.h09_check_expr(ctx, n, expected);
    // a case with a payload is a constructor, a value of it needs the payload
    if (t != .poison_type and self.tree.kind(n) == .member and self.static_pool.tag(t) == .variant_case_type and self.static_pool.get(t).variant_case_type.payload != .none) return self.report(.type_mismatch, n, t, expected);
    return self.h10_expect(n, t, expected);
}

pub fn is_range_kind(k: ParseTree.Node.Kind) bool {
    return node_props[@intFromEnum(k)].range;
}

pub fn push_decl(self: *Resolver, name: NamePool.Index, node: ParseTree.NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index, flags: DeclPool.Entry.Flags) DeclPool.Index {
    const d: DeclPool.Index = @enumFromInt(self.decl_pool.entries.len());
    const lazy = flags.is_global or kind.is_fn() or is_type_decl(kind);
    self.decl_pool.entries.push(.{ .name = name, .node = node, .kind = kind, .flags = flags, .state = if (lazy) .unresolved else .done, .ty = ty, .value = .none, .next_overload = .none });
    return d;
}

pub fn is_type_decl(kind: DeclPool.Entry.Kind) bool {
    return kind == .type_alias or kind == .record or kind == .variant or kind == .trait;
}

// a declared global row is reused, anything else becomes a new local
fn declare(self: *Resolver, id: ParseTree.NodeId, stmt: ParseTree.NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index, flags: DeclPool.Entry.Flags) DeclPool.Index {
    var d = self.node_decl[id];
    if (!self.pre_declared(d, stmt)) {
        d = self.h02_declare_local(self.name_pool.name_of(self.tree, self.src_bytes, id), stmt, kind, ty);
        self.decl_pool.flags()[@intFromEnum(d)] = flags;
        self.node_decl[id] = d;
    } else if (ty != .none) self.decl_pool.tys()[@intFromEnum(d)] = ty;
    _ = self.set(id, if (ty == .none) .unit_type else ty);
    return d;
}

// s1 rows and hoisted local functions of this very statement are reused instead of declared again
fn pre_declared(self: *Resolver, d: DeclPool.Index, stmt: ParseTree.NodeId) bool {
    return d != .none and self.decl_pool.nodes()[@intFromEnum(d)] == stmt and (self.decl_pool.flags()[@intFromEnum(d)].is_global or self.h01_lookup(self.decl_pool.names()[@intFromEnum(d)]) == d);
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
pub fn open_scope(self: *Resolver, barrier: bool, self_type: StaticPool.Index, node: ParseTree.NodeId) void {
    self.h03_push_scope();
    if (barrier) {
        self.local_names.push(.none);
        self.local_decls.push(.none);
    }
    if (self_type != .none) self.decl_pool.flags()[@intFromEnum(self.h02_declare_local(.self, node, .self, self.self_ptr(self_type)))].is_mut = true;
}

// methods: the owning type is the value of the trait body row right before its members; realizations ask their template
fn owner_of(self: *Resolver, decl: DeclPool.Index) StaticPool.Index {
    if (self.template_of.get(decl)) |t| return self.owner_of(t);
    if (self.decl_pool.kinds()[@intFromEnum(decl)] != .trait_member) return .none;
    var d = @intFromEnum(decl);
    while (self.decl_pool.kinds()[d] != .trait) d -= 1;
    return self.decl_pool.values()[d];
}

// the locals a function body reads from the bodies around it, its environment as a closure
pub fn captures(self: *Resolver, d: DeclPool.Index, out: *DynBuf(DeclPool.Index)) void {
    const start = out.head;
    const b = self.bodies.get(self.body_of.get(d) orelse return).?;
    for (self.body_nodes.sliced_field(.decl)[b.start..][0..b.len]) |x| {
        if (x == .none or std.mem.indexOfScalar(DeclPool.Index, out.buf[start..out.head], x) != null) continue;
        const flags = self.decl_pool.flags()[@intFromEnum(x)];
        const node = self.decl_pool.nodes()[@intFromEnum(x)];
        const local = switch (self.decl_pool.kinds()[@intFromEnum(x)]) {
            .variable, .parameter, .loop_variable, .pattern_binder, .arrow_binder, .autoins_it, .autoins_arg, .self => true,
            else => false,
        };
        if (local and !flags.is_global and !(flags.is_stc and self.decl_pool.values()[@intFromEnum(x)] != .none) and (node < b.lo or node >= b.lo + b.len)) out.push(x);
    }
}

// a closure holds a pointer to a mutable or aggregate local, a copy of anything else
pub fn by_ref(self: *Resolver, c: DeclPool.Index) bool {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, self.decl_pool.tys()[@intFromEnum(c)]);
    return self.decl_pool.flags()[@intFromEnum(c)].is_mut or t != .none and (sp.tag(t) == .record_type or sp.tag(t) == .array_type and sp.get(t).array_type.len != StaticPool.dyn_len);
}

pub fn value_node(self: *Resolver, d: DeclPool.Index) ParseTree.NodeId {
    const n = self.decl_pool.nodes()[@intFromEnum(d)];
    return switch (self.tree.kind(n)) {
        .assign, .assign_typed => self.tree.arg(n, 1),
        else => n,
    };
}

pub fn definition(self: *const Resolver, n: ParseTree.NodeId) Def {
    var d = Def{ .core = n };
    while (true) : (d.core = self.tree.arg(d.core, 0)) switch (self.tree.kind(d.core)) {
        .def_type_implof, .def_variant_implof => d.body = self.tree.arg(d.core, 1),
        .def_type_assertsize, .def_variant_assertsize => d.size = self.tree.arg(d.core, 1),
        .def_variant_tagof => d.tagof = self.tree.arg(d.core, 1),
        else => return d,
    };
}

fn core(self: *const Resolver, n: ParseTree.NodeId) ParseTree.NodeId {
    return self.definition(n).core;
}

pub fn meta(kind: DeclPool.Entry.Kind, other: StaticPool.Index) StaticPool.Index {
    return switch (kind) {
        .record => .type_type,
        .variant => .variant_type,
        .trait => .trait_type,
        else => other,
    };
}

pub fn type_kind(self: *const Resolver, n: ParseTree.NodeId) DeclPool.Entry.Kind {
    return switch (self.tree.kind(self.core(n))) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

fn decl_kind(self: *const Resolver, type_node: ParseTree.NodeId, value: ParseTree.NodeId) DeclPool.Entry.Kind {
    const tk = self.type_kind(value);
    return switch (self.tree.kind(type_node)) {
        .type_fun => .function,
        .type_stcfun => .static_function,
        .type_inlfun => .inlined_function,
        .type_type, .type_variant, .type_trait => if (value != 0 and self.tree.kind(value) == .def_fun) .static_function else switch (self.tree.kind(type_node)) {
            .type_type => if (tk == .record) .record else .type_alias,
            .type_variant => if (tk == .variant) .variant else .type_alias,
            else => if (tk == .trait) .trait else .type_alias,
        },
        .none => if (value != 0 and (self.tree.kind(value) == .def_fun or self.tree.kind(value) == .def_fun_declaration)) .function else .variable,
        else => .variable,
    };
}

// unnamed parameters and fields are `$0`, `$1`, ...
pub fn param_name(self: *Resolver, pn: ParseTree.NodeId, i: usize) NamePool.Index {
    return self.name_at(Param.from_node(self, pn), i);
}

pub fn name_at(self: *Resolver, p: Param, i: usize) NamePool.Index {
    const autoinserted_dollarnames = comptime blk: {
        @setEvalBranchQuota(100_000);
        var t: [64][]const u8 = undefined;
        for (&t, 0..) |*s, j| s.* = std.fmt.comptimePrint("${d}", .{j});
        break :blk t;
    };

    return if (p.name != 0) self.name_pool.name_of(self.tree, self.src_bytes, p.name) else self.name_pool.intern_string(autoinserted_dollarnames[@min(i, 63)]);
}

pub fn template_field(self: *Resolver, g: DeclPool.Index, name: NamePool.Index) ?ParseTree.NodeId {
    for (self.fields_of_node(self.core(self.tree.arg(self.value_node(g), 1))), 0..) |f, i| if (self.param_name(f, i) == name) return f;
    return null;
}

pub fn params_of(self: *const Resolver, v: ParseTree.NodeId) []const ParseTree.NodeId {
    if (self.tree.kind(v) != .def_fun and self.tree.kind(v) != .def_fun_declaration) return &.{};
    return self.tree.manychildren(self.tree.arg(self.tree.arg(v, 0), 0));
}

pub fn fields_of_node(self: *const Resolver, c: ParseTree.NodeId) []const ParseTree.NodeId {
    return if (self.tree.kind(c) == .partial__type_def_param_tuple) self.tree.manychildren(c) else self.tree.manychildren(self.tree.arg(c, 0));
}

pub fn fields_of(self: *Resolver, rec: StaticPool.Index) []const ParseTree.NodeId {
    return self.fields_of_node(self.core(self.value_node(self.static_pool.get(rec).custom_type.decl)));
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
pub fn sig(self: *Resolver, d: DeclPool.Index) StaticPool.FunType {
    return self.static_pool.get(self.decl_pool.tys()[@intFromEnum(d)]).function_type;
}

pub fn self_off(self: *Resolver, d: DeclPool.Index) usize {
    return @intFromBool(self.decl_pool.kinds()[@intFromEnum(d)] == .trait_member and self.decl_pool.names()[@intFromEnum(d)] != .init);
}

pub fn self_ptr(self: *Resolver, t: StaticPool.Index) StaticPool.Index {
    return self.static_pool.intern(.{ .ptr_type = .{ .child = t, .mutable = true } });
}

// a value's type looked through one pointer to a record or variant (`self`, `with` / `match` on such pointers)
pub fn deref(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    if (!sp.is_ptr(t)) return t;
    const c = sp.pointee(t);
    return if (sp.get_tag_prop(c).is_nominal or sp.get_tag_prop(c).is_variant) c else t;
}

pub fn fresh_var(self: *Resolver, origin: ParseTree.NodeId) StaticPool.Index {
    return self.static_pool.intern(.{ .abstract_type = self.abstract_pool.fresh(origin) });
}

pub fn fn_ret(self: *Resolver, d: DeclPool.Index) StaticPool.Index {
    const t = types.decl_type(self, d);
    return if (self.static_pool.tag(t) == .function_type) self.static_pool.get(t).function_type.ret else .poison_type;
}

pub fn method(self: *Resolver, node: ParseTree.NodeId, m: DeclPool.Index) StaticPool.Index {
    self.node_decl[node] = m;
    return types.decl_type(self, m);
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
pub fn real(self: *Resolver, d: DeclPool.Index) DeclPool.Index {
    const v = self.decl_pool.values()[@intFromEnum(d)];
    return if (v != .none and self.static_pool.tag(v) == .function_value) self.static_pool.get(v).function else d;
}

pub fn group_head(self: *Resolver, first: DeclPool.Index, d: DeclPool.Index) DeclPool.Index {
    var h = first;
    while (h != d and !calls.same_params(self, h, d)) h = self.decl_pool.next_overloads()[@intFromEnum(h)];
    return h;
}

pub fn template(self: *Resolver, d: DeclPool.Index) DeclPool.Entry.Kind {
    const n = self.decl_pool.nodes()[@intFromEnum(d)];
    if (self.tree.kind(n) != .assign_typed or self.tree.kind(self.tree.arg(n, 1)) != .def_fun) return .variable;
    return switch (self.tree.kind(self.tree.arg(self.tree.arg(n, 0), 0))) {
        .type_type => .record,
        .type_variant => .variant,
        .type_trait => .trait,
        else => .variable,
    };
}

fn elem_ptr(self: *Resolver, t0: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (t0 == .poison_type or t0 == .none) return false;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    return sp.is_ptr(t) and sp.get(sp.pointee(t)) != .array_type;
}

pub fn integer(self: *Resolver, ctx: *FnCtx, n: ParseTree.NodeId) bool {
    const t = self.operand(ctx, n, if (self.tree.kind(n) == .neg_num) .i64_type else .u64_type);
    if (t == .poison_type or self.static_pool.get_tag_prop(t).is_integer) return true;
    _ = self.report(.type_mismatch, n, t, .u64_type);
    return false;
}

pub fn signature_mentions(self: *Resolver, f: ParseTree.NodeId, v: ParseTree.NodeId) bool {
    const header = self.tree.arg(f, 0);
    if (self.tree.kind(header) != .partial__fun_def_header_ret or self.mentions(self.tree.arg(header, 1), v)) return true;
    for (self.params_of(f)) |pn| if (self.mentions(Resolver.Param.from_node(self, pn).ty, v)) return true;
    return false;
}

pub fn mentions(self: *Resolver, n: ParseTree.NodeId, v: ParseTree.NodeId) bool {
    const params = self.params_of(v);
    const s = self.tree.subtree(n);
    for (s[0]..s[1]) |i| {
        if (self.tree.kind(@intCast(i)) != .identifier) continue;
        const nm = self.name_pool.name_of(self.tree, self.src_bytes, @intCast(i));
        for (params, 0..) |pn, j| if (self.param_name(pn, j) == nm) return true;
    }
    return false;
}

// TODO NEXT was ist hier noch rausnehmbar?

pub fn arg_value(self: *const Resolver, a: ParseTree.NodeId) ParseTree.NodeId {
    return if (self.tree.kind(a) == .partial__fun_call_assigned_param) self.tree.arg(a, 1) else a;
}

pub fn concrete(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and self.static_pool.tag(self.static_pool.apply_vars(&self.abstract_pool, t)) != .type_var;
}

fn is_numeric(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and (self.static_pool.get_tag_prop(t).is_integer or self.static_pool.get_tag_prop(t).is_float);
}

fn folded(self: *Resolver, n: ParseTree.NodeId) bool {
    return self.is_literal(n) or self.node_value[n] != .none and switch (self.tree.kind(n)) {
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap => true,
        else => false,
    };
}

fn numeric(self: *Resolver, node: ParseTree.NodeId, t: StaticPool.Index, result: StaticPool.Index) StaticPool.Index {
    if (self.is_numeric(t) or self.static_pool.tag(t) == .type_var) return if (result == .none) t else result;
    return self.mismatch(node, t, .none);
}

pub fn mismatch(self: *Resolver, n: ParseTree.NodeId, t: StaticPool.Index, want: StaticPool.Index) StaticPool.Index {
    return if (t == .poison_type) t else self.report(.type_mismatch, n, t, want);
}

fn operand(self: *Resolver, ctx: *FnCtx, n: ParseTree.NodeId, hint: StaticPool.Index) StaticPool.Index {
    return if (self.is_literal(n)) self.check(ctx, n, hint) else self.h09_check_expr(ctx, n, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn pair(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, l: ParseTree.NodeId, r: ParseTree.NodeId, hint: StaticPool.Index) StaticPool.Index {
    const swap = self.is_literal(l) and !self.is_literal(r);
    const t1 = self.operand(ctx, if (swap) r else l, hint);
    const add = self.tree.kind(node) == .binary_add;
    if ((add or !swap and self.tree.kind(node) == .binary_sub) and self.elem_ptr(t1)) return if (self.integer(ctx, if (swap) l else r)) t1 else .poison_type;
    const t2 = self.operand(ctx, if (swap) l else r, t1);
    if (add and self.elem_ptr(t2) and self.static_pool.get_tag_prop(t1).is_integer) return t2;
    if (t1 == .poison_type or t2 == .poison_type) return .poison_type;
    if (self.static_pool.tag(t1) == .meta_type and self.static_pool.tag(t2) == .meta_type) return t1;
    var j = self.static_pool.join(&self.abstract_pool, t1, t2);
    if (j.ty == .none) j = self.static_pool.join(&self.abstract_pool, self.deref(t1), self.deref(t2)); // `self == Toggle.On`
    return if (j.ty == .none) self.report(.type_mismatch, node, t1, t2) else j.ty;
}

fn need_deinit(self: *Resolver, node: ParseTree.NodeId, t0: StaticPool.Index) void {
    const t = self.static_pool.apply_vars(&self.abstract_pool, t0);
    if (t != .poison_type and self.static_pool.lookup_member(t, .deinit) == .none)
        self.doc.h21_report(.no_deinit, node, t, 0);
}

pub fn writable(self: *Resolver, node: ParseTree.NodeId) Access {
    return switch (self.tree.kind(node)) {
        .capture => self.writable(self.tree.arg(node, 0)),
        .identifier, .identifier_self => blk: {
            const d = self.node_decl[node];
            if (d == .none) break :blk .ok;
            const f = self.decl_pool.flags()[@intFromEnum(d)];
            break :blk if (f.is_mut or f.is_stc or self.decl_pool.kinds()[@intFromEnum(d)] == .self) .ok else .immutable;
        },
        .member => blk: {
            const base = self.through(self.tree.arg(node, 0), true);
            break :blk if (base != .ok) base else if (self.field_mut(self.node_type[self.tree.arg(node, 0)], self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(node, 1)))) .ok else .immutable;
        },
        .array_index => self.through(self.tree.arg(node, 0), true),
        .dereference => self.through(self.tree.arg(node, 0), false),
        else => .immutable,
    };
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent itself is writable
pub fn through(self: *Resolver, parent: ParseTree.NodeId, or_place: bool) Access {
    const sp = &self.static_pool;
    const pt = self.node_type[parent];
    if (pt == .none or pt == .poison_type) return .ok;
    const t = sp.apply_vars(&self.abstract_pool, pt);
    if (sp.get(t) == .ptr_type) return if (sp.get(t).ptr_type.mutable) .ok else .through_ptr;
    return if (or_place) self.writable(parent) else .immutable;
}

fn field_mut(self: *Resolver, pt: StaticPool.Index, name: NamePool.Index) bool {
    const sp = &self.static_pool;
    if (pt == .none or pt == .poison_type) return true;
    var t = sp.apply_vars(&self.abstract_pool, pt);
    t = sp.pointee(t);
    if (sp.tag(t) == .variant_case_type) t = sp.get(t).variant_case_type.payload;
    if (t != .none and sp.tag(t) == .template_type) if (self.template_field(sp.get(t).template_type, name)) |f| return Param.from_node(self, f).is_mut;
    if (t == .none or sp.tag(t) != .record_type) return false;
    for (sp.get(t).custom_type.field_names, 0..) |n, i| if (n == name) return Param.from_node(self, self.fields_of(t)[i]).is_mut;
    return false;
}

fn scalar(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and t != .poison_type and self.static_pool.tag(t) != .record_type and self.static_pool.tag(t) != .array_type;
}

fn track(self: *Resolver, d: DeclPool.Index) void {
    if (self.init_tracked.head >= 64) return;
    self.uninit |= @as(u64, 1) << @intCast(self.init_tracked.head);
    self.init_tracked.push(d);
}

fn init_bit(self: *Resolver, d: DeclPool.Index) u64 {
    return for (self.init_tracked.sliced(), 0..) |x, i| {
        if (x == d) break @as(u64, 1) << @intCast(i);
    } else 0;
}

fn check_init(self: *Resolver, node: ParseTree.NodeId, d: DeclPool.Index) void {
    if (self.uninit == 0) return;
    const bit = self.init_bit(d);
    if (self.uninit & bit == 0) return;
    self.doc.h21_report(.use_before_initialization, node, self.decl_pool.names()[@intFromEnum(d)], 0);
    self.uninit &= ~bit;
}

pub fn node_info(self: *const Resolver, b: Body, comptime field: @EnumLiteral(), n: ParseTree.NodeId) @FieldType(EphemeralNodeInfo, @tagName(field)) {
    if (n -% b.lo < b.len) return @field(self.body_nodes.pool, @tagName(field)).buf[b.start + n - b.lo];
    return @field(self, if (field == .ty) "node_type" else "node_" ++ @tagName(field))[n];
}

pub fn field_of(self: *Resolver, rec: StaticPool.Index, a: ParseTree.NodeId, i: usize) ?u32 {
    if (self.tree.kind(a) != .partial__fun_call_assigned_param) return @intCast(i);
    return switch (self.static_pool.lookup_member(rec, self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0)))) {
        .field => |f| f.index,
        else => null,
    };
}

pub fn narrowed(self: *const Resolver, target: ParseTree.NodeId) ParseTree.NodeId {
    const inner = if (self.tree.kind(target) == .type_ptr or self.tree.kind(target) == .type_ptrmut) self.tree.arg(target, 0) else target;
    return if (self.tree.kind(inner) == .type_array) self.range(self.tree.arg(inner, 0)).lo else 0;
}

pub fn loop_parts(self: *const Resolver, n: ParseTree.NodeId) Loop {
    const a0 = self.tree.arg(n, 0);
    const a1 = self.tree.arg(n, 1);
    return switch (self.tree.kind(n)) {
        .@"while", .stcwhile => .{ .cond = a0, .body = a1 },
        .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => .{ .cond = self.tree.arg(a0, 0), .repeat = a1, .head = a0, .body = self.tree.arg(a0, 1) },
        .loop, .stcloop => .{ .body = a0 },
        .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => .{ .repeat = a0, .body = a1 },
        .for_var_in_seq, .stcfor_var_in_seq => .{ .head = a0, .seq = self.tree.arg(a0, 0), .variable = a1, .body = self.tree.arg(a0, 1) },
        else => .{ .head = n, .seq = a0, .body = a1 },
    };
}

pub fn range(self: *const Resolver, n: ParseTree.NodeId) Range {
    const k = self.tree.kind(n);
    const two = k == .gen_incl or k == .gen_excl;
    return .{
        .lo = if (two or k == .gen_lowerbound) self.tree.arg(n, 0) else 0,
        .hi = if (two) self.tree.arg(n, 1) else if (k == .gen_lowerbound) 0 else self.tree.arg(n, 0),
        .incl = k == .gen_incl or k == .gen_upperbound_incl,
    };
}

pub fn literal_core(self: *const Resolver, node: ParseTree.NodeId, neg: *bool) ParseTree.NodeId {
    var n = node;
    while (true) switch (self.tree.kind(n)) {
        .capture => n = self.tree.arg(n, 0),
        .neg_num => {
            neg.* = !neg.*;
            n = self.tree.arg(n, 0);
        },
        else => return n,
    };
}

pub fn is_literal(self: *const Resolver, node: ParseTree.NodeId) bool {
    var neg = false;
    return Resolver.node_props[@intFromEnum(self.tree.kind(self.literal_core(node, &neg)))].literal;
}
