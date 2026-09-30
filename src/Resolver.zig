const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const ParseTree = @import("ParseTree.zig");

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
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
const none_node: NodeId = std.math.maxInt(NodeId);
const NodeId = ParseTree.NodeId;
const NodeKind = ParseTree.Node.Kind;

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

// one row per declaration: globals, locals, params, fields, binders.
// stored as struct-of-arrays, so every access pattern touches only the columns it needs:
// looking a name up reads `name` only, checking a use reads `kind`, `flags`, `ty`.
pub const Decl = struct {
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: Kind,
    flags: Flags,
    state: State,
    ty: StaticPool.Index,
    value: StaticPool.Index,
    next_overload: Index,

    pub const Kind = enum(u8) {
        variable,
        parameter,
        static_parameter,
        field,
        function,
        static_function,
        inlined_function,
        type_alias,
        record,
        variant,
        variant_case,
        trait,
        trait_member,
        pattern_binder,
        arrow_binder,
        loop_variable,
        self,
        autoins_arg,
        autoins_it,
    };

    pub const Flags = packed struct(u8) {
        is_pub: bool = false,
        is_mut: bool = false,
        is_stc: bool = false,
        is_global: bool = false,
        is_view: bool = false,
        // methods: the body writes through `self`, the `self` local: something writes through it
        writes: bool = false,
        _pad: u2 = 0,
    };

    //   unresolved -> resolving_signature -> signature_ready -> checking_body -> done   (or failed)
    // signature_ready is published before the body is checked, so a function can call itself or a
    // mutually recursive partner: an induced return type is a type var until the bodies fix it.
    // meeting a declaration in resolving_signature again is a real cycle (a type containing itself
    // by value, a static value defined through itself) and an error.
    pub const State = enum(u8) {
        unresolved,
        resolving_signature,
        signature_ready,
        checking_body,
        done,
        failed,
    };

    pub const Index = enum(u32) {
        none = std.math.maxInt(u32),
        _,

        pub fn member(d: Index, i: usize) Index {
            return @enumFromInt(@intFromEnum(d) + 1 + i);
        }
    };
};

// per-body state that would otherwise be globals. lives on the machine stack while a body is
// checked and is passed down by pointer - no table, no allocation.
// ret_type is a type var for induced return types; every `ret` unifies with it.
pub const NodeInfo = struct { ty: StaticPool.Index, decl: Decl.Index, value: StaticPool.Index };
pub const Body = struct { decl: Decl.Index = .none, lo: ParseTree.NodeId = 0, len: u32 = 0, start: u32 = 0, first: u32 = 0, locals: u32 = 0 };

pub const FnCtx = struct {
    decl: Decl.Index = .none,
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

// placeholders for types not known yet and what they turned out to be. see type_system.zig.
abstract_pool: AbstractPool,

// ALL declarations
decls: SoD(Decl),

// the two results, one slot per parse tree node, indexed by ParseTree.NodeId.
// plain arrays of u32: 8 bytes per node in total, and the lowerer reads them with no indirection.
node_type: []StaticPool.Index,
node_decl: []Decl.Index,
node_value: []StaticPool.Index,
bodies: SoD(Body),
body_nodes: SoD(NodeInfo),
body_of: std.AutoHashMapUnmanaged(Decl.Index, u32) = .empty,
template_of: std.AutoHashMapUnmanaged(Decl.Index, Decl.Index) = .empty,
realized_args: std.AutoHashMapUnmanaged(Decl.Index, StaticPool.Index) = .empty,
// functions produced by a stcfun: the realization whose static parameters they see
static_scope: std.AutoHashMapUnmanaged(Decl.Index, StaticPool.AbstractKey) = .empty,
init_tracked: DynBuf(Decl.Index),
uninit: u64 = 0,
deferrals: u32 = 0,
// brk and cont seen so far: a loop without a brk never ends, one without either yields one element per step
jumps: [2]u32 = .{ 0, 0 },
loop_exits: DynBuf(u64),

// global names -> first declaration with that name
// - overloads of the same name handled by `decls.next_overload` for single per-name entry
// - solves: using global before declaring it in a file
globals: std.AutoHashMapUnmanaged(NamePool.Index, Decl.Index),

// the local scope stack. declaring a local pushes (name, decl); a lookup scans `local_names`
// backwards, so the innermost declaration wins and shadowing works for free.
// names and decls are two parallel arrays so the scan reads only a dense run of u32 names -
// for the few dozen locals a body has, that beats any hash map and vectorizes well.
local_names: DynBuf(NamePool.Index),
local_decls: DynBuf(Decl.Index),
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
        .decls = .init(alloc, 4096),
        .node_type = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_decl = alloc.alloc(Decl.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_value = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .bodies = .init(alloc, 256),
        .body_nodes = .init(alloc, 4096),
        .init_tracked = .init(alloc, 64),
        .loop_exits = .init(alloc, 16),
        .globals = .empty,
        .local_names = .init(alloc, 256),
        .local_decls = .init(alloc, 256),
        .local_scope_marks = .init(alloc, 16),
        .doc = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .init(alloc),
    };
}

pub inline fn deinit(self: *Resolver) void {
    inline for (.{ &self.name_pool, &self.static_pool, &self.abstract_pool, &self.decls, &self.bodies, &self.body_nodes, &self.interpreter, &self.init_tracked, &self.loop_exits, &self.local_names, &self.local_decls, &self.local_scope_marks, &self.doc.diagnostics }) |x| x.deinit();
    inline for (.{ &self.body_of, &self.template_of, &self.realized_args, &self.static_scope, &self.globals }) |m| m.deinit(self.alloc);
    inline for (.{ self.node_type, self.node_decl, self.node_value }) |x| self.alloc.free(x);
}

pub inline fn resolve(self: *Resolver) !void {
    inline for (.{ s1_collect_globals, s2_check_globals, s3_apply_inferred_types, s4_check_entry_point }) |step| {
        step(self);
        if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;
    }
}

fn s1_collect_globals(self: *Resolver) void {
    @memset(self.node_type, .none);
    @memset(self.node_decl, .none);
    @memset(self.node_value, .none);
    for ([_][]const u8{ "", "_", "$it", "self", "$init", "$deinit", "$main", "$len", "$has_next", "$next", "$tag" }) |s| _ = self.name_pool.intern(s);
    for (self.roots) |root| {
        const s = self.statement(root);
        var flags = s.flags;
        flags.is_global = true;
        const declares = s.type != 0 or @as(u8, @bitCast(s.flags)) != 0 or s.kind != .variable;
        for (s.ids) |id| {
            const name = self.name_of(id);
            if (name == .none) continue;
            const gop = self.globals.getOrPut(self.alloc, name) catch @panic("OOM");
            if (gop.found_existing and !(is_fn(s.kind) and is_fn(self.dp(.kind, gop.value_ptr.*).*))) {
                if (declares) _ = self.report(.duplicate_declaration, id, name, gop.value_ptr.*);
                if (declares and self.node_decl[root] == .none) self.node_decl[root] = gop.value_ptr.*;
                continue;
            }
            const d = self.push_decl(name, s.node, s.kind, .none, flags);
            // overloads with a where clause come before the ones without, so every group of same-typed
            // overloads reads as a runtime dispatch: its where-clauses in order, the where-less fallback last
            if (gop.found_existing) {
                var at = gop.value_ptr;
                while (at.* != .none and (!calls.has_where(self, d) or calls.has_where(self, at.*))) at = self.dp(.next_overload, at.*);
                self.dp(.next_overload, d).* = at.*;
                at.* = d;
            } else gop.value_ptr.* = d;
            self.node_decl[id] = d;
            if (self.node_decl[root] == .none) self.node_decl[root] = d;
        }
    }
}

fn s2_check_globals(self: *Resolver) void {
    const count = self.decls.len();
    for (0..count) |i| {
        self.h05_ensure_signature(@enumFromInt(i));
        self.h06_check_body(@enumFromInt(i));
    }
    var ctx = FnCtx{};
    for (self.roots) |root| if (self.node_decl[root] == .none) {
        _ = self.h09_check_expr(&ctx, root, .none);
    };
    // overloads that differ only by where clauses dispatch at runtime and need a where-less fallback
    var heads = self.globals.valueIterator();
    while (heads.next()) |h| {
        var c = h.*;
        while (c != .none) : (c = self.dp(.next_overload, c).*) {
            if (self.group_head(h.*, c) != c) continue;
            var size: u32 = 0;
            var fallback = false;
            var m = c;
            while (m != .none) : (m = self.dp(.next_overload, m).*) if (calls.same_params(self, m, c)) {
                size += 1;
                fallback = fallback or !calls.dispatches(self, self.real(m));
            };
            if (size > 1 and !fallback) _ = self.report(.no_matching_overload, self.dp(.node, c).*, size, 0);
        }
    }
}

fn s3_apply_inferred_types(self: *Resolver) void {
    if (self.abstract_pool.count() == 0) return;
    const sp = &self.static_pool;
    for (self.decls.sliced_field(.ty), 0..) |t, i| if (t != .none and sp.has_vars(t)) {
        const at = sp.apply_vars(&self.abstract_pool, t);
        if (statics.open_type_var(self, at) and !statics.length_generic(self, at)) _ = self.report(.uninferable_type, self.decls.pool.node.buf[i], at, .none);
    };
    // lengths nothing fixed are only known at runtime; a loop value then needs its element count at loop entry
    const vs = self.abstract_pool.pool.sliced();
    const group = self.alloc.alloc(NodeId, vs.parent.len) catch @panic("OOM");
    defer self.alloc.free(group);
    @memset(group, none_node);
    for (0..vs.parent.len) |i| {
        const root = @intFromEnum(self.abstract_pool.find(@enumFromInt(i)));
        if (vs.binding[root] != .none) continue;
        const origin = vs.origin[i];
        const k = self.nk(origin);
        const counted = switch (k) {
            .for_seq, .for_var_in_seq => blk: {
                const f = if (k == .for_var_in_seq) self.arg(origin, 0) else origin;
                const seq = self.arg(f, 0);
                const st = self.deref(sp.apply_vars(&self.abstract_pool, self.node_type[seq]));
                break :blk (is_range_kind(self.nk(seq)) and self.nk(seq) != .gen_lowerbound) or (st != .none and sp.tag(st) == .array_type) or control.is_ptr_array(self, self.node_type[seq]);
            },
            .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => false,
            .type_array_unlengthed, .array_index, .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => true,
            else => continue,
        };
        if (group[root] == none_node or !counted) group[root] = if (counted) 0 else origin;
    }
    for (group, 0..) |g, i| if (g != none_node) {
        if (g != 0) _ = self.report(.uninferable_type, g, sp.apply_vars(&self.abstract_pool, self.node_type[g]), .none);
        self.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len);
    };
    for ([_][]StaticPool.Index{ self.node_type, self.decls.sliced_field(.ty) }) |ts| for (ts) |*t| if (t.* != .none and sp.has_vars(t.*)) {
        t.* = sp.apply_vars(&self.abstract_pool, t.*);
    };
}

fn s4_check_entry_point(self: *Resolver) void {
    const main = self.globals.get(.main) orelse return self.doc.h21_report(.missing_main, 0, 0, 0);
    const node = self.dp(.node, main).*;
    if (self.dp(.next_overload, main).* != .none) return self.doc.h21_report(.duplicate_declaration, self.dp(.node, self.dp(.next_overload, main).*).*, NamePool.Index.main, main);
    const ty = self.dp(.ty, main).*;
    const sp = &self.static_pool;
    const ok = ty != .none and sp.tag(ty) == .function_type and blk: {
        const f = sp.get(ty).function_type;
        const args_ok = f.params.len == 0 or (f.params.len == 2 and sp.class(f.params[0]).is_integer and sp.class(f.params[1]).is_pointer);
        break :blk args_ok and (f.ret == .unit_type or f.ret == .runit_type or f.ret == .never_type or sp.class(f.ret).is_integer);
    };
    if (!ok) _ = self.report(.type_mismatch, node, ty, .none);
}

// ------------------------------------------------------------------------------------------ //
// scopes and names
// ------------------------------------------------------------------------------------------ //

pub fn h01_lookup(self: *Resolver, name: NamePool.Index) Decl.Index {
    const names = self.local_names.sliced();
    var i = names.len;
    while (i > 0) {
        i -= 1;
        if (names[i] == name) return self.local_decls.buf[i];
        if (names[i] == .none) break; // barrier: a declaration body never sees its user's locals
    }
    return self.globals.get(name) orelse .none;
}

pub fn use(self: *Resolver, node: NodeId) Decl.Index {
    const name = self.name_of(node);
    const d = self.h01_lookup(name);
    if (d == .none) {
        _ = self.report(.undefined_name, node, name, 0);
        return d;
    }
    self.node_decl[node] = d;
    self.h05_ensure_signature(d);
    return d;
}

pub fn h02_declare_local(self: *Resolver, name: NamePool.Index, node: ParseTree.NodeId, kind: Decl.Kind, ty: StaticPool.Index) Decl.Index {
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

pub fn h05_ensure_signature(self: *Resolver, decl: Decl.Index) void {
    const state = self.dp(.state, decl);
    switch (state.*) {
        .unresolved => {},
        .resolving_signature => {
            _ = self.report(.declaration_cycle, self.dp(.node, decl).*, self.dp(.name, decl).*, 0);
            state.* = .failed;
            return;
        },
        else => return,
    }
    state.* = .resolving_signature;
    const sp = &self.static_pool;
    const kind = self.dp(.kind, decl).*;
    const s = self.statement(self.dp(.node, decl).*);
    if (s.type != 0 and self.nk(s.type) == .type_fun and switch (self.dp(.name, decl).*) {
        .init, .deinit, .main, .has_next, .next => true,
        else => false,
    }) _ = self.report(.redundant_fun, s.type, 0, 0);
    const flags = self.dp(.flags, decl).*;
    var ctx = FnCtx{ .decl = decl, .self_type = self.owner_of(decl), .in_static = flags.is_stc };
    const v = self.value_node(decl);
    self.open_scope(flags.is_global, if (self.self_off(decl) == 1) ctx.self_type else .none, v);
    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => if (self.nk(v) == .def_fun or self.nk(v) == .def_fun_declaration) {
            // stcfun: the first tuple is static, whatever the body produces is the result (a second tuple belongs to the produced function)
            const unit = self.arg(v, 1);
            const tk = self.template(decl);
            const uk = self.type_kind(unit);
            if (kind == .static_function and tk == .variable and uk != .variable) _ = self.report(.missing_ret, unit, 0, 0);
            const res = if (self.nk(unit) == .ret) self.arg(unit, 0) else unit;
            const ret: StaticPool.Index = if (kind == .static_function)
                meta(self.type_kind(res), if (self.nk(res) == .def_fun or self.nk(res) == .def_fun_declaration) .fun_type else .poison_type)
            else if (self.nk(v) == .def_fun_declaration or self.nk(self.arg(v, 0)) == .partial__fun_def_header_ret) .unit_type else self.fresh_var(v);
            if (tk != .variable and uk == .variable) {
                _ = self.report(.redundant_ret, unit, 0, 0);
            } else if (tk != .variable and uk != tk) _ = self.report(.type_mismatch, unit, ret, meta(tk, .trait_type));
            const category: StaticPool.FunType.Category = switch (kind) {
                .static_function => .static,
                .inlined_function => .inlined,
                else => .default,
            };
            // a method's first parameter is the induced `*Self`, `init` constructs and has none
            self.dp(.ty, decl).* = types.fun_type(self, &ctx, v, category, ret, if (self.self_off(decl) == 1) self.self_ptr(ctx.self_type) else .none);
            if (flags.is_global and self.dp(.name, decl).* == .main) self.dp(.ty, decl).* = types.dynify(self, self.dp(.ty, decl).*);
            self.dp(.value, decl).* = if (kind == .static_function)
                sp.intern(.{ .static_fun = .{ .decl = decl, .result_kind = if (sp.tag(ret) == .meta_type) sp.get(ret).meta_type else .stcfun } })
            else
                sp.intern(.{ .function = decl });
        } else {
            // a function produced by a static expression (`fun sub_from_templ = my_templ(i32, false)`)
            const fv = statics.h08_eval_static(self, &ctx, v);
            if (sp.tag(fv) == .function_value) {
                self.dp(.value, decl).* = fv;
                self.dp(.ty, decl).* = self.dp(.ty, sp.get(fv).function).*;
            } else if (fv != .poison_type) _ = self.report(.type_mismatch, v, sp.type_of(fv), .fun_type);
        },
        .record, .variant, .trait => _ = types.h19_check_type_def(self, &ctx, decl, v),
        .type_alias => {
            const t = types.h07_lower_type(self, &ctx, v);
            self.dp(.value, decl).* = t;
            self.dp(.ty, decl).* = sp.type_of(t);
        },
        else => _ = self.h11_check_assign(&ctx, self.dp(.node, decl).*),
    }
    self.h04_pop_scope();
    if (self.dp(.state, decl).* == .resolving_signature) self.dp(.state, decl).* = .signature_ready;
}

pub fn h06_check_body(self: *Resolver, decl: Decl.Index) void {
    const state = self.dp(.state, decl);
    if (state.* != .signature_ready) return;
    const sp = &self.static_pool;
    const kind = self.dp(.kind, decl).*;
    const v = self.value_node(decl);
    const ty = self.dp(.ty, decl).*;
    // stcfun bodies are checked per realization, length-generic ones per length (h20); `main` is realized once, by the runtime
    const generic = statics.length_generic(self, ty) and !self.template_of.contains(decl);
    const abstract = generic and statics.only_templates(self, ty);
    if (kind == .static_function or !is_fn(kind) or self.nk(v) != .def_fun or generic and !abstract) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;
    const first = self.decls.len();
    const mark = self.doc.diagnostics.len();
    const outer = self.init_enter();
    defer self.init_leave(outer);
    // a local function sees which enclosing locals are not written yet
    if (kind == .function and !self.dp(.flags, decl).is_global) self.uninit = outer.uninit;
    const off = self.self_off(decl);
    var ctx = FnCtx{ .decl = decl, .ret_type = sp.get(ty).function_type.ret, .self_type = self.owner_of(decl), .abstract = abstract };
    self.open_scope(self.dp(.flags, decl).is_global, if (off == 1) ctx.self_type else .none, v);
    const g = self.template_of.get(decl);
    const args = self.realized_args.get(decl);
    const view = if (g) |t| !statics.only_templates(self, self.dp(.ty, t).*) else false;
    // a where clause sees its own parameter and the ones before it; realized `type` parameters are static values
    var slot: usize = 0;
    for (self.params_of(v), 0..) |pn, i| {
        const p = self.param(pn);
        const pt = sp.get(ty).function_type.params[i + off];
        if (p.default != 0) _ = self.check(&ctx, p.default, pt);
        for (self.params_of(v)[0..i], 0..) |q, j| if (self.param_name(q, j) == self.name_at(p, i)) self.doc.h21_report(.duplicate_declaration, pn, self.name_at(p, i), decl);
        const pd = self.h02_declare_local(self.name_at(p, i), pn, .parameter, pt);
        self.node_decl[pn] = pd;
        const gp = if (g) |t| self.sig(t).params[i + off] else pt;
        self.dp(.flags, pd).is_view = view and statics.templated(self, gp) != .none;
        if (args) |a| if (statics.generic_slot(self, gp)) {
            if (sp.tag(gp) == .meta_type) self.dp(.value, pd).* = sp.get(a).aggregate.elems[slot];
            slot += 1;
        };
        calls.link(self, p.name, pd, pt);
        self.check_guards(&ctx, p, pt);
    }
    self.check_unit(&ctx, self.arg(v, 1));
    self.h04_pop_scope();
    if (off == 1 and self.dp(.flags, @enumFromInt(first)).writes) self.dp(.flags, decl).writes = true;
    self.dp(.state, decl).* = if (self.errors_since(mark, v)) .failed else .done;
    if (!abstract) statics.snapshot(self, decl, v, first);
}

pub fn errors_since(self: *Resolver, mark: usize, v: NodeId) bool {
    const d = self.doc.diagnostics.sliced();
    var s: ?[2]NodeId = null;
    for (d.severity[mark..], d.node[mark..]) |sev, n| if (sev == .@"error") {
        if (s == null) s = self.subtree(v);
        if (n >= s.?[0] and n < s.?[1]) return true;
    };
    return false;
}

pub fn check_unit(self: *Resolver, ctx: *FnCtx, body: NodeId) void {
    const sp = &self.static_pool;
    if (self.nk(body) != .block) {
        _ = self.check(ctx, body, ctx.ret_type);
        return;
    }
    const t = self.h09_check_expr(ctx, body, .none);
    const r = sp.apply_vars(&self.abstract_pool, ctx.ret_type);
    // a `{}` body that never returns a value returns unit, a body with a result returns it on every path (`$main` falls off with 0)
    if (r != .none and sp.tag(r) == .type_var) _ = sp.unify(&self.abstract_pool, ctx.ret_type, .unit_type) else if (r != .none and (ctx.decl == .none or self.dp(.name, ctx.decl).* != .main) and r != .unit_type and r != .runit_type and r != .poison_type and t != .never_type and t != .poison_type and !self.doc.has(body)) _ = self.report(.missing_ret, body, 0, 0);
}

pub const prim_types = blk: {
    var t: [256]StaticPool.Index = @splat(.none);
    for (@typeInfo(StaticPool.Index).@"enum".fields) |f| if (std.mem.endsWith(u8, f.name, "_type") and @hasField(NodeKind, "type_" ++ f.name[0 .. f.name.len - 5])) {
        t[@intFromEnum(@field(NodeKind, "type_" ++ f.name[0 .. f.name.len - 5]))] = @enumFromInt(f.value);
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
    const a0 = self.arg(node, 0);
    const a1 = self.arg(node, 1);
    const k = self.nk(node);
    if (ctx.interpreted and class(k).stc and !self.doc.has(node)) _ = self.report(.redundant_stc, node, 0, 0);
    const t: StaticPool.Index = switch (k) {
        .int, .float, .char, .string, .boolean_true, .boolean_false => statics.literal_type(self, node, expected),
        .identifier, .identifier_self => blk: {
            const d = self.use(node);
            if (d == .none) break :blk .poison_type;
            self.check_init(node, d);
            const ty = self.dp(.ty, d).*;
            break :blk if (ty == .none) .poison_type else ty;
        },
        .capture => self.h09_check_expr(ctx, a0, expected),
        .block => blk: {
            self.h03_push_scope();
            defer self.h04_pop_scope();
            var last: StaticPool.Index = .unit_type;
            const stmts = self.kids(node);
            for (stmts, 0..) |s, i| {
                const declares = class(self.nk(s)).declares;
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
            const r = if ((k == .binary_add or k == .binary_sub) and self.elem_ptr(j)) j else if (wraps and !sp.class(j).is_integer and sp.tag(j) != .type_var) self.mismatch(node, j, .none) else self.numeric(node, j, j);
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
        .binary_logic_or, .binary_logic_xor, .binary_logic_and => blk: {
            _ = self.check(ctx, a0, .bool_type);
            const before = self.uninit;
            _ = self.check(ctx, a1, .bool_type);
            if (k != .binary_logic_xor) self.uninit = before;
            break :blk .bool_type;
        },
        .neg_logic => blk: { // `!` is logical on bools and bitwise on integers
            const st = self.h09_check_expr(ctx, a0, expected);
            break :blk if (st == .bool_type or sp.class(st).is_integer) st else self.mismatch(node, st, .bool_type);
        },
        .neg_num => if (self.is_literal(node)) statics.literal_type(self, node, expected) else self.numeric(node, self.h09_check_expr(ctx, a0, expected), .none),
        .fun_call, .with => calls.h12_check_call(self, ctx, node),
        .member => self.h13_check_member(ctx, node),
        .array_index => blk: {
            var st = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            if (is_range_kind(self.nk(a1))) break :blk self.report(.genexpr_index, a1, 0, 0);
            const it = self.h09_check_expr(ctx, a1, .none);
            if (!sp.class(it).is_integer) _ = self.mismatch(a1, it, .u64_type);
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
            if (self.nk(a0) == .identifier) self.uninit &= ~self.init_bit(self.h01_lookup(self.name_of(a0)));
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
            const elems = if (k == .array) self.kids(node) else &[_]NodeId{};
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
            break :blk if (!sp.class(from).has_layout or !sp.class(to).has_layout or sp.layout(to).size < sp.layout(from).size) self.report(.invalid_cast, node, from, to) else to;
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
            if (self.nk(a0) == .identifier and statics.is_template(self, self.node_decl[a0])) break :blk self.report(.unrealized_template, a0, 0, 0);
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
            for ([_]NodeId{ g.lo, g.hi }) |x| if (x != 0 and hint != .none and self.is_literal(x) and statics.literal_type(self, x, hint) != hint) {
                hint = .none;
            };
            const b = if (k == .gen_incl or k == .gen_excl) self.pair(ctx, node, a0, a1, hint) else self.operand(ctx, a0, hint);
            if (!sp.class(b).is_integer) break :blk self.mismatch(node, b, .u64_type);
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
            if (k == .deinit and self.nk(a0) == .identifier and self.node_decl[a0] != .none and !self.dp(.flags, self.node_decl[a0]).is_global) {
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
            break :blk self.dp(.ty, d).*;
        },
        // type expressions in value position: the value is a type
        else => if (class(k).type_expr or k == .unify_variants or self.type_kind(node) != .variable) (if (statics.deferred(self, ctx, node)) |v| sp.type_of(v) else types.meta_of(self, node)) else .unit_type,
    };
    return self.set(node, t);
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
    const parts = self.statement(node);
    const n = parts.node;
    const flags = parts.flags;
    const kind = parts.kind;
    if (ctx.interpreted and is_type_decl(kind)) {
        _ = self.h09_check_expr(ctx, parts.value, .none);
        const t = statics.deferred(self, ctx, parts.value);
        for (parts.ids) |id| {
            const d = self.declare(id, n, kind, if (t) |x| sp.type_of(x) else types.meta_of(self, parts.value), flags);
            self.dp(.state, d).* = .done;
            self.dp(.value, d).* = t orelse .none;
        }
        return .unit_type;
    }
    if (kind != .variable) { // local function / type / trait
        for (parts.ids) |id| {
            const d = self.declare(id, n, kind, .none, flags);
            self.h05_ensure_signature(d);
            self.h06_check_body(d);
        }
        return .unit_type;
    }
    const values = parts.values;
    // a write into a place (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    if (parts.ids.len == 1 and self.name_of(parts.ids[0]) == .none) {
        const pt = self.h18_check_place(ctx, parts.ids[0]);
        for (values) |v| _ = self.check(ctx, v, pt);
        return .unit_type;
    }
    const declaring = parts.type != 0 or @as(u8, @bitCast(flags)) != 0;
    var ty: StaticPool.Index = if (parts.type != 0) types.realized_type(self, ctx, parts.type) else .none;
    // untyped: visible names are assigned, their type is shared by the new ones
    var existing: [64]Decl.Index = undefined;
    for (parts.ids, 0..) |id, i| {
        existing[i] = if (declaring or self.pre_declared(self.node_decl[id], n)) .none else self.h01_lookup(self.name_of(id));
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
            const vt = self.check(ctx, v, if (i < parts.ids.len and existing[i] != .none) self.dp(.ty, existing[i]).* else ty);
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
    for (parts.ids, 0..) |id, i| {
        const d = if (existing[i] != .none) existing[i] else self.declare(id, n, .variable, if (ty == .none) .poison_type else ty, flags);
        if (existing[i] != .none) self.uninit &= ~self.init_bit(d) else if (values.len == 0 and !self.dp(.flags, d).is_global and self.scalar(self.dp(.ty, d).*)) self.track(d);
        if (values.len > 0 and self.node_type[values[@min(i, values.len - 1)]] != .poison_type and (existing[i] == .none or (self.interpreter.depth > 0 and !ctx.interpreted)) and (self.dp(.flags, d).is_stc or ctx.in_static)) {
            self.dp(.value, d).* = statics.retype(self, statics.static_of(self, ctx, values[@min(i, values.len - 1)]), self.dp(.ty, d).*);
            // an unlengthed static takes the length of its value
            const v = self.dp(.value, d).*;
            if (v != .none and sp.tag(v) == .aggregate_value and sp.has_vars(self.dp(.ty, d).*)) _ = sp.unify(&self.abstract_pool, self.dp(.ty, d).*, sp.type_of(v));
            const dt = self.dp(.ty, d).*;
            if (v != .none and sp.tag(v) == .aggregate_value and sp.tag(dt) == .array_type and sp.tag(sp.get(dt).array_type.len) == .int_value and sp.get(sp.get(dt).array_type.len).int.bits != sp.get(v).aggregate.elems.len)
                _ = self.report(.type_mismatch, values[@min(i, values.len - 1)], sp.type_of(v), dt);
        }
    }
    return .unit_type;
}

fn h13_check_member(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parent = self.arg(node, 0);
    const name = self.name_of(self.arg(node, 1));
    const pt = self.h09_check_expr(ctx, parent, .none);
    if (pt == .poison_type) return pt;
    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = sp.tag(pt) == .meta_type;
    const base = if (!on_type) sp.apply_vars(&self.abstract_pool, pt) else statics.deferred(self, ctx, parent) orelse return .poison_type;
    if (base == .poison_type) return base;
    if (sp.tag(base) == .type_var) return self.report(.uninferable_type, parent, base, .none);
    if (statics.templated(self, base) != .none) return statics.template_member(self, node, statics.templated(self, base), name);
    const view = if (self.nk(parent) == .identifier and self.node_decl[parent] != .none) self.dp(.flags, self.node_decl[parent]).is_view else false;
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

pub fn write_access(self: *Resolver, node: NodeId, a: Access) void {
    switch (a) {
        .ok => self.wrote(node),
        .immutable => self.doc.h21_report(.assign_to_immutable, node, 0, 0),
        .through_ptr => self.doc.h21_report(.write_through_immutable_pointer, node, 0, 0),
    }
}

// a write into a place rooted at `self` (not through a pointer it holds) makes its method one that writes self
fn wrote(self: *Resolver, place: NodeId) void {
    var n = place;
    while (self.nk(n) != .identifier_self) switch (self.nk(n)) {
        .capture => n = self.arg(n, 0),
        .member, .array_index, .dereference => {
            const p = self.arg(n, 0);
            if (self.nk(p) != .identifier_self and (self.nk(n) == .dereference or self.static_pool.is_ptr(self.node_type[p]))) return;
            n = p;
        },
        else => return,
    };
    const d = self.node_decl[n];
    if (d != .none and self.dp(.kind, d).* == .self) self.dp(.flags, d).writes = true;
}

// ------------------------------------------------------------------------------------------ //
// types, generics, diagnostics
// ------------------------------------------------------------------------------------------ //

// ------------------------------------------------------------------------------------------ //
// helpers
// ------------------------------------------------------------------------------------------ //

pub const max_nesting = 256;
pub const Param = struct { ty: NodeId = 0, name: NodeId = 0, default: NodeId = 0, where: NodeId = 0, @"else": NodeId = 0, is_mut: bool = false, stc: bool = false };
pub const Parts = struct { type: NodeId = 0, ids: []const NodeId = &.{}, value: NodeId = 0 };
pub const Access = enum { ok, immutable, through_ptr };

const dollar_names = blk: {
    @setEvalBranchQuota(100_000);
    var t: [64][]const u8 = undefined;
    for (&t, 0..) |*s, i| s.* = std.fmt.comptimePrint("${d}", .{i});
    break :blk t;
};

pub inline fn nk(self: *const Resolver, n: NodeId) NodeKind {
    return self.tree.ast_nodes.pool.nk.buf[n];
}

pub inline fn arg(self: *const Resolver, n: NodeId, i: u1) NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.tree.ast_nodes.pool.args.buf[n]);
    return slots[i];
}

pub fn kids(self: *const Resolver, n: NodeId) []const NodeId {
    const a = self.tree.ast_nodes.pool.args.buf[n];
    return self.tree.extra_childrefs.buf[a[0]..][0..a[1]];
}

// child i as a list: the children of a `wrapper` node, or the child alone
pub fn list_at(self: *const Resolver, n: NodeId, comptime i: u1, comptime wrapper: NodeKind) []const NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.tree.ast_nodes.pool.args.buf[n]);
    return if (self.nk(slots[i]) == wrapper) self.kids(slots[i]) else slots[i..][0..1];
}

pub fn text(self: *const Resolver, n: NodeId) []const u8 {
    const span = self.tree.span_store[self.arg(n, 0)];
    return self.src_bytes[span[0]..span[1]];
}

pub fn name_of(self: *Resolver, n: NodeId) NamePool.Index {
    return switch (self.nk(n)) {
        .identifier => self.name_pool.intern(self.text(n)),
        .identifier_self => .self,
        else => .none,
    };
}

pub inline fn dp(self: *Resolver, comptime f: @EnumLiteral(), d: Decl.Index) *@FieldType(Decl, @tagName(f)) {
    return &@field(self.decls.pool, @tagName(f)).buf[@intFromEnum(d)];
}

pub inline fn set(self: *Resolver, n: NodeId, t: StaticPool.Index) StaticPool.Index {
    self.node_type[n] = t;
    return t;
}

pub fn report(self: *Resolver, code: Doctor.Disorder, n: NodeId, a: anytype, b: anytype) StaticPool.Index {
    self.doc.h21_report(code, n, a, b);
    return self.set(n, .poison_type);
}

pub fn check_guards(self: *Resolver, ctx: *FnCtx, p: Param, t: StaticPool.Index) void {
    if (p.where != 0) _ = self.check(ctx, p.where, .bool_type);
    if (p.@"else" != 0) _ = if (self.nk(p.@"else") == .assign) self.h09_check_expr(ctx, p.@"else", .none) else self.check(ctx, p.@"else", t);
}

const InitState = struct { tracked: u32, uninit: u64 };

pub fn init_enter(self: *Resolver) InitState {
    defer self.uninit = 0;
    return .{ .tracked = self.init_tracked.head, .uninit = self.uninit };
}

pub fn init_leave(self: *Resolver, s: InitState) void {
    self.init_tracked.head = s.tracked;
    self.uninit = s.uninit;
}

pub fn check(self: *Resolver, ctx: *FnCtx, n: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const t = self.h09_check_expr(ctx, n, expected);
    // a case with a payload is a constructor, a value of it needs the payload
    if (t != .poison_type and self.nk(n) == .member and self.static_pool.tag(t) == .variant_case_type and self.static_pool.get(t).variant_case_type.payload != .none) return self.report(.type_mismatch, n, t, expected);
    return self.h10_expect(n, t, expected);
}

pub const Class = packed struct(u8) { stc: bool = false, loop: bool = false, range: bool = false, type_expr: bool = false, declares: bool = false, runit: bool = false, literal: bool = false, _pad: u1 = 0 };

const classes = blk: {
    var t: [256]Class = @splat(.{});
    for ([_]NodeKind{ .stcif_then, .stcif_else, .stcwhile, .stcwhile_with_repeat_stmt, .stcfor_seq, .stcfor_var_in_seq, .stcloop, .stcloop_with_repeat_stmt, .stcmatch }) |k| t[@intFromEnum(k)].stc = true;
    for ([_]NodeKind{ .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt }) |k| t[@intFromEnum(k)].loop = true;
    for ([_]NodeKind{ .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl }) |k| t[@intFromEnum(k)].range = true;
    for (@intFromEnum(NodeKind.type_ptrmut)..@intFromEnum(NodeKind.type_stcfun) + 1) |i| t[i].type_expr = true;
    for ([_]NodeKind{ .type_array, .type_array_unlengthed, .def_fun_declaration, .typeof }) |k| t[@intFromEnum(k)].type_expr = true;
    for ([_]NodeKind{ .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc }) |k| t[@intFromEnum(k)].declares = true;
    for ([_]NodeKind{ .block, .if_then, .if_else, .stcif_then, .stcif_else, .match, .stcmatch }) |k| t[@intFromEnum(k)].runit = true;
    for ([_]NodeKind{ .int, .float, .char, .string }) |k| t[@intFromEnum(k)].literal = true;
    break :blk t;
};

pub inline fn class(k: NodeKind) Class {
    return classes[@intFromEnum(k)];
}

pub fn is_fn(kind: Decl.Kind) bool {
    return switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => true,
        else => false,
    };
}

pub fn is_range_kind(k: NodeKind) bool {
    return class(k).range;
}

pub fn push_decl(self: *Resolver, name: NamePool.Index, node: NodeId, kind: Decl.Kind, ty: StaticPool.Index, flags: Decl.Flags) Decl.Index {
    const d: Decl.Index = @enumFromInt(self.decls.len());
    const lazy = flags.is_global or is_fn(kind) or is_type_decl(kind);
    self.decls.push(.{ .name = name, .node = node, .kind = kind, .flags = flags, .state = if (lazy) .unresolved else .done, .ty = ty, .value = .none, .next_overload = .none });
    return d;
}

pub fn is_type_decl(kind: Decl.Kind) bool {
    return kind == .type_alias or kind == .record or kind == .variant or kind == .trait;
}

// a declared global row is reused, anything else becomes a new local
fn declare(self: *Resolver, id: NodeId, stmt: NodeId, kind: Decl.Kind, ty: StaticPool.Index, flags: Decl.Flags) Decl.Index {
    var d = self.node_decl[id];
    if (!self.pre_declared(d, stmt)) {
        d = self.h02_declare_local(self.name_of(id), stmt, kind, ty);
        self.dp(.flags, d).* = flags;
        self.node_decl[id] = d;
    } else if (ty != .none) self.dp(.ty, d).* = ty;
    _ = self.set(id, if (ty == .none) .unit_type else ty);
    return d;
}

// s1 rows of this very statement are reused instead of declared again
fn pre_declared(self: *Resolver, d: Decl.Index, stmt: NodeId) bool {
    return d != .none and self.dp(.flags, d).is_global and self.dp(.node, d).* == stmt;
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
pub fn open_scope(self: *Resolver, barrier: bool, self_type: StaticPool.Index, node: NodeId) void {
    self.h03_push_scope();
    if (barrier) {
        self.local_names.push(.none);
        self.local_decls.push(.none);
    }
    if (self_type != .none) self.dp(.flags, self.h02_declare_local(.self, node, .self, self.self_ptr(self_type))).is_mut = true;
}

// methods: the owning type is the value of the trait body row right before its members; realizations ask their template
fn owner_of(self: *Resolver, decl: Decl.Index) StaticPool.Index {
    if (self.template_of.get(decl)) |t| return self.owner_of(t);
    if (self.dp(.kind, decl).* != .trait_member) return .none;
    var d = @intFromEnum(decl);
    while (self.decls.pool.kind.buf[d] != .trait) d -= 1;
    return self.decls.pool.value.buf[d];
}

pub fn value_node(self: *Resolver, d: Decl.Index) NodeId {
    const n = self.dp(.node, d).*;
    return switch (self.nk(n)) {
        .assign, .assign_typed => self.arg(n, 1),
        else => n,
    };
}

pub const Def = struct { core: NodeId, body: NodeId = 0, size: NodeId = 0, tagof: NodeId = 0 };

pub fn definition(self: *const Resolver, n: NodeId) Def {
    var d = Def{ .core = n };
    while (true) : (d.core = self.arg(d.core, 0)) switch (self.nk(d.core)) {
        .def_type_implof, .def_variant_implof => d.body = self.arg(d.core, 1),
        .def_type_assertsize, .def_variant_assertsize => d.size = self.arg(d.core, 1),
        .def_variant_tagof => d.tagof = self.arg(d.core, 1),
        else => return d,
    };
}

fn core(self: *const Resolver, n: NodeId) NodeId {
    return self.definition(n).core;
}

pub fn meta(kind: Decl.Kind, other: StaticPool.Index) StaticPool.Index {
    return switch (kind) {
        .record => .type_type,
        .variant => .variant_type,
        .trait => .trait_type,
        else => other,
    };
}

pub fn type_kind(self: *const Resolver, n: NodeId) Decl.Kind {
    return switch (self.nk(self.core(n))) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

fn decl_kind(self: *const Resolver, type_node: NodeId, value: NodeId) Decl.Kind {
    const tk = self.type_kind(value);
    return switch (self.nk(type_node)) {
        .type_fun => .function,
        .type_stcfun => .static_function,
        .type_inlfun => .inlined_function,
        .type_type, .type_variant, .type_trait => if (value != 0 and self.nk(value) == .def_fun) .static_function else switch (self.nk(type_node)) {
            .type_type => if (tk == .record) .record else .type_alias,
            .type_variant => if (tk == .variant) .variant else .type_alias,
            else => if (tk == .trait) .trait else .type_alias,
        },
        .none => if (value != 0 and (self.nk(value) == .def_fun or self.nk(value) == .def_fun_declaration)) .function else .variable,
        else => .variable,
    };
}

fn unwrap_mods(self: *const Resolver, n0: NodeId, flags: *Decl.Flags) NodeId {
    var n = n0;
    while (true) : (n = self.arg(n, 0)) switch (self.nk(n)) {
        .mod_pub => flags.is_pub = true,
        .mod_mut => flags.is_mut = true,
        .mod_stc => flags.is_stc = true,
        else => return n,
    };
}

pub const Stmt = struct {
    node: NodeId,
    flags: Decl.Flags,
    kind: Decl.Kind,
    type: NodeId,
    ids: []const NodeId,
    value: NodeId,
    values: []const NodeId,

    pub fn is_member(s: Stmt) bool {
        return s.ids.len == 1 and is_fn(s.kind);
    }
};

pub fn statement(self: *const Resolver, n0: NodeId) Stmt {
    var flags = Decl.Flags{};
    const n = self.unwrap_mods(n0, &flags);
    const p = self.stmt_parts(n);
    return .{ .node = n, .flags = flags, .kind = self.decl_kind(p.type, p.value), .type = p.type, .ids = p.ids, .value = p.value, .values = if (p.value == 0) &.{} else self.list_at(n, 1, .partial__assign_multival) };
}

fn stmt_parts(self: *const Resolver, n: NodeId) Parts {
    return switch (self.nk(n)) {
        .def_var => .{ .type = self.arg(n, 0), .ids = self.list_at(n, 1, .partial__destructure) },
        .assign_typed => .{ .type = self.arg(self.arg(n, 0), 0), .ids = self.list_at(self.arg(n, 0), 1, .partial__destructure), .value = self.arg(n, 1) },
        .assign => .{ .ids = self.list_at(n, 0, .partial__destructure), .value = self.arg(n, 1) },
        else => .{},
    };
}

pub fn param(self: *const Resolver, n0: NodeId) Param {
    var p = Param{};
    var n = n0;
    while (true) {
        switch (self.nk(n)) {
            .partial__fun_def_param_named, .partial__type_def_param_named => p.name = self.arg(n, 1),
            .partial__fun_def_param_default, .partial__type_def_param_default => p.default = self.arg(n, 1),
            .partial__fun_def_param_where, .partial__type_def_param_where => p.where = self.arg(n, 1),
            .partial__fun_def_param_stcwhere => {
                p.where = self.arg(n, 1);
                p.stc = true;
            },
            .partial__fun_def_param_where_else, .partial__type_def_param_where_else => p.@"else" = self.arg(n, 1),
            .partial__type_def_param_mut => p.is_mut = true,
            .partial__fun_def_param, .partial__type_def_param => {
                p.ty = self.arg(n, 0);
                return p;
            },
            else => {
                p.ty = n;
                return p;
            },
        }
        n = self.arg(n, 0);
    }
}

// unnamed parameters and fields are `$0`, `$1`, ...
pub fn param_name(self: *Resolver, pn: NodeId, i: usize) NamePool.Index {
    return self.name_at(self.param(pn), i);
}

pub fn name_at(self: *Resolver, p: Param, i: usize) NamePool.Index {
    return if (p.name != 0) self.name_of(p.name) else self.name_pool.intern(dollar_names[@min(i, 63)]);
}

pub fn template_field(self: *Resolver, g: Decl.Index, name: NamePool.Index) ?NodeId {
    for (self.fields_of_node(self.core(self.arg(self.value_node(g), 1))), 0..) |f, i| if (self.param_name(f, i) == name) return f;
    return null;
}

pub fn params_of(self: *const Resolver, v: NodeId) []const NodeId {
    if (self.nk(v) != .def_fun and self.nk(v) != .def_fun_declaration) return &.{};
    return self.kids(self.arg(self.arg(v, 0), 0));
}

pub fn fields_of_node(self: *const Resolver, c: NodeId) []const NodeId {
    return if (self.nk(c) == .partial__type_def_param_tuple) self.kids(c) else self.kids(self.arg(c, 0));
}

pub fn fields_of(self: *Resolver, rec: StaticPool.Index) []const NodeId {
    return self.fields_of_node(self.core(self.value_node(self.static_pool.get(rec).custom_type.decl)));
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
pub fn sig(self: *Resolver, d: Decl.Index) StaticPool.FunType {
    return self.static_pool.get(self.dp(.ty, d).*).function_type;
}

pub fn self_off(self: *Resolver, d: Decl.Index) usize {
    return @intFromBool(self.dp(.kind, d).* == .trait_member and self.dp(.name, d).* != .init);
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
    return if (sp.class(c).is_nominal or sp.class(c).is_variant) c else t;
}

pub fn fresh_var(self: *Resolver, origin: NodeId) StaticPool.Index {
    return self.static_pool.intern(.{ .abstract_type = self.abstract_pool.fresh(origin) });
}

pub fn fn_ret(self: *Resolver, d: Decl.Index) StaticPool.Index {
    const t = types.decl_type(self, d);
    return if (self.static_pool.tag(t) == .function_type) self.static_pool.get(t).function_type.ret else .poison_type;
}

pub fn method(self: *Resolver, node: NodeId, m: Decl.Index) StaticPool.Index {
    self.node_decl[node] = m;
    return types.decl_type(self, m);
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
pub fn real(self: *Resolver, d: Decl.Index) Decl.Index {
    const v = self.dp(.value, d).*;
    return if (v != .none and self.static_pool.tag(v) == .function_value) self.static_pool.get(v).function else d;
}

pub fn group_head(self: *Resolver, first: Decl.Index, d: Decl.Index) Decl.Index {
    var h = first;
    while (h != d and !calls.same_params(self, h, d)) h = self.dp(.next_overload, h).*;
    return h;
}

pub fn template(self: *Resolver, d: Decl.Index) Decl.Kind {
    const n = self.dp(.node, d).*;
    if (self.nk(n) != .assign_typed or self.nk(self.arg(n, 1)) != .def_fun) return .variable;
    return switch (self.nk(self.arg(self.arg(n, 0), 0))) {
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

pub fn integer(self: *Resolver, ctx: *FnCtx, n: NodeId) bool {
    const t = self.operand(ctx, n, if (self.nk(n) == .neg_num) .i64_type else .u64_type);
    if (t == .poison_type or self.static_pool.class(t).is_integer) return true;
    _ = self.report(.type_mismatch, n, t, .u64_type);
    return false;
}

pub fn signature_mentions(self: *Resolver, f: NodeId, v: NodeId) bool {
    const header = self.arg(f, 0);
    if (self.nk(header) != .partial__fun_def_header_ret or self.mentions(self.arg(header, 1), v)) return true;
    for (self.params_of(f)) |pn| if (self.mentions(self.param(pn).ty, v)) return true;
    return false;
}

pub fn mentions(self: *Resolver, n: NodeId, v: NodeId) bool {
    const params = self.params_of(v);
    const s = self.subtree(n);
    for (s[0]..s[1]) |i| {
        if (self.nk(@intCast(i)) != .identifier) continue;
        const nm = self.name_of(@intCast(i));
        for (params, 0..) |pn, j| if (self.param_name(pn, j) == nm) return true;
    }
    return false;
}

pub fn children(self: *const Resolver, n: NodeId) []const NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.tree.ast_nodes.pool.args.buf[n]);
    return switch (ParseTree.Node.nk_childc[@intFromEnum(self.nk(n))]) {
        .one => slots[0..1],
        .two => slots,
        .many => self.kids(n),
        else => &.{},
    };
}

pub fn subtree(self: *const Resolver, n: NodeId) [2]NodeId {
    var s: [2]NodeId = .{ n, n + 1 };
    for (self.children(n)) |c| {
        const x = self.subtree(c);
        s = .{ @min(s[0], x[0]), @max(s[1], x[1]) };
    }
    return s;
}

pub fn arg_value(self: *const Resolver, a: NodeId) NodeId {
    return if (self.nk(a) == .partial__fun_call_assigned_param) self.arg(a, 1) else a;
}

pub fn concrete(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and self.static_pool.tag(self.static_pool.apply_vars(&self.abstract_pool, t)) != .type_var;
}

fn is_numeric(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and (self.static_pool.class(t).is_integer or self.static_pool.class(t).is_float);
}

fn folded(self: *Resolver, n: NodeId) bool {
    return self.is_literal(n) or self.node_value[n] != .none and switch (self.nk(n)) {
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap => true,
        else => false,
    };
}

fn numeric(self: *Resolver, node: NodeId, t: StaticPool.Index, result: StaticPool.Index) StaticPool.Index {
    if (self.is_numeric(t) or self.static_pool.tag(t) == .type_var) return if (result == .none) t else result;
    return self.mismatch(node, t, .none);
}

pub fn mismatch(self: *Resolver, n: NodeId, t: StaticPool.Index, want: StaticPool.Index) StaticPool.Index {
    return if (t == .poison_type) t else self.report(.type_mismatch, n, t, want);
}

fn operand(self: *Resolver, ctx: *FnCtx, n: NodeId, hint: StaticPool.Index) StaticPool.Index {
    return if (self.is_literal(n)) self.check(ctx, n, hint) else self.h09_check_expr(ctx, n, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn pair(self: *Resolver, ctx: *FnCtx, node: NodeId, l: NodeId, r: NodeId, hint: StaticPool.Index) StaticPool.Index {
    const swap = self.is_literal(l) and !self.is_literal(r);
    const t1 = self.operand(ctx, if (swap) r else l, hint);
    const add = self.nk(node) == .binary_add;
    if ((add or !swap and self.nk(node) == .binary_sub) and self.elem_ptr(t1)) return if (self.integer(ctx, if (swap) l else r)) t1 else .poison_type;
    const t2 = self.operand(ctx, if (swap) l else r, t1);
    if (add and self.elem_ptr(t2) and self.static_pool.class(t1).is_integer) return t2;
    if (t1 == .poison_type or t2 == .poison_type) return .poison_type;
    if (self.static_pool.tag(t1) == .meta_type and self.static_pool.tag(t2) == .meta_type) return t1;
    var j = self.static_pool.join(&self.abstract_pool, t1, t2);
    if (j.ty == .none) j = self.static_pool.join(&self.abstract_pool, self.deref(t1), self.deref(t2)); // `self == Toggle.On`
    return if (j.ty == .none) self.report(.type_mismatch, node, t1, t2) else j.ty;
}

fn need_deinit(self: *Resolver, node: NodeId, t0: StaticPool.Index) void {
    const t = self.static_pool.apply_vars(&self.abstract_pool, t0);
    if (t != .poison_type and self.static_pool.lookup_member(t, .deinit) == .none)
        self.doc.h21_report(.no_deinit, node, t, 0);
}

pub fn writable(self: *Resolver, node: NodeId) Access {
    return switch (self.nk(node)) {
        .capture => self.writable(self.arg(node, 0)),
        .identifier, .identifier_self => blk: {
            const d = self.node_decl[node];
            if (d == .none) break :blk .ok;
            const f = self.dp(.flags, d).*;
            break :blk if (f.is_mut or f.is_stc or self.dp(.kind, d).* == .self) .ok else .immutable;
        },
        .member => blk: {
            const base = self.through(self.arg(node, 0), true);
            break :blk if (base != .ok) base else if (self.field_mut(self.node_type[self.arg(node, 0)], self.name_of(self.arg(node, 1)))) .ok else .immutable;
        },
        .array_index => self.through(self.arg(node, 0), true),
        .dereference => self.through(self.arg(node, 0), false),
        else => .immutable,
    };
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent itself is writable
pub fn through(self: *Resolver, parent: NodeId, or_place: bool) Access {
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
    if (t != .none and sp.tag(t) == .template_type) if (self.template_field(sp.get(t).template_type, name)) |f| return self.param(f).is_mut;
    if (t == .none or sp.tag(t) != .record_type) return false;
    for (sp.get(t).custom_type.field_names, 0..) |n, i| if (n == name) return self.param(self.fields_of(t)[i]).is_mut;
    return false;
}

fn scalar(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and t != .poison_type and self.static_pool.tag(t) != .record_type and self.static_pool.tag(t) != .array_type;
}

fn track(self: *Resolver, d: Decl.Index) void {
    if (self.init_tracked.head >= 64) return;
    self.uninit |= @as(u64, 1) << @intCast(self.init_tracked.head);
    self.init_tracked.push(d);
}

fn init_bit(self: *Resolver, d: Decl.Index) u64 {
    return for (self.init_tracked.sliced(), 0..) |x, i| {
        if (x == d) break @as(u64, 1) << @intCast(i);
    } else 0;
}

fn check_init(self: *Resolver, node: NodeId, d: Decl.Index) void {
    if (self.uninit == 0) return;
    const bit = self.init_bit(d);
    if (self.uninit & bit == 0) return;
    self.doc.h21_report(.use_before_initialization, node, self.dp(.name, d).*, 0);
    self.uninit &= ~bit;
}

pub const Loop = struct { cond: NodeId = 0, repeat: NodeId = 0, head: NodeId = 0, seq: NodeId = 0, variable: NodeId = 0, body: NodeId };

pub fn node_info(self: *const Resolver, b: Body, comptime field: @EnumLiteral(), n: NodeId) @FieldType(NodeInfo, @tagName(field)) {
    if (n -% b.lo < b.len) return @field(self.body_nodes.pool, @tagName(field)).buf[b.start + n - b.lo];
    return @field(self, if (field == .ty) "node_type" else "node_" ++ @tagName(field))[n];
}

pub fn field_of(self: *Resolver, rec: StaticPool.Index, a: NodeId, i: usize) ?u32 {
    if (self.nk(a) != .partial__fun_call_assigned_param) return @intCast(i);
    return switch (self.static_pool.lookup_member(rec, self.name_of(self.arg(a, 0)))) {
        .field => |f| f.index,
        else => null,
    };
}

pub fn narrowed(self: *const Resolver, target: NodeId) NodeId {
    const inner = if (self.nk(target) == .type_ptr or self.nk(target) == .type_ptrmut) self.arg(target, 0) else target;
    return if (self.nk(inner) == .type_array) self.range(self.arg(inner, 0)).lo else 0;
}

pub fn loop_parts(self: *const Resolver, n: NodeId) Loop {
    const a0 = self.arg(n, 0);
    const a1 = self.arg(n, 1);
    return switch (self.nk(n)) {
        .@"while", .stcwhile => .{ .cond = a0, .body = a1 },
        .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => .{ .cond = self.arg(a0, 0), .repeat = a1, .head = a0, .body = self.arg(a0, 1) },
        .loop, .stcloop => .{ .body = a0 },
        .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => .{ .repeat = a0, .body = a1 },
        .for_var_in_seq, .stcfor_var_in_seq => .{ .head = a0, .seq = self.arg(a0, 0), .variable = a1, .body = self.arg(a0, 1) },
        else => .{ .head = n, .seq = a0, .body = a1 },
    };
}

pub const Range = struct { lo: NodeId, hi: NodeId, incl: bool };

pub fn range(self: *const Resolver, n: NodeId) Range {
    const k = self.nk(n);
    const two = k == .gen_incl or k == .gen_excl;
    return .{
        .lo = if (two or k == .gen_lowerbound) self.arg(n, 0) else 0,
        .hi = if (two) self.arg(n, 1) else if (k == .gen_lowerbound) 0 else self.arg(n, 0),
        .incl = k == .gen_incl or k == .gen_upperbound_incl,
    };
}

pub fn literal_core(self: *const Resolver, node: NodeId, neg: *bool) NodeId {
    var n = node;
    while (true) switch (self.nk(n)) {
        .capture => n = self.arg(n, 0),
        .neg_num => {
            neg.* = !neg.*;
            n = self.arg(n, 0);
        },
        else => return n,
    };
}

pub fn is_literal(self: *const Resolver, node: NodeId) bool {
    var neg = false;
    return class(self.nk(self.literal_core(node, &neg))).literal;
}

pub fn unescape(raw: []const u8, buf: []u8) []const u8 {
    if (raw.len > buf.len) return raw;
    var n: usize = 0;
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        var c = raw[i];
        if (c == '\\' and i + 1 < raw.len) {
            i += 1;
            c = switch (raw[i]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => 0,
                else => raw[i],
            };
        }
        buf[n] = c;
        n += 1;
    }
    return buf[0..n];
}
