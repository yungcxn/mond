const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Decls = @import("Decls.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const max_nesting = 256;

// templates and realizations: stcfuns realized per static arguments, functions per length, type or template
const Generics = @This();

// needed to map templates / generics to realizations
// - e.g. of a `stcfun`, or of a function with unlengthed array param., or abstract types
// - since the arguments are one pool index, the whole key is 8 bytes and compares as one.
pub const AbstractKey = packed struct(u64) {
    generic_tuple: DeclPool.Index,
    args_tuple: StaticPool.Index, // due to them being a single `static_pool` index
};

// realizations: the template a declaration was realized from and the static arguments it was realized with
template_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
realized_args: std.AutoHashMapUnmanaged(DeclPool.Index, StaticPool.Index) = .empty,
// functions produced by a stcfun: the realization whose static parameters they see
static_scope: std.AutoHashMapUnmanaged(DeclPool.Index, AbstractKey) = .empty,
// every realization by its template and static arguments
realized: std.AutoHashMapUnmanaged(AbstractKey, StaticPool.Index) = .empty,

pub fn res(self: *Generics) *Resolver {
    return @alignCast(@fieldParentPtr("generics", self));
}

pub fn deinit(self: *Generics, alloc: std.mem.Allocator) void {
    self.template_of.deinit(alloc);
    self.realized_args.deinit(alloc);
    self.static_scope.deinit(alloc);
    self.realized.deinit(alloc);
}

pub fn instantiate(self: *Generics, generic: DeclPool.Index, args: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const key = AbstractKey{ .generic_tuple = generic, .args_tuple = args };
    if (self.realized.get(key)) |got| return got;
    const node = r.decl_pool.get_node(generic);
    // a realization that realizes itself forever eats the static budget and stops there
    if (r.scopes.marks.head > max_nesting) return r.report(.static_eval_failed, r.interpreter.origin(node), generic, 0);
    if (!r.interpreter.charge(node, 64)) return .poison_type;
    const argv = r.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    const argc = argv.len;
    @memcpy(argv, sp.get(args).aggregate.elems);

    if (r.decl_pool.get_kind(generic) != .static_function) {
        // length-generic function: a new declaration per tuple of lengths, the lengths bound in order of appearance
        r.decls.check_body(generic);
        if (r.decl_pool.get_state(generic) == .failed) return .poison_type;
        const d = r.decl_pool.push_decl(r.decl_pool.get_name(generic), node, r.decl_pool.get_kind(generic), .none, r.decl_pool.get_flags(generic));
        self.template_of.put(r.alloc, d, generic) catch @panic("OOM");
        const fv = sp.intern(.{ .function = d });
        self.memo(key, fv);
        const outer = self.static_scope.get(generic);
        if (outer) |k| {
            self.static_scope.put(r.alloc, d, k) catch @panic("OOM");
            r.decls.open_scope(true, .none, 0);
            self.bind_static(k.generic_tuple, k.args_tuple);
        }
        defer if (outer != null) r.scopes.pop();
        r.decls.ensure_signature(d);
        self.realized_args.put(r.alloc, d, args) catch @panic("OOM");
        const ft = sp.get(r.decl_pool.get_ty(d)).function_type;
        const ps = r.scratch(StaticPool.Index, ft.params.len);
        @memcpy(ps, ft.params);
        var i: usize = 0;
        for (ps) |*q| {
            var p = q.*;
            if (!sp.generic_slot(p) or i >= argc) continue;
            i += 1;
            if (sp.templated(p) != .none) q.* = if (sp.get(p) == .ptr_type) sp.ptr_of(argv[i - 1], sp.get(p).ptr_type.mutable) else argv[i - 1];
            if (sp.get(p) == .ptr_type) p = sp.get(p).ptr_type.child;
            if (sp.get(p) == .array_type) _ = sp.unify(&r.abstract_pool, sp.get(p).array_type.len, argv[i - 1]);
        }
        r.decl_pool.set_ty(d, sp.intern(.{ .function_type = .{ .category = ft.category, .params = ps, .ret = ft.ret } }));
        r.decls.check_body(d);
        return fv;
    }

    var ctx = FnCtx{ .decl = generic, .in_static = true };
    r.decls.open_scope(true, .none, 0);
    defer r.scopes.pop();
    const v = r.decls.value_node(generic);
    const params = r.tree.params_of(v);
    self.bind_static(generic, args);
    for (params) |pn| {
        const w = ParseTree.Param.from_node(r.tree, pn).where;
        if (w != 0 and r.interpreter.eval_static(&ctx, w) == .bool_false) _ = r.report(.stcwhere_violated, w, generic, args);
    }
    const unit = r.tree.arg(v, 1);
    const kind = r.decls.type_kind(unit);
    if (kind != .variable) { // a type: memoized before its body, so it can mention itself (`Stream(Child)` inside Stream)
        const d = r.decl_pool.push_decl(r.decl_pool.get_name(generic), unit, kind, .none, .{});
        self.realized_args.put(r.alloc, d, args) catch @panic("OOM");
        self.template_of.put(r.alloc, d, generic) catch @panic("OOM");
        r.decl_pool.set_value(d, sp.reserve_nominal(d));
        self.memo(key, r.decl_pool.get_value(d));
        return r.types.check_type_def(&ctx, d, unit);
    }
    if (r.tree.kind(unit) == .def_fun) {
        const d = r.decl_pool.push_decl(r.decl_pool.get_name(generic), unit, .function, .none, .{});
        const fv = sp.intern(.{ .function = d });
        self.memo(key, fv);
        self.static_scope.put(r.alloc, d, key) catch @panic("OOM");
        r.decls.ensure_signature(d);
        r.decls.check_body(d);
        return fv;
    }
    ctx.in_static = false;
    ctx.interpreted = true;
    ctx.ret_type = r.types.sig(generic).ret;
    const first = r.decl_pool.entries.len();
    const vars = r.abstract_pool.count();
    const outer = r.inits.enter();
    const mark = r.doc.diagnostics.len();
    r.decls.check_unit(&ctx, unit);
    ctx.interpreted = false;
    r.inits.leave(outer);
    if (r.doc.errors_since(r.tree, mark, unit)) {
        self.memo(key, .poison_type);
        return .poison_type;
    }
    for (vars..r.abstract_pool.count()) |i| switch (r.tree.kind(r.abstract_pool.pool.sliced_field(.origin)[i])) {
        .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => if (r.abstract_pool.binding(@enumFromInt(i)) == .none) r.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len),
        else => {},
    };
    const got = r.interpreter.run(&ctx, unit, r.capture(generic, v, first));
    const made = if (sp.tag(ctx.ret_type) == .meta_type and sp.get_tag_prop(got).is_type) sp.nominal_decl(&r.abstract_pool, got) else .none;
    if (made != .none and @intFromEnum(made) >= first) self.template_of.put(r.alloc, made, generic) catch @panic("OOM");
    self.memo(key, got);
    return got;
}

// the static parameters of a stcfun as locals holding the arguments of one realization
fn bind_static(self: *Generics, generic: DeclPool.Index, args: StaticPool.Index) void {
    const r = self.res();
    const sp = &r.static_pool;
    const argv = r.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    @memcpy(argv, sp.get(args).aggregate.elems);
    for (r.tree.params_of(r.decls.value_node(generic)), 0..) |pn, i| {
        const pt = if (sp.has_vars(r.types.sig(generic).params[i])) sp.type_of(argv[i]) else r.types.sig(generic).params[i];
        const p = ParseTree.Param.from_node(r.tree, pn);
        const d = r.decls.declare_local(r.decls.name_at(p, i), pn, .static_parameter, pt);
        r.decls.link(p.name, d, pt);
        r.decl_pool.set_value(d, r.statics.retype(argv[i], pt));
    }
}

fn memo(self: *Generics, key: AbstractKey, v: StaticPool.Index) void {
    const r = self.res();
    self.realized.put(r.alloc, key, v) catch @panic("OOM");
}

pub fn is_template(self: *Generics, d: DeclPool.Index) bool {
    const r = self.res();
    if (d == .none or r.decl_pool.get_kind(d) != .static_function or r.decl_pool.get_ty(d) == .none) return false;
    const t = r.decl_pool.get_ty(d);
    return r.static_pool.tag(t) == .function_type and r.static_pool.tag(r.static_pool.get(t).function_type.ret) == .meta_type;
}

pub fn realizes(self: *Generics, t0: StaticPool.Index, tmpl: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    const t = sp.unwrapped(&r.abstract_pool, t0);
    const g = sp.get(tmpl).template_type;
    if (t == tmpl or self.source_of(t) == g) return true;
    const own: []const StaticPool.Index = switch (sp.get(t)) {
        .custom_type => |c| c.traits,
        .variant_type => |v| v.traits,
        else => &.{},
    };
    for (own) |tr| if (sp.tag(tr) == .trait_type and self.template_of.get(sp.get(tr).trait_type.decl) == g) return true;
    return false;
}

pub fn passes(self: *Generics, t0: StaticPool.Index, p: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    const t = sp.apply_vars(&r.abstract_pool, t0);
    if (t == .poison_type) return true;
    if (sp.is_ptr(p) != sp.is_ptr(t)) return false;
    if (sp.get(p) == .ptr_type and sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable) return false;
    return self.realizes(t, sp.templated(p));
}

pub fn source_of(self: *Generics, t: StaticPool.Index) DeclPool.Index {
    const r = self.res();
    const d = r.static_pool.nominal_decl(&r.abstract_pool, t);
    return if (d == .none) .none else self.template_of.get(d) orelse .none;
}

pub fn sibling(self: *Generics, ctx: *FnCtx, t: StaticPool.Index, st: StaticPool.Index) bool {
    const r = self.res();
    if (r.static_pool.templated(st) != .none) return self.realizes(t, r.static_pool.templated(st));
    if (r.static_pool.templated(t) != .none) return self.realizes(st, r.static_pool.templated(t));
    const g = self.source_of(st);
    return g != .none and self.source_of(t) == g and self.opened(ctx);
}

pub fn opened(self: *Generics, ctx: *FnCtx) bool {
    const r = self.res();
    const g = (if (ctx.decl == .none) null else self.template_of.get(ctx.decl)) orelse return false;
    const ty = r.decl_pool.get_ty(g);
    if (ty == .none or r.static_pool.tag(ty) != .function_type) return false;
    for (r.static_pool.get(ty).function_type.params) |p| if (r.static_pool.templated(p) != .none) return true;
    return false;
}

pub fn template_member(self: *Generics, node: NodeId, t: StaticPool.Index, name: NamePool.Index) StaticPool.Index {
    const r = self.res();
    const g = r.static_pool.get(t).template_type;
    const kind = r.decls.template_kind(g);
    if (kind == .variable) return r.report(.generic_member, node, name, t);
    const v = r.decls.value_node(g);
    const unit = r.tree.arg(v, 1);
    var ctx = FnCtx{ .in_static = true };
    r.decls.open_scope(true, .none, 0);
    defer r.scopes.pop();
    if (kind == .record) if (self.template_field(g, name)) |f| {
        const p = ParseTree.Param.from_node(r.tree, f);
        return if (self.mentions(p.ty, v)) r.report(.generic_member, node, name, t) else r.types.lower(&ctx, p.ty);
    };
    const w = ParseTree.Def.from_node(r.tree, unit);
    const tr = if (r.decls.type_kind(w.core) == .trait) w.core else if (w.body != 0) w.body else return r.report(.unknown_member, node, name, t);
    for (r.tree.manychildren(r.tree.arg(tr, if (r.tree.kind(tr) == .def_trait_implof) 1 else 0))) |s| {
        const parts = Decls.Stmt.from_node(r, s);
        if (parts.assignees.len != 1 or r.name_pool.name_of(parts.assignees[0]) != name or !parts.kind.is_fn()) continue;
        return if (self.signature_mentions(parts.values[0], v)) r.report(.generic_member, node, name, t) else r.types.fun_type(&ctx, parts.values[0], .default, .poison_type, .none);
    }
    return r.report(.unknown_member, node, name, t);
}

pub fn template_field(self: *Generics, g: DeclPool.Index, name: NamePool.Index) ?NodeId {
    const r = self.res();
    const fields = r.tree.fields_of(ParseTree.Def.from_node(r.tree, r.tree.arg(r.decls.value_node(g), 1)).core);
    return fields[r.decls.param_index(fields, name) orelse return null];
}

fn signature_mentions(self: *Generics, f: NodeId, v: NodeId) bool {
    const r = self.res();
    const header = r.tree.arg(f, 0);
    if (r.tree.kind(header) != .partial__fun_def_header_ret or self.mentions(r.tree.arg(header, 1), v)) return true;
    for (r.tree.params_of(f)) |pn| if (self.mentions(ParseTree.Param.from_node(r.tree, pn).ty, v)) return true;
    return false;
}

fn mentions(self: *Generics, n: NodeId, v: NodeId) bool {
    const r = self.res();
    const params = r.tree.params_of(v);
    const s = r.tree.subtree(n);
    for (s[0]..s[1]) |i| {
        if (r.tree.kind(@intCast(i)) != .identifier) continue;
        const nm = r.name_pool.name_of(@intCast(i));
        for (params, 0..) |pn, j| if (r.decls.param_name(pn, j) == nm) return true;
    }
    return false;
}
