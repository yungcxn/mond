const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const decls = @import("decls.zig");
const types = @import("types.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const max_nesting = 256;

// templates and realizations: stcfuns realized per static arguments, functions per length, type or template

pub fn h20_instantiate(self: *Resolver, generic: DeclPool.Index, args: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const key = StaticPool.AbstractKey{ .generic_tuple = generic, .args_tuple = args };
    if (sp.realized_abstracts.get(key)) |r| return r;
    const node = self.decl_pool.nodes()[@intFromEnum(generic)];
    // a realization that realizes itself forever eats the static budget and stops there
    if (self.scopes.marks.head > max_nesting) return self.report(.static_eval_failed, self.interpreter.origin(node), generic, 0);
    if (!self.interpreter.charge(node, 64)) return .poison_type;
    const argv = self.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    const argc = argv.len;
    @memcpy(argv, sp.get(args).aggregate.elems);

    if (self.decl_pool.kinds()[@intFromEnum(generic)] != .static_function) {
        // length-generic function: a new declaration per tuple of lengths, the lengths bound in order of appearance
        decls.h06_check_body(self, generic);
        if (self.decl_pool.states()[@intFromEnum(generic)] == .failed) return .poison_type;
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], node, self.decl_pool.kinds()[@intFromEnum(generic)], .none, self.decl_pool.flags()[@intFromEnum(generic)]);
        self.decl_pool.template_of.put(self.alloc, d, generic) catch @panic("OOM");
        const fv = sp.intern(.{ .function = d });
        memo(self, key, fv);
        const outer = self.decl_pool.static_scope.get(generic);
        if (outer) |k| {
            self.decl_pool.static_scope.put(self.alloc, d, k) catch @panic("OOM");
            decls.open_scope(self, true, .none, 0);
            bind_static(self, k.generic_tuple, k.args_tuple);
        }
        defer if (outer != null) self.scopes.h04_pop_scope();
        decls.h05_ensure_signature(self, d);
        self.decl_pool.realized_args.put(self.alloc, d, args) catch @panic("OOM");
        const ft = sp.get(self.decl_pool.tys()[@intFromEnum(d)]).function_type;
        const ps = self.scratch(StaticPool.Index, ft.params.len);
        @memcpy(ps, ft.params);
        var i: usize = 0;
        for (ps) |*q| {
            var p = q.*;
            if (!generic_slot(self, p) or i >= argc) continue;
            i += 1;
            if (sp.templated(p) != .none) q.* = if (sp.get(p) == .ptr_type) sp.intern(.{ .ptr_type = .{ .child = argv[i - 1], .mutable = sp.get(p).ptr_type.mutable } }) else argv[i - 1];
            if (sp.get(p) == .ptr_type) p = sp.get(p).ptr_type.child;
            if (sp.get(p) == .array_type) _ = sp.unify(&self.abstract_pool, sp.get(p).array_type.len, argv[i - 1]);
        }
        self.decl_pool.tys()[@intFromEnum(d)] = sp.intern(.{ .function_type = .{ .category = ft.category, .params = ps, .ret = ft.ret } });
        decls.h06_check_body(self, d);
        return fv;
    }

    var ctx = FnCtx{ .decl = generic, .in_static = true };
    decls.open_scope(self, true, .none, 0);
    defer self.scopes.h04_pop_scope();
    const v = decls.value_node(self, generic);
    const params = syntax.params_of(self.tree, v);
    bind_static(self, generic, args);
    for (params) |pn| {
        const w = syntax.Param.from_node(self.tree, pn).where;
        if (w != 0 and statics.h08_eval_static(self, &ctx, w) == .bool_false) _ = self.report(.stcwhere_violated, w, generic, args);
    }
    const unit = self.tree.arg(v, 1);
    const kind = syntax.type_kind(self.tree, unit);
    if (kind != .variable) { // a type: memoized before its body, so it can mention itself (`Stream(Child)` inside Stream)
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], unit, kind, .none, .{});
        self.decl_pool.realized_args.put(self.alloc, d, args) catch @panic("OOM");
        self.decl_pool.template_of.put(self.alloc, d, generic) catch @panic("OOM");
        self.decl_pool.values()[@intFromEnum(d)] = sp.reserve_nominal(d);
        memo(self, key, self.decl_pool.values()[@intFromEnum(d)]);
        return types.h19_check_type_def(self, &ctx, d, unit);
    }
    if (self.tree.kind(unit) == .def_fun) {
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], unit, .function, .none, .{});
        const fv = sp.intern(.{ .function = d });
        memo(self, key, fv);
        self.decl_pool.static_scope.put(self.alloc, d, key) catch @panic("OOM");
        decls.h05_ensure_signature(self, d);
        decls.h06_check_body(self, d);
        return fv;
    }
    ctx.in_static = false;
    ctx.interpreted = true;
    ctx.ret_type = types.sig(self, generic).ret;
    const first = self.decl_pool.entries.len();
    const vars = self.abstract_pool.count();
    const outer = self.inits.enter();
    const mark = self.doc.diagnostics.len();
    decls.check_unit(self, &ctx, unit);
    ctx.interpreted = false;
    self.inits.leave(outer);
    if (self.doc.errors_since(self.tree, mark, unit)) {
        memo(self, key, .poison_type);
        return .poison_type;
    }
    for (vars..self.abstract_pool.count()) |i| switch (self.tree.kind(self.abstract_pool.pool.sliced_field(.origin)[i])) {
        .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => if (self.abstract_pool.binding(@enumFromInt(i)) == .none) self.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len),
        else => {},
    };
    const r = self.interpreter.run(&ctx, unit, self.capture(generic, v, first));
    const made = if (sp.tag(ctx.ret_type) == .meta_type and sp.get_tag_prop(r).is_type) nominal(self, r) else .none;
    if (made != .none and @intFromEnum(made) >= first) self.decl_pool.template_of.put(self.alloc, made, generic) catch @panic("OOM");
    memo(self, key, r);
    return r;
}

// the static parameters of a stcfun as locals holding the arguments of one realization
fn bind_static(self: *Resolver, generic: DeclPool.Index, args: StaticPool.Index) void {
    const sp = &self.static_pool;
    const argv = self.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    @memcpy(argv, sp.get(args).aggregate.elems);
    for (syntax.params_of(self.tree, decls.value_node(self, generic)), 0..) |pn, i| {
        const pt = if (sp.has_vars(types.sig(self, generic).params[i])) sp.type_of(argv[i]) else types.sig(self, generic).params[i];
        const p = syntax.Param.from_node(self.tree, pn);
        const d = decls.h02_declare_local(self, decls.name_at(self, p, i), pn, .static_parameter, pt);
        decls.link(self, p.name, d, pt);
        self.decl_pool.values()[@intFromEnum(d)] = statics.retype(self, argv[i], pt);
    }
}

fn memo(self: *Resolver, key: StaticPool.AbstractKey, v: StaticPool.Index) void {
    self.static_pool.realized_abstracts.put(self.alloc, key, v) catch @panic("OOM");
}

pub fn is_template(self: *Resolver, d: DeclPool.Index) bool {
    if (d == .none or self.decl_pool.kinds()[@intFromEnum(d)] != .static_function or self.decl_pool.tys()[@intFromEnum(d)] == .none) return false;
    const t = self.decl_pool.tys()[@intFromEnum(d)];
    return self.static_pool.tag(t) == .function_type and self.static_pool.tag(self.static_pool.get(t).function_type.ret) == .meta_type;
}

pub fn length_generic(self: *Resolver, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (ty == .none or sp.tag(ty) != .function_type) return false;
    for (0..sp.get(ty).function_type.params.len) |i| {
        const p = sp.get(ty).function_type.params[i];
        if (sp.has_vars(sp.apply_vars(&self.abstract_pool, p)) or sp.tag(p) == .meta_type or sp.templated(p) != .none) return true;
    }
    return false;
}

pub fn only_templates(self: *Resolver, ty: StaticPool.Index) bool {
    for (self.static_pool.get(ty).function_type.params) |p| if (generic_slot(self, p) and self.static_pool.templated(p) == .none) return false;
    return true;
}

// parameters a function is realized for: unlengthed arrays (per length), `type` parameters (per type) and templates (per realization)
pub fn generic_slot(self: *Resolver, p: StaticPool.Index) bool {
    return self.static_pool.has_vars(p) or self.static_pool.tag(p) == .meta_type or self.static_pool.templated(p) != .none;
}

pub fn realizes(self: *Resolver, t0: StaticPool.Index, tmpl: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = unwrapped(self, t0);
    const g = sp.get(tmpl).template_type;
    if (t == tmpl or source_of(self, t) == g) return true;
    const own: []const StaticPool.Index = switch (sp.get(t)) {
        .custom_type => |c| c.traits,
        .variant_type => |v| v.traits,
        else => &.{},
    };
    for (own) |tr| if (sp.tag(tr) == .trait_type and self.decl_pool.template_of.get(sp.get(tr).trait_type.decl) == g) return true;
    return false;
}

pub fn passes(self: *Resolver, t0: StaticPool.Index, p: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    if (t == .poison_type) return true;
    if (sp.is_ptr(p) != sp.is_ptr(t)) return false;
    if (sp.get(p) == .ptr_type and sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable) return false;
    return realizes(self, t, sp.templated(p));
}

pub fn unwrapped(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const t = self.static_pool.deref(&self.abstract_pool, t0);
    return if (self.static_pool.tag(t) == .variant_case_type) self.static_pool.get(t).variant_case_type.variant else t;
}

fn nominal(self: *Resolver, t0: StaticPool.Index) DeclPool.Index {
    return switch (self.static_pool.get(unwrapped(self, t0))) {
        .custom_type => |c| c.decl,
        .variant_type => |v| v.decl,
        .trait_type => |x| x.decl,
        else => .none,
    };
}

pub fn source_of(self: *Resolver, t: StaticPool.Index) DeclPool.Index {
    const d = nominal(self, t);
    return if (d == .none) .none else self.decl_pool.template_of.get(d) orelse .none;
}

pub fn sibling(self: *Resolver, ctx: *FnCtx, t: StaticPool.Index, st: StaticPool.Index) bool {
    if (self.static_pool.templated(st) != .none) return realizes(self, t, self.static_pool.templated(st));
    if (self.static_pool.templated(t) != .none) return realizes(self, st, self.static_pool.templated(t));
    const g = source_of(self, st);
    return g != .none and source_of(self, t) == g and opened(self, ctx);
}

pub fn opened(self: *Resolver, ctx: *FnCtx) bool {
    const g = (if (ctx.decl == .none) null else self.decl_pool.template_of.get(ctx.decl)) orelse return false;
    const ty = self.decl_pool.tys()[@intFromEnum(g)];
    if (ty == .none or self.static_pool.tag(ty) != .function_type) return false;
    for (self.static_pool.get(ty).function_type.params) |p| if (self.static_pool.templated(p) != .none) return true;
    return false;
}

// the static length an argument gives an unlengthed parameter (`&[5]u32` for `&[]u32`), or none
pub fn arg_len(self: *Resolver, t0: StaticPool.Index, p0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var t = sp.apply_vars(&self.abstract_pool, t0);
    var p = p0;
    if (t == .poison_type) return .none;
    if (sp.get(p) == .ptr_type) {
        if (sp.get(t) != .ptr_type or (sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable)) return .none;
        t = sp.get(t).ptr_type.child;
        p = sp.get(p).ptr_type.child;
    }
    if (sp.get(t) != .array_type or sp.get(p) != .array_type or sp.get(t).array_type.elem != sp.get(p).array_type.elem) return .none;
    const len = sp.get(t).array_type.len;
    return if (sp.tag(len) == .int_value or len == StaticPool.dyn_len) len else .none;
}

pub fn template_member(self: *Resolver, node: NodeId, t: StaticPool.Index, name: NamePool.Index) StaticPool.Index {
    const g = self.static_pool.get(t).template_type;
    const kind = syntax.template_kind(self.tree, self.decl_pool.nodes()[@intFromEnum(g)]);
    if (kind == .variable) return self.report(.generic_member, node, name, t);
    const v = decls.value_node(self, g);
    const unit = self.tree.arg(v, 1);
    var ctx = FnCtx{ .in_static = true };
    decls.open_scope(self, true, .none, 0);
    defer self.scopes.h04_pop_scope();
    if (kind == .record) if (template_field(self, g, name)) |f| {
        const p = syntax.Param.from_node(self.tree, f);
        return if (mentions(self, p.ty, v)) self.report(.generic_member, node, name, t) else types.h07_lower_type(self, &ctx, p.ty);
    };
    const w = syntax.Def.from_node(self.tree, unit);
    const tr = if (syntax.type_kind(self.tree, w.core) == .trait) w.core else if (w.body != 0) w.body else return self.report(.unknown_member, node, name, t);
    for (self.tree.manychildren(self.tree.arg(tr, if (self.tree.kind(tr) == .def_trait_implof) 1 else 0))) |s| {
        const parts = Resolver.Stmt.from_node(self, s);
        if (parts.assignees.len != 1 or self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]) != name or !parts.kind.is_fn()) continue;
        return if (signature_mentions(self, parts.values[0], v)) self.report(.generic_member, node, name, t) else types.fun_type(self, &ctx, parts.values[0], .default, .poison_type, .none);
    }
    return self.report(.unknown_member, node, name, t);
}

pub fn template_field(self: *Resolver, g: DeclPool.Index, name: NamePool.Index) ?NodeId {
    for (syntax.fields_of(self.tree, syntax.Def.from_node(self.tree, self.tree.arg(decls.value_node(self, g), 1)).core), 0..) |f, i| if (decls.param_name(self, f, i) == name) return f;
    return null;
}

pub fn signature_mentions(self: *Resolver, f: NodeId, v: NodeId) bool {
    const header = self.tree.arg(f, 0);
    if (self.tree.kind(header) != .partial__fun_def_header_ret or mentions(self, self.tree.arg(header, 1), v)) return true;
    for (syntax.params_of(self.tree, f)) |pn| if (mentions(self, syntax.Param.from_node(self.tree, pn).ty, v)) return true;
    return false;
}

pub fn mentions(self: *Resolver, n: NodeId, v: NodeId) bool {
    const params = syntax.params_of(self.tree, v);
    const s = self.tree.subtree(n);
    for (s[0]..s[1]) |i| {
        if (self.tree.kind(@intCast(i)) != .identifier) continue;
        const nm = self.name_pool.name_of(self.tree, self.src_bytes, @intCast(i));
        for (params, 0..) |pn, j| if (decls.param_name(self, pn, j) == nm) return true;
    }
    return false;
}
