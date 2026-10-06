const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const exprs = @import("exprs.zig");
const places = @import("places.zig");
const types = @import("types.zig");
const control = @import("control.zig");
const generics = @import("generics.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const Stmt = Resolver.Stmt;
const NodeId = ParseTree.NodeId;

// declarations: names and their scopes, signatures, bodies, statements that declare or assign

pub fn use(self: *Resolver, node: NodeId) DeclPool.Index {
    const name = self.name_pool.name_of(self.tree, self.src_bytes, node);
    const d = self.scopes.h01_lookup(self.decl_pool.kinds(), name);
    if (d == .none) {
        if (!self.doc.has(node)) _ = self.report(.undefined_name, node, name, 0);
        return d;
    }
    self.node_decl[node] = d;
    h05_ensure_signature(self, d);
    return d;
}

pub fn h02_declare_local(self: *Resolver, name: NamePool.Index, node: NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index) DeclPool.Index {
    const d = self.decl_pool.push_decl(name, node, kind, ty, .{});
    self.scopes.bind(name, d);
    return d;
}

pub fn redeclared(self: *Resolver, name: NamePool.Index, at: NodeId) void {
    const d = self.scopes.in_scope(name);
    if (d != .none) self.doc.h21_report(.duplicate_declaration, at, name, d);
}

pub fn link(self: *Resolver, id: NodeId, d: DeclPool.Index, t: StaticPool.Index) void {
    if (id == 0) return;
    self.node_decl[id] = d;
    self.node_type[id] = t;
}

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
    var ctx = FnCtx{ .decl = decl, .self_type = self.decl_pool.owner_of(decl), .in_static = flags.is_stc };
    const v = value_node(self, decl);
    open_scope(self, flags.is_global, if (self.decl_pool.self_off(decl) == 1) ctx.self_type else .none, v);
    if (!flags.is_global and kind.is_type_decl()) {
        self.scopes.bind(.wall, .none);
    }
    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => if (self.tree.kind(v) == .def_fun or self.tree.kind(v) == .def_fun_declaration) {
            // stcfun: the first tuple is static, whatever the body produces is the result (a second tuple belongs to the produced function)
            const unit = self.tree.arg(v, 1);
            const tk = syntax.template_kind(self.tree, self.decl_pool.nodes()[@intFromEnum(decl)]);
            const uk = syntax.type_kind(self.tree, unit);
            if (kind == .static_function and tk == .variable and uk != .variable) _ = self.report(.missing_ret, unit, 0, 0);
            const res = if (self.tree.kind(unit) == .ret) self.tree.arg(unit, 0) else unit;
            const ret: StaticPool.Index = if (kind == .static_function)
                types.meta(syntax.type_kind(self.tree, res), if (self.tree.kind(res) == .def_fun or self.tree.kind(res) == .def_fun_declaration) .fun_type else .poison_type)
            else if (self.tree.kind(v) == .def_fun_declaration or self.tree.kind(self.tree.arg(v, 0)) == .partial__fun_def_header_ret) .unit_type else sp.fresh_var(&self.abstract_pool, v);
            if (tk != .variable and uk == .variable) {
                _ = self.report(.redundant_ret, unit, 0, 0);
            } else if (tk != .variable and uk != tk) _ = self.report(.type_mismatch, unit, ret, types.meta(tk, .trait_type));
            const category: StaticPool.FunType.Category = switch (kind) {
                .static_function => .static,
                .inlined_function => .inlined,
                else => .default,
            };
            // a method's first parameter is the induced `*Self`, `init` constructs and has none
            self.decl_pool.tys()[@intFromEnum(decl)] = types.fun_type(self, &ctx, v, category, ret, if (self.decl_pool.self_off(decl) == 1) sp.ptr_mut(ctx.self_type) else .none);
            if (!self.decl_pool.template_of.contains(decl)) for (syntax.params_of(self.tree, v), 0..) |pn, i| for (syntax.params_of(self.tree, v)[0..i], 0..) |q, j| if (param_name(self, q, j) == param_name(self, pn, i)) self.doc.h21_report(.duplicate_declaration, pn, param_name(self, pn, i), decl);
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
        else => _ = h11_check_assign(self, &ctx, self.decl_pool.nodes()[@intFromEnum(decl)]),
    }
    self.scopes.h04_pop_scope();
    if (self.decl_pool.states()[@intFromEnum(decl)] == .resolving_signature) self.decl_pool.states()[@intFromEnum(decl)] = .signature_ready;
}

pub fn h06_check_body(self: *Resolver, decl: DeclPool.Index) void {
    const state = &self.decl_pool.states()[@intFromEnum(decl)];
    if (state.* != .signature_ready) return;
    const sp = &self.static_pool;
    const kind = self.decl_pool.kinds()[@intFromEnum(decl)];
    const v = value_node(self, decl);
    const ty = self.decl_pool.tys()[@intFromEnum(decl)];
    // stcfun bodies are checked per realization, length-generic ones per length (h20); `main` is realized once, by the runtime
    const generic = generics.length_generic(self, ty) and !self.decl_pool.template_of.contains(decl);
    const abstract = generic and generics.only_templates(self, ty);
    if (kind == .static_function or !kind.is_fn() or self.tree.kind(v) != .def_fun or generic and !abstract) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;
    const first = self.decl_pool.entries.len();
    const mark = self.doc.diagnostics.len();
    const outer = self.inits.enter();
    defer self.inits.leave(outer);
    // a local function sees which enclosing locals are not written yet
    if (kind == .function and !self.decl_pool.flags()[@intFromEnum(decl)].is_global) self.inits.import(0, outer, 0);
    const off = self.decl_pool.self_off(decl);
    var ctx = FnCtx{ .decl = decl, .ret_type = sp.get(ty).function_type.ret, .self_type = self.decl_pool.owner_of(decl), .abstract = abstract };
    open_scope(self, self.decl_pool.flags()[@intFromEnum(decl)].is_global, if (off == 1) ctx.self_type else .none, v);
    const g = self.decl_pool.template_of.get(decl);
    const args = self.decl_pool.realized_args.get(decl);
    const view = if (g) |t| !generics.only_templates(self, self.decl_pool.tys()[@intFromEnum(t)]) else false;
    // a where clause sees its own parameter and the ones before it; realized `type` parameters are static values
    var slot: usize = 0;
    for (syntax.params_of(self.tree, v), 0..) |pn, i| {
        const p = syntax.Param.from_node(self.tree, pn);
        const pt = sp.get(ty).function_type.params[i + off];
        if (p.default != 0) _ = exprs.check(self, &ctx, p.default, pt);
        const pd = h02_declare_local(self, name_at(self, p, i), pn, .parameter, pt);
        self.node_decl[pn] = pd;
        const gp = if (g) |t| types.sig(self, t).params[i + off] else pt;
        self.decl_pool.flags()[@intFromEnum(pd)].is_view = view and sp.templated(gp) != .none;
        if (args) |a| if (generics.generic_slot(self, gp)) {
            if (sp.tag(gp) == .meta_type) self.decl_pool.values()[@intFromEnum(pd)] = sp.get(a).aggregate.elems[slot];
            slot += 1;
        };
        link(self, p.name, pd, pt);
        check_guards(self, &ctx, p, pt);
    }
    check_unit(self, &ctx, self.tree.arg(v, 1));
    self.scopes.h04_pop_scope();
    if (off == 1 and self.decl_pool.flags()[first].writes) self.decl_pool.flags()[@intFromEnum(decl)].writes = true;
    self.decl_pool.states()[@intFromEnum(decl)] = if (self.doc.errors_since(self.tree, mark, v)) .failed else .done;
    if (!abstract) self.bodies.put(self.capture(decl, v, first));
}

pub fn check_unit(self: *Resolver, ctx: *FnCtx, body: NodeId) void {
    const sp = &self.static_pool;
    if (self.tree.kind(body) != .block) {
        _ = exprs.check(self, ctx, body, ctx.ret_type);
        return;
    }
    const t = exprs.h09_check_expr(self, ctx, body, .none);
    const r = sp.apply_vars(&self.abstract_pool, ctx.ret_type);
    // a `{}` body that never returns a value returns unit, a body with a result returns it on every path (`$main` falls off with 0)
    if (r != .none and sp.tag(r) == .type_var) _ = sp.unify(&self.abstract_pool, ctx.ret_type, .unit_type) else if (r != .none and (ctx.decl == .none or self.decl_pool.names()[@intFromEnum(ctx.decl)] != .main) and r != .unit_type and r != .runit_type and r != .poison_type and t != .never_type and t != .poison_type and !self.doc.has(body)) _ = self.report(.missing_ret, body, 0, 0);
}

pub fn h11_check_assign(self: *Resolver, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parts = Stmt.from_node(self, node);
    const n = parts.node;
    const flags = parts.flags;
    const kind = parts.kind;
    if (ctx.interpreted and kind.is_type_decl()) {
        _ = exprs.h09_check_expr(self, ctx, parts.values[0], .none);
        const t = statics.deferred(self, ctx, parts.values[0]);
        for (parts.assignees) |id| {
            const d = declare(self, id, n, kind, if (t) |x| sp.type_of(x) else types.meta_of(self, parts.values[0]), flags);
            self.decl_pool.states()[@intFromEnum(d)] = .done;
            self.decl_pool.values()[@intFromEnum(d)] = t orelse .none;
        }
        return .unit_type;
    }
    if (kind == .function and parts.type == 0 and parts.assignees.len == 1) {
        const e = self.scopes.h01_lookup(self.decl_pool.kinds(), self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]));
        if (e != .none and !self.decl_pool.kinds()[@intFromEnum(e)].is_fn() and self.decl_pool.tys()[@intFromEnum(e)] != .none and sp.tag(sp.apply_vars(&self.abstract_pool, self.decl_pool.tys()[@intFromEnum(e)])) == .function_type) {
            self.node_decl[parts.assignees[0]] = e;
            return h11_check_assign(self, ctx, node);
        }
    }
    if (kind != .variable) { // local function / type / trait
        for (parts.assignees) |id| {
            const d = declare(self, id, n, kind, .none, flags);
            h05_ensure_signature(self, d);
            h06_check_body(self, d);
        }
        return .unit_type;
    }
    const values = parts.values;
    // a write into a place (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    if (parts.assignees.len == 1 and self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]) == .none) {
        const pt = places.h18_check_place(self, ctx, parts.assignees[0]);
        for (values) |v| _ = exprs.check(self, ctx, v, pt);
        return .unit_type;
    }
    const declaring = parts.type != 0 or @as(u8, @bitCast(flags)) != 0;
    var ty: StaticPool.Index = if (parts.type != 0) types.realized_type(self, ctx, parts.type) else .none;
    // untyped: visible names are assigned, their type is shared by the new ones
    const existing = self.scratch(DeclPool.Index, parts.assignees.len);
    for (parts.assignees, 0..) |id, i| {
        existing[i] = if (declaring or pre_declared(self, self.node_decl[id], n)) .none else self.scopes.h01_lookup(self.decl_pool.kinds(), self.name_pool.name_of(self.tree, self.src_bytes, id));
        if (existing[i] == .none) continue;
        const outer = self.inits.save(0);
        self.inits.clear(0);
        const et = places.h18_check_place(self, ctx, id);
        self.inits.copy(0, outer);
        self.inits.release(outer);
        if (ty == .none) ty = et else if (et != ty and et != .poison_type) _ = self.report(.destructure_type_conflict, id, et, ty);
    }
    self.scopes.h03_push_scope();
    if (values.len > 1) {
        var shared = ty;
        const lits = self.scratch(bool, values.len);
        for (values, 0..) |v, i| {
            const want = if (i < parts.assignees.len and existing[i] != .none) self.decl_pool.tys()[@intFromEnum(existing[i])] else ty;
            lits[i] = want == .none and syntax.is_literal(self.tree, v);
            if (lits[i]) continue;
            const vt = exprs.check(self, ctx, v, want);
            if (shared == .none) shared = vt else if (ty == .none) {
                const j = sp.join(&self.abstract_pool, shared, vt);
                shared = if (j.ty == .none) self.report(.destructure_type_conflict, v, shared, vt) else j.ty;
            }
        }
        if (ty == .none) {
            for (values, 0..) |v, i| if (lits[i]) {
                _ = exprs.h09_check_expr(self, ctx, v, .none);
            };
            if (shared == .none) shared = control.literals_type(self, values);
            if (shared == .none) shared = self.node_type[values[0]];
            for (values, 0..) |v, i| if (lits[i] and shared != .poison_type) {
                const lt = statics.literal_type(self, v, shared);
                const j = sp.join(&self.abstract_pool, shared, lt);
                shared = if (j.ty == .none) self.report(.destructure_type_conflict, v, shared, lt) else j.ty;
            };
            for (values, 0..) |v, i| if (lits[i] and shared != .poison_type) {
                _ = exprs.h10_expect(self, v, self.node_type[v], shared);
            };
        }
        ty = shared;
    } else if (values.len == 1) {
        // a fresh var as expectation means "a value is wanted" (loops / ifs as values) without fixing its type
        const got = exprs.check(self, ctx, values[0], if (ty != .none) ty else sp.fresh_var(&self.abstract_pool, n));
        if (ty == .none) ty = sp.apply_vars(&self.abstract_pool, got);
        if (ty != .none and sp.tag(ty) == .function_type and sp.holds_template(ty)) ty = self.report(.unrealized_template, values[0], ty, 0);
    }
    self.scopes.h04_pop_scope();
    for (parts.assignees, 0..) |id, i| {
        const d = if (existing[i] != .none) existing[i] else declare(self, id, n, .variable, if (ty == .none) .poison_type else ty, flags);
        if (existing[i] != .none) self.inits.written(d) else if (values.len == 0 and !self.decl_pool.flags()[@intFromEnum(d)].is_global and scalar(self, self.decl_pool.tys()[@intFromEnum(d)])) self.inits.track(d);
        if (values.len > 0 and (existing[i] == .none or (self.interpreter.depth > 0 and !ctx.interpreted)) and (self.decl_pool.flags()[@intFromEnum(d)].is_stc or ctx.in_static)) {
            self.decl_pool.values()[@intFromEnum(d)] = if (self.node_type[values[@min(i, values.len - 1)]] == .poison_type) .poison_type else statics.retype(self, statics.static_of(self, ctx, values[@min(i, values.len - 1)]), self.decl_pool.tys()[@intFromEnum(d)]);
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

pub fn check_guards(self: *Resolver, ctx: *FnCtx, p: syntax.Param, t: StaticPool.Index) void {
    if (p.where != 0) _ = exprs.check(self, ctx, p.where, .bool_type);
    if (p.@"else" != 0) _ = if (self.tree.kind(p.@"else") == .assign) exprs.h09_check_expr(self, ctx, p.@"else", .none) else exprs.check(self, ctx, p.@"else", t);
}

// a declared global row is reused, anything else becomes a new local
fn declare(self: *Resolver, id: NodeId, stmt: NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index, flags: DeclPool.Entry.Flags) DeclPool.Index {
    var d = self.node_decl[id];
    if (!pre_declared(self, d, stmt)) {
        redeclared(self, self.name_pool.name_of(self.tree, self.src_bytes, id), id);
        d = h02_declare_local(self, self.name_pool.name_of(self.tree, self.src_bytes, id), stmt, kind, ty);
        self.decl_pool.flags()[@intFromEnum(d)] = flags;
        self.node_decl[id] = d;
    } else if (ty != .none) self.decl_pool.tys()[@intFromEnum(d)] = ty;
    _ = self.set(id, if (ty == .none) .unit_type else ty);
    return d;
}

// s1 rows and hoisted local functions of this very statement are reused instead of declared again
fn pre_declared(self: *Resolver, d: DeclPool.Index, stmt: NodeId) bool {
    return d != .none and self.decl_pool.nodes()[@intFromEnum(d)] == stmt and (self.decl_pool.flags()[@intFromEnum(d)].is_global or self.scopes.h01_lookup(self.decl_pool.kinds(), self.decl_pool.names()[@intFromEnum(d)]) == d);
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
pub fn open_scope(self: *Resolver, barrier: bool, self_type: StaticPool.Index, node: NodeId) void {
    self.scopes.h03_push_scope();
    if (barrier) {
        self.scopes.bind(.none, .none);
    }
    if (self_type != .none) self.decl_pool.flags()[@intFromEnum(h02_declare_local(self, .self, node, .self, self.static_pool.ptr_mut(self_type)))].is_mut = true;
}

pub fn value_node(self: *Resolver, d: DeclPool.Index) NodeId {
    const n = self.decl_pool.nodes()[@intFromEnum(d)];
    return switch (self.tree.kind(n)) {
        .assign, .assign_typed => self.tree.arg(n, 1),
        else => n,
    };
}

// unnamed parameters and fields are `$0`, `$1`, ...
pub fn param_name(self: *Resolver, pn: NodeId, i: usize) NamePool.Index {
    return name_at(self, syntax.Param.from_node(self.tree, pn), i);
}

pub fn name_at(self: *Resolver, p: syntax.Param, i: usize) NamePool.Index {
    const autoinserted_dollarnames = comptime blk: {
        @setEvalBranchQuota(100_000);
        var t: [64][]const u8 = undefined;
        for (&t, 0..) |*s, j| s.* = std.fmt.comptimePrint("${d}", .{j});
        break :blk t;
    };

    if (p.name != 0) return self.name_pool.name_of(self.tree, self.src_bytes, p.name);
    if (i < autoinserted_dollarnames.len) return self.name_pool.intern_string(autoinserted_dollarnames[i]);
    var buf: [24]u8 = undefined;
    return self.name_pool.intern_owned(std.fmt.bufPrint(&buf, "${d}", .{i}) catch unreachable);
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
pub fn real(self: *Resolver, d: DeclPool.Index) DeclPool.Index {
    const v = self.decl_pool.values()[@intFromEnum(d)];
    return if (v != .none and self.static_pool.tag(v) == .function_value) self.static_pool.get(v).function else d;
}

fn scalar(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and t != .poison_type and self.static_pool.tag(t) != .record_type and self.static_pool.tag(t) != .array_type;
}
