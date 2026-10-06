const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// declarations: names and their scopes, signatures, bodies, statements that declare or assign
const Decls = @This();

pub const Stmt = struct {
    node: NodeId, // actual parent, e.g. the unwrapper assignment parent node

    // all other of these fields may be fully unset:
    flags: DeclPool.Entry.Flags,
    kind: DeclPool.Entry.Kind,
    type: NodeId,
    assignees: []const NodeId,
    values: []const NodeId,

    pub fn from_node(r: *Resolver, n0: NodeId) Stmt {
        var flags = DeclPool.Entry.Flags{};

        // assignments are possibly with modifiers, which must be unpacked and put into flags
        const non_assignmoded_root = blk: {
            var n = n0;
            outer: while (true) : (n = r.tree.arg(n, 0)) switch (r.tree.kind(n)) {
                .mod_pub => flags.is_pub = true,
                .mod_mut => flags.is_mut = true,
                .mod_stc => flags.is_stc = true,
                else => break :outer,
            };
            break :blk n;
        };

        var stmt_type: NodeId = 0;
        var stmt_value: NodeId = 0;
        var stmt_ids: []const NodeId = &.{};

        switch (r.tree.kind(non_assignmoded_root)) {
            .def_var => {
                const def_var_ch = r.tree.laidout_children(.def_var, non_assignmoded_root);
                stmt_type = def_var_ch.type;
                stmt_ids = if (r.tree.kind(def_var_ch.identifier) == .partial__destructure) r.tree.manychildren(def_var_ch.identifier) else r.tree.arg_ptr(non_assignmoded_root, 1)[0..1];
            },
            .assign_typed => {
                const assign_typed_ch = r.tree.laidout_children(.assign_typed, non_assignmoded_root);
                const def_var_ch = r.tree.laidout_children(.def_var, assign_typed_ch.def_var);
                stmt_value = assign_typed_ch.assigned;
                stmt_type = r.tree.arg(assign_typed_ch.def_var, 0);
                stmt_ids = if (r.tree.kind(def_var_ch.identifier) == .partial__destructure) r.tree.manychildren(def_var_ch.identifier) else r.tree.arg_ptr(assign_typed_ch.def_var, 1)[0..1];
            },
            .assign => {
                const assign_ch = r.tree.laidout_children(.assign, non_assignmoded_root);
                stmt_value = r.tree.arg(non_assignmoded_root, 1);
                stmt_ids = if (r.tree.kind(assign_ch.assignee) == .partial__destructure) r.tree.manychildren(assign_ch.assignee) else r.tree.arg_ptr(non_assignmoded_root, 0)[0..1];
            },
            else => {},
        }

        const decl_id = if (stmt_ids.len == 1) r.node_decl[stmt_ids[0]] else .none;
        const assignable = stmt_ids.len == 1 and !r.tree.props(stmt_ids[0]).name;
        const assigns = stmt_type == 0 and (assignable or decl_id != .none and !r.decl_pool.get_kind(decl_id).is_fn());

        var values: []const NodeId = &.{};
        if (stmt_value != 0) {
            const r_ch = r.tree.arg(non_assignmoded_root, 1);
            values = if (r.tree.kind(r_ch) == .partial__assign_multival) r.tree.manychildren(r_ch) else r.tree.arg_ptr(non_assignmoded_root, 1)[0..1];
        }

        return .{
            .node = non_assignmoded_root,
            .flags = flags,
            .kind = if (assigns) .variable else r.decls.decl_kind(stmt_type, stmt_value),
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
pub fn res(self: *Decls) *Resolver {
    return @alignCast(@fieldParentPtr("decls", self));
}

pub fn use(self: *Decls, node: NodeId) DeclPool.Index {
    const r = self.res();
    const name = r.name_pool.name_of(node);
    const d = r.scopes.lookup(&r.decl_pool, name);
    if (d == .none) {
        if (!r.doc.has(node)) _ = r.report(.undefined_name, node, name, 0);
        return d;
    }
    r.node_decl[node] = d;
    self.ensure_signature(d);
    return d;
}

pub fn declare_local(self: *Decls, name: NamePool.Index, node: NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index) DeclPool.Index {
    const r = self.res();
    const d = r.decl_pool.push_decl(name, node, kind, ty, .{});
    r.scopes.bind(name, d);
    return d;
}

pub fn redeclared(self: *Decls, name: NamePool.Index, at: NodeId) void {
    const r = self.res();
    const d = r.scopes.in_scope(name);
    if (d != .none) r.doc.report(.duplicate_declaration, at, name, d);
}

pub fn link(self: *Decls, id: NodeId, d: DeclPool.Index, t: StaticPool.Index) void {
    const r = self.res();
    if (id == 0) return;
    r.node_decl[id] = d;
    r.node_type[id] = t;
}

pub fn ensure_signature(self: *Decls, decl: DeclPool.Index) void {
    const r = self.res();
    const state = r.decl_pool.state_ptr(decl);
    switch (state.*) {
        .unresolved => {},
        .resolving_signature => {
            _ = r.report(.declaration_cycle, r.decl_pool.get_node(decl), r.decl_pool.get_name(decl), 0);
            state.* = .failed;
            return;
        },
        else => return,
    }
    state.* = .resolving_signature;
    const sp = &r.static_pool;
    const kind = r.decl_pool.get_kind(decl);
    const s = Stmt.from_node(r, r.decl_pool.get_node(decl));
    if (s.type != 0 and r.tree.kind(s.type) == .type_fun and switch (r.decl_pool.get_name(decl)) {
        .init, .deinit, .main, .has_next, .next => true,
        else => false,
    }) _ = r.report(.redundant_fun, s.type, 0, 0);
    const flags = r.decl_pool.get_flags(decl);
    var ctx = FnCtx{ .decl = decl, .self_type = self.owner_of(decl), .in_static = flags.is_stc };
    const v = self.value_node(decl);
    self.open_scope(flags.is_global, if (r.decl_pool.self_off(decl) == 1) ctx.self_type else .none, v);
    if (!flags.is_global and kind.is_type_decl()) r.scopes.bind(.wall, .none);
    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => if (r.tree.props(v).function) {
            // stcfun: the first tuple is static, whatever the body produces is the result (a second tuple belongs to the produced function)
            const unit = r.tree.arg(v, 1);
            const tk = self.template_kind(decl);
            const uk = self.type_kind(unit);
            if (kind == .static_function and tk == .variable and uk != .variable) _ = r.report(.missing_ret, unit, 0, 0);
            const out = if (r.tree.kind(unit) == .ret) r.tree.arg(unit, 0) else unit;
            const ret: StaticPool.Index = if (kind == .static_function)
                self.type_kind(out).meta(if (r.tree.props(out).function) .fun_type else .poison_type)
            else if (r.tree.kind(v) == .def_fun_declaration or r.tree.kind(r.tree.arg(v, 0)) == .partial__fun_def_header_ret) .unit_type else sp.fresh_var(&r.abstract_pool, v);
            if (tk != .variable and uk == .variable) {
                _ = r.report(.redundant_ret, unit, 0, 0);
            } else if (tk != .variable and uk != tk) _ = r.report(.type_mismatch, unit, ret, tk.meta(.trait_type));
            const category: StaticPool.FunType.Category = switch (kind) {
                .static_function => .static,
                .inlined_function => .inlined,
                else => .default,
            };
            // a method's first parameter is the induced `*Self`, `init` constructs and has none
            r.decl_pool.set_ty(decl, r.types.fun_type(&ctx, v, category, ret, if (r.decl_pool.self_off(decl) == 1) sp.ptr_of(ctx.self_type, true) else .none));
            if (!r.generics.template_of.contains(decl)) for (r.tree.params_of(v), 0..) |pn, i| for (r.tree.params_of(v)[0..i], 0..) |q, j| if (self.param_name(q, j) == self.param_name(pn, i)) r.doc.report(.duplicate_declaration, pn, self.param_name(pn, i), decl);
            if (flags.is_global and r.decl_pool.get_name(decl) == .main) r.decl_pool.set_ty(decl, r.types.dynify(r.decl_pool.get_ty(decl)));
            r.decl_pool.set_value(decl, if (kind == .static_function)
                sp.intern(.{ .static_fun = .{ .decl = decl, .result_kind = if (sp.tag(ret) == .meta_type) sp.get(ret).meta_type else .stcfun } })
            else
                sp.intern(.{ .function = decl }));
        } else {
            // a function produced by a static expression (`fun sub_from_templ = my_templ(i32, false)`)
            const fv = r.interpreter.eval_static(&ctx, v);
            if (sp.tag(fv) == .function_value) {
                r.decl_pool.set_value(decl, fv);
                r.decl_pool.set_ty(decl, r.decl_pool.get_ty(sp.get(fv).function));
            } else if (fv != .poison_type) _ = r.report(.type_mismatch, v, sp.type_of(fv), .fun_type);
        },
        .record, .variant, .trait => _ = r.types.check_type_def(&ctx, decl, v),
        .type_alias => {
            const t = r.types.lower(&ctx, v);
            r.decl_pool.set_value(decl, t);
            r.decl_pool.set_ty(decl, sp.type_of(t));
        },
        else => _ = self.check_stmt(&ctx, r.decl_pool.get_node(decl)),
    }
    r.scopes.pop();
    if (r.decl_pool.get_state(decl) == .resolving_signature) r.decl_pool.set_state(decl, .signature_ready);
}

pub fn check_body(self: *Decls, decl: DeclPool.Index) void {
    const r = self.res();
    const state = r.decl_pool.state_ptr(decl);
    if (state.* != .signature_ready) return;
    const sp = &r.static_pool;
    const kind = r.decl_pool.get_kind(decl);
    const v = self.value_node(decl);
    const ty = r.decl_pool.get_ty(decl);
    // stcfun bodies are checked per realization, length-generic ones per length (`instantiate`); `main` is realized once, by the runtime
    const generic = sp.length_generic(&r.abstract_pool, ty) and !r.generics.template_of.contains(decl);
    const abstract = generic and sp.only_templates(ty);
    if (kind == .static_function or !kind.is_fn() or r.tree.kind(v) != .def_fun or generic and !abstract) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;
    const first = r.decl_pool.entries.len();
    const mark = r.doc.diagnostics.len();
    const outer = r.inits.enter();
    defer r.inits.leave(outer);
    // a local function sees which enclosing locals are not written yet
    if (kind == .function and !r.decl_pool.get_flags(decl).is_global) r.inits.import(0, outer, 0);
    const off = r.decl_pool.self_off(decl);
    var ctx = FnCtx{ .decl = decl, .ret_type = sp.get(ty).function_type.ret, .self_type = self.owner_of(decl), .abstract = abstract };
    self.open_scope(r.decl_pool.get_flags(decl).is_global, if (off == 1) ctx.self_type else .none, v);
    const g = r.generics.template_of.get(decl);
    const args = r.generics.realized_args.get(decl);
    const view = if (g) |t| !sp.only_templates(r.decl_pool.get_ty(t)) else false;
    // a where clause sees its own parameter and the ones before it; realized `type` parameters are static values
    var slot: usize = 0;
    for (r.tree.params_of(v), 0..) |pn, i| {
        const p = ParseTree.Param.from_node(r.tree, pn);
        const pt = sp.get(ty).function_type.params[i + off];
        if (p.default != 0) _ = r.exprs.check(&ctx, p.default, pt);
        const pd = self.declare_local(self.name_at(p, i), pn, .parameter, pt);
        r.node_decl[pn] = pd;
        const gp = if (g) |t| r.types.sig(t).params[i + off] else pt;
        r.decl_pool.flags_ptr(pd).is_view = view and sp.templated(gp) != .none;
        if (args) |a| if (sp.generic_slot(gp)) {
            if (sp.tag(gp) == .meta_type) r.decl_pool.set_value(pd, sp.get(a).aggregate.elems[slot]);
            slot += 1;
        };
        self.link(p.name, pd, pt);
        self.check_guards(&ctx, p, pt);
    }
    self.check_unit(&ctx, r.tree.arg(v, 1));
    r.scopes.pop();
    if (off == 1 and r.decl_pool.get_flags(@enumFromInt(first)).writes) r.decl_pool.flags_ptr(decl).writes = true;
    r.decl_pool.set_state(decl, if (r.doc.errors_since(r.tree, mark, v)) .failed else .done);
    if (!abstract) r.bodies.put(r.capture(decl, v, first));
}

pub fn check_unit(self: *Decls, ctx: *FnCtx, body: NodeId) void {
    const r = self.res();
    const sp = &r.static_pool;
    if (r.tree.kind(body) != .block) {
        _ = r.exprs.check(ctx, body, ctx.ret_type);
        return;
    }
    const t = r.exprs.infer(ctx, body, .none);
    const ret = sp.apply_vars(&r.abstract_pool, ctx.ret_type);
    // a `{}` body that never returns a value returns unit, a body with a result returns it on every path (`$main` falls off with 0)
    if (ret != .none and sp.tag(ret) == .type_var) _ = sp.unify(&r.abstract_pool, ctx.ret_type, .unit_type) else if (ret != .none and (ctx.decl == .none or r.decl_pool.get_name(ctx.decl) != .main) and ret != .unit_type and ret != .runit_type and ret != .poison_type and t != .never_type and t != .poison_type and !r.doc.has(body)) _ = r.report(.missing_ret, body, 0, 0);
}

pub fn check_stmt(self: *Decls, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const parts = Stmt.from_node(r, node);
    const n = parts.node;
    const flags = parts.flags;
    const kind = parts.kind;
    if (ctx.interpreted and kind.is_type_decl()) {
        _ = r.exprs.infer(ctx, parts.values[0], .none);
        const t = r.statics.deferred(ctx, parts.values[0]);
        for (parts.assignees) |id| {
            const d = self.declare(id, n, kind, if (t) |x| sp.type_of(x) else r.types.meta_of(parts.values[0]), flags);
            r.decl_pool.set_state(d, .done);
            r.decl_pool.set_value(d, t orelse .none);
        }
        return .unit_type;
    }
    if (kind == .function and parts.type == 0 and parts.assignees.len == 1) {
        const e = r.scopes.lookup(&r.decl_pool, r.name_pool.name_of(parts.assignees[0]));
        if (e != .none and !r.decl_pool.get_kind(e).is_fn() and r.decl_pool.get_ty(e) != .none and sp.tag(sp.apply_vars(&r.abstract_pool, r.decl_pool.get_ty(e))) == .function_type) {
            r.node_decl[parts.assignees[0]] = e;
            return self.check_stmt(ctx, node);
        }
    }
    if (kind != .variable) { // local function / type / trait
        for (parts.assignees) |id| {
            const d = self.declare(id, n, kind, .none, flags);
            self.ensure_signature(d);
            self.check_body(d);
        }
        return .unit_type;
    }
    const values = parts.values;
    // a write into an assignable (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    if (parts.assignees.len == 1 and r.name_pool.name_of(parts.assignees[0]) == .none) {
        const pt = r.mutability.check_assignable(ctx, parts.assignees[0]);
        for (values) |v| _ = r.exprs.check(ctx, v, pt);
        return .unit_type;
    }
    const declaring = parts.type != 0 or @as(u8, @bitCast(flags)) != 0;
    var ty: StaticPool.Index = if (parts.type != 0) r.types.realized_type(ctx, parts.type) else .none;
    // untyped: visible names are assigned, their type is shared by the new ones
    const existing = r.scratch(DeclPool.Index, parts.assignees.len);
    for (parts.assignees, 0..) |id, i| {
        existing[i] = if (declaring or self.pre_declared(r.node_decl[id], n)) .none else r.scopes.lookup(&r.decl_pool, r.name_pool.name_of(id));
        if (existing[i] == .none) continue;
        const outer = r.inits.save(0);
        r.inits.clear(0);
        const et = r.mutability.check_assignable(ctx, id);
        r.inits.copy(0, outer);
        r.inits.release(outer);
        if (ty == .none) ty = et else if (et != ty and et != .poison_type) _ = r.report(.destructure_type_conflict, id, et, ty);
    }
    r.scopes.push();
    if (values.len > 1) {
        var shared = ty;
        const lits = r.scratch(bool, values.len);
        for (values, 0..) |v, i| {
            const want = if (i < parts.assignees.len and existing[i] != .none) r.decl_pool.get_ty(existing[i]) else ty;
            lits[i] = want == .none and r.tree.is_literal(v);
            if (lits[i]) continue;
            const vt = r.exprs.check(ctx, v, want);
            if (shared == .none) shared = vt else if (ty == .none) {
                const j = sp.join(&r.abstract_pool, shared, vt);
                shared = if (j.ty == .none) r.report(.destructure_type_conflict, v, shared, vt) else j.ty;
            }
        }
        if (ty == .none) {
            for (values, 0..) |v, i| if (lits[i]) {
                _ = r.exprs.infer(ctx, v, .none);
            };
            if (shared == .none) shared = r.flow.literals_type(values);
            if (shared == .none) shared = r.node_type[values[0]];
            for (values, 0..) |v, i| if (lits[i] and shared != .poison_type) {
                const lt = r.statics.literal_type(v, shared);
                const j = sp.join(&r.abstract_pool, shared, lt);
                shared = if (j.ty == .none) r.report(.destructure_type_conflict, v, shared, lt) else j.ty;
            };
            for (values, 0..) |v, i| if (lits[i] and shared != .poison_type) {
                _ = r.exprs.expect(v, r.node_type[v], shared);
            };
        }
        ty = shared;
    } else if (values.len == 1) {
        // a fresh var as expectation means "a value is wanted" (loops / ifs as values) without fixing its type
        const got = r.exprs.check(ctx, values[0], if (ty != .none) ty else sp.fresh_var(&r.abstract_pool, n));
        if (ty == .none) ty = sp.apply_vars(&r.abstract_pool, got);
        if (ty != .none and sp.tag(ty) == .function_type and sp.holds_template(ty)) ty = r.report(.unrealized_template, values[0], ty, 0);
    }
    r.scopes.pop();
    for (parts.assignees, 0..) |id, i| {
        const d = if (existing[i] != .none) existing[i] else self.declare(id, n, .variable, if (ty == .none) .poison_type else ty, flags);
        const dt = r.decl_pool.get_ty(d);
        // scalars declared without a value must be written before they are read
        const scalar = dt != .none and dt != .poison_type and sp.tag(dt) != .record_type and sp.tag(dt) != .array_type;
        if (existing[i] != .none) r.inits.written(d) else if (values.len == 0 and !r.decl_pool.get_flags(d).is_global and scalar) r.inits.track(d);
        if (values.len > 0 and (existing[i] == .none or (r.interpreter.depth > 0 and !ctx.interpreted)) and (r.decl_pool.get_flags(d).is_stc or ctx.in_static)) {
            const val = values[@min(i, values.len - 1)];
            r.decl_pool.set_value(d, if (r.node_type[val] == .poison_type) .poison_type else r.statics.retype(r.statics.static_of(ctx, val), dt));
            // an unlengthed static takes the length of its value
            const v = r.decl_pool.get_value(d);
            if (v != .none and sp.tag(v) == .aggregate_value and sp.has_vars(dt)) _ = sp.unify(&r.abstract_pool, dt, sp.type_of(v));
            if (v != .none and sp.tag(v) == .aggregate_value and (if (sp.static_len(dt)) |len| len != sp.get(v).aggregate.elems.len else false))
                _ = r.report(.type_mismatch, val, sp.type_of(v), dt);
        }
    }
    return .unit_type;
}

pub fn check_guards(self: *Decls, ctx: *FnCtx, p: ParseTree.Param, t: StaticPool.Index) void {
    const r = self.res();
    if (p.where != 0) _ = r.exprs.check(ctx, p.where, .bool_type);
    if (p.@"else" != 0) _ = if (r.tree.kind(p.@"else") == .assign) r.exprs.infer(ctx, p.@"else", .none) else r.exprs.check(ctx, p.@"else", t);
}

// a declared global row is reused, anything else becomes a new local
fn declare(self: *Decls, id: NodeId, stmt: NodeId, kind: DeclPool.Entry.Kind, ty: StaticPool.Index, flags: DeclPool.Entry.Flags) DeclPool.Index {
    const r = self.res();
    var d = r.node_decl[id];
    if (!self.pre_declared(d, stmt)) {
        self.redeclared(r.name_pool.name_of(id), id);
        d = self.declare_local(r.name_pool.name_of(id), stmt, kind, ty);
        r.decl_pool.set_flags(d, flags);
        r.node_decl[id] = d;
    } else if (ty != .none) r.decl_pool.set_ty(d, ty);
    _ = r.set(id, if (ty == .none) .unit_type else ty);
    return d;
}

// global rows and hoisted local functions of this very statement are reused instead of declared again
fn pre_declared(self: *Decls, d: DeclPool.Index, stmt: NodeId) bool {
    const r = self.res();
    return d != .none and r.decl_pool.get_node(d) == stmt and (r.decl_pool.get_flags(d).is_global or r.scopes.lookup(&r.decl_pool, r.decl_pool.get_name(d)) == d);
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
pub fn open_scope(self: *Decls, barrier: bool, self_type: StaticPool.Index, node: NodeId) void {
    const r = self.res();
    r.scopes.push();
    if (barrier) r.scopes.bind(.none, .none);
    if (self_type != .none) r.decl_pool.flags_ptr(self.declare_local(.self, node, .self, r.static_pool.ptr_of(self_type, true))).is_mut = true;
}

// methods: the owning type is the value of the trait body row right before its members; realizations ask their template
fn owner_of(self: *Decls, decl: DeclPool.Index) StaticPool.Index {
    const r = self.res();
    if (r.generics.template_of.get(decl)) |t| return self.owner_of(t);
    if (r.decl_pool.get_kind(decl) != .trait_member) return .none;
    var d = @intFromEnum(decl);
    while (r.decl_pool.get_kind(@enumFromInt(d)) != .trait) d -= 1;
    return r.decl_pool.get_value(@enumFromInt(d));
}

// the kind of type a definition node declares, `variable` for anything else
pub fn type_kind(self: *Decls, n: NodeId) DeclPool.Entry.Kind {
    const r = self.res();
    return switch (r.tree.kind(ParseTree.Def.from_node(r.tree, n).core)) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

// the kind a statement declares, read from its type and value
pub fn decl_kind(self: *Decls, type_node: NodeId, value: NodeId) DeclPool.Entry.Kind {
    const tree = self.res().tree;
    const tk = self.type_kind(value);
    return switch (tree.kind(type_node)) {
        .type_fun => .function,
        .type_stcfun => .static_function,
        .type_inlfun => .inlined_function,
        .type_type, .type_variant, .type_trait => if (value != 0 and tree.kind(value) == .def_fun) .static_function else switch (tree.kind(type_node)) {
            .type_type => if (tk == .record) .record else .type_alias,
            .type_variant => if (tk == .variant) .variant else .type_alias,
            else => if (tk == .trait) .trait else .type_alias,
        },
        .none => if (value != 0 and tree.props(value).function) .function else .variable,
        else => .variable,
    };
}

// what a stcfun declared as `type` / `variant` / `trait` produces
pub fn template_kind(self: *Decls, decl: DeclPool.Index) DeclPool.Entry.Kind {
    const r = self.res();
    const tree = r.tree;
    const decl_node = r.decl_pool.get_node(decl);
    if (tree.kind(decl_node) != .assign_typed or tree.kind(tree.arg(decl_node, 1)) != .def_fun) return .variable;
    return switch (tree.kind(tree.arg(tree.arg(decl_node, 0), 0))) {
        .type_type => .record,
        .type_variant => .variant,
        .type_trait => .trait,
        else => .variable,
    };
}

pub fn value_node(self: *Decls, d: DeclPool.Index) NodeId {
    const r = self.res();
    const n = r.decl_pool.get_node(d);
    return switch (r.tree.kind(n)) {
        .assign, .assign_typed => r.tree.arg(n, 1),
        else => n,
    };
}

pub fn param_name(self: *Decls, pn: NodeId, i: usize) NamePool.Index {
    const r = self.res();
    return self.name_at(ParseTree.Param.from_node(r.tree, pn), i);
}

// the index of the parameter or field `name` among `params`
pub fn param_index(self: *Decls, params: []const NodeId, name: NamePool.Index) ?u32 {
    for (params, 0..) |pn, j| if (self.param_name(pn, j) == name) return @intCast(j);
    return null;
}

pub fn name_at(self: *Decls, p: ParseTree.Param, i: usize) NamePool.Index {
    const r = self.res();
    return if (p.name != 0) r.name_pool.name_of(p.name) else r.name_pool.indexed(i);
}

// a closure holds a pointer to a mutable or aggregate local, a copy of anything else
pub fn by_ref(self: *Decls, d: DeclPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    const t = sp.apply_vars(&r.abstract_pool, r.decl_pool.get_ty(d));
    return r.decl_pool.get_flags(d).is_mut or t != .none and (sp.tag(t) == .record_type or sp.tag(t) == .array_type and sp.get(t).array_type.len != StaticPool.dyn_len);
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
pub fn real(self: *Decls, d: DeclPool.Index) DeclPool.Index {
    const r = self.res();
    const v = r.decl_pool.get_value(d);
    return if (v != .none and r.static_pool.tag(v) == .function_value) r.static_pool.get(v).function else d;
}

// every root declares its names globally, overloads of a name are chained in dispatch order
pub fn collect_globals(self: *Decls) void {
    const r = self.res();
    for (r.roots) |root| {

        // every root is assumed to be a "statement", but statements did not exist up until now,
        //   as statements were expressions aswell in the `Parser`
        const s = Stmt.from_node(r, root);

        var flags = s.flags;
        flags.is_global = true;
        const declares = s.declares();

        for (s.assignees) |assignee_id| {
            // possibly not an identifier, therefore `continue` for `.none`
            const name = r.name_pool.name_of(assignee_id);
            if (name == .none) continue;

            const gop = r.scopes.globals.getOrPut(r.alloc, name) catch @panic("OOM");
            const name_has_decl = gop.found_existing;

            // if the name is declared and not a new function overload -> duplicate decl error
            if (name_has_decl and !(s.kind.is_fn() and r.decl_pool.get_kind(gop.value_ptr.*).is_fn())) {
                if (declares) {
                    _ = r.report(.duplicate_declaration, assignee_id, name, gop.value_ptr.*);
                    if (r.node_decl[root] == .none) r.node_decl[root] = gop.value_ptr.*;
                }
                continue;
            }

            const new_decl = r.decl_pool.push_decl(name, s.node, s.kind, .none, flags);

            // overloads with a where clause come before the ones without, so every group of same-typed
            // overloads reads as a runtime dispatch: its where-clauses in order, the where-less fallback last
            if (gop.found_existing) {
                var at = gop.value_ptr;
                while (at.* != .none and (!r.calls.has_where(new_decl) or r.calls.has_where(at.*))) at = r.decl_pool.next_overload_ptr(at.*);
                r.decl_pool.set_next_overload(new_decl, at.*);
                at.* = new_decl;
            } else gop.value_ptr.* = new_decl;
            r.node_decl[assignee_id] = new_decl;
            if (r.node_decl[root] == .none) r.node_decl[root] = new_decl;
        }
    }
}

// `main` is declared once with a signature the runtime can call
pub fn check_main(self: *Decls) void {
    const r = self.res();
    const main = r.scopes.globals.get(.main) orelse return r.doc.report(.missing_main, 0, 0, 0);
    const node = r.decl_pool.get_node(main);
    if (r.decl_pool.get_next_overload(main) != .none) return r.doc.report(.duplicate_declaration, r.decl_pool.get_node(r.decl_pool.get_next_overload(main)), NamePool.Index.main, main);
    const ty = r.decl_pool.get_ty(main);
    const sp = &r.static_pool;
    const ok = ty != .none and sp.tag(ty) == .function_type and blk: {
        const f = sp.get(ty).function_type;
        const args_ok = f.params.len == 0 or (f.params.len == 2 and sp.get_tag_prop(f.params[0]).is_integer and sp.get_tag_prop(f.params[1]).is_pointer);
        break :blk args_ok and (f.ret == .unit_type or f.ret == .runit_type or f.ret == .never_type or sp.get_tag_prop(f.ret).is_integer);
    };
    if (!ok) _ = r.report(.type_mismatch, node, ty, .none);
}
