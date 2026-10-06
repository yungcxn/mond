const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

// match: arms tried in order, patterns tested against values and their binders bound
const Patterns = @This();

pub fn interp(self: *Patterns) *Interpreter {
    return @alignCast(@fieldParentPtr("patterns", self));
}

pub fn match(self: *Patterns, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const x = ip.eval(r.tree.arg(n, 0));
    const t = if (ip.framed()) ip.info(.ty, r.tree.arg(n, 0)) else x.ty;
    const v = if (x.is_ref() and r.static_pool.deref(&r.abstract_pool, t) != t) ip.deref(x) else x;
    if (v.is(.poison_type) or ip.unwind != .none) return v;
    const scoped = !ip.framed();
    if (scoped) r.scopes.push();
    defer if (scoped) r.scopes.pop();
    if (!scoped) for (r.tree.manychildren(r.tree.arg(n, 1))) |arm| if (ip.info(.value, arm) == .bool_true) return ip.eval(r.tree.arg(arm, 1));
    for (r.tree.manychildren(r.tree.arg(n, 1))) |arm| if (self.matches(r.tree.arg(arm, 0), v)) return ip.eval(r.tree.arg(arm, 1));
    return ip.fail(n, .non_exhaustive_match, ip.pool(v), .none);
}

// a case value is pooled, or a block of its payload fields when they hold references
pub fn case_of(self: *Patterns, v: Value) Index {
    const ip = self.interp();
    const sp = &ip.res().static_pool;
    if (v.is_heap() and sp.tag(v.ty) == .variant_case_type) return v.ty;
    if (!v.is_pool() or v.is(.none)) return .none;
    return switch (sp.tag(v.index())) {
        .variant_value => sp.get(v.index()).variant_value.case,
        .variant_case_type => v.index(),
        else => .none,
    };
}

fn same(self: *Patterns, a: Value, b: Value) bool {
    const ip = self.interp();
    return Value.eql(if (a.is_heap()) .pooled(ip.pool(a)) else a, if (b.is_heap()) .pooled(ip.pool(b)) else b);
}

pub fn matches(self: *Patterns, p: NodeId, v: Value) bool {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const framed = ip.framed();
    switch (r.tree.kind(p)) {
        .identifier => {
            self.name(p, v);
            return true;
        },
        .partial__match_case_pattern_or => {
            for (r.tree.manychildren(p)) |alt| if (self.matches(alt, v)) return true;
            return false;
        },
        .partial__match_case_pattern_typecast => {
            const t = if (framed) ip.info(.ty, r.tree.arg(p, 1)) else r.types.lower(ip.ctx, r.tree.arg(p, 0));
            const c = self.case_of(v);
            const vt = ip.vtype(v);
            const ok = if (c != .none) sp.get(c).variant_case_type.variant == t or sp.tag(t) == .variant_union_type else vt == t or sp.implements(vt, t);
            if (ok) self.name(r.tree.arg(p, 1), v);
            return ok;
        },
        .labelarrow => {
            if (!self.matches(r.tree.arg(p, 0), v)) return false;
            self.label(r.tree.arg(p, 1), self.payload(v) orelse v);
            return true;
        },
        .fun_call => {
            const h = ip.info(.ty, p);
            const target = if (h != .none) h else ip.pool(ip.eval(r.tree.arg(p, 0)));
            var rec = target;
            var fields = v;
            if (sp.tag(target) == .variant_case_type) {
                if (self.case_of(v) != target) return false;
                rec = sp.get(target).variant_case_type.payload;
                fields = if (v.is_heap()) .block(rec, v.at(), v.len()) else if (sp.tag(v.index()) == .variant_value) .of(sp, sp.get(v.index()).variant_value.payload) else .empty;
            }
            for (r.tree.manychildren(r.tree.arg(p, 1)), 0..) |a, i| {
                const fi = r.calls.field_of(rec, a, i) orelse return false;
                if (fi >= (ip.span(fields) orelse 0) or !self.matches(r.tree.arg_value(a), ip.elem(fields, @intCast(fi)))) return false;
            }
            return true;
        },
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => {
            const g = ParseTree.Range.from_node(r.tree, p);
            if (!Value.is_int(v.ty) or g.lo != 0 and Value.less(v, ip.eval(g.lo))) return false;
            if (g.hi == 0) return true;
            const hi = ip.eval(g.hi);
            return if (g.incl) !Value.less(hi, v) else Value.less(v, hi);
        },
        else => {
            const pv = ip.eval(p);
            if (pv.is_pool() and !pv.is(.none) and sp.tag(pv.index()) == .variant_case_type) return self.case_of(v) == pv.index();
            return !pv.is(.poison_type) and self.same(pv, v);
        },
    }
}

fn name(self: *Patterns, id: NodeId, v: Value) void {
    const ip = self.interp();
    const r = ip.res();
    if (ip.framed()) return ip.variables.bind(ip.info(.decl, id), v);
    const nm = r.name_pool.name_of(id);
    if (nm == .underscore) return;
    const d = r.decls.declare_local(nm, id, .pattern_binder, ip.vtype(v));
    r.node_decl[id] = d;
    ip.variables.bind(d, v);
}

pub fn label(self: *Patterns, l: NodeId, v: Value) void {
    const ip = self.interp();
    const r = ip.res();
    if (r.tree.kind(l) != .partial__destructure) return self.name(l, v);
    for (r.tree.manychildren(l), 0..) |id, i| self.name(id, if (i < (ip.span(v) orelse 0)) ip.elem(v, @intCast(i)) else .poison);
}

pub fn payload(self: *Patterns, v: Value) ?Value {
    const ip = self.interp();
    const sp = &ip.res().static_pool;
    if (v.is_heap() and sp.tag(v.ty) == .variant_case_type) return if (v.len() == 1) ip.mem.buf[v.at()] else .block(sp.get(v.ty).variant_case_type.payload, v.at(), v.len());
    if (!v.is_pool() or v.is(.none) or sp.tag(v.index()) != .variant_value) return null;
    const pv = sp.get(v.index()).variant_value.payload;
    if (pv == .none) return null;
    const elems = sp.get(pv).aggregate.elems;
    return .of(sp, if (elems.len == 1) elems[0] else pv);
}
