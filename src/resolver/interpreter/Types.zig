const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// types: type values built while evaluating, casts and questions about types
const Types = @This();

pub fn interp(self: *Types) *Interpreter {
    return @alignCast(@fieldParentPtr("types", self));
}

pub fn of(self: *Types, n: NodeId) ?Index {
    const ip = self.interp();
    const v = ip.eval(n);
    if (v.is(.poison_type)) return null;
    if (v.is_pool() and !v.is(.none) and ip.res().static_pool.get_tag_prop(v.index()).is_type) return v.index();
    _ = ip.fail(n, .not_a_type, ip.pool(v), .none);
    return null;
}

pub fn admits(self: *Types, v: Value, t: Index) bool {
    const ip = self.interp();
    const r = ip.res();
    const vt = ip.vtype(v);
    if ((Value.is_int(vt) or Value.is_float(vt)) and (Value.is_int(t) or Value.is_float(t))) return true;
    return vt == t or r.static_pool.coerce(&r.abstract_pool, vt, t) != .incompatible;
}

pub fn joined(self: *Types, vs: []const Value) Index {
    const ip = self.interp();
    if (vs.len == 0) return .unit_type;
    const sp = &ip.res().static_pool;
    const t = ip.vtype(vs[0]);
    for (vs[1..]) |v| if (ip.vtype(v) != t and sp.tag(t) == .array_type) return sp.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = sp.get(t).array_type.elem } });
    return t;
}

pub fn static(self: *Types, n: NodeId, k: Kind) Value {
    const ip = self.interp();
    const r = ip.res();
    if (!ip.framed()) return .pooled(r.types.static_type(ip.ctx, n));
    return switch (k) {
        .def_fun => ip.calls.closure(ip.info(.decl, n)),
        .type_array, .type_array_unlengthed, .type_ptr, .type_ptrmut, .unify_variants => self.build(n),
        else => .pooled(self.define(n)),
    };
}

fn build(self: *Types, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const k = r.tree.kind(n);
    if (k == .unify_variants) {
        const mark = ip.ids.head;
        defer ip.ids.head = mark;
        for ([_]NodeId{ r.tree.arg(n, 0), r.tree.arg(n, 1) }) |side| {
            const t = self.of(side) orelse return .poison;
            switch (sp.tag(t)) {
                .variant_union_type => ip.ids.append(sp.get(t).variant_union_type),
                .variant_type => ip.ids.push(t),
                else => return ip.fail(side, .type_mismatch, t, .variant_type),
            }
        }
        return .pooled(sp.intern(.{ .variant_union_type = ip.ids.buf[mark..ip.ids.head] }));
    }
    const child = self.of(r.tree.arg(n, if (k == .type_array) 1 else 0)) orelse return .poison;
    if (r.tree.props(n).pointer) return .pooled(sp.ptr_of(child, k == .type_ptrmut));
    if (k == .type_array_unlengthed) return .pooled(sp.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = child } }));
    const len = ip.eval(r.tree.arg(n, 0));
    if (!Value.is_int(len.ty)) return if (len.is(.poison_type)) len else ip.fail(r.tree.arg(n, 0), .not_static, ip.pool(len), 0);
    return .pooled(sp.array_of(len.bits, child));
}

fn define(self: *Types, n: NodeId) Index {
    const ip = self.interp();
    const r = ip.res();
    var ctx = Resolver.FnCtx{ .decl = .none, .ret_type = .none, .self_type = .none, .loop_depth = 0, .in_static = true };
    r.decls.open_scope(true, .none, 0);
    defer r.scopes.pop();
    const s = r.tree.subtree(n);
    for (s[0]..s[1]) |i| {
        const id: NodeId = @intCast(i);
        const d = ip.info(.decl, id);
        if (!r.tree.props(id).name or d == .none or r.decl_pool.get_flags(d).is_global) continue;
        const v = ip.variables.peek(d);
        if (v.is(.none)) continue;
        const x = ip.pool(v);
        r.decl_pool.set_value(r.decls.declare_local(r.decl_pool.get_name(d), id, .static_parameter, r.decl_pool.get_ty(d)), x);
    }
    return r.types.static_type(&ctx, n);
}

pub fn cast(self: *Types, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const a1 = r.tree.arg(n, 1);
    const framed = ip.framed();
    const x = ip.eval(a0);
    if (!framed or ip.info(.ty, n) != .poison_type) {
        const c = ip.patterns.case_of(x);
        const from = if (framed) sp.apply_vars(&r.abstract_pool, ip.info(.ty, a0)) else if (c != .none) c else ip.vtype(x);
        const t = if (framed) ip.info(.ty, n) else r.types.cast_target(ip.ctx, a1, from);
        const ck = sp.cast(from, t);
        if (ck == .bit_reinterpret and Value.is_int(t) and sp.get_tag_prop(from).is_variant) return self.tag(n, x, t);
        if (ck == .variant_retag) return self.retag(n, x, t);
        return if (ck == .array_narrow or ck == .pointer_relength) self.shrink(n, x, t) else .cast(x, t);
    }
    if (ip.info(.value, a1) != .none) return .poison;
    const t = self.of(a1) orelse return .poison;
    return if (sp.cast(ip.vtype(x), t) == .invalid) ip.fail(n, .invalid_cast, ip.vtype(x), t) else .cast(x, t);
}

// a variant case without payload reinterpreted as an integer is its tag
fn tag(self: *Types, n: NodeId, x: Value, t: Index) Value {
    const ip = self.interp();
    const sp = &ip.res().static_pool;
    const c = ip.patterns.case_of(x);
    if (c == .none or sp.get(c).variant_case_type.payload != .none) return ip.fail(n, .not_static, 0, 0);
    return .int(t, sp.get(sp.get(c).variant_case_type.tag).int.bits);
}

// another case of the same variant keeps the payload bits
fn retag(self: *Types, n: NodeId, x: Value, t: Index) Value {
    const ip = self.interp();
    const sp = &ip.res().static_pool;
    const c = ip.patterns.case_of(x);
    if (c == t) return x;
    const to = sp.get(t).variant_case_type.payload;
    if (to == .none) return .pooled(t);
    if (c == .none or !x.is_pool() or sp.tag(x.index()) != .variant_value) return ip.fail(n, .not_static, 0, 0);
    const k = sp.get(to).custom_type.field_types.len;
    if (sp.get(sp.get(c).variant_case_type.payload).custom_type.field_types.len != k) return ip.fail(n, .not_static, 0, 0);
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    ip.ids.append(sp.get(sp.get(x.index()).variant_value.payload).aggregate.elems);
    for (0..k) |i| {
        const f = sp.field_type(sp.get(c).variant_case_type.payload, i);
        const into = sp.field_type(to, i);
        if (f != into) ip.ids.buf[mark + i] = ip.pool(Value.reinterpret(.of(sp, ip.ids.buf[mark + i]), into) orelse return ip.fail(n, .not_static, 0, 0));
    }
    return .pooled(sp.intern(.{ .variant_value = .{ .case = t, .payload = sp.intern(.{ .aggregate = .{ .ty = to, .elems = ip.ids.buf[mark..ip.ids.head] } }) } }));
}

fn shrink(self: *Types, n: NodeId, x: Value, t: Index) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    if (x.is(.poison_type) or t == .poison_type) return .poison;
    const ptr = sp.is_ptr(t);
    const at = sp.pointee(t);
    if (sp.tag(sp.get(at).array_type.len) != .int_value) return if (ptr and x.is_ref()) .ref(t, x.at()) else x;
    const g = r.tree.narrowed(r.tree.arg(n, 1));
    const lo: u32 = if (g != 0) @truncate(ip.eval(g).bits) else 0;
    const c0 = if (x.is_ref()) x.at() else ip.put(x);
    const c = if (ip.span(ip.mem.buf[c0]) != null) ip.thaw(c0).at() else c0;
    const view: Value = .block(at, c + lo, @intCast(sp.get(sp.get(at).array_type.len).int.bits));
    return if (ptr) .ref(t, ip.put(view)) else view;
}

pub fn asbits(self: *Types, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const x = Value.fit(ip.eval(r.tree.arg(n, 0)), ip.info(.ty, r.tree.arg(n, 0)));
    if (x.is(.poison_type)) return x;
    return Value.reinterpret(x, if (ip.framed()) ip.info(.ty, n) else r.types.lower(ip.ctx, r.tree.arg(n, 1))) orelse ip.fail(n, .not_static, ip.pool(x), 0);
}

pub fn oftype(self: *Types, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const a1 = r.tree.arg(n, 1);
    const framed = ip.framed();
    const st = if (framed) Index.none else sp.deref(&r.abstract_pool, r.exprs.infer(ip.ctx, a0, .none));
    const known = st != .none and st != .poison_type and sp.tag(st) != .meta_type and sp.tag(st) != .trait_type and sp.templated(st) == .none;
    const x = if (known) st else ip.pool(ip.deref(ip.eval(a0)));
    const c0 = if (framed) ip.info(.value, a1) else r.types.lower(ip.ctx, a1);
    const c = if (c0 != .none and sp.tag(c0) == .generic) sp.intern(.{ .template_type = sp.get(c0).static_fun.decl }) else c0;
    const t = if (c != .none) c else self.of(a1) orelse return .poison;
    const vt = if (sp.get_tag_prop(x).is_type) x else sp.type_of(x);
    if (sp.tag(t) == .template_type) return .boolean(r.generics.realizes(vt, t));
    return .boolean(vt == t or sp.type_of(x) == t or sp.implements(vt, t));
}

pub fn sizeof(self: *Types, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const t = ip.checked(a0);
    const ty = if (sp.tag(t) == .meta_type) ip.pool(ip.eval(a0)) else sp.apply_vars(&r.abstract_pool, t);
    if (r.generics.is_template(ip.info(.decl, a0)) or ty != .poison_type and sp.holds_template(ty)) return ip.fail(a0, .unrealized_template, ty, 0);
    return if (ty == .poison_type) .poison else .int(.u64_type, sp.layout(r.types.dynify(ty)).size);
}
