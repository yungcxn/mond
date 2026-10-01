const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const places = @import("places.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

pub fn of(ip: *Interpreter, n: NodeId) ?Index {
    const v = ip.eval(n);
    if (v.is(.poison_type)) return null;
    if (v.is_pool() and !v.is(.none) and ip.res().static_pool.get_tag_prop(v.index()).is_type) return v.index();
    _ = ip.fail(n, .not_a_type, ip.pool(v), .none);
    return null;
}

pub fn admits(ip: *Interpreter, v: Value, t: Index) bool {
    const r = ip.res();
    const vt = ip.vtype(v);
    if ((Value.is_int(vt) or Value.is_float(vt)) and (Value.is_int(t) or Value.is_float(t))) return true;
    return vt == t or r.static_pool.coerce(&r.abstract_pool, vt, t) != .incompatible;
}

pub fn unknown(sp: *const StaticPool, t: Index) bool {
    if (t == .none) return false;
    return t == .poison_type or switch (sp.get(t)) {
        .array_type => |a| a.len == .poison_type or unknown(sp, a.elem),
        .ptr_type => |p| unknown(sp, p.child),
        else => false,
    };
}

pub fn array_type(ip: *Interpreter, len: u64, et: Index) Index {
    const sp = &ip.res().static_pool;
    return sp.intern(.{ .array_type = .{ .len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = len } }), .elem = et } });
}

pub fn elem_type(ip: *Interpreter, t0: Index) Index {
    const r = ip.res();
    if (t0 == .none) return .none;
    const t = r.static_pool.apply_vars(&r.abstract_pool, t0);
    if (r.static_pool.tag(t) != .array_type) return .none;
    const e = r.static_pool.get(t).array_type.elem;
    return if (r.static_pool.has_vars(e)) .none else e;
}

pub fn static(ip: *Interpreter, n: NodeId, k: Kind) Value {
    const r = ip.res();
    if (!ip.framed()) return .pooled(r.static_type(ip.ctx, n));
    return switch (k) {
        .def_fun => ip.closure(ip.info(.decl, n)),
        .type_array, .type_array_unlengthed, .type_ptr, .type_ptrmut, .unify_variants => build(ip, n),
        else => .pooled(define(ip, n)),
    };
}

fn build(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const k = r.tree.kind(n);
    if (k == .unify_variants) {
        const mark = ip.ids.head;
        defer ip.ids.head = mark;
        for ([_]NodeId{ r.tree.arg(n, 0), r.tree.arg(n, 1) }) |side| {
            const t = of(ip, side) orelse return .poison;
            switch (sp.tag(t)) {
                .variant_union_type => ip.ids.append(sp.get(t).variant_union_type),
                .variant_type => ip.ids.push(t),
                else => return ip.fail(side, .type_mismatch, t, .variant_type),
            }
        }
        return .pooled(sp.intern(.{ .variant_union_type = ip.ids.buf[mark..ip.ids.head] }));
    }
    const child = of(ip, r.tree.arg(n, if (k == .type_array) 1 else 0)) orelse return .poison;
    if (k == .type_ptr or k == .type_ptrmut) return .pooled(sp.intern(.{ .ptr_type = .{ .child = child, .mutable = k == .type_ptrmut } }));
    if (k == .type_array_unlengthed) return .pooled(sp.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = child } }));
    const len = ip.eval(r.tree.arg(n, 0));
    if (!Value.is_int(len.ty)) return if (len.is(.poison_type)) len else ip.fail(r.tree.arg(n, 0), .not_static, ip.pool(len), 0);
    return .pooled(array_type(ip, len.bits, child));
}

fn define(ip: *Interpreter, n: NodeId) Index {
    const r = ip.res();
    var ctx = Resolver.FnCtx{ .decl = .none, .ret_type = .none, .self_type = .none, .loop_depth = 0, .in_static = true };
    r.open_scope(true, .none, 0);
    defer r.h04_pop_scope();
    const s = r.subtree(n);
    for (s[0]..s[1]) |i| {
        const id: NodeId = @intCast(i);
        const d = ip.info(.decl, id);
        if (!places.named(r.tree.kind(id)) or d == .none or r.dp(.flags, d).is_global) continue;
        const v = places.peek(ip, d);
        if (v.is(.none)) continue;
        const x = ip.pool(v);
        r.dp(.value, r.h02_declare_local(r.dp(.name, d).*, id, .static_parameter, r.dp(.ty, d).*)).* = x;
    }
    return r.static_type(&ctx, n);
}

pub fn cast(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const a1 = r.tree.arg(n, 1);
    const framed = ip.framed();
    const x = ip.eval(a0);
    if (!framed or ip.info(.ty, n) != .poison_type) {
        const from = if (framed) sp.apply_vars(&r.abstract_pool, ip.info(.ty, a0)) else ip.vtype(x);
        const t = if (framed) ip.info(.ty, n) else r.cast_target(ip.ctx, a1, from);
        const ck = sp.cast(from, t);
        if (ck == .bit_reinterpret and Value.is_int(t) and sp.get_tag_prop(from).is_variant) return tag(ip, n, x, t);
        return if (ck == .array_narrow or ck == .pointer_relength) shrink(ip, n, x, t) else .cast(x, t);
    }
    if (ip.info(.value, a1) != .none) return .poison;
    const t = of(ip, a1) orelse return .poison;
    return if (sp.cast(ip.vtype(x), t) == .invalid) ip.fail(n, .invalid_cast, ip.vtype(x), t) else .cast(x, t);
}

// a variant case without payload reinterpreted as an integer is its tag
fn tag(ip: *Interpreter, n: NodeId, x: Value, t: Index) Value {
    const sp = &ip.res().static_pool;
    const c = @import("control.zig").case_of(ip, x);
    if (c == .none or sp.get(c).variant_case_type.payload != .none) return ip.fail(n, .not_static, 0, 0);
    return .int(t, sp.get(sp.get(c).variant_case_type.tag).int.bits);
}

fn shrink(ip: *Interpreter, n: NodeId, x: Value, t: Index) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    if (x.is(.poison_type) or t == .poison_type) return .poison;
    const ptr = sp.is_ptr(t);
    const at = sp.pointee(t);
    if (sp.tag(sp.get(at).array_type.len) != .int_value) return if (ptr and x.is_ref()) .ref(t, x.at()) else x;
    const g = r.narrowed(r.tree.arg(n, 1));
    const lo: u32 = if (g != 0) @truncate(ip.eval(g).bits) else 0;
    const c0 = if (x.is_ref()) x.at() else ip.put(x);
    const c = if (ip.span(ip.mem.buf[c0]) != null) ip.thaw(c0).at() else c0;
    const view: Value = .block(at, c + lo, @intCast(sp.get(sp.get(at).array_type.len).int.bits));
    return if (ptr) .ref(t, ip.put(view)) else view;
}

pub fn asbits(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const x = Value.fit(ip.eval(r.tree.arg(n, 0)), ip.info(.ty, r.tree.arg(n, 0)));
    if (x.is(.poison_type)) return x;
    return Value.reinterpret(x, if (ip.framed()) ip.info(.ty, n) else r.h07_lower_type(ip.ctx, r.tree.arg(n, 1))) orelse ip.fail(n, .not_static, ip.pool(x), 0);
}

pub fn oftype(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const a1 = r.tree.arg(n, 1);
    const framed = ip.framed();
    const st = if (framed) Index.none else r.deref(r.h09_check_expr(ip.ctx, a0, .none));
    const known = st != .none and st != .poison_type and sp.tag(st) != .meta_type and sp.tag(st) != .trait_type and r.templated(st) == .none;
    const x = if (known) st else ip.pool(ip.deref(ip.eval(a0)));
    const c0 = if (framed) ip.info(.value, a1) else r.h07_lower_type(ip.ctx, a1);
    const c = if (c0 != .none and sp.tag(c0) == .generic) sp.intern(.{ .template_type = sp.get(c0).static_fun.decl }) else c0;
    const t = if (c != .none) c else of(ip, a1) orelse return .poison;
    const vt = if (sp.get_tag_prop(x).is_type) x else sp.type_of(x);
    if (sp.tag(t) == .template_type) return .boolean(r.realizes(vt, t));
    return .boolean(vt == t or sp.type_of(x) == t or sp.implements(vt, t));
}

pub fn sizeof(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const a0 = r.tree.arg(n, 0);
    const t = ip.checked(a0);
    const ty = if (sp.tag(t) == .meta_type) ip.pool(ip.eval(a0)) else sp.apply_vars(&r.abstract_pool, t);
    if (r.is_template(ip.info(.decl, a0)) or ty != .poison_type and r.holds_template(ty)) return ip.fail(a0, .unrealized_template, ty, 0);
    return if (ty == .poison_type) .poison else .int(.u64_type, sp.layout(ty).size);
}
