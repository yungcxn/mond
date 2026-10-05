const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const calls = @import("calls.zig");
const places = @import("places.zig");
const types = @import("types.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const Decl = Resolver.Decl;

pub fn jump(ip: *Interpreter, n: NodeId, k: Kind) Value {
    const x: Value = if (k == .ret) ip.eval(ip.res().tree.arg(n, 0)) else .unit;
    ip.unwind = switch (k) {
        .brk => .brk,
        .cont => .cont,
        else => .ret,
    };
    return x;
}

pub fn defer_(ip: *Interpreter, n: NodeId, k: Kind) Value {
    if (k == .@"defer") {
        ip.defers.push(.{ .node = ip.res().tree.arg(n, 0), .cell = Interpreter.no_cell });
        return .unit;
    }
    const x = ip.eval(ip.res().tree.arg(n, 0));
    ip.defers.push(.{ .node = n, .cell = ip.put(ip.own(x)) });
    return x;
}

pub fn branch(ip: *Interpreter, n: NodeId, k: Kind) Value {
    const r = ip.res();
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) r.tree.arg(n, 0) else n;
    const c = ip.eval(r.tree.arg(it, 0));
    if (c.ty != .bool_type) return if (c.is(.poison_type)) c else ip.fail(r.tree.arg(it, 0), .type_mismatch, ip.pool(c), .bool_type);
    if (c.bits != 0) return ip.eval(r.tree.arg(it, 1));
    return if (has_else) ip.eval(r.tree.arg(n, 1)) else .unit;
}

pub fn block(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const scoped = !ip.framed();
    if (scoped) r.h03_push_scope();
    defer if (scoped) r.h04_pop_scope();
    const mark = ip.defers.head;
    var v: Value = .unit;
    for (r.tree.manychildren(n)) |s| {
        v = ip.eval(s);
        if (ip.unwind != .none or v.is(.poison_type)) break;
    }
    const u = ip.unwind;
    while (ip.defers.head > mark) {
        ip.defers.head -= 1;
        const d = ip.defers.buf[ip.defers.head];
        ip.unwind = .none;
        if (d.cell == Interpreter.no_cell) _ = ip.eval(d.node) else calls.deinit(ip, d.node, d.cell);
    }
    ip.unwind = u;
    return v;
}

pub fn loop(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const framed = ip.framed();
    if (!framed) r.h03_push_scope();
    defer if (!framed) r.h04_pop_scope();
    const l = r.loop_parts(n);
    const pre = l.repeat != 0 and l.cond == 0;
    var seq: Value = .empty;
    var lo: Value = .empty;
    var hi: Value = .empty;
    var incl = false;
    var it: DeclPool.Index = .none;
    var iter: Index = .none;
    var recv: Value = .empty;
    if (l.seq != 0) {
        const s = l.seq;
        const sk = r.tree.kind(s);
        if (Resolver.is_range_kind(sk)) {
            const g = r.range(s);
            lo = if (g.lo != 0) ip.eval(g.lo) else .int(.u64_type, 0);
            if (g.hi != 0) hi = ip.eval(g.hi);
            incl = g.incl;
            if (!Value.is_int(lo.ty) or !(hi.is(.none) or Value.is_int(hi.ty))) return if (lo.is(.poison_type) or hi.is(.poison_type)) .poison else ip.fail(s, .not_static, 0, 0);
            lo = .fit(lo, types.elem_type(ip, ip.hint(s)));
        } else {
            const place = switch (sk) {
                .identifier, .identifier_self, .member, .array_index, .dereference, .capture => true,
                else => false,
            };
            const sp = &r.static_pool;
            const early = place and !places.named(sk) and !(framed and sp.tag(sp.pointee(sp.apply_vars(&r.abstract_pool, ip.info(.ty, s)))) == .array_type);
            const c0: ?u32 = if (early) places.cell(ip, s) orelse return .poison else null;
            const sv = if (c0) |c| ip.mem.buf[c] else ip.eval(s);
            seq = ip.deref(sv);
            if (seq.is(.poison_type)) return seq;
            if (ip.count(seq) == null) {
                const c = c0 orelse if (place) places.cell(ip, s) orelse return .poison else ip.put(sv);
                const held = ip.mem.buf[c];
                recv = if (held.is_ref()) held else .ref(r.self_ptr(ip.vtype(held)), c);
                iter = ip.vtype(ip.deref(held));
                seq = .empty;
            }
        }
        it = if (framed) ip.info(.decl, l.head) else r.h02_declare_local(if (l.variable != 0) r.name_pool.name_of(r.tree, r.src_bytes, l.variable) else .it, n, .loop_variable, .none);
    }
    const want = !framed or r.static_pool.tag(r.static_pool.apply_vars(&r.abstract_pool, ip.info(.ty, n))) == .array_type;
    const mark = ip.list.head;
    defer ip.list.head = mark;
    const total = if (seq.is(.none)) 0 else ip.count(seq).?;
    var cur = lo;
    var i: u32 = 0;
    var last = false;
    while (!last) : (i += 1) {
        if (!lo.is(.none)) {
            if (!hi.is(.none) and (if (incl) Value.less(hi, cur) else !Value.less(cur, hi))) break;
            places.bind(ip, it, cur);
            last = incl and cur.bits == hi.bits;
            cur = .int(cur.ty, cur.bits +% 1);
        } else if (!seq.is(.none)) {
            if (i >= total) break;
            places.bind(ip, it, ip.elem(seq, i));
        } else if (iter != .none) {
            const more = calls.method(ip, l.seq, iter, .has_next, recv);
            if (more.ty != .bool_type) return if (more.is(.poison_type)) more else ip.fail(l.seq, .type_mismatch, ip.pool(more), .bool_type);
            if (more.bits == 0) break;
            const x = calls.method(ip, l.seq, iter, .next, recv);
            if (x.is(.poison_type)) return x;
            places.bind(ip, it, x);
        }
        if (pre and ip.eval(l.repeat).is(.poison_type)) return .poison;
        if (l.cond != 0) {
            const c = ip.eval(l.cond);
            if (c.ty != .bool_type) return if (c.is(.poison_type)) c else ip.fail(l.cond, .type_mismatch, ip.pool(c), .bool_type);
            if (c.bits == 0) break;
        }
        const v = ip.eval(l.body);
        if (v.is(.poison_type)) return v;
        switch (ip.unwind) {
            .brk => {
                ip.unwind = .none;
                break;
            },
            .ret => return v,
            .cont => ip.unwind = .none,
            .none => if (want) ip.list.push(v),
        }
        if (!pre and l.repeat != 0 and ip.eval(l.repeat).is(.poison_type)) return .poison;
    }
    if (!want) return .unit;
    const len = ip.list.head - mark;
    var et = types.elem_type(ip, ip.hint(n));
    if (et == .none) et = types.joined(ip, ip.list.buf[mark..][0..len]);
    const at = ip.alloc(len);
    for (0..len) |j| ip.fill(at + j, ip.list.buf[mark + j], et);
    return .block(types.array_type(ip, len, et), at, len);
}

pub fn match(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const x = ip.eval(r.tree.arg(n, 0));
    const t = if (ip.framed()) ip.info(.ty, r.tree.arg(n, 0)) else x.ty;
    const v = if (x.is_ref() and r.deref(t) != t) ip.deref(x) else x;
    if (v.is(.poison_type) or ip.unwind != .none) return v;
    const scoped = !ip.framed();
    if (scoped) r.h03_push_scope();
    defer if (scoped) r.h04_pop_scope();
    if (!scoped) for (r.tree.manychildren(r.tree.arg(n, 1))) |arm| if (ip.info(.value, arm) == .bool_true) return ip.eval(r.tree.arg(arm, 1));
    for (r.tree.manychildren(r.tree.arg(n, 1))) |arm| if (matches(ip, r.tree.arg(arm, 0), v)) return ip.eval(r.tree.arg(arm, 1));
    return ip.fail(n, .non_exhaustive_match, ip.pool(v), .none);
}

// a case value is pooled, or a block of its payload fields when they hold references
pub fn case_of(ip: *Interpreter, v: Value) Index {
    const sp = &ip.res().static_pool;
    if (v.is_heap() and sp.tag(v.ty) == .variant_case_type) return v.ty;
    if (!v.is_pool() or v.is(.none)) return .none;
    return switch (sp.tag(v.index())) {
        .variant_value => sp.get(v.index()).variant_value.case,
        .variant_case_type => v.index(),
        else => .none,
    };
}

fn same(ip: *Interpreter, a: Value, b: Value) bool {
    return Value.eql(if (a.is_heap()) .pooled(ip.pool(a)) else a, if (b.is_heap()) .pooled(ip.pool(b)) else b);
}

pub fn matches(ip: *Interpreter, p: NodeId, v: Value) bool {
    const r = ip.res();
    const sp = &r.static_pool;
    const framed = ip.framed();
    switch (r.tree.kind(p)) {
        .identifier => {
            name(ip, p, v);
            return true;
        },
        .partial__match_case_pattern_or => {
            for (r.tree.manychildren(p)) |alt| if (matches(ip, alt, v)) return true;
            return false;
        },
        .partial__match_case_pattern_typecast => {
            const t = if (framed) ip.info(.ty, r.tree.arg(p, 1)) else r.h07_lower_type(ip.ctx, r.tree.arg(p, 0));
            const c = case_of(ip, v);
            const vt = ip.vtype(v);
            const ok = if (c != .none) sp.get(c).variant_case_type.variant == t or sp.tag(t) == .variant_union_type else vt == t or sp.implements(vt, t);
            if (ok) name(ip, r.tree.arg(p, 1), v);
            return ok;
        },
        .labelarrow => {
            if (!matches(ip, r.tree.arg(p, 0), v)) return false;
            label(ip, r.tree.arg(p, 1), payload(ip, v) orelse v);
            return true;
        },
        .fun_call => {
            const h = ip.hint(p);
            const target = if (h != .none) h else ip.pool(ip.eval(r.tree.arg(p, 0)));
            var rec = target;
            var fields = v;
            if (sp.tag(target) == .variant_case_type) {
                if (case_of(ip, v) != target) return false;
                rec = sp.get(target).variant_case_type.payload;
                fields = if (v.is_heap()) .block(rec, v.at(), v.len()) else if (sp.tag(v.index()) == .variant_value) .of(sp, sp.get(v.index()).variant_value.payload) else .empty;
            }
            for (r.tree.manychildren(r.tree.arg(p, 1)), 0..) |a, i| {
                const fi = r.field_of(rec, a, i) orelse return false;
                if (fi >= (ip.span(fields) orelse 0) or !matches(ip, r.arg_value(a), ip.elem(fields, @intCast(fi)))) return false;
            }
            return true;
        },
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => {
            const g = r.range(p);
            if (!Value.is_int(v.ty) or g.lo != 0 and Value.less(v, ip.eval(g.lo))) return false;
            if (g.hi == 0) return true;
            const hi = ip.eval(g.hi);
            return if (g.incl) !Value.less(hi, v) else Value.less(v, hi);
        },
        else => {
            const pv = ip.eval(p);
            if (pv.is_pool() and !pv.is(.none) and sp.tag(pv.index()) == .variant_case_type) return case_of(ip, v) == pv.index();
            return !pv.is(.poison_type) and same(ip, pv, v);
        },
    }
}

fn name(ip: *Interpreter, id: NodeId, v: Value) void {
    const r = ip.res();
    if (ip.framed()) return places.bind(ip, ip.info(.decl, id), v);
    const nm = r.name_pool.name_of(r.tree, r.src_bytes, id);
    if (nm == .underscore) return;
    const d = r.h02_declare_local(nm, id, .pattern_binder, ip.vtype(v));
    r.node_decl[id] = d;
    places.bind(ip, d, v);
}

fn label(ip: *Interpreter, l: NodeId, v: Value) void {
    const r = ip.res();
    if (r.tree.kind(l) != .partial__destructure) return name(ip, l, v);
    for (r.tree.manychildren(l), 0..) |id, i| name(ip, id, if (i < (ip.span(v) orelse 0)) ip.elem(v, @intCast(i)) else .poison);
}

fn payload(ip: *Interpreter, v: Value) ?Value {
    const sp = &ip.res().static_pool;
    if (v.is_heap() and sp.tag(v.ty) == .variant_case_type) return if (v.len() == 1) ip.mem.buf[v.at()] else .block(sp.get(v.ty).variant_case_type.payload, v.at(), v.len());
    if (!v.is_pool() or v.is(.none) or sp.tag(v.index()) != .variant_value) return null;
    const pv = sp.get(v.index()).variant_value.payload;
    if (pv == .none) return null;
    const elems = sp.get(pv).aggregate.elems;
    return .of(sp, if (elems.len == 1) elems[0] else pv);
}

pub fn unwrap(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const k = r.tree.kind(n);
    if (!ip.framed() and (k == .labelarrow or k == .selftag_arrow)) return ip.fail(n, .not_static, 0, 0);
    const v = ip.eval(r.tree.arg(n, 0));
    if (v.is(.poison_type) or ip.unwind != .none) return v;
    if (k == .labelarrow) {
        label(ip, r.tree.arg(n, 1), v);
        return v;
    }
    const sp = &r.static_pool;
    const c = case_of(ip, v);
    const p = if (c == .none or sp.tag(ip.hint(r.tree.arg(n, 0))) == .variant_case_type or sp.payload_case(sp.get(c).variant_case_type.variant) == c) payload(ip, v) else null;
    return switch (k) {
        .selftag_arrow => blk: {
            if (p) |x| label(ip, r.tree.arg(n, 1), x);
            break :blk .boolean(p != null);
        },
        .selftag_unwrap_fallback => p orelse ip.eval(r.tree.arg(n, 1)),
        else => p orelse ip.fail(n, .static_eval_failed, ip.pool(v), 0),
    };
}
