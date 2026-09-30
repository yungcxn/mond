const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const control = @import("control.zig");
const places = @import("places.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Decl = Resolver.Decl;

pub fn member(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const parent = r.arg(n, 0);
    const name = r.name_of(r.arg(n, 1));
    if (name == .len and !ip.framed()) {
        const t = sp.pointee(sp.apply_vars(&r.abstract_pool, r.h09_check_expr(ip.ctx, parent, .none)));
        if (sp.get(t) == .array_type and sp.tag(sp.get(t).array_type.len) == .int_value) return .of(sp, sp.get(t).array_type.len);
    }
    const pv = ip.deref(ip.eval(parent));
    if (pv.is(.poison_type)) return pv;
    if (name == .len) if (ip.count(pv)) |c| return .int(.u64_type, c);
    if (name == .tag) {
        const c = control.case_of(ip, pv);
        if (c == .none) return ip.fail(n, .not_static, 0, 0);
        const st = r.deref(ip.checked(parent));
        const v = sp.get(c).variant_case_type;
        return .int(sp.tag_type_of(st), sp.get(v.tag).int.bits + if (sp.tag(st) == .variant_union_type) sp.union_offset(st, v.variant) else 0);
    }
    const pt = ip.vtype(pv);
    if (pv.is_heap() or sp.tag(pt) == .record_type) switch (sp.lookup_member(pt, name)) {
        .field => |f| return ip.elem(pv, f.index),
        else => {},
    };
    if (!pv.is_pool() or !sp.class(pv.index()).is_type) return ip.fail(n, .not_static, 0, 0);
    return switch (sp.lookup_member(pv.index(), name)) {
        .case => |c| .pooled(c),
        .method => |m| blk: {
            r.h05_ensure_signature(m);
            break :blk .of(sp, r.dp(.value, m).*);
        },
        else => ip.fail(n, .unknown_member, name, pv.index()),
    };
}

pub fn call(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const callee = r.arg(n, 0);
    const args = r.kids(r.arg(n, 1));
    const d = ip.info(.decl, n);
    const cd = ip.info(.decl, callee);
    if (d != .none and Resolver.is_fn(r.dp(.kind, d).*) and (cd == .none or r.dp(.kind, cd).* != .static_function)) {
        if (r.self_off(r.real(d)) == 0 or r.nk(callee) != .member or sp.tag(ip.info(.ty, r.arg(callee, 0))) == .meta_type) return invoke(ip, n, d, args, .empty);
        const c = places.cell(ip, r.arg(callee, 0)) orelse return .poison;
        return invoke(ip, n, d, args, if (ip.mem.buf[c].is_ref()) ip.mem.buf[c] else .ref(r.self_ptr(ip.vtype(ip.mem.buf[c])), c));
    }
    const cv = ip.eval(callee);
    if (!cv.is_pool() or cv.is(.poison_type)) return if (cv.is(.poison_type)) cv else ip.fail(n, .not_static, 0, 0);
    const c = cv.index();
    if (!ip.framed() and ip.ctx.interpreted and sp.tag(c) == .generic and sp.get(c).static_fun.decl == ip.ctx.decl) return .poison;
    return switch (sp.tag(c)) {
        .record_type, .variant_case_type => construct(ip, c, args),
        .function_value => invoke(ip, n, sp.get(c).function, args, .empty),
        .generic => blk: {
            const g = sp.get(c).static_fun.decl;
            const want = sp.get(r.dp(.ty, g).*).function_type.params.len;
            if (args.len != want) break :blk ip.fail(n, .wrong_arity, args.len, want);
            const mark = ip.ids.head;
            defer ip.ids.head = mark;
            for (args) |a| {
                const x = ip.eval(r.arg_value(a));
                if (x.is(.poison_type)) break :blk x;
                const i = ip.pool(x);
                ip.ids.push(i);
            }
            const tuple = sp.intern(.{ .aggregate = .{ .ty = .none, .elems = ip.ids.buf[mark..ip.ids.head] } });
            break :blk .of(sp, r.h20_instantiate(g, tuple));
        },
        else => ip.fail(n, .not_static, 0, 0),
    };
}

pub fn method(ip: *Interpreter, n: NodeId, t: Index, name: NamePool.Index, self: Value) Value {
    return switch (ip.res().static_pool.lookup_member(t, name)) {
        .method => |m| invoke(ip, n, m, &.{}, self),
        else => ip.fail(n, .not_static, 0, 0),
    };
}

pub fn deinit(ip: *Interpreter, n: NodeId, c: u32) void {
    const r = ip.res();
    const t = ip.vtype(ip.mem.buf[c]);
    switch (r.static_pool.lookup_member(t, .deinit)) {
        .method => |m| _ = invoke(ip, n, m, &.{}, .ref(r.self_ptr(t), c)),
        else => {},
    }
}

fn invoke(ip: *Interpreter, n: NodeId, d0: Decl.Index, all: []const NodeId, self0: Value) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    if (ip.frames.head > Interpreter.max_depth) return ip.fail(n, .static_eval_failed, 0, 0);
    const mark = ip.list.head;
    defer ip.list.head = mark;
    for (all) |a| {
        const x = ip.eval(r.arg_value(a));
        if (x.is(.poison_type) or ip.unwind != .none) return x;
        ip.list.push(x);
    }
    var d = r.real(d0);
    var self = self0;
    var args = all;
    var base = mark;
    if (self.is(.none) and r.self_off(d) == 1) {
        if (args.len == 0) return ip.fail(n, .wrong_arity, 0, 1);
        self = ip.list.buf[mark];
        args = args[1..];
        base += 1;
    }
    if (r.dp(.kind, d).* == .trait_member and self.is_ref()) d = switch (sp.lookup_member(ip.vtype(ip.mem.buf[self.at()]), r.dp(.name, d).*)) {
        .method => |m| m,
        else => d,
    };
    r.h05_ensure_signature(d);
    if (r.length_generic(r.dp(.ty, d).*)) d = realize(ip, n, d, args, base) orelse return .poison;
    const ty = r.dp(.ty, d).*;
    var c = d;
    while (c != .none) : (c = r.dp(.next_overload, c).*) {
        if (c != d and !r.same_params(r.dp(.ty, r.real(c)).*, ty)) continue;
        if (attempt(ip, n, r.real(c), args, base, self)) |v| return v;
    }
    return ip.fail(n, .no_matching_overload, args.len, 0);
}

fn realize(ip: *Interpreter, n: NodeId, d: Decl.Index, args: []const NodeId, base: u32) ?Decl.Index {
    const r = ip.res();
    const sp = &r.static_pool;
    const pnodes = r.params_of(r.value_node(d));
    var map: [64]u32 = undefined;
    if (!r.bind_args(pnodes, args, &map, false)) return null;
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    for (0..pnodes.len) |j| {
        const p = sp.get(r.dp(.ty, d).*).function_type.params[j + r.self_off(d)];
        if (!r.generic_slot(p)) continue;
        for (0..args.len) |i| if (map[i] == j) {
            const v = ip.list.buf[base + i];
            const x = if (r.templated(p) != .none) ip.vtype(ip.deref(v)) else if (sp.tag(p) == .meta_type) ip.pool(v) else sp.intern(.{ .int = .{ .ty = .u64_type, .bits = ip.count(ip.deref(v)) orelse return null } });
            ip.ids.push(x);
        };
    }
    const f = r.h20_instantiate(d, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = ip.ids.buf[mark..ip.ids.head] } }));
    if (sp.tag(f) != .function_value) {
        _ = ip.fail(n, .not_static, 0, 0);
        return null;
    }
    return sp.get(f).function;
}

fn attempt(ip: *Interpreter, n: NodeId, d: Decl.Index, args: []const NodeId, base: u32, self: Value) ?Value {
    const r = ip.res();
    r.h05_ensure_signature(d);
    r.h06_check_body(d);
    const bi = r.body_of.get(d) orelse return ip.fail(n, .not_static, 0, 0);
    const v = r.value_node(d);
    if (r.dp(.state, d).* == .failed) return Value.poison;
    const pnodes = r.params_of(v);
    var map: [64]u32 = undefined;
    if (!r.bind_args(pnodes, args, &map, false)) return ip.fail(n, .wrong_arity, args.len, pnodes.len);
    const body = r.bodies.get(bi).?;
    const caller = ip.frames.buf[ip.frames.head - 1].body.decl;
    const unchecked = caller != .none and r.dp(.kind, caller).* == .static_function;
    ip.enter(body);
    var keep = false;
    defer ip.leave(keep);
    if (r.self_off(d) == 1) places.bind(ip, @enumFromInt(body.first), self);
    var bound: u64 = 0;
    for (0..args.len) |i| {
        bound |= @as(u64, 1) << @intCast(map[i]);
        _ = places.store(ip, pnodes[map[i]], ip.info(.decl, pnodes[map[i]]), ip.list.buf[base + i]);
    }
    for (pnodes, 0..) |pn, j| if (bound >> @intCast(j) & 1 == 0) {
        _ = places.store(ip, pn, ip.info(.decl, pn), ip.eval(r.param(pn).default));
    };
    for (pnodes) |pn| {
        const p = r.param(pn);
        if (p.where == 0) continue;
        const w = ip.eval(p.where);
        if (w.ty != .bool_type) return Value.poison;
        if (w.bits != 0) continue;
        if (p.stc) return if (unchecked) ip.fail(n, .stcwhere_violated, d, .none) else Value.poison;
        if (p.@"else" == 0) return null;
        const e = ip.eval(p.@"else");
        if (ip.unwind == .ret) return ip.result(e);
        if (r.nk(p.@"else") != .assign) _ = places.store(ip, pn, ip.info(.decl, pn), e);
    }
    const out = ip.result(ip.eval(r.arg(v, 1)));
    keep = out.is_boxed();
    return out;
}

pub fn construct(ip: *Interpreter, target: Index, args: []const NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const is_case = sp.tag(target) == .variant_case_type;
    const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
    if (rec == .none) return .pooled(target);
    const fields = r.fields_of(rec);
    const len: u32 = @intCast(fields.len);
    const at = ip.alloc(len);
    for (args, 0..) |a, i| {
        const fi = r.field_of(rec, a, i) orelse return ip.fail(a, .unknown_named_argument, r.name_of(r.arg(a, 0)), rec);
        const x = ip.eval(r.arg_value(a));
        if (x.is(.poison_type)) return x;
        ip.fill(at + fi, x, sp.get(rec).custom_type.field_types[fi]);
    }
    for (fields, 0..) |f, i| if (ip.mem.buf[at + i].is(.none)) {
        const t = sp.get(rec).custom_type.field_types[i];
        const dflt = r.param(f).default;
        ip.fill(at + i, if (dflt != 0) ip.detached(dflt) else ip.zero(t), t);
    };
    if (!guard(ip, rec, at)) return .poison;
    const agg: Value = .block(rec, at, len);
    if (!is_case) return agg;
    if (ip.escapes(agg) and args.len > 0) return ip.fail(args[0], .not_static, 0, 0);
    return .pooled(sp.intern(.{ .variant_value = .{ .case = target, .payload = ip.pool(agg) } }));
}

pub fn with(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    const base = ip.deref(ip.eval(r.arg(n, 0)));
    if (base.is(.poison_type)) return base;
    const t = ip.vtype(base);
    const len = ip.span(base) orelse return ip.fail(n, .not_static, 0, 0);
    if (sp.tag(t) != .record_type) return ip.fail(n, .not_static, 0, 0);
    const at = ip.alloc(len);
    for (0..len) |i| {
        const x = ip.own(ip.elem(base, @intCast(i)));
        ip.mem.buf[at + i] = x;
    }
    for (r.kids(r.arg(n, 1)), 0..) |a, i| {
        const fi = r.field_of(t, a, i) orelse return ip.fail(a, .unknown_named_argument, r.name_of(r.arg(a, 0)), t);
        const x = ip.eval(r.arg_value(a));
        if (x.is(.poison_type)) return x;
        ip.fill(at + fi, x, sp.get(t).custom_type.field_types[fi]);
    }
    return if (guard(ip, t, at)) .block(t, at, len) else .poison;
}

// a field's `where .. else` repairs the value being built, the fields are the locals of the type's frame
fn guard(ip: *Interpreter, rec: Index, at: u32) bool {
    const r = ip.res();
    const fields = r.fields_of(rec);
    for (fields) |f| {
        if (r.param(f).@"else" != 0) break;
    } else return true;
    const types = r.static_pool.get(rec).custom_type.field_types;
    ip.enter(r.bodies.get(r.body_of.get(r.static_pool.get(rec).custom_type.decl) orelse return true).?);
    defer ip.leave(false);
    const base = ip.top().base;
    for (0..fields.len) |i| ip.mem.buf[base + i] = ip.mem.buf[at + i];
    for (fields, 0..) |f, i| {
        const p = r.param(f);
        if (p.where == 0 or p.@"else" == 0) continue;
        const w = ip.eval(p.where);
        if (w.ty != .bool_type) return false;
        if (w.bits != 0) continue;
        const e = ip.eval(p.@"else");
        if (e.is(.poison_type)) return false;
        if (r.nk(p.@"else") != .assign) ip.fill(base + i, e, types[i]);
    }
    for (0..fields.len) |i| ip.fill(at + i, ip.mem.buf[base + i], types[i]);
    return true;
}
