const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

// calls: functions and methods invoked, closures, values built by constructors and `with`
const Calls = @This();

pub fn interp(self: *Calls) *Interpreter {
    return @alignCast(@fieldParentPtr("calls", self));
}

pub fn member(self: *Calls, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const parent = r.tree.arg(n, 0);
    const name = r.name_pool.name_of(r.tree.arg(n, 1));
    if (name == .len and !ip.framed()) {
        const t = sp.pointee(sp.apply_vars(&r.abstract_pool, r.exprs.infer(ip.ctx, parent, .none)));
        if (sp.static_len(t)) |len| return .int(.u64_type, len);
    }
    const pv = ip.deref(ip.eval(parent));
    if (pv.is(.poison_type)) return pv;
    if (name == .len) if (ip.count(pv)) |c| return .int(.u64_type, c);
    if (name == .tag) {
        const c = ip.patterns.case_of(pv);
        if (c == .none) return ip.fail(n, .not_static, 0, 0);
        const st = sp.deref(&r.abstract_pool, ip.checked(parent));
        const v = sp.get(c).variant_case_type;
        return .int(sp.tag_type_of(st), sp.get(v.tag).int.bits + if (sp.tag(st) == .variant_union_type) sp.union_offset(st, v.variant) else 0);
    }
    const pt = ip.vtype(pv);
    const fields = if (pv.is_pool() and sp.tag(pt) == .variant_case_type and sp.tag(pv.index()) == .variant_value) Value.of(sp, sp.get(pv.index()).variant_value.payload) else pv;
    if (pv.is_heap() or sp.tag(pt) == .record_type or sp.tag(pt) == .variant_case_type) switch (sp.lookup_member(pt, name)) {
        .field => |f| return ip.elem(fields, f.index),
        else => {},
    };
    if (!pv.is_pool() or !sp.get_tag_prop(pv.index()).is_type) return ip.fail(n, .not_static, 0, 0);
    return switch (sp.lookup_member(pv.index(), name)) {
        .case => |c| .pooled(c),
        .method => |m| blk: {
            r.decls.ensure_signature(m);
            break :blk .of(sp, r.decl_pool.get_value(m));
        },
        else => ip.fail(n, .unknown_member, name, pv.index()),
    };
}

pub fn call(self: *Calls, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const callee = r.tree.arg(n, 0);
    const args = r.tree.manychildren(r.tree.arg(n, 1));
    const d = ip.info(.decl, n);
    const cd = ip.info(.decl, callee);
    if (d != .none and r.decl_pool.get_kind(d).is_fn() and (cd == .none or r.decl_pool.get_kind(cd) != .static_function)) {
        if (r.decl_pool.self_off(r.decls.real(d)) == 0 or r.tree.kind(callee) != .member or sp.tag(ip.info(.ty, r.tree.arg(callee, 0))) == .meta_type) return self.invoke(n, d, args, .empty, .empty);
        const c = ip.variables.cell(r.tree.arg(callee, 0)) orelse return .poison;
        return self.invoke(n, d, args, if (ip.mem.buf[c].is_ref()) ip.mem.buf[c] else .ref(sp.ptr_of(ip.vtype(ip.mem.buf[c]), true), c), .empty);
    }
    if (d == .none and r.tree.kind(callee) == .member) switch (r.calls.builtin_of(callee, ip.info(.ty, r.tree.arg(callee, 0)), ip.info(.ty, n))) {
        .builtin_init => return ip.zero(ip.info(.ty, n)),
        .builtin_deinit => return .unit,
        else => {},
    };
    const cv = ip.eval(callee);
    if (cv.is_heap() and sp.tag(cv.ty) == .function_type) return self.invoke(n, sp.get(ip.mem.buf[cv.at()].index()).function, args, .empty, cv);
    if (!cv.is_pool() or cv.is(.poison_type)) return if (cv.is(.poison_type)) cv else ip.fail(n, .not_static, 0, 0);
    const c = cv.index();
    if (!ip.framed() and ip.ctx.interpreted and sp.tag(c) == .generic and sp.get(c).static_fun.decl == ip.ctx.decl) return .poison;
    return switch (sp.tag(c)) {
        .record_type, .variant_case_type => self.construct(c, args),
        .function_value => self.invoke(n, sp.get(c).function, args, .empty, .empty),
        .generic => blk: {
            const g = sp.get(c).static_fun.decl;
            const params = sp.get(r.decl_pool.get_ty(g)).function_type.params;
            if (args.len != params.len) break :blk ip.fail(n, .wrong_arity, args.len, params.len);
            const mark = ip.ids.head;
            defer ip.ids.head = mark;
            for (args, params) |a, p| {
                const x = ip.eval(r.tree.arg_value(a));
                if (x.is(.poison_type)) break :blk x;
                if (ip.escapes(x)) break :blk ip.fail(r.tree.arg_value(a), .not_static, 0, 0);
                const i = ip.pool(x);
                const ok = if (sp.tag(p) == .meta_type) p == .type_type and sp.get_tag_prop(i).is_type or sp.type_of(i) == p else if (sp.get_tag_prop(p).is_integer or sp.get_tag_prop(p).is_float) sp.fits(i, p) else p != .bool_type and sp.tag(p) != .record_type or sp.type_of(i) == p;
                if (!ok) break :blk ip.fail(r.tree.arg_value(a), .type_mismatch, sp.type_of(i), p);
                ip.ids.push(r.statics.retype(i, p));
            }
            const tuple = sp.intern(.{ .aggregate = .{ .ty = .none, .elems = ip.ids.buf[mark..ip.ids.head] } });
            break :blk .of(sp, r.generics.instantiate(g, tuple));
        },
        else => ip.fail(n, .not_static, 0, 0),
    };
}

pub fn method(self: *Calls, n: NodeId, t: Index, name: NamePool.Index, selfvalue: Value) Value {
    const ip = self.interp();
    return switch (ip.res().static_pool.lookup_member(t, name)) {
        .method => |m| self.invoke(n, m, &.{}, selfvalue, .empty),
        else => ip.fail(n, .not_static, 0, 0),
    };
}

pub fn deinit_cell(self: *Calls, n: NodeId, c: u32) void {
    const ip = self.interp();
    const r = ip.res();
    const t = ip.vtype(ip.mem.buf[c]);
    switch (r.static_pool.lookup_member(t, .deinit)) {
        .method => |m| _ = self.invoke(n, m, &.{}, .ref(r.static_pool.ptr_of(t, true), c), .empty),
        else => {},
    }
}

fn invoke(self: *Calls, n: NodeId, d0: DeclPool.Index, all: []const NodeId, self0: Value, env: Value) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    if (ip.frames.head > Interpreter.max_depth) return ip.fail(ip.origin(n), .static_eval_failed, 0, 0);
    const mark = ip.list.head;
    defer ip.list.head = mark;
    for (all) |a| {
        const x = ip.eval(r.tree.arg_value(a));
        if (x.is(.poison_type) or ip.unwind != .none) return x;
        ip.list.push(x);
    }
    var d = r.decls.real(d0);
    var selfvalue0 = self0;
    var args = all;
    var base = mark;
    if (selfvalue0.is(.none) and r.decl_pool.self_off(d) == 1) {
        if (args.len == 0) return ip.fail(n, .wrong_arity, 0, 1);
        selfvalue0 = ip.list.buf[mark];
        args = args[1..];
        base += 1;
    }
    if (r.decl_pool.get_kind(d) == .trait_member and selfvalue0.is_ref()) d = switch (sp.lookup_member(ip.vtype(ip.mem.buf[selfvalue0.at()]), r.decl_pool.get_name(d))) {
        .method => |m| m,
        else => d,
    };
    r.decls.ensure_signature(d);
    if (sp.length_generic(&r.abstract_pool, r.decl_pool.get_ty(d))) d = self.realize(n, d, args, base) orelse return .poison;
    var c = d;
    while (c != .none) : (c = r.decl_pool.get_next_overload(c)) {
        if (c != d and !r.calls.same_params(c, d)) continue;
        if (self.attempt(n, r.decls.real(c), args, base, selfvalue0, env)) |v| return v;
    }
    return ip.fail(n, .no_matching_overload, args.len, 0);
}

fn realize(self: *Calls, n: NodeId, d: DeclPool.Index, args: []const NodeId, base: u32) ?DeclPool.Index {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const pnodes = r.tree.params_of(r.decls.value_node(d));
    const map = r.scratch(u32, args.len);
    if (!r.calls.bind_args(pnodes, args, map, false)) return null;
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    for (0..pnodes.len) |j| {
        const p = sp.get(r.decl_pool.get_ty(d)).function_type.params[j + r.decl_pool.self_off(d)];
        if (!sp.generic_slot(p)) continue;
        for (0..args.len) |i| if (map[i] == j) {
            const v = ip.list.buf[base + i];
            const x = if (sp.templated(p) != .none) ip.vtype(ip.deref(v)) else if (sp.tag(p) == .meta_type) ip.pool(v) else sp.intern(.{ .int = .{ .ty = .u64_type, .bits = ip.count(ip.deref(v)) orelse return null } });
            ip.ids.push(x);
        };
    }
    const f = r.generics.instantiate(d, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = ip.ids.buf[mark..ip.ids.head] } }));
    if (sp.tag(f) != .function_value) {
        _ = ip.fail(n, .not_static, 0, 0);
        return null;
    }
    return sp.get(f).function;
}

fn attempt(self: *Calls, n: NodeId, d: DeclPool.Index, args: []const NodeId, base: u32, valueself: Value, env: Value) ?Value {
    const ip = self.interp();
    const r = ip.res();
    r.decls.ensure_signature(d);
    r.decls.check_body(d);
    const body = r.bodies.get(d) orelse return ip.fail(n, .not_static, 0, 0);
    const v = r.decls.value_node(d);
    if (r.decl_pool.get_state(d) == .failed) return Value.poison;
    const pnodes = r.tree.params_of(v);
    const map = r.scratch(u32, args.len);
    if (!r.calls.bind_args(pnodes, args, map, false)) return ip.fail(n, .wrong_arity, args.len, pnodes.len);
    const caller = ip.frames.buf[ip.frames.head - 1].body.decl;
    const unchecked = caller != .none and r.decl_pool.get_kind(caller) == .static_function;
    ip.enter(body);
    ip.frames.buf[ip.frames.head - 1].env = env;
    var keep = false;
    defer ip.leave(keep);
    if (r.decl_pool.self_off(d) == 1) ip.variables.bind(@enumFromInt(body.first), valueself);
    for (0..args.len) |i| {
        _ = ip.variables.store(pnodes[map[i]], ip.info(.decl, pnodes[map[i]]), ip.list.buf[base + i]);
    }
    for (pnodes, 0..) |pn, j| if (std.mem.indexOfScalar(u32, map, @intCast(j)) == null) {
        _ = ip.variables.store(pn, ip.info(.decl, pn), ip.eval(ParseTree.Param.from_node(r.tree, pn).default));
    };
    for (pnodes) |pn| {
        const p = ParseTree.Param.from_node(r.tree, pn);
        if (p.where == 0) continue;
        const w = ip.eval(p.where);
        if (w.ty != .bool_type) return Value.poison;
        if (w.bits != 0) continue;
        if (p.stc) return if (unchecked) ip.fail(n, .stcwhere_violated, d, .none) else Value.poison;
        if (p.@"else" == 0) return null;
        const e = ip.eval(p.@"else");
        if (ip.unwind == .ret) return ip.result(e);
        if (r.tree.kind(p.@"else") != .assign) _ = ip.variables.store(pn, ip.info(.decl, pn), e);
    }
    const out = ip.coerce(ip.result(ip.eval(r.tree.arg(v, 1))), r.types.sig(d).ret);
    keep = out.is_boxed();
    return out;
}

pub fn construct(self: *Calls, target: Index, args: []const NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const is_case = sp.tag(target) == .variant_case_type;
    const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
    if (rec == .none) return .pooled(target);
    const fields = r.types.fields_of(rec);
    const len: u32 = @intCast(fields.len);
    const at = ip.alloc(len);
    if (self.fill_args(rec, at, args)) |x| return x;
    if (!self.complete(rec, at)) return .poison;
    const agg: Value = .block(rec, at, len);
    if (!is_case) return agg;
    if (ip.escapes(agg)) return .block(target, at, len);
    return .pooled(sp.intern(.{ .variant_value = .{ .case = target, .payload = ip.pool(agg) } }));
}

pub fn with(self: *Calls, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const base = ip.deref(ip.eval(r.tree.arg(n, 0)));
    if (base.is(.poison_type)) return base;
    const t = ip.vtype(base);
    const len = ip.span(base) orelse return ip.fail(n, .not_static, 0, 0);
    if (sp.tag(t) != .record_type) return ip.fail(n, .not_static, 0, 0);
    const at = ip.alloc(len);
    for (0..len) |i| {
        const x = ip.own(ip.elem(base, @intCast(i)));
        ip.mem.buf[at + i] = x;
    }
    if (self.fill_args(t, at, r.tree.manychildren(r.tree.arg(n, 1)))) |x| return x;
    return if (self.complete(t, at)) .block(t, at, len) else .poison;
}

// the arguments of a constructor or `with` written into the fields of `rec` at `at`, a failure is returned
fn fill_args(self: *Calls, rec: Index, at: u32, args: []const NodeId) ?Value {
    const ip = self.interp();
    const r = ip.res();
    for (args, 0..) |a, i| {
        const fi = r.calls.field_of(rec, a, i) orelse return ip.fail(a, .unknown_named_argument, r.name_pool.name_of(r.tree.arg_name(a)), rec);
        const x = ip.eval(r.tree.arg_value(a));
        if (x.is(.poison_type)) return x;
        ip.fill(at + fi, x, r.static_pool.field_type(rec, fi));
    }
    return null;
}

// the defaults and `where .. else` of the fields of a value being built, in the frame of the type where the fields are the locals
fn complete(self: *Calls, rec: Index, at: u32) bool {
    const ip = self.interp();
    const r = ip.res();
    const fields = r.types.fields_of(rec);
    var framed = false;
    for (fields, 0..) |f, i| framed = framed or ParseTree.Param.from_node(r.tree, f).@"else" != 0 or ParseTree.Param.from_node(r.tree, f).default != 0 and ip.mem.buf[at + i].is(.none);
    if (!framed) {
        for (0..fields.len) |i| if (ip.mem.buf[at + i].is(.none)) ip.fill(at + i, ip.zero(r.static_pool.field_type(rec, i)), r.static_pool.field_type(rec, i));
        return true;
    }
    const decl = r.static_pool.get(rec).custom_type.decl;
    const body = r.bodies.get(decl) orelse {
        _ = ip.fail(r.decl_pool.get_node(decl), .not_static, 0, 0);
        return false;
    };
    ip.enter(body);
    defer ip.leave(false);
    const base = ip.top().base;
    for (0..fields.len) |i| ip.mem.buf[base + i] = ip.mem.buf[at + i];
    for (fields, 0..) |f, i| if (ip.mem.buf[base + i].is(.none)) {
        const d = ParseTree.Param.from_node(r.tree, f).default;
        const x = if (d != 0) ip.eval(d) else ip.zero(r.static_pool.field_type(rec, i));
        if (x.is(.poison_type)) return false;
        ip.fill(base + i, x, r.static_pool.field_type(rec, i));
    };
    for (fields, 0..) |f, i| {
        const p = ParseTree.Param.from_node(r.tree, f);
        if (p.where == 0 or p.@"else" == 0) continue;
        const w = ip.eval(p.where);
        if (w.ty != .bool_type) return false;
        if (w.bits != 0) continue;
        const e = ip.eval(p.@"else");
        if (e.is(.poison_type)) return false;
        if (r.tree.kind(p.@"else") != .assign) ip.fill(base + i, e, r.static_pool.field_type(rec, i));
    }
    for (0..fields.len) |i| ip.fill(at + i, ip.mem.buf[base + i], r.static_pool.field_type(rec, i));
    return true;
}

// a function as a value: with captures a block of the function and its environment, like the lowerer's closure
pub fn closure(self: *Calls, d: DeclPool.Index) Value {
    const ip = self.interp();
    const r = ip.res();
    const f: Value = .of(&r.static_pool, r.decl_pool.get_value(d));
    const caps = ip.res().bodies.captures(&ip.res().decl_pool, d);
    if (caps.len == 0) return f;
    const at = ip.alloc(@intCast(caps.len + 1));
    ip.mem.buf[at] = f;
    for (caps, 1..) |c, i| {
        const s = ip.variables.slot(c);
        const x: Value = if (s != null and ip.res().decls.by_ref(c)) .ref(r.static_pool.ptr_of(r.decl_pool.get_ty(c), true), s.?) else ip.own(ip.variables.peek(c));
        ip.mem.buf[at + i] = x;
    }
    return .block(r.decl_pool.get_ty(d), at, @intCast(caps.len + 1));
}

// the cell of a capture of the closure a frame runs in
pub fn captured(self: *Calls, f: Interpreter.Frame, d: DeclPool.Index) ?u32 {
    const ip = self.interp();
    if (!f.env.is_heap() or f.body.decl == .none) return null;
    const k = std.mem.indexOfScalar(DeclPool.Index, ip.res().bodies.captures(&ip.res().decl_pool, f.body.decl), d) orelse return null;
    const c = f.env.at() + 1 + @as(u32, @intCast(k));
    return if (ip.mem.buf[c].is_ref() and ip.res().decls.by_ref(d)) ip.mem.buf[c].at() else c;
}
