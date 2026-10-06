const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const syntax = @import("../syntax.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const control = @import("control.zig");
const calls = @import("../checker/calls.zig");
const places = @import("places.zig");
const decls = @import("../checker/decls.zig");
const exprs = @import("../checker/exprs.zig");
const types = @import("../checker/types.zig");
const generics = @import("../checker/generics.zig");
const statics = @import("../checker/statics.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

pub fn member(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const parent = r.tree.arg(n, 0);
    const name = r.name_pool.name_of(r.tree, r.src_bytes, r.tree.arg(n, 1));
    if (name == .len and !self.framed()) {
        const t = sp.pointee(sp.apply_vars(&r.abstract_pool, exprs.h09_check_expr(r, self.ctx, parent, .none)));
        if (sp.get(t) == .array_type and sp.tag(sp.get(t).array_type.len) == .int_value) return .of(sp, sp.get(t).array_type.len);
    }
    const pv = self.deref(self.eval(parent));
    if (pv.is(.poison_type)) return pv;
    if (name == .len) if (self.count(pv)) |c| return .int(.u64_type, c);
    if (name == .tag) {
        const c = control.case_of(self, pv);
        if (c == .none) return self.fail(n, .not_static, 0, 0);
        const st = sp.deref(&r.abstract_pool, self.checked(parent));
        const v = sp.get(c).variant_case_type;
        return .int(sp.tag_type_of(st), sp.get(v.tag).int.bits + if (sp.tag(st) == .variant_union_type) sp.union_offset(st, v.variant) else 0);
    }
    const pt = self.vtype(pv);
    const fields = if (pv.is_pool() and sp.tag(pt) == .variant_case_type and sp.tag(pv.index()) == .variant_value) Value.of(sp, sp.get(pv.index()).variant_value.payload) else pv;
    if (pv.is_heap() or sp.tag(pt) == .record_type or sp.tag(pt) == .variant_case_type) switch (sp.lookup_member(pt, name)) {
        .field => |f| return self.elem(fields, f.index),
        else => {},
    };
    if (!pv.is_pool() or !sp.get_tag_prop(pv.index()).is_type) return self.fail(n, .not_static, 0, 0);
    return switch (sp.lookup_member(pv.index(), name)) {
        .case => |c| .pooled(c),
        .method => |m| blk: {
            decls.h05_ensure_signature(r, m);
            break :blk .of(sp, r.decl_pool.values()[@intFromEnum(m)]);
        },
        else => self.fail(n, .unknown_member, name, pv.index()),
    };
}

pub fn call(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const callee = r.tree.arg(n, 0);
    const args = r.tree.manychildren(r.tree.arg(n, 1));
    const d = self.info(.decl, n);
    const cd = self.info(.decl, callee);
    if (d != .none and r.decl_pool.kinds()[@intFromEnum(d)].is_fn() and (cd == .none or r.decl_pool.kinds()[@intFromEnum(cd)] != .static_function)) {
        if (r.decl_pool.self_off(decls.real(r, d)) == 0 or r.tree.kind(callee) != .member or sp.tag(self.info(.ty, r.tree.arg(callee, 0))) == .meta_type) return invoke(self, n, d, args, .empty, .empty);
        const c = places.cell(self, r.tree.arg(callee, 0)) orelse return .poison;
        return invoke(self, n, d, args, if (self.mem.buf[c].is_ref()) self.mem.buf[c] else .ref(sp.ptr_mut(self.vtype(self.mem.buf[c])), c), .empty);
    }
    if (d == .none and r.tree.kind(callee) == .member) switch (calls.builtin_of(r, callee, self.hint(r.tree.arg(callee, 0)), self.hint(n))) {
        .builtin_init => return self.zero(self.hint(n)),
        .builtin_deinit => return .unit,
        else => {},
    };
    const cv = self.eval(callee);
    if (cv.is_heap() and sp.tag(cv.ty) == .function_type) return invoke(self, n, sp.get(self.mem.buf[cv.at()].index()).function, args, .empty, cv);
    if (!cv.is_pool() or cv.is(.poison_type)) return if (cv.is(.poison_type)) cv else self.fail(n, .not_static, 0, 0);
    const c = cv.index();
    if (!self.framed() and self.ctx.interpreted and sp.tag(c) == .generic and sp.get(c).static_fun.decl == self.ctx.decl) return .poison;
    return switch (sp.tag(c)) {
        .record_type, .variant_case_type => construct(self, c, args),
        .function_value => invoke(self, n, sp.get(c).function, args, .empty, .empty),
        .generic => blk: {
            const g = sp.get(c).static_fun.decl;
            const params = sp.get(r.decl_pool.tys()[@intFromEnum(g)]).function_type.params;
            if (args.len != params.len) break :blk self.fail(n, .wrong_arity, args.len, params.len);
            const mark = self.ids.head;
            defer self.ids.head = mark;
            for (args, params) |a, p| {
                const x = self.eval(syntax.arg_value(r.tree, a));
                if (x.is(.poison_type)) break :blk x;
                if (self.escapes(x)) break :blk self.fail(syntax.arg_value(r.tree, a), .not_static, 0, 0);
                const i = self.pool(x);
                const ok = if (sp.tag(p) == .meta_type) p == .type_type and sp.get_tag_prop(i).is_type or sp.type_of(i) == p else if (sp.get_tag_prop(p).is_integer or sp.get_tag_prop(p).is_float) sp.fits(i, p) else p != .bool_type and sp.tag(p) != .record_type or sp.type_of(i) == p;
                if (!ok) break :blk self.fail(syntax.arg_value(r.tree, a), .type_mismatch, sp.type_of(i), p);
                self.ids.push(statics.retype(r, i, p));
            }
            const tuple = sp.intern(.{ .aggregate = .{ .ty = .none, .elems = self.ids.buf[mark..self.ids.head] } });
            break :blk .of(sp, generics.h20_instantiate(r, g, tuple));
        },
        else => self.fail(n, .not_static, 0, 0),
    };
}

pub fn method(self: *Interpreter, n: NodeId, t: Index, name: NamePool.Index, selfvalue: Value) Value {
    return switch (self.res().static_pool.lookup_member(t, name)) {
        .method => |m| invoke(self, n, m, &.{}, selfvalue, .empty),
        else => self.fail(n, .not_static, 0, 0),
    };
}

pub fn deinit(self: *Interpreter, n: NodeId, c: u32) void {
    const r = self.res();
    const t = self.vtype(self.mem.buf[c]);
    switch (r.static_pool.lookup_member(t, .deinit)) {
        .method => |m| _ = invoke(self, n, m, &.{}, .ref(r.static_pool.ptr_mut(t), c), .empty),
        else => {},
    }
}

fn invoke(self: *Interpreter, n: NodeId, d0: DeclPool.Index, all: []const NodeId, self0: Value, env: Value) Value {
    const r = self.res();
    const sp = &r.static_pool;
    if (self.frames.head > Interpreter.max_depth) return self.fail(self.origin(n), .static_eval_failed, 0, 0);
    const mark = self.list.head;
    defer self.list.head = mark;
    for (all) |a| {
        const x = self.eval(syntax.arg_value(r.tree, a));
        if (x.is(.poison_type) or self.unwind != .none) return x;
        self.list.push(x);
    }
    var d = decls.real(r, d0);
    var selfvalue0 = self0;
    var args = all;
    var base = mark;
    if (selfvalue0.is(.none) and r.decl_pool.self_off(d) == 1) {
        if (args.len == 0) return self.fail(n, .wrong_arity, 0, 1);
        selfvalue0 = self.list.buf[mark];
        args = args[1..];
        base += 1;
    }
    if (r.decl_pool.kinds()[@intFromEnum(d)] == .trait_member and selfvalue0.is_ref()) d = switch (sp.lookup_member(self.vtype(self.mem.buf[selfvalue0.at()]), r.decl_pool.names()[@intFromEnum(d)])) {
        .method => |m| m,
        else => d,
    };
    decls.h05_ensure_signature(r, d);
    if (generics.length_generic(r, r.decl_pool.tys()[@intFromEnum(d)])) d = realize(self, n, d, args, base) orelse return .poison;
    var c = d;
    while (c != .none) : (c = r.decl_pool.next_overloads()[@intFromEnum(c)]) {
        if (c != d and !calls.same_params(r, c, d)) continue;
        if (attempt(self, n, decls.real(r, c), args, base, selfvalue0, env)) |v| return v;
    }
    return self.fail(n, .no_matching_overload, args.len, 0);
}

fn realize(self: *Interpreter, n: NodeId, d: DeclPool.Index, args: []const NodeId, base: u32) ?DeclPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const pnodes = syntax.params_of(r.tree, decls.value_node(r, d));
    const map = r.scratch(u32, args.len);
    if (!calls.bind_args(r, pnodes, args, map, false)) return null;
    const mark = self.ids.head;
    defer self.ids.head = mark;
    for (0..pnodes.len) |j| {
        const p = sp.get(r.decl_pool.tys()[@intFromEnum(d)]).function_type.params[j + r.decl_pool.self_off(d)];
        if (!generics.generic_slot(r, p)) continue;
        for (0..args.len) |i| if (map[i] == j) {
            const v = self.list.buf[base + i];
            const x = if (sp.templated(p) != .none) self.vtype(self.deref(v)) else if (sp.tag(p) == .meta_type) self.pool(v) else sp.intern(.{ .int = .{ .ty = .u64_type, .bits = self.count(self.deref(v)) orelse return null } });
            self.ids.push(x);
        };
    }
    const f = generics.h20_instantiate(r, d, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = self.ids.buf[mark..self.ids.head] } }));
    if (sp.tag(f) != .function_value) {
        _ = self.fail(n, .not_static, 0, 0);
        return null;
    }
    return sp.get(f).function;
}

fn attempt(self: *Interpreter, n: NodeId, d: DeclPool.Index, args: []const NodeId, base: u32, valueself: Value, env: Value) ?Value {
    const r = self.res();
    decls.h05_ensure_signature(r, d);
    decls.h06_check_body(r, d);
    const body = r.bodies.get(d) orelse return self.fail(n, .not_static, 0, 0);
    const v = decls.value_node(r, d);
    if (r.decl_pool.states()[@intFromEnum(d)] == .failed) return Value.poison;
    const pnodes = syntax.params_of(r.tree, v);
    const map = r.scratch(u32, args.len);
    if (!calls.bind_args(r, pnodes, args, map, false)) return self.fail(n, .wrong_arity, args.len, pnodes.len);
    const caller = self.frames.buf[self.frames.head - 1].body.decl;
    const unchecked = caller != .none and r.decl_pool.kinds()[@intFromEnum(caller)] == .static_function;
    self.enter(body);
    self.frames.buf[self.frames.head - 1].env = env;
    var keep = false;
    defer self.leave(keep);
    if (r.decl_pool.self_off(d) == 1) places.bind(self, @enumFromInt(body.first), valueself);
    for (0..args.len) |i| {
        _ = places.store(self, pnodes[map[i]], self.info(.decl, pnodes[map[i]]), self.list.buf[base + i]);
    }
    for (pnodes, 0..) |pn, j| if (std.mem.indexOfScalar(u32, map, @intCast(j)) == null) {
        _ = places.store(self, pn, self.info(.decl, pn), self.eval(syntax.Param.from_node(self.res().tree, pn).default));
    };
    for (pnodes) |pn| {
        const p = syntax.Param.from_node(self.res().tree, pn);
        if (p.where == 0) continue;
        const w = self.eval(p.where);
        if (w.ty != .bool_type) return Value.poison;
        if (w.bits != 0) continue;
        if (p.stc) return if (unchecked) self.fail(n, .stcwhere_violated, d, .none) else Value.poison;
        if (p.@"else" == 0) return null;
        const e = self.eval(p.@"else");
        if (self.unwind == .ret) return self.result(e);
        if (r.tree.kind(p.@"else") != .assign) _ = places.store(self, pn, self.info(.decl, pn), e);
    }
    const out = self.coerce(self.result(self.eval(r.tree.arg(v, 1))), types.sig(r, d).ret);
    keep = out.is_boxed();
    return out;
}

pub fn construct(self: *Interpreter, target: Index, args: []const NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const is_case = sp.tag(target) == .variant_case_type;
    const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
    if (rec == .none) return .pooled(target);
    const fields = types.fields_of(r, rec);
    const len: u32 = @intCast(fields.len);
    const at = self.alloc(len);
    for (args, 0..) |a, i| {
        const fi = calls.field_of(r, rec, a, i) orelse return self.fail(a, .unknown_named_argument, r.name_pool.name_of(r.tree, r.src_bytes, r.tree.arg(a, 0)), rec);
        const x = self.eval(syntax.arg_value(r.tree, a));
        if (x.is(.poison_type)) return x;
        self.fill(at + fi, x, sp.get(rec).custom_type.field_types[fi]);
    }
    if (!complete(self, rec, at)) return .poison;
    const agg: Value = .block(rec, at, len);
    if (!is_case) return agg;
    if (self.escapes(agg)) return .block(target, at, len);
    return .pooled(sp.intern(.{ .variant_value = .{ .case = target, .payload = self.pool(agg) } }));
}

pub fn with(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const base = self.deref(self.eval(r.tree.arg(n, 0)));
    if (base.is(.poison_type)) return base;
    const t = self.vtype(base);
    const len = self.span(base) orelse return self.fail(n, .not_static, 0, 0);
    if (sp.tag(t) != .record_type) return self.fail(n, .not_static, 0, 0);
    const at = self.alloc(len);
    for (0..len) |i| {
        const x = self.own(self.elem(base, @intCast(i)));
        self.mem.buf[at + i] = x;
    }
    for (r.tree.manychildren(r.tree.arg(n, 1)), 0..) |a, i| {
        const fi = calls.field_of(r, t, a, i) orelse return self.fail(a, .unknown_named_argument, r.name_pool.name_of(r.tree, r.src_bytes, r.tree.arg(a, 0)), t);
        const x = self.eval(syntax.arg_value(r.tree, a));
        if (x.is(.poison_type)) return x;
        self.fill(at + fi, x, sp.get(t).custom_type.field_types[fi]);
    }
    return if (complete(self, t, at)) .block(t, at, len) else .poison;
}

// the defaults and `where .. else` of the fields of a value being built, in the frame of the type where the fields are the locals
fn complete(self: *Interpreter, rec: Index, at: u32) bool {
    const r = self.res();
    const fields = types.fields_of(r, rec);
    var framed = false;
    for (fields, 0..) |f, i| framed = framed or syntax.Param.from_node(self.res().tree, f).@"else" != 0 or syntax.Param.from_node(self.res().tree, f).default != 0 and self.mem.buf[at + i].is(.none);
    if (!framed) {
        for (0..fields.len) |i| if (self.mem.buf[at + i].is(.none)) self.fill(at + i, self.zero(field(self, rec, i)), field(self, rec, i));
        return true;
    }
    const decl = r.static_pool.get(rec).custom_type.decl;
    const body = r.bodies.get(decl) orelse {
        _ = self.fail(r.decl_pool.nodes()[@intFromEnum(decl)], .not_static, 0, 0);
        return false;
    };
    self.enter(body);
    defer self.leave(false);
    const base = self.top().base;
    for (0..fields.len) |i| self.mem.buf[base + i] = self.mem.buf[at + i];
    for (fields, 0..) |f, i| if (self.mem.buf[base + i].is(.none)) {
        const d = syntax.Param.from_node(self.res().tree, f).default;
        const x = if (d != 0) self.eval(d) else self.zero(field(self, rec, i));
        if (x.is(.poison_type)) return false;
        self.fill(base + i, x, field(self, rec, i));
    };
    for (fields, 0..) |f, i| {
        const p = syntax.Param.from_node(self.res().tree, f);
        if (p.where == 0 or p.@"else" == 0) continue;
        const w = self.eval(p.where);
        if (w.ty != .bool_type) return false;
        if (w.bits != 0) continue;
        const e = self.eval(p.@"else");
        if (e.is(.poison_type)) return false;
        if (r.tree.kind(p.@"else") != .assign) self.fill(base + i, e, field(self, rec, i));
    }
    for (0..fields.len) |i| self.fill(at + i, self.mem.buf[base + i], field(self, rec, i));
    return true;
}

fn field(self: *Interpreter, rec: Index, i: usize) Index {
    return self.res().static_pool.get(rec).custom_type.field_types[i];
}
