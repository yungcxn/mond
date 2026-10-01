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

pub fn member(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const parent = r.tree.arg(n, 0);
    const name = r.name_of(r.tree.arg(n, 1));
    if (name == .len and !self.framed()) {
        const t = sp.pointee(sp.apply_vars(&r.abstract_pool, r.h09_check_expr(self.ctx, parent, .none)));
        if (sp.get(t) == .array_type and sp.tag(sp.get(t).array_type.len) == .int_value) return .of(sp, sp.get(t).array_type.len);
    }
    const pv = self.deref(self.eval(parent));
    if (pv.is(.poison_type)) return pv;
    if (name == .len) if (self.count(pv)) |c| return .int(.u64_type, c);
    if (name == .tag) {
        const c = control.case_of(self, pv);
        if (c == .none) return self.fail(n, .not_static, 0, 0);
        const st = r.deref(self.checked(parent));
        const v = sp.get(c).variant_case_type;
        return .int(sp.tag_type_of(st), sp.get(v.tag).int.bits + if (sp.tag(st) == .variant_union_type) sp.union_offset(st, v.variant) else 0);
    }
    const pt = self.vtype(pv);
    if (pv.is_heap() or sp.tag(pt) == .record_type) switch (sp.lookup_member(pt, name)) {
        .field => |f| return self.elem(pv, f.index),
        else => {},
    };
    if (!pv.is_pool() or !sp.get_tag_prop(pv.index()).is_type) return self.fail(n, .not_static, 0, 0);
    return switch (sp.lookup_member(pv.index(), name)) {
        .case => |c| .pooled(c),
        .method => |m| blk: {
            r.h05_ensure_signature(m);
            break :blk .of(sp, r.dp(.value, m).*);
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
    if (d != .none and Resolver.is_fn(r.dp(.kind, d).*) and (cd == .none or r.dp(.kind, cd).* != .static_function)) {
        if (r.self_off(r.real(d)) == 0 or r.tree.kind(callee) != .member or sp.tag(self.info(.ty, r.tree.arg(callee, 0))) == .meta_type) return invoke(self, n, d, args, .empty, .empty);
        const c = places.cell(self, r.tree.arg(callee, 0)) orelse return .poison;
        return invoke(self, n, d, args, if (self.mem.buf[c].is_ref()) self.mem.buf[c] else .ref(r.self_ptr(self.vtype(self.mem.buf[c])), c), .empty);
    }
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
            const params = sp.get(r.dp(.ty, g).*).function_type.params;
            if (args.len != params.len) break :blk self.fail(n, .wrong_arity, args.len, params.len);
            const mark = self.ids.head;
            defer self.ids.head = mark;
            for (args, params) |a, p| {
                const x = self.eval(r.arg_value(a));
                if (x.is(.poison_type)) break :blk x;
                const i = self.pool(x);
                const ok = if (sp.tag(p) == .meta_type) p == .type_type and sp.get_tag_prop(i).is_type or sp.type_of(i) == p else !sp.get_tag_prop(p).is_integer or sp.tag(i) == .int_value and sp.fits(i, p);
                if (!ok) break :blk self.fail(r.arg_value(a), .type_mismatch, sp.type_of(i), p);
                self.ids.push(r.retype(i, p));
            }
            const tuple = sp.intern(.{ .aggregate = .{ .ty = .none, .elems = self.ids.buf[mark..self.ids.head] } });
            break :blk .of(sp, r.h20_instantiate(g, tuple));
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
        .method => |m| _ = invoke(self, n, m, &.{}, .ref(r.self_ptr(t), c), .empty),
        else => {},
    }
}

fn invoke(self: *Interpreter, n: NodeId, d0: Decl.Index, all: []const NodeId, self0: Value, env: Value) Value {
    const r = self.res();
    const sp = &r.static_pool;
    if (self.frames.head > Interpreter.max_depth) return self.fail(n, .static_eval_failed, 0, 0);
    const mark = self.list.head;
    defer self.list.head = mark;
    for (all) |a| {
        const x = self.eval(r.arg_value(a));
        if (x.is(.poison_type) or self.unwind != .none) return x;
        self.list.push(x);
    }
    var d = r.real(d0);
    var selfvalue0 = self0;
    var args = all;
    var base = mark;
    if (selfvalue0.is(.none) and r.self_off(d) == 1) {
        if (args.len == 0) return self.fail(n, .wrong_arity, 0, 1);
        selfvalue0 = self.list.buf[mark];
        args = args[1..];
        base += 1;
    }
    if (r.dp(.kind, d).* == .trait_member and selfvalue0.is_ref()) d = switch (sp.lookup_member(self.vtype(self.mem.buf[selfvalue0.at()]), r.dp(.name, d).*)) {
        .method => |m| m,
        else => d,
    };
    r.h05_ensure_signature(d);
    if (r.length_generic(r.dp(.ty, d).*)) d = realize(self, n, d, args, base) orelse return .poison;
    var c = d;
    while (c != .none) : (c = r.dp(.next_overload, c).*) {
        if (c != d and !r.same_params(c, d)) continue;
        if (attempt(self, n, r.real(c), args, base, selfvalue0, env)) |v| return v;
    }
    return self.fail(n, .no_matching_overload, args.len, 0);
}

fn realize(self: *Interpreter, n: NodeId, d: Decl.Index, args: []const NodeId, base: u32) ?Decl.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const pnodes = r.params_of(r.value_node(d));
    var map: [64]u32 = undefined;
    if (!r.bind_args(pnodes, args, &map, false)) return null;
    const mark = self.ids.head;
    defer self.ids.head = mark;
    for (0..pnodes.len) |j| {
        const p = sp.get(r.dp(.ty, d).*).function_type.params[j + r.self_off(d)];
        if (!r.generic_slot(p)) continue;
        for (0..args.len) |i| if (map[i] == j) {
            const v = self.list.buf[base + i];
            const x = if (r.templated(p) != .none) self.vtype(self.deref(v)) else if (sp.tag(p) == .meta_type) self.pool(v) else sp.intern(.{ .int = .{ .ty = .u64_type, .bits = self.count(self.deref(v)) orelse return null } });
            self.ids.push(x);
        };
    }
    const f = r.h20_instantiate(d, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = self.ids.buf[mark..self.ids.head] } }));
    if (sp.tag(f) != .function_value) {
        _ = self.fail(n, .not_static, 0, 0);
        return null;
    }
    return sp.get(f).function;
}

fn attempt(self: *Interpreter, n: NodeId, d: Decl.Index, args: []const NodeId, base: u32, valueself: Value, env: Value) ?Value {
    const r = self.res();
    r.h05_ensure_signature(d);
    r.h06_check_body(d);
    const bi = r.body_of.get(d) orelse return self.fail(n, .not_static, 0, 0);
    const v = r.value_node(d);
    if (r.dp(.state, d).* == .failed) return Value.poison;
    const pnodes = r.params_of(v);
    var map: [64]u32 = undefined;
    if (!r.bind_args(pnodes, args, &map, false)) return self.fail(n, .wrong_arity, args.len, pnodes.len);
    const body = r.bodies.get(bi).?;
    const caller = self.frames.buf[self.frames.head - 1].body.decl;
    const unchecked = caller != .none and r.dp(.kind, caller).* == .static_function;
    self.enter(body);
    self.frames.buf[self.frames.head - 1].env = env;
    var keep = false;
    defer self.leave(keep);
    if (r.self_off(d) == 1) places.bind(self, @enumFromInt(body.first), valueself);
    var bound: u64 = 0;
    for (0..args.len) |i| {
        bound |= @as(u64, 1) << @intCast(map[i]);
        _ = places.store(self, pnodes[map[i]], self.info(.decl, pnodes[map[i]]), self.list.buf[base + i]);
    }
    for (pnodes, 0..) |pn, j| if (bound >> @intCast(j) & 1 == 0) {
        _ = places.store(self, pn, self.info(.decl, pn), self.eval(r.param(pn).default));
    };
    for (pnodes) |pn| {
        const p = r.param(pn);
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
    const out = self.result(self.eval(r.tree.arg(v, 1)));
    keep = out.is_boxed();
    return out;
}

pub fn construct(self: *Interpreter, target: Index, args: []const NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    const is_case = sp.tag(target) == .variant_case_type;
    const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
    if (rec == .none) return .pooled(target);
    const fields = r.fields_of(rec);
    const len: u32 = @intCast(fields.len);
    const at = self.alloc(len);
    for (args, 0..) |a, i| {
        const fi = r.field_of(rec, a, i) orelse return self.fail(a, .unknown_named_argument, r.name_of(r.tree.arg(a, 0)), rec);
        const x = self.eval(r.arg_value(a));
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
        const fi = r.field_of(t, a, i) orelse return self.fail(a, .unknown_named_argument, r.name_of(r.tree.arg(a, 0)), t);
        const x = self.eval(r.arg_value(a));
        if (x.is(.poison_type)) return x;
        self.fill(at + fi, x, sp.get(t).custom_type.field_types[fi]);
    }
    return if (complete(self, t, at)) .block(t, at, len) else .poison;
}

// the defaults and `where .. else` of the fields of a value being built, in the frame of the type where the fields are the locals
fn complete(self: *Interpreter, rec: Index, at: u32) bool {
    const r = self.res();
    const fields = r.fields_of(rec);
    var framed = false;
    for (fields, 0..) |f, i| framed = framed or r.param(f).@"else" != 0 or r.param(f).default != 0 and self.mem.buf[at + i].is(.none);
    if (!framed) {
        for (0..fields.len) |i| if (self.mem.buf[at + i].is(.none)) self.fill(at + i, self.zero(field(self, rec, i)), field(self, rec, i));
        return true;
    }
    const decl = r.static_pool.get(rec).custom_type.decl;
    const bi = r.body_of.get(decl) orelse {
        _ = self.fail(r.dp(.node, decl).*, .not_static, 0, 0);
        return false;
    };
    self.enter(r.bodies.get(bi).?);
    defer self.leave(false);
    const base = self.top().base;
    for (0..fields.len) |i| self.mem.buf[base + i] = self.mem.buf[at + i];
    for (fields, 0..) |f, i| if (self.mem.buf[base + i].is(.none)) {
        const d = r.param(f).default;
        const x = if (d != 0) self.eval(d) else self.zero(field(self, rec, i));
        if (x.is(.poison_type)) return false;
        self.fill(base + i, x, field(self, rec, i));
    };
    for (fields, 0..) |f, i| {
        const p = r.param(f);
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
