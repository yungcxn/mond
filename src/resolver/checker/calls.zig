const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const statics = @import("statics.zig");
const StaticPool = @import("../StaticPool.zig");
const Decl = Resolver.Decl;
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const is_fn = Resolver.is_fn;

pub fn h12_check_call(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const args = self.kids(self.arg(node, 1));
    if (self.nk(node) == .with) { // a copy of a record, the named arguments must be its fields
        const t = self.deref(self.h09_check_expr(ctx, self.arg(node, 0), .none));
        for (args) |a| {
            const m = if (self.nk(a) == .partial__fun_call_assigned_param and t != .poison_type) sp.lookup_member(t, self.name_of(self.arg(a, 0))) else StaticPool.Member.none;
            _ = if (m == .field) self.check(ctx, self.arg(a, 1), named(self, a, m.field.ty)) else if (t == .poison_type) t else self.report(.unknown_named_argument, a, self.name_of(self.arg(a, 0)), t);
        }
        return t;
    }
    const callee = self.arg(node, 0);
    const ct = self.h09_check_expr(ctx, callee, .none);
    // a stcfun call producing a function is called like that function
    const d = if (self.nk(callee) != .fun_call) self.node_decl[callee] else if (self.node_decl[self.arg(callee, 0)] != .none and self.dp(.kind, self.node_decl[self.arg(callee, 0)]).* == .static_function) self.node_decl[callee] else .none;
    // `x.m(..)` binds x as the self argument, `Type.m(x.&, ..)` passes it like any other argument
    const recv = if (self.nk(callee) == .member and sp.tag(self.node_type[self.arg(callee, 0)]) != .meta_type) self.arg(callee, 0) else 0;
    if (ct != .poison_type and d != .none and is_fn(self.dp(.kind, d).*)) return call_decl(self, ctx, node, d, args, recv);
    const target = if (sp.tag(ct) != .meta_type) sp.apply_vars(&self.abstract_pool, ct) else statics.deferred(self, ctx, callee) orelse {
        for (args) |a| _ = self.h09_check_expr(ctx, self.arg_value(a), .none);
        return .poison_type;
    };
    switch (sp.tag(target)) {
        // type constructors: records (`Person(name = ..)`) and variant cases (`Event.Key(13)`)
        .record_type, .variant_case_type => {
            const rec = if (sp.tag(target) == .variant_case_type) sp.get(target).variant_case_type.payload else target;
            var map: [64]u32 = undefined;
            if (rec == .none and args.len > 0) return self.report(.wrong_arity, node, args.len, 0);
            if (rec != .none and !bind_args(self, self.fields_of(rec), args, &map, false)) return bad_args(self, node, self.fields_of(rec), args);
            for (args, 0..) |a, i| _ = self.check(ctx, self.arg_value(a), named(self, a, sp.get(rec).custom_type.field_types[map[i]]));
            return target;
        },
        // a value of function type (`op(a, b)`, `make_adder(1)(2)`, a lambda called directly)
        .function_type => {
            if (sp.get(target).function_type.params.len != args.len) return self.report(.wrong_arity, node, args.len, sp.get(target).function_type.params.len);
            for (args, 0..) |a, i| _ = self.check(ctx, self.arg_value(a), sp.get(target).function_type.params[i]);
            return sp.get(target).function_type.ret;
        },
        else => {
            for (args) |a| _ = self.h09_check_expr(ctx, self.arg_value(a), .none);
            return if (target == .poison_type) target else self.report(.not_callable, callee, ct, .none);
        },
    }
}

// calls of declared functions: overload resolution, stcfun realization, length-generic realization
fn call_decl(self: *Resolver, ctx: *FnCtx, node: NodeId, first: Decl.Index, all_args: []const NodeId, recv: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    if (self.dp(.kind, first).* == .static_function) {
        const want = self.sig(first).params.len;
        if (all_args.len != want) return self.report(.wrong_arity, node, all_args.len, want);
        const ret = self.sig(first).ret;
        var bad = false;
        for (all_args, 0..) |a, i| {
            const p = self.sig(first).params[i];
            if (statics.templated(self, p) != .none) {
                const at = self.h09_check_expr(ctx, self.arg_value(a), .none);
                if (!statics.passes(self, at, p)) bad = self.report(.type_mismatch, self.arg_value(a), at, p) == .poison_type;
                continue;
            }
            if (sp.tag(p) != .meta_type) {
                if (sp.has_vars(p)) {
                    const at = self.h09_check_expr(ctx, self.arg_value(a), p);
                    if (at != .poison_type and statics.arg_len(self, at, p) == .none) _ = self.report(.type_mismatch, self.arg_value(a), at, p);
                    bad = bad or at == .poison_type or statics.arg_len(self, at, p) == .none;
                } else if (self.check(ctx, self.arg_value(a), p) == .poison_type) bad = true;
                continue;
            }
            const at = self.h09_check_expr(ctx, self.arg_value(a), p);
            if (at == .poison_type) bad = true else if (sp.tag(at) != .meta_type or p != .type_type and at != p) {
                _ = self.report(.type_mismatch, self.arg_value(a), at, p);
                bad = true;
            }
        }
        if (bad) return .poison_type;
        if (ctx.interpreted and ret != .fun_type) return ret;
        var vals: [64]StaticPool.Index = undefined;
        for (all_args, 0..) |a, i| {
            vals[i] = statics.retype(self, statics.h08_eval_static(self, ctx, self.arg_value(a)), self.sig(first).params[i]);
            if (statics.holds_template(self, vals[i])) return .poison_type;
        }
        const r = statics.h20_instantiate(self, first, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = vals[0..all_args.len] } }));
        if (sp.tag(ret) != .meta_type) self.node_value[node] = r;
        if (sp.tag(r) != .function_value) return if (sp.tag(ret) == .meta_type or ret == .poison_type) sp.type_of(r) else ret;
        self.node_decl[node] = sp.get(r).function;
        return self.dp(.ty, sp.get(r).function).*;
    }
    // the self argument of a method: the receiver, or the first argument when called through the type
    const off = self.self_off(first);
    var args = all_args;
    if (off == 1) {
        const ft = self.dp(.ty, self.real(first)).*;
        const p0 = if (ft != .none and sp.tag(ft) == .function_type) sp.get(ft).function_type.params[0] else StaticPool.Index.poison_type;
        if (recv != 0) {
            const rt = sp.apply_vars(&self.abstract_pool, self.node_type[recv]);
            const child = sp.pointee(p0);
            if (rt != .poison_type and p0 != .poison_type and rt != child and !sp.implements(rt, child) and sp.coerce(&self.abstract_pool, rt, p0) == .incompatible)
                _ = self.report(.type_mismatch, recv, rt, p0);
        } else if (args.len > 0) {
            _ = self.check(ctx, self.arg_value(args[0]), p0);
            args = args[1..];
        } else return self.report(.wrong_arity, node, 0, 1);
    }
    // argument types once, with the first candidate's parameters as expectation
    var tys: [64]StaticPool.Index = undefined;
    var map: [64]u32 = undefined;
    const f0 = self.real(first);
    const f0_ok = self.dp(.ty, f0).* != .none and bind_args(self, self.params_of(self.value_node(f0)), args, &map, false);
    for (args, 0..) |a, i| {
        const hint = if (f0_ok) self.sig(f0).params[map[i] + off] else .none;
        tys[i] = self.h09_check_expr(ctx, self.arg_value(a), hint);
    }
    // most specific candidate: exact > coercion > unlengthed, a where clause beats none
    var best: Decl.Index = .none;
    var best_score: i32 = -1;
    var ambiguous = false;
    var count: u32 = 0;
    var c = first;
    while (c != .none) : (c = self.dp(.next_overload, c).*) {
        count += 1;
        const s = score(self, c, args, tys[0..args.len], off);
        if (s > best_score) {
            best, best_score, ambiguous = .{ c, s, false };
        } else if (s == best_score and s >= 0 and !has_where(self, self.real(c)) and !has_where(self, self.real(best))) ambiguous = true;
    }
    if (best == .none) {
        if (count > 1) return self.report(.no_matching_overload, node, args.len, 0);
        if (!f0_ok) return bad_args(self, node, self.params_of(self.value_node(f0)), args);
        for (args, 0..) |a, i| _ = self.h10_expect(self.arg_value(a), tys[i], self.sig(f0).params[map[i] + off]);
        return .poison_type;
    }
    if (ambiguous) _ = self.report(.ambiguous_overload, node, best, 0);
    var callee = self.real(best);
    const pnodes = self.params_of(self.value_node(callee));
    _ = bind_args(self, pnodes, args, &map, false);
    check_stcwhere(self, ctx, node, callee, pnodes, args, map[0..args.len]);
    if (statics.length_generic(self, self.dp(.ty, callee).*)) {
        // the argument lengths, in parameter order, pick the realization
        var lens: [64]StaticPool.Index = undefined;
        var n: usize = 0;
        for (0..pnodes.len) |j| {
            const p = self.sig(callee).params[j + off];
            if (!statics.generic_slot(self, p)) continue;
            for (0..args.len) |i| if (map[i] == j) {
                lens[n] = if (statics.templated(self, p) != .none) statics.unwrapped(self, tys[i]) else if (sp.tag(p) != .meta_type) statics.arg_len(self, tys[i], p) else statics.try_static(self, ctx, self.arg_value(args[i])) orelse if (ctx.interpreted) .none else return self.report(.not_static, args[i], 0, 0);
                n += 1;
            };
        }
        if (std.mem.indexOfScalar(StaticPool.Index, lens[0..n], .none) != null) {
            if (ctx.interpreted) self.node_decl[node] = callee;
            return .poison_type;
        }
        for (lens[0..n]) |l| if (l != .none and sp.tag(l) == .template_type) {
            self.h06_check_body(callee);
            return self.sig(callee).ret;
        };
        const realized = statics.h20_instantiate(self, callee, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = lens[0..n] } }));
        if (sp.tag(realized) != .function_value) return .poison_type;
        callee = sp.get(realized).function;
        self.node_decl[node] = callee;
    } else {
        for (args, 0..) |a, i| _ = self.h10_expect(self.arg_value(a), tys[i], named(self, a, self.sig(callee).params[map[i] + off]));
        // the call names the head of its dispatch group: the lowerer walks `next_overload` from there over the
        // overloads with the identical parameter types, tests their where clauses in order, the where-less one last
        self.node_decl[node] = self.real(self.group_head(first, best));
    }
    return self.sig(callee).ret;
}

// stcwhere holds at every call: the callee's parameters are bound to the static arguments in a scope of their own
fn check_stcwhere(self: *Resolver, ctx: *FnCtx, node: NodeId, callee: Decl.Index, pnodes: []const NodeId, args: []const NodeId, map: []const u32) void {
    if (ctx.interpreted) return;
    for (pnodes) |pn| {
        if (self.param(pn).stc) break;
    } else return;
    const ft = self.dp(.ty, callee).*;
    const off = self.self_off(callee);
    self.open_scope(true, .none, 0);
    defer self.h04_pop_scope();
    for (pnodes, 0..) |pn, j| {
        var v: StaticPool.Index = .none;
        var at: StaticPool.Index = .none;
        for (args, 0..) |a, i| if (map[i] == j) {
            v = statics.try_static(self, ctx, self.arg_value(a)) orelse .none;
            at = self.node_type[self.arg_value(a)];
        };
        const pt0 = self.static_pool.get(ft).function_type.params[j + off];
        const pt = if (statics.templated(self, pt0) != .none and at != .none) at else pt0;
        self.dp(.value, self.h02_declare_local(self.param_name(pn, j), pn, .static_parameter, pt)).* = if (v == .none) v else statics.retype(self, v, pt);
    }
    for (pnodes) |pn| {
        const p = self.param(pn);
        if (!p.stc) continue;
        const r = statics.try_static(self, ctx, p.where) orelse {
            _ = self.report(.not_static, node, 0, 0);
            continue;
        };
        if (r == .bool_false) _ = self.report(.stcwhere_violated, node, callee, .none);
    }
}

pub fn dispatches(self: *Resolver, d: Decl.Index) bool {
    for (self.params_of(self.value_node(d))) |pn| {
        const p = self.param(pn);
        if (p.where != 0 and p.@"else" == 0 and !p.stc) return true;
    }
    return false;
}

fn score(self: *Resolver, c: Decl.Index, args: []const NodeId, tys: []const StaticPool.Index, off: usize) i32 {
    const sp = &self.static_pool;
    self.h05_ensure_signature(c);
    const r = self.real(c);
    const ft = self.dp(.ty, r).*;
    if (ft == .none or sp.tag(ft) != .function_type) return -1;
    var map: [64]u32 = undefined;
    const pnodes = self.params_of(self.value_node(r));
    if (!bind_args(self, pnodes, args, &map, false)) return -1;
    var total: i32 = 0;
    for (args, tys, 0..) |a, t, i| {
        const p = sp.get(ft).function_type.params[map[i] + off];
        const v = self.arg_value(a);
        total += if (statics.templated(self, p) != .none)
            (if (statics.passes(self, t, p)) 5 else return -1)
        else if (t == p or t == .poison_type or (self.is_literal(v) and sp.coerce(&self.abstract_pool, statics.literal_type(self, v, p), p) == .identity))
            @as(i32, 6) - @intFromBool(sp.class(p).is_float and !sp.class(t).is_float)
        else if (sp.has_vars(p))
            (if (statics.arg_len(self, t, p) != .none) 2 else return -1)
        else if (sp.coerce(&self.abstract_pool, t, p) != .incompatible) 4 else return -1;
        if (self.param(pnodes[map[i]]).where != 0) total += 1;
    }
    return total;
}

pub fn has_where(self: *Resolver, d: Decl.Index) bool {
    for (self.params_of(self.value_node(d))) |pn| if (self.param(pn).where != 0) return true;
    return false;
}

// one dispatch group: the same parameter types under the same names
pub fn same_params(self: *Resolver, a0: Decl.Index, b0: Decl.Index) bool {
    const sp = &self.static_pool;
    const a = self.real(a0);
    const b = self.real(b0);
    const ta = self.dp(.ty, a).*;
    const tb = self.dp(.ty, b).*;
    if (ta != tb and (ta == .none or tb == .none or sp.tag(ta) != .function_type or sp.tag(tb) != .function_type or !std.mem.eql(StaticPool.Index, sp.get(ta).function_type.params, sp.get(tb).function_type.params))) return false;
    const pa = self.params_of(self.value_node(a));
    const pb = self.params_of(self.value_node(b));
    if (pa.len != pb.len) return false;
    for (pa, pb, 0..) |x, y, i| if (self.param_name(x, i) != self.param_name(y, i)) return false;
    return true;
}

pub fn bind_args(self: *Resolver, params: []const NodeId, args: []const NodeId, map: []u32, partial: bool) bool {
    if (args.len > params.len or params.len > 64) return false;
    var bound: u64 = 0;
    for (args, 0..) |a, i| {
        var p: usize = i;
        if (self.nk(a) == .partial__fun_call_assigned_param) {
            const name = self.name_of(self.arg(a, 0));
            p = for (params, 0..) |pn, j| {
                if (self.param_name(pn, j) == name) break j;
            } else return false;
        }
        if (bound >> @intCast(p) & 1 != 0) return false;
        bound |= @as(u64, 1) << @intCast(p);
        map[i] = @intCast(p);
    }
    if (!partial) for (params, 0..) |pn, j| if (bound >> @intCast(j) & 1 == 0 and self.param(pn).default == 0) return false;
    return true;
}

pub fn named(self: *Resolver, a: NodeId, t: StaticPool.Index) StaticPool.Index {
    if (self.nk(a) == .partial__fun_call_assigned_param) self.node_type[self.arg(a, 0)] = t;
    return t;
}

fn bad_args(self: *Resolver, node: NodeId, params: []const NodeId, args: []const NodeId) StaticPool.Index {
    for (args) |a| if (self.nk(a) == .partial__fun_call_assigned_param) {
        const name = self.name_of(self.arg(a, 0));
        for (params, 0..) |pn, j| {
            if (self.param_name(pn, j) == name) break;
        } else return self.report(.unknown_named_argument, a, name, .none);
    };
    return self.report(.wrong_arity, node, args.len, params.len);
}

pub fn link(self: *Resolver, id: NodeId, d: Decl.Index, t: StaticPool.Index) void {
    if (id == 0) return;
    self.node_decl[id] = d;
    self.node_type[id] = t;
}
