const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// calls: overloads and their dispatch groups, arguments bound to parameters, stcfun and length-generic calls
const Calls = @This();

pub fn res(self: *Calls) *Resolver {
    return @alignCast(@fieldParentPtr("calls", self));
}

pub fn check_call(self: *Calls, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const args = r.tree.manychildren(r.tree.arg(node, 1));
    if (r.tree.kind(node) == .with) { // a copy of a record, the named arguments must be its fields
        const t = sp.deref(&r.abstract_pool, r.exprs.infer(ctx, r.tree.arg(node, 0), .none));
        for (args) |a| {
            const name = r.name_pool.name_of(r.tree.arg_name(a));
            const m = if (r.tree.arg_name(a) != 0 and t != .poison_type) sp.lookup_member(t, name) else StaticPool.Member.none;
            _ = if (m == .field) r.exprs.check(ctx, r.tree.arg_value(a), self.named(a, m.field.ty)) else if (t == .poison_type) t else r.report(.unknown_named_argument, a, name, t);
        }
        return t;
    }
    const callee = r.tree.arg(node, 0);
    const ct = r.exprs.infer(ctx, callee, .none);
    // a stcfun call producing a function is called like that function
    const d = if (r.tree.kind(callee) != .fun_call) r.node_decl[callee] else if (r.node_decl[r.tree.arg(callee, 0)] != .none and r.decl_pool.get_kind(r.node_decl[r.tree.arg(callee, 0)]) == .static_function) r.node_decl[callee] else .none;
    // `x.m(..)` binds x as the self argument, `Type.m(x.&, ..)` passes it like any other argument
    const recv = if (r.tree.kind(callee) == .member and sp.tag(r.node_type[r.tree.arg(callee, 0)]) != .meta_type) r.tree.arg(callee, 0) else 0;
    if (ct != .poison_type and d != .none and r.decl_pool.get_kind(d).is_fn()) return self.call_decl(ctx, node, d, args, recv);
    const target = if (sp.tag(ct) != .meta_type) sp.apply_vars(&r.abstract_pool, ct) else r.statics.deferred(ctx, callee) orelse {
        for (args) |a| _ = r.exprs.infer(ctx, r.tree.arg_value(a), .none);
        return .poison_type;
    };
    const value = sp.tag(ct) != .meta_type and (r.tree.kind(callee) != .member or recv != 0);
    switch (if (value and (sp.tag(target) == .record_type or sp.tag(target) == .variant_case_type)) .simple_type else sp.tag(target)) {
        // type constructors: records (`Person(name = ..)`) and variant cases (`Event.Key(13)`)
        .record_type, .variant_case_type => {
            const rec = if (sp.tag(target) == .variant_case_type) sp.get(target).variant_case_type.payload else target;
            const map = r.scratch(u32, args.len);
            if (rec == .none and args.len > 0) return r.report(.wrong_arity, node, args.len, 0);
            if (rec != .none and !self.bind_args(r.types.fields_of(rec), args, map, false)) return self.bad_args(node, r.types.fields_of(rec), args);
            for (args, 0..) |a, i| _ = r.exprs.check(ctx, r.tree.arg_value(a), self.named(a, sp.field_type(rec, map[i])));
            return target;
        },
        // a value of function type (`op(a, b)`, `make_adder(1)(2)`, a lambda called directly)
        .function_type => {
            if (sp.get(target).function_type.params.len != args.len) return r.report(.wrong_arity, node, args.len, sp.get(target).function_type.params.len);
            for (args, 0..) |a, i| _ = r.exprs.check(ctx, r.tree.arg_value(a), sp.get(target).function_type.params[i]);
            return sp.get(target).function_type.ret;
        },
        else => {
            for (args) |a| _ = r.exprs.infer(ctx, r.tree.arg_value(a), .none);
            return if (target == .poison_type) target else r.report(.not_callable, callee, ct, .none);
        },
    }
}

// calls of declared functions: overload resolution, stcfun realization, length-generic realization
fn call_decl(self: *Calls, ctx: *FnCtx, node: NodeId, first: DeclPool.Index, all_args: []const NodeId, recv: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    if (r.decl_pool.get_kind(first) == .static_function) {
        const want = r.types.sig(first).params.len;
        if (all_args.len != want) return r.report(.wrong_arity, node, all_args.len, want);
        const ret = r.types.sig(first).ret;
        var bad = false;
        for (all_args, 0..) |a, i| {
            const p = r.types.sig(first).params[i];
            if (sp.templated(p) != .none) {
                const at = r.exprs.infer(ctx, r.tree.arg_value(a), .none);
                if (!r.generics.passes(at, p)) bad = r.report(.type_mismatch, r.tree.arg_value(a), at, p) == .poison_type;
                continue;
            }
            if (sp.tag(p) != .meta_type) {
                if (sp.has_vars(p)) {
                    const at = r.exprs.infer(ctx, r.tree.arg_value(a), p);
                    if (at != .poison_type and sp.arg_len(&r.abstract_pool, at, p) == .none) _ = r.report(.type_mismatch, r.tree.arg_value(a), at, p);
                    bad = bad or at == .poison_type or sp.arg_len(&r.abstract_pool, at, p) == .none;
                } else if (r.exprs.check(ctx, r.tree.arg_value(a), p) == .poison_type) bad = true;
                continue;
            }
            const at = r.exprs.infer(ctx, r.tree.arg_value(a), p);
            if (at == .poison_type) bad = true else if (sp.tag(at) != .meta_type or p != .type_type and at != p) {
                _ = r.report(.type_mismatch, r.tree.arg_value(a), at, p);
                bad = true;
            }
        }
        if (bad) return .poison_type;
        if (ctx.interpreted and ret != .fun_type) return ret;
        const vals = r.scratch(StaticPool.Index, all_args.len);
        for (all_args, 0..) |a, i| {
            vals[i] = r.statics.retype(r.interpreter.eval_static(ctx, r.tree.arg_value(a)), r.types.sig(first).params[i]);
            if (sp.holds_template(vals[i])) return .poison_type;
        }
        if (r.interpreter.depth == 0) r.interpreter.root = node;
        const got = r.generics.instantiate(first, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = vals } }));
        if (sp.tag(ret) != .meta_type) r.node_value[node] = got;
        if (sp.tag(got) != .function_value) return if (sp.tag(ret) == .meta_type or ret == .poison_type) sp.type_of(got) else ret;
        r.node_decl[node] = sp.get(got).function;
        return r.decl_pool.get_ty(sp.get(got).function);
    }
    // the self argument of a method: the receiver, or the first argument when called through the type
    const off = r.decl_pool.self_off(first);
    var args = all_args;
    if (off == 1) {
        const ft = r.decl_pool.get_ty(r.decls.real(first));
        const p0 = if (ft != .none and sp.tag(ft) == .function_type) sp.get(ft).function_type.params[0] else StaticPool.Index.poison_type;
        if (recv != 0) {
            const rt = sp.apply_vars(&r.abstract_pool, r.node_type[recv]);
            const child = sp.pointee(p0);
            if (rt != .poison_type and p0 != .poison_type and rt != child and !sp.implements(rt, child) and sp.coerce(&r.abstract_pool, rt, p0) == .incompatible)
                _ = r.report(.type_mismatch, recv, rt, p0);
        } else if (args.len > 0) {
            // a method that does not write `self` takes a read only one as well
            _ = r.exprs.check(ctx, r.tree.arg_value(args[0]), if (sp.is_ptr(p0)) sp.ptr_of(sp.pointee(p0), false) else p0);
            args = args[1..];
        } else return r.report(.wrong_arity, node, 0, 1);
    }
    // argument types once, with the first candidate's parameters as expectation
    const tys = r.scratch(StaticPool.Index, args.len);
    const map = r.scratch(u32, args.len);
    const f0 = r.decls.real(first);
    const f0_ok = r.decl_pool.get_ty(f0) != .none and self.bind_args(r.tree.params_of(r.decls.value_node(f0)), args, map, false);
    for (args, 0..) |a, i| {
        const hint = if (f0_ok) r.types.sig(f0).params[map[i] + off] else .none;
        tys[i] = r.exprs.infer(ctx, r.tree.arg_value(a), hint);
    }
    // most specific candidate: exact > coercion > unlengthed, a where clause beats none
    var best: DeclPool.Index = .none;
    var best_score: i32 = -1;
    var ambiguous = false;
    var count: u32 = 0;
    var c = first;
    while (c != .none) : (c = r.decl_pool.get_next_overload(c)) {
        count += 1;
        const s = self.score(c, args, tys, off);
        if (s > best_score) {
            best, best_score, ambiguous = .{ c, s, false };
        } else if (s == best_score and s >= 0 and !self.has_where(r.decls.real(c)) and !self.has_where(r.decls.real(best))) ambiguous = true;
    }
    if (best == .none) {
        if (count > 1) return r.report(.no_matching_overload, node, args.len, 0);
        if (!f0_ok) return self.bad_args(node, r.tree.params_of(r.decls.value_node(f0)), args);
        for (args, 0..) |a, i| {
            const p = r.types.sig(f0).params[map[i] + off];
            _ = if (!sp.has_vars(p)) r.exprs.expect(r.tree.arg_value(a), tys[i], p) else if (sp.arg_len(&r.abstract_pool, tys[i], p) == .none) r.mismatch(r.tree.arg_value(a), tys[i], p) else tys[i];
        }
        return .poison_type;
    }
    if (ambiguous) _ = r.report(.ambiguous_overload, node, best, 0);
    var callee = r.decls.real(best);
    if (off == 1 and r.decl_pool.get_flags(callee).writes) {
        const got = if (recv != 0) recv else r.tree.arg_value(all_args[0]);
        const rt = sp.apply_vars(&r.abstract_pool, r.node_type[got]);
        const assignable = r.tree.props(got).assignable;
        if (recv == 0) {
            if (sp.tag(rt) == .ptr_type) _ = r.report(.type_mismatch, got, rt, r.types.sig(callee).params[0]);
        } else if (sp.is_ptr(rt)) {
            r.mutability.write_access(got, if (sp.tag(rt) == .ptr_type) .through_ptr else .ok);
        } else if (assignable) r.mutability.write_access(got, r.mutability.writable(got));
    }
    const pnodes = r.tree.params_of(r.decls.value_node(callee));
    _ = self.bind_args(pnodes, args, map, false);
    self.check_stcwhere(ctx, node, callee, pnodes, args, map);
    if (sp.length_generic(&r.abstract_pool, r.decl_pool.get_ty(callee))) {
        // the argument lengths, in parameter order, pick the realization
        const lens = r.scratch(StaticPool.Index, args.len);
        var n: usize = 0;
        for (0..pnodes.len) |j| {
            const p = r.types.sig(callee).params[j + off];
            if (!sp.generic_slot(p)) continue;
            for (0..args.len) |i| if (map[i] == j) {
                lens[n] = if (sp.templated(p) != .none) sp.unwrapped(&r.abstract_pool, tys[i]) else if (sp.tag(p) != .meta_type) sp.arg_len(&r.abstract_pool, tys[i], p) else r.statics.try_static(ctx, r.tree.arg_value(args[i])) orelse if (ctx.interpreted) .none else return r.report(.not_static, args[i], 0, 0);
                n += 1;
            };
        }
        if (std.mem.indexOfScalar(StaticPool.Index, lens[0..n], .none) != null) {
            if (ctx.interpreted) r.node_decl[node] = callee;
            return .poison_type;
        }
        for (lens[0..n]) |l| if (l != .none and sp.tag(l) == .template_type) {
            r.decls.check_body(callee);
            return r.types.sig(callee).ret;
        };
        const realized = r.generics.instantiate(callee, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = lens[0..n] } }));
        if (sp.tag(realized) != .function_value) return .poison_type;
        callee = sp.get(realized).function;
        r.node_decl[node] = callee;
    } else {
        for (args, 0..) |a, i| _ = r.exprs.expect(r.tree.arg_value(a), tys[i], self.named(a, r.types.sig(callee).params[map[i] + off]));
        // the call names the head of its dispatch group: the lowerer walks `next_overload` from there over the
        // overloads with the identical parameter types, tests their where clauses in order, the where-less one last
        r.node_decl[node] = r.decls.real(self.group_head(first, best));
    }
    return r.types.sig(callee).ret;
}

// stcwhere holds at every call: the callee's parameters are bound to the static arguments in a scope of their own
fn check_stcwhere(self: *Calls, ctx: *FnCtx, node: NodeId, callee: DeclPool.Index, pnodes: []const NodeId, args: []const NodeId, map: []const u32) void {
    const r = self.res();
    if (ctx.interpreted) return;
    for (pnodes) |pn| {
        if (ParseTree.Param.from_node(r.tree, pn).stc) break;
    } else return;
    const ft = r.decl_pool.get_ty(callee);
    const off = r.decl_pool.self_off(callee);
    const vs = r.scratch(StaticPool.Index, pnodes.len);
    @memset(vs, .none);
    const ts = r.scratch(StaticPool.Index, pnodes.len);
    @memset(ts, .none);
    for (args, 0..) |a, i| {
        vs[map[i]] = r.statics.try_static(ctx, r.tree.arg_value(a)) orelse .none;
        ts[map[i]] = r.node_type[r.tree.arg_value(a)];
    }
    r.decls.open_scope(true, .none, 0);
    defer r.scopes.pop();
    for (pnodes, 0..) |pn, j| {
        const pt0 = r.static_pool.get(ft).function_type.params[j + off];
        const pt = if (r.static_pool.templated(pt0) != .none and ts[j] != .none) ts[j] else pt0;
        r.decl_pool.set_value(r.decls.declare_local(r.decls.param_name(pn, j), pn, .static_parameter, pt), if (vs[j] == .none) .none else r.statics.retype(vs[j], pt));
    }
    for (pnodes) |pn| {
        const p = ParseTree.Param.from_node(r.tree, pn);
        if (!p.stc) continue;
        const got = r.statics.try_static(ctx, p.where) orelse {
            _ = r.report(.not_static, node, 0, 0);
            continue;
        };
        if (got == .bool_false) _ = r.report(.stcwhere_violated, node, callee, .none);
    }
}

// overloads that differ only by where clauses dispatch at runtime and need a where-less fallback
pub fn check_groups(self: *Calls) void {
    const r = self.res();
    var heads = r.scopes.globals.valueIterator();
    while (heads.next()) |h| {
        var c = h.*;
        while (c != .none) : (c = r.decl_pool.get_next_overload(c)) {
            if (self.group_head(h.*, c) != c) continue;
            var size: u32 = 0;
            var plain: u32 = 0;
            var m = c;
            while (m != .none) : (m = r.decl_pool.get_next_overload(m)) if (self.same_params(m, c)) {
                size += 1;
                const fallback = !self.dispatches(r.decls.real(m));
                plain += @intFromBool(fallback);
                if (fallback and plain > 1) r.doc.report(.duplicate_declaration, r.decl_pool.get_node(m), r.decl_pool.get_name(m), c);
            };
            if (size > 1 and plain == 0) _ = r.report(.no_matching_overload, r.decl_pool.get_node(c), size, 0);
        }
    }
}

fn dispatches(self: *Calls, d: DeclPool.Index) bool {
    const r = self.res();
    for (r.tree.params_of(r.decls.value_node(d))) |pn| {
        const p = ParseTree.Param.from_node(r.tree, pn);
        if (p.where != 0 and p.@"else" == 0 and !p.stc) return true;
    }
    return false;
}

fn score(self: *Calls, c: DeclPool.Index, args: []const NodeId, tys: []const StaticPool.Index, off: usize) i32 {
    const r = self.res();
    const sp = &r.static_pool;
    r.decls.ensure_signature(c);
    const f = r.decls.real(c);
    const ft = r.decl_pool.get_ty(f);
    if (ft == .none or sp.tag(ft) != .function_type) return -1;
    const map = r.scratch(u32, args.len);
    const pnodes = r.tree.params_of(r.decls.value_node(f));
    if (!self.bind_args(pnodes, args, map, false)) return -1;
    var total: i32 = 0;
    for (args, tys, 0..) |a, t, i| {
        const p = sp.get(ft).function_type.params[map[i] + off];
        const v = r.tree.arg_value(a);
        total += if (sp.templated(p) != .none)
            (if (r.generics.passes(t, p)) 5 else return -1)
        else if (sp.has_vars(p) and t != .poison_type)
            (if (sp.arg_len(&r.abstract_pool, t, p) != .none) 2 else return -1)
        else if (t == p or t == .poison_type or (r.tree.is_literal(v) and sp.coerce(&r.abstract_pool, r.statics.literal_type(v, p), p) == .identity))
            @as(i32, 6) - @intFromBool(sp.get_tag_prop(p).is_float and !sp.get_tag_prop(t).is_float)
        else if (sp.coerce(&r.abstract_pool, t, p) != .incompatible) 4 else return -1;
        if (ParseTree.Param.from_node(r.tree, pnodes[map[i]]).where != 0) total += 1;
    }
    return total;
}

pub fn has_where(self: *Calls, d: DeclPool.Index) bool {
    const r = self.res();
    for (r.tree.params_of(r.decls.value_node(d))) |pn| if (ParseTree.Param.from_node(r.tree, pn).where != 0) return true;
    return false;
}

// one dispatch group: the same parameter types under the same names
pub fn same_params(self: *Calls, a0: DeclPool.Index, b0: DeclPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    const a = r.decls.real(a0);
    const b = r.decls.real(b0);
    const ta = r.decl_pool.get_ty(a);
    const tb = r.decl_pool.get_ty(b);
    if (ta != tb and (ta == .none or tb == .none or sp.tag(ta) != .function_type or sp.tag(tb) != .function_type or !std.mem.eql(StaticPool.Index, sp.get(ta).function_type.params, sp.get(tb).function_type.params))) return false;
    const pa = r.tree.params_of(r.decls.value_node(a));
    const pb = r.tree.params_of(r.decls.value_node(b));
    if (pa.len != pb.len) return false;
    for (pa, pb, 0..) |x, y, i| if (r.decls.param_name(x, i) != r.decls.param_name(y, i)) return false;
    return true;
}

pub fn bind_args(self: *Calls, params: []const NodeId, args: []const NodeId, map: []u32, partial: bool) bool {
    const r = self.res();
    if (args.len > params.len) return false;
    for (args, 0..) |a, i| {
        const p: u32 = if (r.tree.arg_name(a) != 0) r.decls.param_index(params, r.name_pool.name_of(r.tree.arg_name(a))) orelse return false else @intCast(i);
        if (std.mem.indexOfScalar(u32, map[0..i], p) != null) return false;
        map[i] = p;
    }
    if (!partial) for (params, 0..) |pn, j| if (std.mem.indexOfScalar(u32, map[0..args.len], @intCast(j)) == null and ParseTree.Param.from_node(r.tree, pn).default == 0) return false;
    return true;
}

pub fn named(self: *Calls, a: NodeId, t: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    if (r.tree.arg_name(a) != 0) r.node_type[r.tree.arg_name(a)] = t;
    return t;
}

fn bad_args(self: *Calls, node: NodeId, params: []const NodeId, args: []const NodeId) StaticPool.Index {
    const r = self.res();
    for (args) |a| if (r.tree.arg_name(a) != 0) {
        const name = r.name_pool.name_of(r.tree.arg_name(a));
        if (r.decls.param_index(params, name) == null) return r.report(.unknown_named_argument, a, name, .none);
    };
    return r.report(.wrong_arity, node, args.len, params.len);
}

// an overloaded function as a value is the overload of the expected type
pub fn overload_for(self: *Calls, node: NodeId, d: DeclPool.Index, expected: StaticPool.Index) DeclPool.Index {
    const r = self.res();
    const e = r.static_pool.apply_vars(&r.abstract_pool, expected);
    if (d == .none or e == .none or r.static_pool.tag(e) != .function_type or !r.decl_pool.get_kind(d).is_fn()) return d;
    var c = d;
    while (c != .none) : (c = r.decl_pool.get_next_overload(c)) if (r.types.decl_type(c) == e) {
        r.node_decl[node] = c;
        return c;
    };
    return d;
}

// `T.$init()` / `x.$deinit()` of a type that declares neither: a default value, nothing
pub fn builtin_of(self: *Calls, callee: NodeId, pt: StaticPool.Index, t: StaticPool.Index) StaticPool.Member {
    const r = self.res();
    if (pt == .none or pt == .poison_type or t == .none) return .none;
    return r.static_pool.lookup_member(if (r.static_pool.tag(pt) == .meta_type) t else r.static_pool.deref(&r.abstract_pool, pt), r.name_pool.name_of(r.tree.arg(callee, 1)));
}

fn group_head(self: *Calls, first: DeclPool.Index, d: DeclPool.Index) DeclPool.Index {
    const r = self.res();
    var h = first;
    while (h != d and !self.same_params(h, d)) h = r.decl_pool.get_next_overload(h);
    return h;
}

pub fn field_of(self: *Calls, rec: StaticPool.Index, a: NodeId, i: usize) ?u32 {
    const r = self.res();
    if (r.tree.arg_name(a) == 0) return @intCast(i);
    return switch (r.static_pool.lookup_member(rec, r.name_pool.name_of(r.tree.arg_name(a)))) {
        .field => |f| f.index,
        else => null,
    };
}
