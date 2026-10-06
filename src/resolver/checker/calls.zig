const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const decls = @import("decls.zig");
const exprs = @import("exprs.zig");
const places = @import("places.zig");
const types = @import("types.zig");
const generics = @import("generics.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// calls: overloads and their dispatch groups, arguments bound to parameters, stcfun and length-generic calls

// calls: overloads and their dispatch groups, arguments bound to parameters, stcfun and length-generic calls

// calls: overloads and their dispatch groups, arguments bound to parameters, stcfun and length-generic calls

pub fn h12_check_call(self: *Resolver, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const args = self.tree.manychildren(self.tree.arg(node, 1));
    if (self.tree.kind(node) == .with) { // a copy of a record, the named arguments must be its fields
        const t = sp.deref(&self.abstract_pool, exprs.h09_check_expr(self, ctx, self.tree.arg(node, 0), .none));
        for (args) |a| {
            const m = if (self.tree.kind(a) == .partial__fun_call_assigned_param and t != .poison_type) sp.lookup_member(t, self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0))) else StaticPool.Member.none;
            _ = if (m == .field) exprs.check(self, ctx, self.tree.arg(a, 1), named(self, a, m.field.ty)) else if (t == .poison_type) t else self.report(.unknown_named_argument, a, self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0)), t);
        }
        return t;
    }
    const callee = self.tree.arg(node, 0);
    const ct = exprs.h09_check_expr(self, ctx, callee, .none);
    // a stcfun call producing a function is called like that function
    const d = if (self.tree.kind(callee) != .fun_call) self.node_decl[callee] else if (self.node_decl[self.tree.arg(callee, 0)] != .none and self.decl_pool.kinds()[@intFromEnum(self.node_decl[self.tree.arg(callee, 0)])] == .static_function) self.node_decl[callee] else .none;
    // `x.m(..)` binds x as the self argument, `Type.m(x.&, ..)` passes it like any other argument
    const recv = if (self.tree.kind(callee) == .member and sp.tag(self.node_type[self.tree.arg(callee, 0)]) != .meta_type) self.tree.arg(callee, 0) else 0;
    if (ct != .poison_type and d != .none and self.decl_pool.kinds()[@intFromEnum(d)].is_fn()) return call_decl(self, ctx, node, d, args, recv);
    const target = if (sp.tag(ct) != .meta_type) sp.apply_vars(&self.abstract_pool, ct) else statics.deferred(self, ctx, callee) orelse {
        for (args) |a| _ = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), .none);
        return .poison_type;
    };
    const value = sp.tag(ct) != .meta_type and (self.tree.kind(callee) != .member or recv != 0);
    switch (if (value and (sp.tag(target) == .record_type or sp.tag(target) == .variant_case_type)) .simple_type else sp.tag(target)) {
        // type constructors: records (`Person(name = ..)`) and variant cases (`Event.Key(13)`)
        .record_type, .variant_case_type => {
            const rec = if (sp.tag(target) == .variant_case_type) sp.get(target).variant_case_type.payload else target;
            const map = self.scratch(u32, args.len);
            if (rec == .none and args.len > 0) return self.report(.wrong_arity, node, args.len, 0);
            if (rec != .none and !bind_args(self, types.fields_of(self, rec), args, map, false)) return bad_args(self, node, types.fields_of(self, rec), args);
            for (args, 0..) |a, i| _ = exprs.check(self, ctx, syntax.arg_value(self.tree, a), named(self, a, sp.get(rec).custom_type.field_types[map[i]]));
            return target;
        },
        // a value of function type (`op(a, b)`, `make_adder(1)(2)`, a lambda called directly)
        .function_type => {
            if (sp.get(target).function_type.params.len != args.len) return self.report(.wrong_arity, node, args.len, sp.get(target).function_type.params.len);
            for (args, 0..) |a, i| _ = exprs.check(self, ctx, syntax.arg_value(self.tree, a), sp.get(target).function_type.params[i]);
            return sp.get(target).function_type.ret;
        },
        else => {
            for (args) |a| _ = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), .none);
            return if (target == .poison_type) target else self.report(.not_callable, callee, ct, .none);
        },
    }
}

// calls of declared functions: overload resolution, stcfun realization, length-generic realization
fn call_decl(self: *Resolver, ctx: *FnCtx, node: NodeId, first: DeclPool.Index, all_args: []const NodeId, recv: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    if (self.decl_pool.kinds()[@intFromEnum(first)] == .static_function) {
        const want = types.sig(self, first).params.len;
        if (all_args.len != want) return self.report(.wrong_arity, node, all_args.len, want);
        const ret = types.sig(self, first).ret;
        var bad = false;
        for (all_args, 0..) |a, i| {
            const p = types.sig(self, first).params[i];
            if (sp.templated(p) != .none) {
                const at = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), .none);
                if (!generics.passes(self, at, p)) bad = self.report(.type_mismatch, syntax.arg_value(self.tree, a), at, p) == .poison_type;
                continue;
            }
            if (sp.tag(p) != .meta_type) {
                if (sp.has_vars(p)) {
                    const at = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), p);
                    if (at != .poison_type and generics.arg_len(self, at, p) == .none) _ = self.report(.type_mismatch, syntax.arg_value(self.tree, a), at, p);
                    bad = bad or at == .poison_type or generics.arg_len(self, at, p) == .none;
                } else if (exprs.check(self, ctx, syntax.arg_value(self.tree, a), p) == .poison_type) bad = true;
                continue;
            }
            const at = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), p);
            if (at == .poison_type) bad = true else if (sp.tag(at) != .meta_type or p != .type_type and at != p) {
                _ = self.report(.type_mismatch, syntax.arg_value(self.tree, a), at, p);
                bad = true;
            }
        }
        if (bad) return .poison_type;
        if (ctx.interpreted and ret != .fun_type) return ret;
        const vals = self.scratch(StaticPool.Index, all_args.len);
        for (all_args, 0..) |a, i| {
            vals[i] = statics.retype(self, statics.h08_eval_static(self, ctx, syntax.arg_value(self.tree, a)), types.sig(self, first).params[i]);
            if (sp.holds_template(vals[i])) return .poison_type;
        }
        if (self.interpreter.depth == 0) self.interpreter.root = node;
        const r = generics.h20_instantiate(self, first, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = vals } }));
        if (sp.tag(ret) != .meta_type) self.node_value[node] = r;
        if (sp.tag(r) != .function_value) return if (sp.tag(ret) == .meta_type or ret == .poison_type) sp.type_of(r) else ret;
        self.node_decl[node] = sp.get(r).function;
        return self.decl_pool.tys()[@intFromEnum(sp.get(r).function)];
    }
    // the self argument of a method: the receiver, or the first argument when called through the type
    const off = self.decl_pool.self_off(first);
    var args = all_args;
    if (off == 1) {
        const ft = self.decl_pool.tys()[@intFromEnum(decls.real(self, first))];
        const p0 = if (ft != .none and sp.tag(ft) == .function_type) sp.get(ft).function_type.params[0] else StaticPool.Index.poison_type;
        if (recv != 0) {
            const rt = sp.apply_vars(&self.abstract_pool, self.node_type[recv]);
            const child = sp.pointee(p0);
            if (rt != .poison_type and p0 != .poison_type and rt != child and !sp.implements(rt, child) and sp.coerce(&self.abstract_pool, rt, p0) == .incompatible)
                _ = self.report(.type_mismatch, recv, rt, p0);
        } else if (args.len > 0) {
            // a method that does not write `self` takes a read only one as well
            _ = exprs.check(self, ctx, syntax.arg_value(self.tree, args[0]), if (sp.is_ptr(p0)) sp.intern(.{ .ptr_type = .{ .child = sp.pointee(p0), .mutable = false } }) else p0);
            args = args[1..];
        } else return self.report(.wrong_arity, node, 0, 1);
    }
    // argument types once, with the first candidate's parameters as expectation
    const tys = self.scratch(StaticPool.Index, args.len);
    const map = self.scratch(u32, args.len);
    const f0 = decls.real(self, first);
    const f0_ok = self.decl_pool.tys()[@intFromEnum(f0)] != .none and bind_args(self, syntax.params_of(self.tree, decls.value_node(self, f0)), args, map, false);
    for (args, 0..) |a, i| {
        const hint = if (f0_ok) types.sig(self, f0).params[map[i] + off] else .none;
        tys[i] = exprs.h09_check_expr(self, ctx, syntax.arg_value(self.tree, a), hint);
    }
    // most specific candidate: exact > coercion > unlengthed, a where clause beats none
    var best: DeclPool.Index = .none;
    var best_score: i32 = -1;
    var ambiguous = false;
    var count: u32 = 0;
    var c = first;
    while (c != .none) : (c = self.decl_pool.next_overloads()[@intFromEnum(c)]) {
        count += 1;
        const s = score(self, c, args, tys, off);
        if (s > best_score) {
            best, best_score, ambiguous = .{ c, s, false };
        } else if (s == best_score and s >= 0 and !has_where(self, decls.real(self, c)) and !has_where(self, decls.real(self, best))) ambiguous = true;
    }
    if (best == .none) {
        if (count > 1) return self.report(.no_matching_overload, node, args.len, 0);
        if (!f0_ok) return bad_args(self, node, syntax.params_of(self.tree, decls.value_node(self, f0)), args);
        for (args, 0..) |a, i| {
            const p = types.sig(self, f0).params[map[i] + off];
            _ = if (!sp.has_vars(p)) exprs.h10_expect(self, syntax.arg_value(self.tree, a), tys[i], p) else if (generics.arg_len(self, tys[i], p) == .none) self.mismatch(syntax.arg_value(self.tree, a), tys[i], p) else tys[i];
        }
        return .poison_type;
    }
    if (ambiguous) _ = self.report(.ambiguous_overload, node, best, 0);
    var callee = decls.real(self, best);
    if (off == 1 and self.decl_pool.flags()[@intFromEnum(callee)].writes) {
        const r = if (recv != 0) recv else syntax.arg_value(self.tree, all_args[0]);
        const rt = sp.apply_vars(&self.abstract_pool, self.node_type[r]);
        const place = switch (self.tree.kind(r)) {
            .identifier, .identifier_self, .member, .array_index, .dereference, .capture => true,
            else => false,
        };
        if (recv == 0) {
            if (sp.tag(rt) == .ptr_type) _ = self.report(.type_mismatch, r, rt, types.sig(self, callee).params[0]);
        } else if (sp.is_ptr(rt)) {
            places.write_access(self, r, if (sp.tag(rt) == .ptr_type) .through_ptr else .ok);
        } else if (place) places.write_access(self, r, places.writable(self, r));
    }
    const pnodes = syntax.params_of(self.tree, decls.value_node(self, callee));
    _ = bind_args(self, pnodes, args, map, false);
    check_stcwhere(self, ctx, node, callee, pnodes, args, map);
    if (generics.length_generic(self, self.decl_pool.tys()[@intFromEnum(callee)])) {
        // the argument lengths, in parameter order, pick the realization
        const lens = self.scratch(StaticPool.Index, args.len);
        var n: usize = 0;
        for (0..pnodes.len) |j| {
            const p = types.sig(self, callee).params[j + off];
            if (!generics.generic_slot(self, p)) continue;
            for (0..args.len) |i| if (map[i] == j) {
                lens[n] = if (sp.templated(p) != .none) generics.unwrapped(self, tys[i]) else if (sp.tag(p) != .meta_type) generics.arg_len(self, tys[i], p) else statics.try_static(self, ctx, syntax.arg_value(self.tree, args[i])) orelse if (ctx.interpreted) .none else return self.report(.not_static, args[i], 0, 0);
                n += 1;
            };
        }
        if (std.mem.indexOfScalar(StaticPool.Index, lens[0..n], .none) != null) {
            if (ctx.interpreted) self.node_decl[node] = callee;
            return .poison_type;
        }
        for (lens[0..n]) |l| if (l != .none and sp.tag(l) == .template_type) {
            decls.h06_check_body(self, callee);
            return types.sig(self, callee).ret;
        };
        const realized = generics.h20_instantiate(self, callee, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = lens[0..n] } }));
        if (sp.tag(realized) != .function_value) return .poison_type;
        callee = sp.get(realized).function;
        self.node_decl[node] = callee;
    } else {
        for (args, 0..) |a, i| _ = exprs.h10_expect(self, syntax.arg_value(self.tree, a), tys[i], named(self, a, types.sig(self, callee).params[map[i] + off]));
        // the call names the head of its dispatch group: the lowerer walks `next_overload` from there over the
        // overloads with the identical parameter types, tests their where clauses in order, the where-less one last
        self.node_decl[node] = decls.real(self, group_head(self, first, best));
    }
    return types.sig(self, callee).ret;
}

// stcwhere holds at every call: the callee's parameters are bound to the static arguments in a scope of their own
fn check_stcwhere(self: *Resolver, ctx: *FnCtx, node: NodeId, callee: DeclPool.Index, pnodes: []const NodeId, args: []const NodeId, map: []const u32) void {
    if (ctx.interpreted) return;
    for (pnodes) |pn| {
        if (syntax.Param.from_node(self.tree, pn).stc) break;
    } else return;
    const ft = self.decl_pool.tys()[@intFromEnum(callee)];
    const off = self.decl_pool.self_off(callee);
    const vs = self.scratch(StaticPool.Index, pnodes.len);
    @memset(vs, .none);
    const ts = self.scratch(StaticPool.Index, pnodes.len);
    @memset(ts, .none);
    for (args, 0..) |a, i| {
        vs[map[i]] = statics.try_static(self, ctx, syntax.arg_value(self.tree, a)) orelse .none;
        ts[map[i]] = self.node_type[syntax.arg_value(self.tree, a)];
    }
    decls.open_scope(self, true, .none, 0);
    defer self.scopes.h04_pop_scope();
    for (pnodes, 0..) |pn, j| {
        const pt0 = self.static_pool.get(ft).function_type.params[j + off];
        const pt = if (self.static_pool.templated(pt0) != .none and ts[j] != .none) ts[j] else pt0;
        self.decl_pool.values()[@intFromEnum(decls.h02_declare_local(self, decls.param_name(self, pn, j), pn, .static_parameter, pt))] = if (vs[j] == .none) .none else statics.retype(self, vs[j], pt);
    }
    for (pnodes) |pn| {
        const p = syntax.Param.from_node(self.tree, pn);
        if (!p.stc) continue;
        const r = statics.try_static(self, ctx, p.where) orelse {
            _ = self.report(.not_static, node, 0, 0);
            continue;
        };
        if (r == .bool_false) _ = self.report(.stcwhere_violated, node, callee, .none);
    }
}

// overloads that differ only by where clauses dispatch at runtime and need a where-less fallback
pub fn check_groups(self: *Resolver) void {
    var heads = self.scopes.globals.valueIterator();
    while (heads.next()) |h| {
        var c = h.*;
        while (c != .none) : (c = self.decl_pool.next_overloads()[@intFromEnum(c)]) {
            if (group_head(self, h.*, c) != c) continue;
            var size: u32 = 0;
            var plain: u32 = 0;
            var m = c;
            while (m != .none) : (m = self.decl_pool.next_overloads()[@intFromEnum(m)]) if (same_params(self, m, c)) {
                size += 1;
                const fallback = !dispatches(self, decls.real(self, m));
                plain += @intFromBool(fallback);
                if (fallback and plain > 1) self.doc.h21_report(.duplicate_declaration, self.decl_pool.nodes()[@intFromEnum(m)], self.decl_pool.names()[@intFromEnum(m)], c);
            };
            if (size > 1 and plain == 0) _ = self.report(.no_matching_overload, self.decl_pool.nodes()[@intFromEnum(c)], size, 0);
        }
    }
}

pub fn dispatches(self: *Resolver, d: DeclPool.Index) bool {
    for (syntax.params_of(self.tree, decls.value_node(self, d))) |pn| {
        const p = syntax.Param.from_node(self.tree, pn);
        if (p.where != 0 and p.@"else" == 0 and !p.stc) return true;
    }
    return false;
}

fn score(self: *Resolver, c: DeclPool.Index, args: []const NodeId, tys: []const StaticPool.Index, off: usize) i32 {
    const sp = &self.static_pool;
    decls.h05_ensure_signature(self, c);
    const r = decls.real(self, c);
    const ft = self.decl_pool.tys()[@intFromEnum(r)];
    if (ft == .none or sp.tag(ft) != .function_type) return -1;
    const map = self.scratch(u32, args.len);
    const pnodes = syntax.params_of(self.tree, decls.value_node(self, r));
    if (!bind_args(self, pnodes, args, map, false)) return -1;
    var total: i32 = 0;
    for (args, tys, 0..) |a, t, i| {
        const p = sp.get(ft).function_type.params[map[i] + off];
        const v = syntax.arg_value(self.tree, a);
        total += if (sp.templated(p) != .none)
            (if (generics.passes(self, t, p)) 5 else return -1)
        else if (sp.has_vars(p) and t != .poison_type)
            (if (generics.arg_len(self, t, p) != .none) 2 else return -1)
        else if (t == p or t == .poison_type or (syntax.is_literal(self.tree, v) and sp.coerce(&self.abstract_pool, statics.literal_type(self, v, p), p) == .identity))
            @as(i32, 6) - @intFromBool(sp.get_tag_prop(p).is_float and !sp.get_tag_prop(t).is_float)
        else if (sp.coerce(&self.abstract_pool, t, p) != .incompatible) 4 else return -1;
        if (syntax.Param.from_node(self.tree, pnodes[map[i]]).where != 0) total += 1;
    }
    return total;
}

pub fn has_where(self: *Resolver, d: DeclPool.Index) bool {
    for (syntax.params_of(self.tree, decls.value_node(self, d))) |pn| if (syntax.Param.from_node(self.tree, pn).where != 0) return true;
    return false;
}

// one dispatch group: the same parameter types under the same names
pub fn same_params(self: *Resolver, a0: DeclPool.Index, b0: DeclPool.Index) bool {
    const sp = &self.static_pool;
    const a = decls.real(self, a0);
    const b = decls.real(self, b0);
    const ta = self.decl_pool.tys()[@intFromEnum(a)];
    const tb = self.decl_pool.tys()[@intFromEnum(b)];
    if (ta != tb and (ta == .none or tb == .none or sp.tag(ta) != .function_type or sp.tag(tb) != .function_type or !std.mem.eql(StaticPool.Index, sp.get(ta).function_type.params, sp.get(tb).function_type.params))) return false;
    const pa = syntax.params_of(self.tree, decls.value_node(self, a));
    const pb = syntax.params_of(self.tree, decls.value_node(self, b));
    if (pa.len != pb.len) return false;
    for (pa, pb, 0..) |x, y, i| if (decls.param_name(self, x, i) != decls.param_name(self, y, i)) return false;
    return true;
}

pub fn bind_args(self: *Resolver, params: []const NodeId, args: []const NodeId, map: []u32, partial: bool) bool {
    if (args.len > params.len) return false;
    for (args, 0..) |a, i| {
        var p: usize = i;
        if (self.tree.kind(a) == .partial__fun_call_assigned_param) {
            const name = self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0));
            p = for (params, 0..) |pn, j| {
                if (decls.param_name(self, pn, j) == name) break j;
            } else return false;
        }
        if (std.mem.indexOfScalar(u32, map[0..i], @intCast(p)) != null) return false;
        map[i] = @intCast(p);
    }
    if (!partial) for (params, 0..) |pn, j| if (std.mem.indexOfScalar(u32, map[0..args.len], @intCast(j)) == null and syntax.Param.from_node(self.tree, pn).default == 0) return false;
    return true;
}

pub fn named(self: *Resolver, a: NodeId, t: StaticPool.Index) StaticPool.Index {
    if (self.tree.kind(a) == .partial__fun_call_assigned_param) self.node_type[self.tree.arg(a, 0)] = t;
    return t;
}

fn bad_args(self: *Resolver, node: NodeId, params: []const NodeId, args: []const NodeId) StaticPool.Index {
    for (args) |a| if (self.tree.kind(a) == .partial__fun_call_assigned_param) {
        const name = self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0));
        for (params, 0..) |pn, j| {
            if (decls.param_name(self, pn, j) == name) break;
        } else return self.report(.unknown_named_argument, a, name, .none);
    };
    return self.report(.wrong_arity, node, args.len, params.len);
}

// an overloaded function as a value is the overload of the expected type
pub fn overload_for(self: *Resolver, node: NodeId, d: DeclPool.Index, expected: StaticPool.Index) DeclPool.Index {
    const e = self.static_pool.apply_vars(&self.abstract_pool, expected);
    if (d == .none or e == .none or self.static_pool.tag(e) != .function_type or !self.decl_pool.kinds()[@intFromEnum(d)].is_fn()) return d;
    var c = d;
    while (c != .none) : (c = self.decl_pool.next_overloads()[@intFromEnum(c)]) if (types.decl_type(self, c) == e) {
        self.node_decl[node] = c;
        return c;
    };
    return d;
}

// `T.$init()` / `x.$deinit()` of a type that declares neither: a default value, nothing
pub fn builtin_of(self: *Resolver, callee: NodeId, pt: StaticPool.Index, t: StaticPool.Index) StaticPool.Member {
    if (pt == .none or pt == .poison_type or t == .none) return .none;
    return self.static_pool.lookup_member(if (self.static_pool.tag(pt) == .meta_type) t else self.static_pool.deref(&self.abstract_pool, pt), self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(callee, 1)));
}

pub fn group_head(self: *Resolver, first: DeclPool.Index, d: DeclPool.Index) DeclPool.Index {
    var h = first;
    while (h != d and !same_params(self, h, d)) h = self.decl_pool.next_overloads()[@intFromEnum(h)];
    return h;
}

pub fn field_of(self: *Resolver, rec: StaticPool.Index, a: NodeId, i: usize) ?u32 {
    if (self.tree.kind(a) != .partial__fun_call_assigned_param) return @intCast(i);
    return switch (self.static_pool.lookup_member(rec, self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(a, 0)))) {
        .field => |f| f.index,
        else => null,
    };
}
