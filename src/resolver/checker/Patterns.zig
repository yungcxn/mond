const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// match: arms, patterns and their binders, exhaustiveness and redundancy
const Patterns = @This();

pub fn res(self: *Patterns) *Resolver {
    return @alignCast(@fieldParentPtr("patterns", self));
}

pub fn check_match(self: *Patterns, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const arms = r.tree.manychildren(r.tree.arg(node, 1));
    const st = r.static_pool.deref(&r.abstract_pool, r.exprs.infer(ctx, r.tree.arg(node, 0), .none));
    const is_stc = r.tree.kind(node) == .stcmatch and !ctx.interpreted and !ctx.abstract;
    for (arms) |arm| r.node_value[arm] = .none;
    const known = if (ctx.interpreted or ctx.abstract and r.tree.kind(node) == .stcmatch) r.statics.try_static(ctx, r.tree.arg(node, 0)) else null;
    // stcmatch needs a static scrutinee, only the matching arm is checked, like any match on a known value in a stcfun
    if (is_stc or known != null) {
        const v = known orelse r.interpreter.eval_static(ctx, r.tree.arg(node, 0));
        if (v == .poison_type) return v;
        r.scopes.push();
        defer r.scopes.pop();
        for (arms) |arm| if (r.interpreter.static_match(ctx, r.tree.arg(arm, 0), v)) {
            r.node_value[arm] = .bool_true;
            return r.flow.branch(ctx, r.tree.arg(arm, 1), expected);
        };
        return r.report(.non_exhaustive_match, node, v, .none);
    }
    var quiet = r.generics.opened(ctx);
    var catch_all = false;
    var result: StaticPool.Index = .none;
    const m = r.inits.count;
    defer r.inits.release(m);
    const before = r.inits.save(0);
    const after = r.inits.new();
    defer r.inits.copy(0, after);
    var rows: std.ArrayList(NodeId) = .empty;
    defer rows.deinit(r.alloc);
    for (arms) |arm| rows.append(r.alloc, r.tree.arg(arm, 0)) catch @panic("OOM");
    var settled = arms.len;
    for (arms, 0..) |arm, i| {
        if (settled == arms.len and r.static_pool.concrete(&r.abstract_pool, expected)) settled = i;
        r.inits.copy(0, before);
        r.scopes.push();
        const mark = r.doc.diagnostics.len();
        const pat = self.pattern(ctx, r.tree.arg(arm, 0), st);
        quiet = quiet or r.doc.errors_since(r.tree, mark, arm);
        if (!quiet and st != .poison_type and self.covers(ctx, &.{st}, rows.items[0..i], i, rows.items[i..][0..1])) r.doc.report(.redundant_match_arm, arm, 0, 0);
        catch_all = catch_all or pat;
        const t = r.flow.branch(ctx, r.tree.arg(arm, 1), expected);
        if (t != .never_type) r.inits.merge(after, 0);
        r.scopes.pop();
        result = r.flow.merge(arm, result, if (!r.static_pool.concrete(&r.abstract_pool, expected) and r.tree.is_literal(r.tree.arg(arm, 1))) .never_type else t, expected);
    }
    if (!r.static_pool.concrete(&r.abstract_pool, expected) and (result == .none or result == .never_type)) {
        const bodies = r.scratch(NodeId, arms.len);
        for (arms, 0..) |arm, i| bodies[i] = r.tree.arg(arm, 1);
        const lt = r.flow.literals_type(bodies);
        if (lt != .none) result = lt;
    }
    if (!r.static_pool.concrete(&r.abstract_pool, expected)) for (arms) |arm| if (r.tree.is_literal(r.tree.arg(arm, 1))) {
        result = r.flow.merge(arm, result, r.flow.adapt(r.tree.arg(arm, 1), r.node_type[r.tree.arg(arm, 1)], result), expected);
    };
    if (r.static_pool.concrete(&r.abstract_pool, expected)) for (arms[0..settled]) |arm| {
        _ = r.flow.settle(r.tree.arg(arm, 1), r.static_pool.apply_vars(&r.abstract_pool, r.node_type[r.tree.arg(arm, 1)]), expected);
    };
    if (!catch_all and st != .poison_type and !self.covers(ctx, &.{st}, rows.items, arms.len, &.{0}))
        _ = r.report(.non_exhaustive_match, node, st, .none);
    return if (result == .none) .unit_type else result;
}

// whether the pattern takes every value of its type
fn pattern(self: *Patterns, ctx: *FnCtx, p: NodeId, st: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    switch (r.tree.kind(p)) {
        .identifier => {
            const name = r.name_pool.name_of(p);
            r.decls.redeclared(name, p);
            if (name != .underscore) r.node_decl[p] = r.decls.declare_local(name, p, .pattern_binder, st);
            _ = r.set(p, st);
            return true;
        },
        .partial__match_case_pattern_or => {
            // every alternative binds the same names, sharing the declarations of the first one
            var got = false;
            const names = &r.scopes.names;
            const from = names.head;
            var first = from;
            for (r.tree.manychildren(p), 0..) |alt, i| {
                if (i > 0) r.scopes.push();
                const mark = names.head;
                const s = self.pattern(ctx, alt, st);
                got = got or s;
                if (i == 0) {
                    first = names.head;
                    continue;
                }
                for (names.buf[from..first]) |n| if (std.mem.indexOfScalar(NamePool.Index, names.buf[mark..names.head], n) == null) r.doc.report(.undefined_name, alt, n, 0);
                for (mark..names.head) |j| {
                    const id = r.decl_pool.get_node(r.scopes.decls.buf[j]);
                    const k = std.mem.indexOfScalar(NamePool.Index, names.buf[from..first], names.buf[j]) orelse {
                        r.doc.report(.undefined_name, id, names.buf[j], 0);
                        continue;
                    };
                    r.node_decl[id] = r.scopes.decls.buf[from + k];
                    const t = r.decl_pool.get_ty(r.node_decl[id]);
                    if (r.node_type[id] != t and r.node_type[id] != .poison_type and t != .poison_type) _ = r.report(.type_mismatch, id, r.node_type[id], t);
                }
                r.scopes.pop();
            }
            return got;
        },
        .partial__match_case_pattern_typecast => {
            const t = r.types.realized_type(ctx, r.tree.arg(p, 0));
            const v = r.tree.arg(p, 1);
            r.decls.redeclared(r.name_pool.name_of(v), v);
            r.node_decl[v] = r.decls.declare_local(r.name_pool.name_of(v), v, .pattern_binder, t);
            _ = r.set(v, t);
            const widen = t == st or t == .poison_type or st == .poison_type or sp.coerce(&r.abstract_pool, st, t) != .incompatible;
            const narrow = switch (sp.tag(st)) {
                .variant_type, .variant_union_type, .trait_type => sp.coerce(&r.abstract_pool, t, st) != .incompatible,
                else => false,
            };
            if (!widen and !narrow and !r.generics.sibling(ctx, t, st)) _ = r.report(.type_mismatch, p, t, st);
            return widen;
        },
        .labelarrow => {
            const got = self.pattern(ctx, r.tree.arg(p, 0), st);
            const ct = r.node_type[r.tree.arg(p, 0)];
            const pt = sp.payload_of(&r.abstract_pool, ct);
            r.flow.bind_label(r.tree.arg(p, 1), if (pt == .none) ct else pt);
            return got;
        },
        .fun_call => {
            const callee = r.tree.arg(p, 0);
            const ct = r.exprs.infer(ctx, callee, .none);
            const target = r.set(p, if (sp.tag(ct) == .meta_type) r.interpreter.eval_static(ctx, callee) else ct);
            if (target == .poison_type) { // binders still exist, as poison
                for (r.tree.manychildren(r.tree.arg(p, 1))) |a| _ = self.pattern(ctx, r.tree.arg_value(a), target);
                return false;
            }
            if (target != st and sp.coerce(&r.abstract_pool, target, st) == .incompatible and !r.generics.sibling(ctx, target, st)) _ = r.report(.type_mismatch, p, target, st);
            const is_case = sp.tag(target) == .variant_case_type;
            const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
            const args = r.tree.manychildren(r.tree.arg(p, 1));
            const map = r.scratch(u32, args.len);
            if (rec == .none or sp.tag(rec) != .record_type or !r.calls.bind_args(r.types.fields_of(rec), args, map, true)) {
                if (args.len > 0) _ = r.report(.wrong_arity, p, args.len, 0);
                return false;
            }
            var all = true;
            for (args, 0..) |a, i| all = self.pattern(ctx, r.tree.arg_value(a), r.calls.named(a, sp.field_type(rec, map[i]))) and all;
            return !is_case and all;
        },
        else => { // literals, ranges and constant paths (`Toggle.On`)
            const t = r.exprs.infer(ctx, p, st);
            if (r.tree.props(p).range) {
                const e = sp.apply_vars(&r.abstract_pool, t);
                if (t != .poison_type and st != .poison_type and sp.get(e) == .array_type and sp.coerce(&r.abstract_pool, sp.get(e).array_type.elem, st) == .incompatible) _ = r.report(.type_mismatch, p, sp.get(e).array_type.elem, st);
                return false;
            }
            if (!r.generics.sibling(ctx, t, st)) _ = r.exprs.expect(p, t, st);
            return false;
        },
    }
}

// whether the rows cover the pattern vector `q` (0 is a wildcard): exhaustiveness asks it for wildcards, redundancy for an arm,
// rows of patterns over columns of types, a column splits by the constructors of its type: bools, variant cases with their
// payload fields, the fields of a record, the integer segments between the pattern bounds; any other type by wildcards only
fn covers(self: *Patterns, ctx: *FnCtx, cols: []const StaticPool.Index, rows: []const NodeId, n: usize, q: []const NodeId) bool {
    const r = self.res();
    if (n == 0) return false;
    if (cols.len == 0) return true;
    const sp = &r.static_pool;
    const w = cols.len;
    const t = cols[0];
    var qs: std.ArrayList(NodeId) = .empty;
    defer qs.deinit(r.alloc);
    self.spread(q, q[0], t, &qs);
    if (qs.items.len > w) {
        for (0..qs.items.len / w) |ri| if (!self.covers(ctx, cols, rows, n, qs.items[ri * w ..][0..w])) return false;
        return true;
    }
    const p = qs.items[0];
    var flat: std.ArrayList(NodeId) = .empty;
    defer flat.deinit(r.alloc);
    for (0..n) |ri| self.spread(rows[ri * w ..][0..w], rows[ri * w], t, &flat);
    var next: std.ArrayList(NodeId) = .empty;
    defer next.deinit(r.alloc);
    var nq: std.ArrayList(NodeId) = .empty;
    defer nq.deinit(r.alloc);
    if (t == .bool_type) {
        for ([_]StaticPool.Index{ .bool_true, .bool_false }) |k| {
            nq.clearRetainingCapacity();
            if (self.specialize(qs.items, w, k, &.{}, &nq) == 0) continue;
            next.clearRetainingCapacity();
            const m = self.specialize(flat.items, w, k, &.{}, &next);
            if (!self.covers(ctx, cols[1..], next.items, m, nq.items)) return false;
        }
        return true;
    }
    switch (sp.tag(t)) {
        .variant_type, .variant_union_type, .record_type => {
            const ms = if (sp.tag(t) == .variant_union_type) sp.get(t).variant_union_type.len else 1;
            var nk: usize = 0;
            for (0..ms) |mi| nk += if (sp.tag(t) == .variant_union_type) sp.get(sp.get(t).variant_union_type[mi]).variant_type.cases.len else if (sp.tag(t) == .variant_type) sp.get(t).variant_type.cases.len else 1;
            const ks = r.scratch(StaticPool.Index, nk);
            nk = 0;
            for (0..ms) |mi| {
                const mv = if (sp.tag(t) == .variant_union_type) sp.get(t).variant_union_type[mi] else t;
                for (0..if (sp.tag(mv) == .record_type) 1 else sp.get(mv).variant_type.cases.len) |ci| {
                    ks[nk] = if (sp.tag(mv) == .record_type) mv else sp.get(mv).variant_type.cases[ci];
                    nk += 1;
                }
            }
            for (ks) |k| {
                const rec = if (sp.tag(k) == .variant_case_type) sp.get(k).variant_case_type.payload else k;
                const fields = if (rec == .none) &[_]NodeId{} else r.types.fields_of(rec);
                nq.clearRetainingCapacity();
                if (self.specialize(qs.items, w, k, fields, &nq) == 0) continue;
                const tys = r.scratch(StaticPool.Index, fields.len + w - 1);
                for (0..fields.len) |i| tys[i] = sp.field_type(rec, i);
                @memcpy(tys[fields.len..][0 .. w - 1], cols[1..]);
                next.clearRetainingCapacity();
                const m = self.specialize(flat.items, w, k, fields, &next);
                if (!self.covers(ctx, tys, next.items, m, nq.items)) return false;
            }
            return true;
        },
        .int_type => {
            const it = sp.get(t).int_type;
            const bits: u7 = @intCast(it.bits);
            const one: i128 = 1;
            const min: i128 = if (it.signedness == .signed) -(one << (bits - 1)) else 0;
            const max: i128 = if (it.signedness == .signed) (one << (bits - 1)) - 1 else (one << bits) - 1;
            const qi = if (p == 0) null else self.interval(ctx, p) orelse return false;
            var cuts: std.ArrayList(i128) = .empty;
            defer cuts.deinit(r.alloc);
            cuts.append(r.alloc, min) catch @panic("OOM");
            if (qi) |iv| cuts.appendSlice(r.alloc, &.{ iv[0], iv[1] +| 1 }) catch @panic("OOM");
            for (0..flat.items.len / w) |ri| if (flat.items[ri * w] != 0) if (self.interval(ctx, flat.items[ri * w])) |iv| {
                cuts.appendSlice(r.alloc, &.{ iv[0], iv[1] +| 1 }) catch @panic("OOM");
            };
            std.mem.sort(i128, cuts.items, {}, std.sort.asc(i128));
            for (cuts.items, 0..) |lo, ci| {
                if (lo < min or lo > max or ci > 0 and cuts.items[ci - 1] == lo) continue;
                var hi = max;
                for (cuts.items[ci..]) |c| if (c > lo) {
                    hi = @min(c - 1, max);
                    break;
                };
                if (qi) |iv| if (lo < iv[0] or hi > iv[1]) continue;
                next.clearRetainingCapacity();
                var m: usize = 0;
                for (0..flat.items.len / w) |ri| {
                    const rp = flat.items[ri * w];
                    const iv = if (rp == 0) null else self.interval(ctx, rp);
                    if (rp != 0 and (iv == null or iv.?[0] > lo or iv.?[1] < hi)) continue;
                    next.appendSlice(r.alloc, flat.items[ri * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
                    m += 1;
                }
                if (!self.covers(ctx, cols[1..], next.items, m, qs.items[1..w])) return false;
            }
            return true;
        },
        else => {
            var m: usize = 0;
            for (0..flat.items.len / w) |ri| if (flat.items[ri * w] == 0) {
                next.appendSlice(r.alloc, flat.items[ri * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
                m += 1;
            };
            return self.covers(ctx, cols[1..], next.items, m, qs.items[1..w]);
        },
    }
}

// a row with its first pattern normalized: binders and widening type patterns are wildcards, alternatives are rows of their own
fn spread(self: *Patterns, row: []const NodeId, p0: NodeId, t: StaticPool.Index, out: *std.ArrayList(NodeId)) void {
    const r = self.res();
    var p = p0;
    while (p != 0) switch (r.tree.kind(p)) {
        .capture, .labelarrow => p = r.tree.arg(p, 0),
        .identifier => p = 0,
        .partial__match_case_pattern_or => return for (r.tree.manychildren(p)) |alt| self.spread(row, alt, t, out),
        .partial__match_case_pattern_typecast => {
            const x = r.node_type[r.tree.arg(p, 1)];
            if (x == t or x == .poison_type or r.static_pool.coerce(&r.abstract_pool, t, x) != .incompatible) p = 0 else break;
        },
        else => break,
    };
    out.append(r.alloc, p) catch @panic("OOM");
    out.appendSlice(r.alloc, row[1..]) catch @panic("OOM");
}

// the rows of constructor k (a case, a record or a bool), the first column replaced by the patterns of its fields
fn specialize(self: *Patterns, rows: []const NodeId, w: usize, k: StaticPool.Index, fields: []const NodeId, out: *std.ArrayList(NodeId)) usize {
    const r = self.res();
    const sp = &r.static_pool;
    var n: usize = 0;
    for (0..rows.len / w) |ri| {
        const p = rows[ri * w];
        const pt = if (p == 0) .none else if (r.tree.kind(p) == .partial__match_case_pattern_typecast) r.node_type[r.tree.arg(p, 1)] else r.node_type[p];
        const hit = p == 0 or switch (sp.tag(k)) {
            .variant_case_type => pt == sp.get(k).variant_case_type.variant or self.same(pt, k),
            .record_type => self.same(pt, k),
            else => r.tree.kind(p) == (if (k == .bool_true) ParseTree.Node.Kind.boolean_true else ParseTree.Node.Kind.boolean_false),
        };
        if (!hit) continue;
        const at = out.items.len;
        out.appendNTimes(r.alloc, 0, fields.len) catch @panic("OOM");
        const args = if (p != 0 and r.tree.kind(p) == .fun_call) r.tree.manychildren(r.tree.arg(p, 1)) else &[_]NodeId{};
        const map = r.scratch(u32, args.len);
        if (r.calls.bind_args(fields, args, map, true)) for (args, 0..) |a, i| {
            out.items[at + map[i]] = r.tree.arg_value(a);
        };
        out.appendSlice(r.alloc, rows[ri * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
        n += 1;
    }
    return n;
}

// a constructor of another realization of the same template stands for this one
fn same(self: *Patterns, a: StaticPool.Index, b: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    if (a == b) return true;
    if (a == .none or sp.tag(a) != sp.tag(b)) return false;
    const g = r.generics.source_of(a);
    return g != .none and g == r.generics.source_of(b) and (sp.tag(a) != .variant_case_type or sp.get(a).variant_case_type.case == sp.get(b).variant_case_type.case);
}

// the integer values a literal or range pattern covers, as a closed interval
fn interval(self: *Patterns, ctx: *FnCtx, p: NodeId) ?[2]i128 {
    const r = self.res();
    if (!r.tree.props(p).range) {
        const v = r.statics.static_int(ctx, p) orelse return null;
        return .{ v, v };
    }
    const g = ParseTree.Range.from_node(r.tree, p);
    const lo = if (g.lo == 0) std.math.minInt(i128) else r.statics.static_int(ctx, g.lo) orelse return null;
    const hi = if (g.hi == 0) std.math.maxInt(i128) else (r.statics.static_int(ctx, g.hi) orelse return null) - @intFromBool(!g.incl);
    return .{ lo, hi };
}
