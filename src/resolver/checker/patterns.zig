const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const decls = @import("decls.zig");
const exprs = @import("exprs.zig");
const types = @import("types.zig");
const calls = @import("calls.zig");
const control = @import("control.zig");
const generics = @import("generics.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// match: arms, patterns and their binders, exhaustiveness and redundancy

pub fn h14_check_match(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const arms = self.tree.manychildren(self.tree.arg(node, 1));
    const st = self.static_pool.deref(&self.abstract_pool, exprs.h09_check_expr(self, ctx, self.tree.arg(node, 0), .none));
    const is_stc = self.tree.kind(node) == .stcmatch and !ctx.interpreted and !ctx.abstract;
    for (arms) |arm| self.node_value[arm] = .none;
    const known = if (ctx.interpreted or ctx.abstract and self.tree.kind(node) == .stcmatch) statics.try_static(self, ctx, self.tree.arg(node, 0)) else null;
    // stcmatch needs a static scrutinee, only the matching arm is checked, like any match on a known value in a stcfun
    if (is_stc or known != null) {
        const v = known orelse statics.h08_eval_static(self, ctx, self.tree.arg(node, 0));
        if (v == .poison_type) return v;
        self.scopes.h03_push_scope();
        defer self.scopes.h04_pop_scope();
        for (arms) |arm| if (self.interpreter.static_match(ctx, self.tree.arg(arm, 0), v)) {
            self.node_value[arm] = .bool_true;
            return control.branch(self, ctx, self.tree.arg(arm, 1), expected);
        };
        return self.report(.non_exhaustive_match, node, v, .none);
    }
    var quiet = generics.opened(self, ctx);
    var catch_all = false;
    var result: StaticPool.Index = .none;
    const m = self.inits.count;
    defer self.inits.release(m);
    const before = self.inits.save(0);
    const after = self.inits.new();
    defer self.inits.copy(0, after);
    var rows: std.ArrayList(NodeId) = .empty;
    defer rows.deinit(self.alloc);
    for (arms) |arm| rows.append(self.alloc, self.tree.arg(arm, 0)) catch @panic("OOM");
    var settled = arms.len;
    for (arms, 0..) |arm, i| {
        if (settled == arms.len and self.static_pool.concrete(&self.abstract_pool, expected)) settled = i;
        self.inits.copy(0, before);
        self.scopes.h03_push_scope();
        const mark = self.doc.diagnostics.len();
        const pat = pattern(self, ctx, self.tree.arg(arm, 0), st);
        quiet = quiet or self.doc.errors_since(self.tree, mark, arm);
        if (!quiet and st != .poison_type and covers(self, ctx, &.{st}, rows.items[0..i], i, rows.items[i..][0..1])) self.doc.h21_report(.redundant_match_arm, arm, 0, 0);
        catch_all = catch_all or pat;
        const t = control.branch(self, ctx, self.tree.arg(arm, 1), expected);
        if (t != .never_type) self.inits.merge(after, 0);
        self.scopes.h04_pop_scope();
        result = control.merge(self, arm, result, if (!self.static_pool.concrete(&self.abstract_pool, expected) and syntax.is_literal(self.tree, self.tree.arg(arm, 1))) .never_type else t, expected);
    }
    if (!self.static_pool.concrete(&self.abstract_pool, expected) and (result == .none or result == .never_type)) {
        const bodies = self.scratch(NodeId, arms.len);
        for (arms, 0..) |arm, i| bodies[i] = self.tree.arg(arm, 1);
        const lt = control.literals_type(self, bodies);
        if (lt != .none) result = lt;
    }
    if (!self.static_pool.concrete(&self.abstract_pool, expected)) for (arms) |arm| if (syntax.is_literal(self.tree, self.tree.arg(arm, 1))) {
        result = control.merge(self, arm, result, control.adapt(self, self.tree.arg(arm, 1), self.node_type[self.tree.arg(arm, 1)], result), expected);
    };
    if (self.static_pool.concrete(&self.abstract_pool, expected)) for (arms[0..settled]) |arm| {
        _ = control.settle(self, self.tree.arg(arm, 1), self.static_pool.apply_vars(&self.abstract_pool, self.node_type[self.tree.arg(arm, 1)]), expected);
    };
    if (!catch_all and st != .poison_type and !covers(self, ctx, &.{st}, rows.items, arms.len, &.{0}))
        _ = self.report(.non_exhaustive_match, node, st, .none);
    return if (result == .none) .unit_type else result;
}

// whether the pattern takes every value of its type
fn pattern(self: *Resolver, ctx: *FnCtx, p: NodeId, st: StaticPool.Index) bool {
    const sp = &self.static_pool;
    switch (self.tree.kind(p)) {
        .identifier => {
            const name = self.name_pool.name_of(self.tree, self.src_bytes, p);
            decls.redeclared(self, name, p);
            if (name != .underscore) self.node_decl[p] = decls.h02_declare_local(self, name, p, .pattern_binder, st);
            _ = self.set(p, st);
            return true;
        },
        .partial__match_case_pattern_or => {
            // every alternative binds the same names, sharing the declarations of the first one
            var r = false;
            const names = &self.scopes.names;
            const from = names.head;
            var first = from;
            for (self.tree.manychildren(p), 0..) |alt, i| {
                if (i > 0) self.scopes.h03_push_scope();
                const mark = names.head;
                const s = pattern(self, ctx, alt, st);
                r = r or s;
                if (i == 0) {
                    first = names.head;
                    continue;
                }
                for (names.buf[from..first]) |n| if (std.mem.indexOfScalar(NamePool.Index, names.buf[mark..names.head], n) == null) self.doc.h21_report(.undefined_name, alt, n, 0);
                for (mark..names.head) |j| {
                    const id = self.decl_pool.nodes()[@intFromEnum(self.scopes.decls.buf[j])];
                    const k = std.mem.indexOfScalar(NamePool.Index, names.buf[from..first], names.buf[j]) orelse {
                        self.doc.h21_report(.undefined_name, id, names.buf[j], 0);
                        continue;
                    };
                    self.node_decl[id] = self.scopes.decls.buf[from + k];
                    const t = self.decl_pool.tys()[@intFromEnum(self.node_decl[id])];
                    if (self.node_type[id] != t and self.node_type[id] != .poison_type and t != .poison_type) _ = self.report(.type_mismatch, id, self.node_type[id], t);
                }
                self.scopes.h04_pop_scope();
            }
            return r;
        },
        .partial__match_case_pattern_typecast => {
            const t = types.realized_type(self, ctx, self.tree.arg(p, 0));
            const v = self.tree.arg(p, 1);
            decls.redeclared(self, self.name_pool.name_of(self.tree, self.src_bytes, v), v);
            self.node_decl[v] = decls.h02_declare_local(self, self.name_pool.name_of(self.tree, self.src_bytes, v), v, .pattern_binder, t);
            _ = self.set(v, t);
            const widen = t == st or t == .poison_type or st == .poison_type or sp.coerce(&self.abstract_pool, st, t) != .incompatible;
            const narrow = switch (sp.tag(st)) {
                .variant_type, .variant_union_type, .trait_type => sp.coerce(&self.abstract_pool, t, st) != .incompatible,
                else => false,
            };
            if (!widen and !narrow and !generics.sibling(self, ctx, t, st)) _ = self.report(.type_mismatch, p, t, st);
            return widen;
        },
        .labelarrow => {
            const r = pattern(self, ctx, self.tree.arg(p, 0), st);
            const ct = self.node_type[self.tree.arg(p, 0)];
            const pt = control.payload_of(self, ct);
            control.bind_label(self, self.tree.arg(p, 1), if (pt == .none) ct else pt);
            return r;
        },
        .fun_call => {
            const callee = self.tree.arg(p, 0);
            const ct = exprs.h09_check_expr(self, ctx, callee, .none);
            const target = self.set(p, if (sp.tag(ct) == .meta_type) statics.h08_eval_static(self, ctx, callee) else ct);
            if (target == .poison_type) { // binders still exist, as poison
                for (self.tree.manychildren(self.tree.arg(p, 1))) |a| _ = pattern(self, ctx, syntax.arg_value(self.tree, a), target);
                return false;
            }
            if (target != st and sp.coerce(&self.abstract_pool, target, st) == .incompatible and !generics.sibling(self, ctx, target, st)) _ = self.report(.type_mismatch, p, target, st);
            const is_case = sp.tag(target) == .variant_case_type;
            const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
            const args = self.tree.manychildren(self.tree.arg(p, 1));
            const map = self.scratch(u32, args.len);
            if (rec == .none or sp.tag(rec) != .record_type or !calls.bind_args(self, types.fields_of(self, rec), args, map, true)) {
                if (args.len > 0) _ = self.report(.wrong_arity, p, args.len, 0);
                return false;
            }
            var all = true;
            for (args, 0..) |a, i| all = pattern(self, ctx, syntax.arg_value(self.tree, a), calls.named(self, a, sp.get(rec).custom_type.field_types[map[i]])) and all;
            return !is_case and all;
        },
        else => { // literals, ranges and constant paths (`Toggle.On`)
            const t = exprs.h09_check_expr(self, ctx, p, st);
            if (syntax.props(self.tree.kind(p)).range) {
                const e = sp.apply_vars(&self.abstract_pool, t);
                if (t != .poison_type and st != .poison_type and sp.get(e) == .array_type and sp.coerce(&self.abstract_pool, sp.get(e).array_type.elem, st) == .incompatible) _ = self.report(.type_mismatch, p, sp.get(e).array_type.elem, st);
                return false;
            }
            if (!generics.sibling(self, ctx, t, st)) _ = exprs.h10_expect(self, p, t, st);
            return false;
        },
    }
}

// whether the rows cover the pattern vector `q` (0 is a wildcard): exhaustiveness asks it for wildcards, redundancy for an arm,
// rows of patterns over columns of types, a column splits by the constructors of its type: bools, variant cases with their
// payload fields, the fields of a record, the integer segments between the pattern bounds; any other type by wildcards only
fn covers(self: *Resolver, ctx: *FnCtx, cols: []const StaticPool.Index, rows: []const NodeId, n: usize, q: []const NodeId) bool {
    if (n == 0) return false;
    if (cols.len == 0) return true;
    const sp = &self.static_pool;
    const w = cols.len;
    const t = cols[0];
    var qs: std.ArrayList(NodeId) = .empty;
    defer qs.deinit(self.alloc);
    spread(self, q, q[0], t, &qs);
    if (qs.items.len > w) {
        for (0..qs.items.len / w) |r| if (!covers(self, ctx, cols, rows, n, qs.items[r * w ..][0..w])) return false;
        return true;
    }
    const p = qs.items[0];
    var flat: std.ArrayList(NodeId) = .empty;
    defer flat.deinit(self.alloc);
    for (0..n) |r| spread(self, rows[r * w ..][0..w], rows[r * w], t, &flat);
    var next: std.ArrayList(NodeId) = .empty;
    defer next.deinit(self.alloc);
    var nq: std.ArrayList(NodeId) = .empty;
    defer nq.deinit(self.alloc);
    if (t == .bool_type) {
        for ([_]StaticPool.Index{ .bool_true, .bool_false }) |k| {
            nq.clearRetainingCapacity();
            if (specialize(self, qs.items, w, k, &.{}, &nq) == 0) continue;
            next.clearRetainingCapacity();
            const m = specialize(self, flat.items, w, k, &.{}, &next);
            if (!covers(self, ctx, cols[1..], next.items, m, nq.items)) return false;
        }
        return true;
    }
    switch (sp.tag(t)) {
        .variant_type, .variant_union_type, .record_type => {
            const ms = if (sp.tag(t) == .variant_union_type) sp.get(t).variant_union_type.len else 1;
            var nk: usize = 0;
            for (0..ms) |mi| nk += if (sp.tag(t) == .variant_union_type) sp.get(sp.get(t).variant_union_type[mi]).variant_type.cases.len else if (sp.tag(t) == .variant_type) sp.get(t).variant_type.cases.len else 1;
            const ks = self.scratch(StaticPool.Index, nk);
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
                const fields = if (rec == .none) &[_]NodeId{} else types.fields_of(self, rec);
                nq.clearRetainingCapacity();
                if (specialize(self, qs.items, w, k, fields, &nq) == 0) continue;
                const tys = self.scratch(StaticPool.Index, fields.len + w - 1);
                for (0..fields.len) |i| tys[i] = sp.get(rec).custom_type.field_types[i];
                @memcpy(tys[fields.len..][0 .. w - 1], cols[1..]);
                next.clearRetainingCapacity();
                const m = specialize(self, flat.items, w, k, fields, &next);
                if (!covers(self, ctx, tys, next.items, m, nq.items)) return false;
            }
            return true;
        },
        .int_type => {
            const it = sp.get(t).int_type;
            const bits: u7 = @intCast(it.bits);
            const one: i128 = 1;
            const min: i128 = if (it.signedness == .signed) -(one << (bits - 1)) else 0;
            const max: i128 = if (it.signedness == .signed) (one << (bits - 1)) - 1 else (one << bits) - 1;
            const qi = if (p == 0) null else interval(self, ctx, p) orelse return false;
            var cuts: std.ArrayList(i128) = .empty;
            defer cuts.deinit(self.alloc);
            cuts.append(self.alloc, min) catch @panic("OOM");
            if (qi) |iv| cuts.appendSlice(self.alloc, &.{ iv[0], iv[1] +| 1 }) catch @panic("OOM");
            for (0..flat.items.len / w) |r| if (flat.items[r * w] != 0) if (interval(self, ctx, flat.items[r * w])) |iv| {
                cuts.appendSlice(self.alloc, &.{ iv[0], iv[1] +| 1 }) catch @panic("OOM");
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
                for (0..flat.items.len / w) |r| {
                    const rp = flat.items[r * w];
                    const iv = if (rp == 0) null else interval(self, ctx, rp);
                    if (rp != 0 and (iv == null or iv.?[0] > lo or iv.?[1] < hi)) continue;
                    next.appendSlice(self.alloc, flat.items[r * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
                    m += 1;
                }
                if (!covers(self, ctx, cols[1..], next.items, m, qs.items[1..w])) return false;
            }
            return true;
        },
        else => {
            var m: usize = 0;
            for (0..flat.items.len / w) |r| if (flat.items[r * w] == 0) {
                next.appendSlice(self.alloc, flat.items[r * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
                m += 1;
            };
            return covers(self, ctx, cols[1..], next.items, m, qs.items[1..w]);
        },
    }
}

// a row with its first pattern normalized: binders and widening type patterns are wildcards, alternatives are rows of their own
fn spread(self: *Resolver, row: []const NodeId, p0: NodeId, t: StaticPool.Index, out: *std.ArrayList(NodeId)) void {
    var p = p0;
    while (p != 0) switch (self.tree.kind(p)) {
        .capture, .labelarrow => p = self.tree.arg(p, 0),
        .identifier => p = 0,
        .partial__match_case_pattern_or => return for (self.tree.manychildren(p)) |alt| spread(self, row, alt, t, out),
        .partial__match_case_pattern_typecast => {
            const x = self.node_type[self.tree.arg(p, 1)];
            if (x == t or x == .poison_type or self.static_pool.coerce(&self.abstract_pool, t, x) != .incompatible) p = 0 else break;
        },
        else => break,
    };
    out.append(self.alloc, p) catch @panic("OOM");
    out.appendSlice(self.alloc, row[1..]) catch @panic("OOM");
}

// the rows of constructor k (a case, a record or a bool), the first column replaced by the patterns of its fields
fn specialize(self: *Resolver, rows: []const NodeId, w: usize, k: StaticPool.Index, fields: []const NodeId, out: *std.ArrayList(NodeId)) usize {
    const sp = &self.static_pool;
    var n: usize = 0;
    for (0..rows.len / w) |r| {
        const p = rows[r * w];
        const pt = if (p == 0) .none else if (self.tree.kind(p) == .partial__match_case_pattern_typecast) self.node_type[self.tree.arg(p, 1)] else self.node_type[p];
        const hit = p == 0 or switch (sp.tag(k)) {
            .variant_case_type => pt == sp.get(k).variant_case_type.variant or same(self, pt, k),
            .record_type => same(self, pt, k),
            else => self.tree.kind(p) == (if (k == .bool_true) ParseTree.Node.Kind.boolean_true else ParseTree.Node.Kind.boolean_false),
        };
        if (!hit) continue;
        const at = out.items.len;
        out.appendNTimes(self.alloc, 0, fields.len) catch @panic("OOM");
        const args = if (p != 0 and self.tree.kind(p) == .fun_call) self.tree.manychildren(self.tree.arg(p, 1)) else &[_]NodeId{};
        const map = self.scratch(u32, args.len);
        if (calls.bind_args(self, fields, args, map, true)) for (args, 0..) |a, i| {
            out.items[at + map[i]] = syntax.arg_value(self.tree, a);
        };
        out.appendSlice(self.alloc, rows[r * w + 1 ..][0 .. w - 1]) catch @panic("OOM");
        n += 1;
    }
    return n;
}

// a constructor of another realization of the same template stands for this one
fn same(self: *Resolver, a: StaticPool.Index, b: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (a == b) return true;
    if (a == .none or sp.tag(a) != sp.tag(b)) return false;
    const g = generics.source_of(self, a);
    return g != .none and g == generics.source_of(self, b) and (sp.tag(a) != .variant_case_type or sp.get(a).variant_case_type.case == sp.get(b).variant_case_type.case);
}

// the integer values a literal or range pattern covers, as a closed interval
fn interval(self: *Resolver, ctx: *FnCtx, p: NodeId) ?[2]i128 {
    if (!syntax.props(self.tree.kind(p)).range) {
        const v = statics.static_int(self, ctx, p) orelse return null;
        return .{ v, v };
    }
    const g = syntax.Range.from_node(self.tree, p);
    const lo = if (g.lo == 0) std.math.minInt(i128) else statics.static_int(self, ctx, g.lo) orelse return null;
    const hi = if (g.hi == 0) std.math.maxInt(i128) else (statics.static_int(self, ctx, g.hi) orelse return null) - @intFromBool(!g.incl);
    return .{ lo, hi };
}
