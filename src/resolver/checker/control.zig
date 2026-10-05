const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const calls = @import("calls.zig");
const statics = @import("statics.zig");
const types = @import("types.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const is_range_kind = Resolver.is_range_kind;

pub fn h14_check_match(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const arms = self.tree.manychildren(self.tree.arg(node, 1));
    const st = self.deref(self.h09_check_expr(ctx, self.tree.arg(node, 0), .none));
    const is_stc = self.tree.kind(node) == .stcmatch and !ctx.interpreted and !ctx.abstract;
    for (arms) |arm| self.node_value[arm] = .none;
    const known = if (ctx.interpreted or ctx.abstract and self.tree.kind(node) == .stcmatch) statics.try_static(self, ctx, self.tree.arg(node, 0)) else null;
    // stcmatch needs a static scrutinee, only the matching arm is checked, like any match on a known value in a stcfun
    if (is_stc or known != null) {
        const v = known orelse statics.h08_eval_static(self, ctx, self.tree.arg(node, 0));
        if (v == .poison_type) return v;
        self.h03_push_scope();
        defer self.h04_pop_scope();
        for (arms) |arm| if (self.interpreter.static_match(ctx, self.tree.arg(arm, 0), v)) {
            self.node_value[arm] = .bool_true;
            return branch(self, ctx, self.tree.arg(arm, 1), expected);
        };
        return self.report(.non_exhaustive_match, node, v, .none);
    }
    var quiet = statics.opened(self, ctx);
    var catch_all = false;
    var result: StaticPool.Index = .none;
    const before = self.uninit;
    var after: u64 = 0;
    defer self.uninit = after;
    var rows: std.ArrayList(NodeId) = .empty;
    defer rows.deinit(self.alloc);
    for (arms) |arm| rows.append(self.alloc, self.tree.arg(arm, 0)) catch @panic("OOM");
    var settled = arms.len;
    for (arms, 0..) |arm, i| {
        if (settled == arms.len and self.concrete(expected)) settled = i;
        self.uninit = before;
        self.h03_push_scope();
        const mark = self.doc.diagnostics.len();
        const pat = pattern(self, ctx, self.tree.arg(arm, 0), st);
        quiet = quiet or self.errors_since(mark, arm);
        if (!quiet and st != .poison_type and covers(self, ctx, &.{st}, rows.items[0..i], i, rows.items[i..][0..1])) self.doc.h21_report(.redundant_match_arm, arm, 0, 0);
        catch_all = catch_all or pat;
        const t = branch(self, ctx, self.tree.arg(arm, 1), expected);
        if (t != .never_type) after |= self.uninit;
        self.h04_pop_scope();
        result = merge(self, arm, result, if (!self.concrete(expected) and self.is_literal(self.tree.arg(arm, 1))) .never_type else t, expected);
    }
    if (!self.concrete(expected) and (result == .none or result == .never_type)) {
        var bodies: [512]NodeId = undefined;
        for (arms, 0..) |arm, i| bodies[i] = self.tree.arg(arm, 1);
        const lt = literals_type(self, bodies[0..arms.len]);
        if (lt != .none) result = lt;
    }
    if (!self.concrete(expected)) for (arms) |arm| if (self.is_literal(self.tree.arg(arm, 1))) {
        result = merge(self, arm, result, adapt(self, self.tree.arg(arm, 1), self.node_type[self.tree.arg(arm, 1)], result), expected);
    };
    if (self.concrete(expected)) for (arms[0..settled]) |arm| {
        _ = settle(self, self.tree.arg(arm, 1), self.static_pool.apply_vars(&self.abstract_pool, self.node_type[self.tree.arg(arm, 1)]), expected);
    };
    if (!catch_all and st != .poison_type and !covers(self, ctx, &.{st}, rows.items, arms.len, &.{0}))
        _ = self.report(.non_exhaustive_match, node, st, .none);
    return if (result == .none) .unit_type else result;
}

pub fn h15_check_branching(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.tree.kind(node);
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) self.tree.arg(node, 0) else node;
    const cond = self.tree.arg(it, 0);
    const then = self.tree.arg(it, 1);
    const stc = k == .stcif_then or k == .stcif_else;
    const c = if (ctx.interpreted or stc and ctx.abstract) statics.try_static(self, ctx, cond) orelse .none else if (stc) statics.h08_eval_static(self, ctx, cond) else .none;
    if (c == .bool_true or c == .bool_false or c != .none and !ctx.interpreted) {
        _ = self.set(cond, .bool_type);
        if (c == .bool_true) return branch(self, ctx, then, expected);
        if (c != .bool_false) return if (c == .poison_type) c else self.report(.type_mismatch, cond, self.static_pool.type_of(c), .bool_type);
        return if (has_else) branch(self, ctx, self.tree.arg(node, 1), expected) else .unit_type;
    }
    // binders of the condition (`x ?<- v`) are visible in the then branch only
    self.h03_push_scope();
    const w = self.condition(ctx, cond);
    self.uninit = w[0];
    const was = self.concrete(expected);
    const tt = branch(self, ctx, then, expected);
    const after_then = if (tt == .never_type) 0 else self.uninit;
    self.uninit = w[1];
    self.h04_pop_scope();
    if (!has_else) {
        self.uninit |= after_then;
        const valued = tt != .never_type and tt != .runit_type and tt != .poison_type and tt != .unit_type;
        return if (self.concrete(expected) and valued) self.report(.runit_mixing, node, tt, .unit_type) else merge(self, node, tt, .unit_type, if (valued) .none else expected);
    }
    const et = branch(self, ctx, self.tree.arg(node, 1), expected);
    self.uninit = after_then | if (et == .never_type) 0 else self.uninit;
    const ts = if (was) tt else settle(self, then, tt, expected);
    return merge(self, node, adapt(self, then, ts, et), adapt(self, self.tree.arg(node, 1), et, ts), expected);
}

// the first type of the literals among `ns` that every one of them fits
pub fn literals_type(self: *Resolver, ns: []const NodeId) StaticPool.Index {
    for (ns) |c| if (self.is_literal(c)) {
        const ct = self.node_type[c];
        for (ns) |n| {
            if (self.is_literal(n) and statics.literal_type(self, n, ct) != ct) break;
        } else return ct;
    };
    return .none;
}

// a literal branch takes the type of the others (`if c: n else: 3`)
fn adapt(self: *Resolver, n: NodeId, t: StaticPool.Index, other: StaticPool.Index) StaticPool.Index {
    if (!self.is_literal(n) or other == .none or statics.literal_type(self, n, other) != other) return t;
    return self.set(n, other);
}

pub fn h16_check_loop(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.tree.kind(node);
    const lp = self.loop_parts(node);
    const exp = sp.apply_vars(&self.abstract_pool, expected);
    const elem_hint = sp.array_elem(exp);
    self.h03_push_scope();
    defer self.h04_pop_scope();
    if (lp.cond != 0) _ = self.check(ctx, lp.cond, .bool_type);
    if (lp.repeat != 0) _ = self.h09_check_expr(ctx, lp.repeat, .none);
    if (lp.cond != 0 and lp.repeat != 0) _ = self.set(lp.head, .unit_type);
    if (lp.seq != 0) {
        const st = sp.pointee(sp.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, lp.seq, if (elem_hint != .none and sp.get_tag_prop(elem_hint).is_integer and is_range_kind(self.tree.kind(lp.seq))) exp else .none)));
        const elem = switch (sp.lookup_member(st, if (sp.get(st) == .array_type) .len else .next)) {
            .builtin_len => sp.get(st).array_type.elem,
            .method => |m| self.fn_ret(m),
            .trait_method => |m| self.fn_ret(sp.method_decl(m)),
            else => self.mismatch(lp.seq, st, .none),
        };
        const v = lp.variable;
        const it = self.h02_declare_local(if (v != 0) self.name_pool.name_of(self.tree, self.src_bytes, v) else .it, if (v != 0) v else lp.head, if (v != 0) .loop_variable else .autoins_it, elem);
        self.node_decl[lp.head] = it;
        if (v != 0) {
            self.node_decl[v] = it;
            _ = self.set(v, elem);
            _ = self.set(lp.head, .unit_type);
        }
    }
    const at_exit = self.uninit;
    self.loop_exits.push(0);
    ctx.loop_depth += 1;
    const jumps = self.jumps;
    // a stc loop body is static per iteration: checked like a stcfun body, evaluated with the loop
    const outer = ctx.interpreted;
    ctx.interpreted = outer or Resolver.node_props[@intFromEnum(k)].stc;
    const bt = self.h09_check_expr(ctx, lp.body, if (expected == .none) .none else if (elem_hint != .none) elem_hint else self.fresh_var(lp.body));
    ctx.interpreted = outer;
    ctx.loop_depth -= 1;
    const broke = self.jumps[0] != jumps[0];
    const stepped = !broke and self.jumps[1] == jumps[1];
    self.jumps = jumps;
    self.loop_exits.head -= 1;
    self.uninit = self.loop_exits.buf[self.loop_exits.head] | if (lp.cond != 0 or lp.seq != 0) at_exit else 0;
    if (!ctx.interpreted and !ctx.abstract and Resolver.node_props[@intFromEnum(k)].stc) _ = statics.static_of(self, ctx, node);
    // used as a value: an array of the body values; brk ends it without adding one, cont skips one
    if (lp.cond == 0 and lp.seq == 0 and !broke and elem_hint == .none) return .never_type;
    if (expected == .none) return .unit_type;
    const n = if (stepped and lp.seq != 0) steps(self, ctx, lp.seq) else null;
    return sp.intern(.{ .array_type = .{ .len = if (n) |x| sp.intern(.{ .int = .{ .ty = .u64_type, .bits = x } }) else self.fresh_var(node), .elem = if (bt == .never_type or bt == .runit_type) (if (elem_hint != .none) elem_hint else .unit_type) else bt } });
}

// the static number of steps of a `for` over a range with static bounds or an array of static length
fn steps(self: *Resolver, ctx: *FnCtx, seq: NodeId) ?u64 {
    const sp = &self.static_pool;
    if (!is_range_kind(self.tree.kind(seq))) {
        const st = sp.pointee(sp.apply_vars(&self.abstract_pool, self.node_type[seq]));
        return if (st != .poison_type and sp.tag(st) == .array_type and sp.tag(sp.get(st).array_type.len) == .int_value) sp.get(sp.get(st).array_type.len).int.bits else null;
    }
    const g = self.range(seq);
    if (g.hi == 0) return null;
    const lo = if (g.lo == 0) 0 else statics.static_int(self, ctx, g.lo) orelse return null;
    const hi = (statics.static_int(self, ctx, g.hi) orelse return null) + @intFromBool(g.incl);
    return if (hi > lo) @intCast(hi - lo) else 0;
}

// binders belong to their statement: a block scopes every non-declaring statement, a declaration its values
pub fn h17_check_unwrap(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.tree.kind(node);
    const vt = self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, self.tree.arg(node, 0), if (k == .labelarrow) expected else .none));
    if (k == .labelarrow) {
        bind_label(self, self.tree.arg(node, 1), vt);
        return vt;
    }
    const pt = payload_of(self, vt);
    if (pt == .none) return self.mismatch(self.tree.arg(node, 0), vt, .none);
    return switch (k) {
        .selftag_unwrap_fallback => blk: {
            const before = self.uninit;
            _ = self.check(ctx, self.tree.arg(node, 1), pt);
            self.uninit = before;
            break :blk pt;
        },
        .selftag_arrow => blk: {
            bind_label(self, self.tree.arg(node, 1), pt);
            break :blk .bool_type;
        },
        else => pt,
    };
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
fn branch(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    return settle(self, node, self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, node, expected)), expected);
}

fn settle(self: *Resolver, node: NodeId, t0: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    const t = if (t0 == .unit_type and Resolver.node_props[@intFromEnum(self.tree.kind(node))].runit) .runit_type else t0;
    if (!self.concrete(expected) or t == .never_type or t == .runit_type or t == .poison_type) return t;
    if (t == .unit_type and expected != .unit_type) return self.report(.runit_mixing, node, t, expected);
    return self.h10_expect(node, t, expected);
}

fn merge(self: *Resolver, node: NodeId, acc: StaticPool.Index, t: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    if (self.concrete(expected)) return expected;
    if (acc == .none) return t;
    const j = self.static_pool.join(&self.abstract_pool, acc, t);
    if (j.ty != .none) return j.ty;
    if (expected == .none) return if (acc == .unit_type or t == .unit_type) .unit_type else self.report(.type_mismatch, node, acc, t);
    return self.report(if (acc == .unit_type or t == .unit_type) .runit_mixing else .type_mismatch, node, acc, t);
}

// `<- name` binds the value, `<- a, b` destructures a record in field order
fn bind_label(self: *Resolver, label: NodeId, t: StaticPool.Index) void {
    const sp = &self.static_pool;
    if (self.tree.kind(label) != .partial__destructure) {
        self.redeclared(self.name_pool.name_of(self.tree, self.src_bytes, label), label);
        self.node_decl[label] = self.h02_declare_local(self.name_pool.name_of(self.tree, self.src_bytes, label), label, .arrow_binder, t);
        _ = self.set(label, t);
        return;
    }
    const rt = sp.apply_vars(&self.abstract_pool, t);
    for (self.tree.manychildren(label), 0..) |id, i| {
        const ft = if (sp.tag(rt) == .record_type and i < sp.get(rt).custom_type.field_types.len) sp.get(rt).custom_type.field_types[i] else self.mismatch(id, t, .none);
        self.redeclared(self.name_pool.name_of(self.tree, self.src_bytes, id), id);
        self.node_decl[id] = self.h02_declare_local(self.name_pool.name_of(self.tree, self.src_bytes, id), id, .arrow_binder, ft);
        _ = self.set(id, ft);
    }
}

// what `??` / `?<-` unwrap: the payload of a case, or of the first case that has one
pub fn payload_of(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    const case = switch (sp.tag(t)) {
        .variant_case_type => t,
        .variant_type => sp.payload_case(t),
        else => .none,
    };
    if (case == .none) return .none;
    const p = sp.get(case).variant_case_type.payload;
    if (p == .none) return .none;
    const f = sp.get(p).custom_type.field_types;
    return if (f.len == 1) f[0] else p;
}

// whether the pattern takes every value of its type
fn pattern(self: *Resolver, ctx: *FnCtx, p: NodeId, st: StaticPool.Index) bool {
    const sp = &self.static_pool;
    switch (self.tree.kind(p)) {
        .identifier => {
            const name = self.name_pool.name_of(self.tree, self.src_bytes, p);
            self.redeclared(name, p);
            if (name != .underscore) self.node_decl[p] = self.h02_declare_local(name, p, .pattern_binder, st);
            _ = self.set(p, st);
            return true;
        },
        .partial__match_case_pattern_or => {
            // every alternative binds the same names, sharing the declarations of the first one
            var r = false;
            const names = &self.local_names;
            const from = names.head;
            var first = from;
            for (self.tree.manychildren(p), 0..) |alt, i| {
                if (i > 0) self.h03_push_scope();
                const mark = names.head;
                const s = pattern(self, ctx, alt, st);
                r = r or s;
                if (i == 0) {
                    first = names.head;
                    continue;
                }
                for (names.buf[from..first]) |n| if (std.mem.indexOfScalar(NamePool.Index, names.buf[mark..names.head], n) == null) self.doc.h21_report(.undefined_name, alt, n, 0);
                for (mark..names.head) |j| {
                    const id = self.decl_pool.nodes()[@intFromEnum(self.local_decls.buf[j])];
                    const k = std.mem.indexOfScalar(NamePool.Index, names.buf[from..first], names.buf[j]) orelse {
                        self.doc.h21_report(.undefined_name, id, names.buf[j], 0);
                        continue;
                    };
                    self.node_decl[id] = self.local_decls.buf[from + k];
                    const t = self.decl_pool.tys()[@intFromEnum(self.node_decl[id])];
                    if (self.node_type[id] != t and self.node_type[id] != .poison_type and t != .poison_type) _ = self.report(.type_mismatch, id, self.node_type[id], t);
                }
                self.h04_pop_scope();
            }
            return r;
        },
        .partial__match_case_pattern_typecast => {
            const t = types.realized_type(self, ctx, self.tree.arg(p, 0));
            const v = self.tree.arg(p, 1);
            self.redeclared(self.name_pool.name_of(self.tree, self.src_bytes, v), v);
            self.node_decl[v] = self.h02_declare_local(self.name_pool.name_of(self.tree, self.src_bytes, v), v, .pattern_binder, t);
            _ = self.set(v, t);
            const widen = t == st or t == .poison_type or st == .poison_type or sp.coerce(&self.abstract_pool, st, t) != .incompatible;
            const narrow = switch (sp.tag(st)) {
                .variant_type, .variant_union_type, .trait_type => sp.coerce(&self.abstract_pool, t, st) != .incompatible,
                else => false,
            };
            if (!widen and !narrow and !statics.sibling(self, ctx, t, st)) _ = self.report(.type_mismatch, p, t, st);
            return widen;
        },
        .labelarrow => {
            const r = pattern(self, ctx, self.tree.arg(p, 0), st);
            const ct = self.node_type[self.tree.arg(p, 0)];
            const pt = payload_of(self, ct);
            bind_label(self, self.tree.arg(p, 1), if (pt == .none) ct else pt);
            return r;
        },
        .fun_call => {
            const callee = self.tree.arg(p, 0);
            const ct = self.h09_check_expr(ctx, callee, .none);
            const target = self.set(p, if (sp.tag(ct) == .meta_type) statics.h08_eval_static(self, ctx, callee) else ct);
            if (target == .poison_type) { // binders still exist, as poison
                for (self.tree.manychildren(self.tree.arg(p, 1))) |a| _ = pattern(self, ctx, self.arg_value(a), target);
                return false;
            }
            if (target != st and sp.coerce(&self.abstract_pool, target, st) == .incompatible and !statics.sibling(self, ctx, target, st)) _ = self.report(.type_mismatch, p, target, st);
            const is_case = sp.tag(target) == .variant_case_type;
            const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
            const args = self.tree.manychildren(self.tree.arg(p, 1));
            var map: [64]u32 = undefined;
            if (rec == .none or sp.tag(rec) != .record_type or !calls.bind_args(self, self.fields_of(rec), args, &map, true)) {
                if (args.len > 0) _ = self.report(.wrong_arity, p, args.len, 0);
                return false;
            }
            var all = true;
            for (args, 0..) |a, i| all = pattern(self, ctx, self.arg_value(a), calls.named(self, a, sp.get(rec).custom_type.field_types[map[i]])) and all;
            return !is_case and all;
        },
        else => { // literals, ranges and constant paths (`Toggle.On`)
            const t = self.h09_check_expr(ctx, p, st);
            if (is_range_kind(self.tree.kind(p))) {
                const e = sp.apply_vars(&self.abstract_pool, t);
                if (t != .poison_type and st != .poison_type and sp.get(e) == .array_type and sp.coerce(&self.abstract_pool, sp.get(e).array_type.elem, st) == .incompatible) _ = self.report(.type_mismatch, p, sp.get(e).array_type.elem, st);
                return false;
            }
            if (!statics.sibling(self, ctx, t, st)) _ = self.h10_expect(p, t, st);
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
    var tys: [64]StaticPool.Index = undefined;
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
            var ks: [256]StaticPool.Index = undefined;
            var nk: usize = 0;
            if (sp.tag(t) == .record_type) {
                ks[0] = t;
                nk = 1;
            } else for (0..if (sp.tag(t) == .variant_type) 1 else sp.get(t).variant_union_type.len) |mi| {
                const m = if (sp.tag(t) == .variant_type) t else sp.get(t).variant_union_type[mi];
                for (0..sp.get(m).variant_type.cases.len) |ci| {
                    ks[nk] = sp.get(m).variant_type.cases[ci];
                    nk += 1;
                }
            }
            for (ks[0..nk]) |k| {
                const rec = if (sp.tag(k) == .variant_case_type) sp.get(k).variant_case_type.payload else k;
                const fields = if (rec == .none) &[_]NodeId{} else self.fields_of(rec);
                nq.clearRetainingCapacity();
                if (specialize(self, qs.items, w, k, fields, &nq) == 0) continue;
                for (0..fields.len) |i| tys[i] = sp.get(rec).custom_type.field_types[i];
                @memcpy(tys[fields.len..][0 .. w - 1], cols[1..]);
                next.clearRetainingCapacity();
                const m = specialize(self, flat.items, w, k, fields, &next);
                if (!covers(self, ctx, tys[0 .. fields.len + w - 1], next.items, m, nq.items)) return false;
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
        var map: [64]u32 = undefined;
        const args = if (p != 0 and self.tree.kind(p) == .fun_call) self.tree.manychildren(self.tree.arg(p, 1)) else &[_]NodeId{};
        if (calls.bind_args(self, fields, args, &map, true)) for (args, 0..) |a, i| {
            out.items[at + map[i]] = self.arg_value(a);
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
    const g = statics.source_of(self, a);
    return g != .none and g == statics.source_of(self, b) and (sp.tag(a) != .variant_case_type or sp.get(a).variant_case_type.case == sp.get(b).variant_case_type.case);
}

// the integer values a literal or range pattern covers, as a closed interval
fn interval(self: *Resolver, ctx: *FnCtx, p: NodeId) ?[2]i128 {
    if (!is_range_kind(self.tree.kind(p))) {
        const v = statics.static_int(self, ctx, p) orelse return null;
        return .{ v, v };
    }
    const g = self.range(p);
    const lo = if (g.lo == 0) std.math.minInt(i128) else statics.static_int(self, ctx, g.lo) orelse return null;
    const hi = if (g.hi == 0) std.math.maxInt(i128) else (statics.static_int(self, ctx, g.hi) orelse return null) - @intFromBool(!g.incl);
    return .{ lo, hi };
}

pub fn is_ptr_array(self: *Resolver, t0: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    return sp.is_ptr(t) and sp.get(sp.pointee(t)) == .array_type;
}
