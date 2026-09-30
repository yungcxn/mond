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
const class = Resolver.class;
const is_range_kind = Resolver.is_range_kind;

const Pat = struct { mask: u64 = 0, all: bool = false };

pub fn h14_check_match(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const arms = self.kids(self.arg(node, 1));
    const st = self.deref(self.h09_check_expr(ctx, self.arg(node, 0), .none));
    const is_stc = self.nk(node) == .stcmatch and !ctx.interpreted and !ctx.abstract;
    for (arms) |arm| self.node_value[arm] = .none;
    const known = if (ctx.interpreted or ctx.abstract and self.nk(node) == .stcmatch) statics.try_static(self, ctx, self.arg(node, 0)) else null;
    // stcmatch needs a static scrutinee, only the matching arm is checked, like any match on a known value in a stcfun
    if (is_stc or known != null) {
        const v = known orelse statics.h08_eval_static(self, ctx, self.arg(node, 0));
        if (v == .poison_type) return v;
        self.h03_push_scope();
        defer self.h04_pop_scope();
        for (arms) |arm| if (self.interpreter.static_match(ctx, self.arg(arm, 0), v)) {
            self.node_value[arm] = .bool_true;
            return branch(self, ctx, self.arg(arm, 1), expected);
        };
        return self.report(.non_exhaustive_match, node, v, .none);
    }
    var ivs: std.ArrayList([2]i128) = .empty;
    defer ivs.deinit(self.alloc);
    var quiet = statics.opened(self, ctx);
    var covered: u64 = 0;
    var catch_all = false;
    var result: StaticPool.Index = .none;
    const before = self.uninit;
    var after: u64 = 0;
    defer self.uninit = after;
    for (arms) |arm| {
        self.uninit = before;
        self.h03_push_scope();
        const mark = self.doc.diagnostics.len();
        const pat = pattern(self, ctx, self.arg(arm, 0), st);
        intervals(self, ctx, self.arg(arm, 0), &ivs);
        if (!quiet and (catch_all or (!pat.all and pat.mask != 0 and pat.mask & ~covered == 0))) self.doc.h21_report(.redundant_match_arm, arm, 0, 0);
        quiet = quiet or self.errors_since(mark, arm);
        covered |= pat.mask;
        catch_all = catch_all or pat.all;
        const t = branch(self, ctx, self.arg(arm, 1), expected);
        if (t != .never_type) after |= self.uninit;
        self.h04_pop_scope();
        result = merge(self, arm, result, t, expected);
    }
    // variants, unions and bools by their case bits, integers by interval coverage, strings only with `_` or a binder
    const cases = case_count(self, st);
    const all_cases = cases <= 64 and covered == @as(u64, std.math.maxInt(u64)) >> @intCast(64 - cases);
    if (!catch_all and st != .poison_type and !all_cases and !covers(self, st, ivs.items))
        _ = self.report(.non_exhaustive_match, node, st, .none);
    return if (result == .none) .unit_type else result;
}

pub fn h15_check_branching(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.nk(node);
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) self.arg(node, 0) else node;
    const cond = self.arg(it, 0);
    const then = self.arg(it, 1);
    const stc = k == .stcif_then or k == .stcif_else;
    const c = if (ctx.interpreted or stc and ctx.abstract) statics.try_static(self, ctx, cond) orelse .none else if (stc) statics.h08_eval_static(self, ctx, cond) else .none;
    if (c == .bool_true or c == .bool_false or c != .none and !ctx.interpreted) {
        _ = self.set(cond, .bool_type);
        if (c == .bool_true) return branch(self, ctx, then, expected);
        if (c != .bool_false) return if (c == .poison_type) c else self.report(.type_mismatch, cond, self.static_pool.type_of(c), .bool_type);
        return if (has_else) branch(self, ctx, self.arg(node, 1), expected) else .unit_type;
    }
    // binders of the condition (`x ?<- v`) are visible in the then branch only
    self.h03_push_scope();
    _ = self.check(ctx, cond, .bool_type);
    const before = self.uninit;
    const tt = branch(self, ctx, then, expected);
    const after_then = if (tt == .never_type) 0 else self.uninit;
    self.uninit = before;
    self.h04_pop_scope();
    if (!has_else) {
        const valued = tt != .never_type and tt != .runit_type and tt != .poison_type and tt != .unit_type;
        return if (self.concrete(expected) and valued) self.report(.runit_mixing, node, tt, .unit_type) else merge(self, node, tt, .unit_type, if (valued) .none else expected);
    }
    const et = branch(self, ctx, self.arg(node, 1), expected);
    self.uninit = after_then | if (et == .never_type) 0 else self.uninit;
    return merge(self, node, tt, et, expected);
}

pub fn h16_check_loop(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(node);
    const lp = self.loop_parts(node);
    const exp = sp.apply_vars(&self.abstract_pool, expected);
    const elem_hint = sp.array_elem(exp);
    self.h03_push_scope();
    defer self.h04_pop_scope();
    if (lp.cond != 0) _ = self.check(ctx, lp.cond, .bool_type);
    if (lp.repeat != 0) _ = self.h09_check_expr(ctx, lp.repeat, .none);
    if (lp.cond != 0 and lp.repeat != 0) _ = self.set(lp.head, .unit_type);
    if (lp.seq != 0) {
        const st = sp.pointee(sp.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, lp.seq, if (elem_hint != .none and sp.class(elem_hint).is_integer and is_range_kind(self.nk(lp.seq))) exp else .none)));
        const elem = switch (sp.lookup_member(st, if (sp.get(st) == .array_type) .len else .next)) {
            .builtin_len => sp.get(st).array_type.elem,
            .method => |m| self.fn_ret(m),
            .trait_method => |m| self.fn_ret(sp.method_decl(m)),
            else => self.mismatch(lp.seq, st, .none),
        };
        const v = lp.variable;
        const it = self.h02_declare_local(if (v != 0) self.name_of(v) else .dollar_it, if (v != 0) v else lp.head, if (v != 0) .loop_variable else .autoins_it, elem);
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
    // a stc loop body is static per iteration: checked like a stcfun body, evaluated with the loop
    const outer = ctx.interpreted;
    ctx.interpreted = outer or class(k).stc;
    const bt = self.h09_check_expr(ctx, lp.body, if (expected == .none) .none else if (elem_hint != .none) elem_hint else self.fresh_var(lp.body));
    ctx.interpreted = outer;
    ctx.loop_depth -= 1;
    self.loop_exits.head -= 1;
    self.uninit = self.loop_exits.buf[self.loop_exits.head] | if (lp.cond != 0 or lp.seq != 0) at_exit else 0;
    if (!ctx.interpreted and !ctx.abstract and class(k).stc) _ = statics.static_of(self, ctx, node);
    // used as a value: an array of the body values; brk ends it without adding one
    if (expected == .none) return .unit_type;
    return sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = if (bt == .never_type or bt == .runit_type) (if (elem_hint != .none) elem_hint else .unit_type) else bt } });
}

// binders belong to their statement: a block scopes every non-declaring statement, a declaration its values
pub fn h17_check_unwrap(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.nk(node);
    const vt = self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, self.arg(node, 0), if (k == .labelarrow) expected else .none));
    if (k == .labelarrow) {
        bind_label(self, self.arg(node, 1), vt);
        return vt;
    }
    const pt = payload_of(self, vt);
    if (pt == .none) return self.mismatch(self.arg(node, 0), vt, .none);
    return switch (k) {
        .selftag_unwrap_fallback => blk: {
            const before = self.uninit;
            _ = self.check(ctx, self.arg(node, 1), pt);
            self.uninit = before;
            break :blk pt;
        },
        .selftag_arrow => blk: {
            bind_label(self, self.arg(node, 1), pt);
            break :blk .bool_type;
        },
        else => pt,
    };
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
fn branch(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    var t = self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, node, expected));
    if (t == .unit_type and class(self.nk(node)).runit) t = .runit_type;
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
    if (self.nk(label) != .partial__destructure) {
        self.node_decl[label] = self.h02_declare_local(self.name_of(label), label, .arrow_binder, t);
        _ = self.set(label, t);
        return;
    }
    const rt = sp.apply_vars(&self.abstract_pool, t);
    for (self.kids(label), 0..) |id, i| {
        const ft = if (sp.tag(rt) == .record_type and i < sp.get(rt).custom_type.field_types.len) sp.get(rt).custom_type.field_types[i] else self.mismatch(id, t, .none);
        self.node_decl[id] = self.h02_declare_local(self.name_of(id), id, .arrow_binder, ft);
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

fn pattern(self: *Resolver, ctx: *FnCtx, p: NodeId, st: StaticPool.Index) Pat {
    const sp = &self.static_pool;
    switch (self.nk(p)) {
        .identifier => {
            const name = self.name_of(p);
            if (name != .underscore) self.node_decl[p] = self.h02_declare_local(name, p, .pattern_binder, st);
            _ = self.set(p, st);
            return .{ .all = true };
        },
        .partial__match_case_pattern_or => {
            // every alternative binds the same names, sharing the declarations of the first one
            var r = Pat{};
            const names = &self.local_names;
            const from = names.head;
            var first = from;
            for (self.kids(p), 0..) |alt, i| {
                const mark = names.head;
                const s = pattern(self, ctx, alt, st);
                r = .{ .mask = r.mask | s.mask, .all = r.all or s.all };
                if (i == 0) {
                    first = names.head;
                    continue;
                }
                for (names.buf[from..first]) |n| if (std.mem.indexOfScalar(NamePool.Index, names.buf[mark..names.head], n) == null) self.doc.h21_report(.undefined_name, alt, n, 0);
                for (mark..names.head) |j| {
                    const id = self.dp(.node, self.local_decls.buf[j]).*;
                    const k = std.mem.indexOfScalar(NamePool.Index, names.buf[from..first], names.buf[j]) orelse {
                        self.doc.h21_report(.undefined_name, id, names.buf[j], 0);
                        continue;
                    };
                    self.node_decl[id] = self.local_decls.buf[from + k];
                    const t = self.dp(.ty, self.node_decl[id]).*;
                    if (self.node_type[id] != t and self.node_type[id] != .poison_type and t != .poison_type) _ = self.report(.type_mismatch, id, self.node_type[id], t);
                }
                names.head = mark;
                self.local_decls.head = mark;
            }
            return r;
        },
        .partial__match_case_pattern_typecast => {
            const t = types.realized_type(self, ctx, self.arg(p, 0));
            const v = self.arg(p, 1);
            self.node_decl[v] = self.h02_declare_local(self.name_of(v), v, .pattern_binder, t);
            _ = self.set(v, t);
            const widen = t == st or t == .poison_type or st == .poison_type or sp.coerce(&self.abstract_pool, st, t) != .incompatible;
            const narrow = switch (sp.tag(st)) {
                .variant_type, .variant_union_type, .trait_type => sp.coerce(&self.abstract_pool, t, st) != .incompatible,
                else => false,
            };
            if (!widen and !narrow and !statics.sibling(self, ctx, t, st)) _ = self.report(.type_mismatch, p, t, st);
            return .{ .all = widen, .mask = if (t != .poison_type and sp.tag(t) == .variant_type) member_bits(self, t, st) else 0 };
        },
        .labelarrow => {
            const r = pattern(self, ctx, self.arg(p, 0), st);
            const ct = self.node_type[self.arg(p, 0)];
            const pt = payload_of(self, ct);
            bind_label(self, self.arg(p, 1), if (pt == .none) ct else pt);
            return r;
        },
        .fun_call => {
            const callee = self.arg(p, 0);
            const ct = self.h09_check_expr(ctx, callee, .none);
            const target = self.set(p, if (sp.tag(ct) == .meta_type) statics.h08_eval_static(self, ctx, callee) else ct);
            if (target == .poison_type) { // binders still exist, as poison
                for (self.kids(self.arg(p, 1))) |a| _ = pattern(self, ctx, self.arg_value(a), target);
                return .{};
            }
            if (target != st and sp.coerce(&self.abstract_pool, target, st) == .incompatible and !statics.sibling(self, ctx, target, st)) _ = self.report(.type_mismatch, p, target, st);
            const is_case = sp.tag(target) == .variant_case_type;
            const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
            const args = self.kids(self.arg(p, 1));
            var map: [64]u32 = undefined;
            if (rec == .none or sp.tag(rec) != .record_type or !calls.bind_args(self, self.fields_of(rec), args, &map, true)) {
                if (args.len > 0) _ = self.report(.wrong_arity, p, args.len, 0);
                return .{ .mask = if (is_case and args.len == 0) case_bit(self, target, st) else 0 };
            }
            var all = true;
            for (args, 0..) |a, i| all = pattern(self, ctx, self.arg_value(a), calls.named(self, a, sp.get(rec).custom_type.field_types[map[i]])).all and all;
            return if (is_case) .{ .mask = if (all) case_bit(self, target, st) else 0 } else .{ .all = all };
        },
        else => { // literals, ranges and constant paths (`Toggle.On`)
            const t = self.h09_check_expr(ctx, p, st);
            if (is_range_kind(self.nk(p))) {
                const e = sp.apply_vars(&self.abstract_pool, t);
                if (t != .poison_type and st != .poison_type and sp.get(e) == .array_type and sp.coerce(&self.abstract_pool, sp.get(e).array_type.elem, st) == .incompatible) _ = self.report(.type_mismatch, p, sp.get(e).array_type.elem, st);
                return .{};
            }
            if (!statics.sibling(self, ctx, t, st)) _ = self.h10_expect(p, t, st);
            if (sp.tag(t) == .variant_case_type) return .{ .mask = case_bit(self, t, st) };
            return .{ .mask = if (st == .bool_type and self.nk(p) == .boolean_true) 1 else if (st == .bool_type and self.nk(p) == .boolean_false) 2 else 0 };
        },
    }
}

// the integer values a pattern covers as closed intervals, for exhaustiveness over integer scrutinees
fn intervals(self: *Resolver, ctx: *FnCtx, p: NodeId, out: *std.ArrayList([2]i128)) void {
    const k = self.nk(p);
    if (k == .partial__match_case_pattern_or) return for (self.kids(p)) |alt| intervals(self, ctx, alt, out);
    if (!is_range_kind(k)) {
        const v = statics.static_int(self, ctx, p) orelse return;
        return out.append(self.alloc, .{ v, v }) catch @panic("OOM");
    }
    const g = self.range(p);
    const lo = if (g.lo == 0) std.math.minInt(i128) else statics.static_int(self, ctx, g.lo);
    const hi = if (g.hi == 0) std.math.maxInt(i128) else (statics.static_int(self, ctx, g.hi) orelse return) - @intFromBool(!g.incl);
    out.append(self.alloc, .{ lo orelse return, hi }) catch @panic("OOM");
}

fn covers(self: *Resolver, st: StaticPool.Index, ivs: [][2]i128) bool {
    const sp = &self.static_pool;
    if (st == .none or sp.get(st) != .int_type) return false;
    const t = sp.get(st).int_type;
    const bits: u7 = @intCast(t.bits);
    const one: i128 = 1;
    var cur: i128 = if (t.signedness == .signed) -(one << (bits - 1)) else 0;
    const max: i128 = if (t.signedness == .signed) (one << (bits - 1)) - 1 else (one << bits) - 1;
    std.mem.sort([2]i128, ivs, {}, struct {
        fn lt(_: void, a: [2]i128, b: [2]i128) bool {
            return a[0] < b[0];
        }
    }.lt);
    for (ivs) |iv| {
        if (iv[0] > cur) return false;
        if (iv[1] >= max) return true;
        cur = @max(cur, iv[1] + 1);
    }
    return false;
}

fn case_base(self: *Resolver, variant: StaticPool.Index, st: StaticPool.Index) ?u64 {
    const sp = &self.static_pool;
    if (variant == st) return 0;
    if (st == .none or sp.tag(st) != .variant_union_type) return null;
    var base: u64 = 0;
    for (sp.get(st).variant_union_type) |m| {
        if (m == variant) return base;
        base += sp.get(m).variant_type.cases.len;
    }
    return null;
}

fn case_count(self: *Resolver, st: StaticPool.Index) usize {
    const sp = &self.static_pool;
    if (st == .bool_type) return 2;
    if (sp.tag(st) == .variant_type) return sp.get(st).variant_type.cases.len;
    if (sp.tag(st) != .variant_union_type) return 65;
    var n: usize = 0;
    for (sp.get(st).variant_union_type) |m| n += sp.get(m).variant_type.cases.len;
    return n;
}

fn case_bit(self: *Resolver, case: StaticPool.Index, st: StaticPool.Index) u64 {
    const c = self.static_pool.get(case).variant_case_type;
    const bit = (case_base(self, c.variant, st) orelse return 0) + c.case;
    return if (bit < 64) @as(u64, 1) << @intCast(bit) else 0;
}

fn member_bits(self: *Resolver, member: StaticPool.Index, st: StaticPool.Index) u64 {
    const base = case_base(self, member, st) orelse return 0;
    const n = self.static_pool.get(member).variant_type.cases.len;
    return if (base + n > 64) 0 else (@as(u64, std.math.maxInt(u64)) >> @intCast(64 - n)) << @intCast(base);
}

pub fn is_ptr_array(self: *Resolver, t0: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    return sp.is_ptr(t) and sp.get(sp.pointee(t)) == .array_type;
}
