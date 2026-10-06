const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const decls = @import("decls.zig");
const places = @import("places.zig");
const types = @import("types.zig");
const calls = @import("calls.zig");
const control = @import("control.zig");
const patterns = @import("patterns.zig");
const generics = @import("generics.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const Stmt = Resolver.Stmt;
const NodeId = ParseTree.NodeId;

// expressions: the walk over a body, every node gets its type here or in the module of its kind

pub fn h09_check_expr(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const ap = &self.abstract_pool;
    const a0 = self.tree.arg(node, 0);
    const a1 = self.tree.arg(node, 1);
    const k = self.tree.kind(node);
    if (ctx.interpreted and syntax.props(k).stc and !self.doc.has(node)) _ = self.report(.redundant_stc, node, 0, 0);
    const t: StaticPool.Index = switch (k) {
        .int, .float, .char, .string, .boolean_true, .boolean_false => statics.literal_type(self, node, expected),
        .identifier, .identifier_self => blk: {
            const d = calls.overload_for(self, node, decls.use(self, node), expected);
            if (d == .none) break :blk .poison_type;
            if (self.inits.unwritten(d)) self.doc.h21_report(.use_before_initialization, node, self.decl_pool.names()[@intFromEnum(d)], 0);
            const ty = self.decl_pool.tys()[@intFromEnum(d)];
            break :blk if (ty == .none) .poison_type else ty;
        },
        .capture => h09_check_expr(self, ctx, a0, expected),
        .block => blk: {
            self.scopes.h03_push_scope();
            defer self.scopes.h04_pop_scope();
            var last: StaticPool.Index = .unit_type;
            const stmts = self.tree.manychildren(node);
            // local functions are visible in their whole block
            for (stmts) |s| {
                const st = Stmt.from_node(self, s);
                if (st.kind != .function or st.assignees.len != 1 or st.type == 0 or self.tree.kind(st.type) != .type_fun) continue;
                if (self.scopes.in_scope(self.name_pool.name_of(self.tree, self.src_bytes, st.assignees[0])) != .none) continue;
                const d = decls.h02_declare_local(self, self.name_pool.name_of(self.tree, self.src_bytes, st.assignees[0]), st.node, .function, .none);
                self.decl_pool.flags()[@intFromEnum(d)] = st.flags;
                self.node_decl[st.assignees[0]] = d;
            }
            for (stmts, 0..) |s, i| {
                const declares = syntax.props(self.tree.kind(s)).declares;
                if (!declares) self.scopes.h03_push_scope();
                last = h09_check_expr(self, ctx, s, if (i + 1 == stmts.len) expected else .none);
                if (!declares) self.scopes.h04_pop_scope();
            }
            break :blk last;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => decls.h11_check_assign(self, ctx, node),
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => blk: {
            const lt = places.h18_check_place(self, ctx, a0);
            if ((k == .assign_add or k == .assign_sub) and elem_ptr(self, lt)) break :blk if (integer(self, ctx, a1)) .unit_type else .poison_type;
            _ = check(self, ctx, a1, lt);
            break :blk numeric(self, node, lt, .unit_type);
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix => blk: {
            const lt = places.h18_check_place(self, ctx, a0);
            break :blk if (elem_ptr(self, lt)) lt else numeric(self, node, lt, lt);
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap => blk: {
            const j = pair(self, ctx, node, a0, a1, if (sp.is_numeric(expected)) expected else .none);
            const wraps = switch (k) {
                .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod => false,
                else => true,
            };
            const r = if ((k == .binary_add or k == .binary_sub) and elem_ptr(self, j)) j else if (wraps and !sp.get_tag_prop(j).is_integer and sp.tag(j) != .type_var) self.mismatch(node, j, .none) else numeric(self, node, j, j);
            // arithmetic on constants is folded, an overflow is an error as soon as it can be seen
            if (r != .poison_type and !ctx.abstract and folded(self, a0) and folded(self, a1)) {
                _ = self.set(node, r);
                _ = statics.h08_eval_static(self, ctx, node);
            }
            break :blk r;
        },
        .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => blk: {
            const j = pair(self, ctx, node, a0, a1, .none);
            break :blk if (j == .poison_type) j else .bool_type;
        },
        .binary_logic_or, .binary_logic_and => blk: {
            const m = self.inits.count;
            defer self.inits.release(m);
            const w = control.condition(self, ctx, node);
            self.inits.copy(0, w[0]);
            self.inits.merge(0, w[1]);
            break :blk .bool_type;
        },
        .binary_logic_xor => blk: {
            _ = check(self, ctx, a0, .bool_type);
            _ = check(self, ctx, a1, .bool_type);
            break :blk .bool_type;
        },
        .neg_logic => blk: { // `!` is logical on bools and bitwise on integers
            const st = h09_check_expr(self, ctx, a0, expected);
            break :blk if (st == .bool_type or sp.get_tag_prop(st).is_integer) st else self.mismatch(node, st, .bool_type);
        },
        .neg_num => if (syntax.is_literal(self.tree, node)) statics.literal_type(self, node, expected) else numeric(self, node, h09_check_expr(self, ctx, a0, expected), .none),
        .fun_call, .with => calls.h12_check_call(self, ctx, node),
        .member => h13_check_member(self, ctx, node),
        .array_index => blk: {
            var st = sp.apply_vars(ap, h09_check_expr(self, ctx, a0, .none));
            if (syntax.props(self.tree.kind(a1)).range) break :blk self.report(.genexpr_index, a1, 0, 0);
            const it = h09_check_expr(self, ctx, a1, .none);
            if (!sp.get_tag_prop(it).is_integer) _ = self.mismatch(a1, it, .u64_type);
            if (st == .poison_type) break :blk st;
            const through_ptr = sp.is_ptr(st);
            st = sp.pointee(st);
            // pointers index like arrays (`*u8 buf; buf[i]`), arrays auto-deref once
            const elem = if (sp.get(st) == .array_type) sp.get(st).array_type.elem else if (through_ptr) st else break :blk self.report(.type_mismatch, a0, st, .none);
            // lengths of realizations and stcfun bodies are the interpreter's to check, their constant indices may be guarded
            if (!ctx.interpreted and !(ctx.decl != .none and self.decl_pool.template_of.contains(ctx.decl)) and sp.get(st) == .array_type and sp.tag(sp.get(st).array_type.len) == .int_value and syntax.is_literal(self.tree, a1)) {
                const i = statics.static_int(self, ctx, a1) orelse break :blk elem;
                if (i < 0 or i >= sp.get(sp.get(st).array_type.len).int.bits) _ = self.report(.static_eval_failed, a1, 0, 0);
            }
            break :blk elem;
        },
        .dereference => blk: {
            const st = sp.apply_vars(ap, h09_check_expr(self, ctx, a0, .none));
            break :blk if (sp.is_ptr(st)) sp.pointee(st) else self.mismatch(node, st, .none);
        },
        .address_of => blk: {
            if (self.tree.kind(a0) == .identifier) self.inits.written(self.scopes.h01_lookup(self.decl_pool.kinds(), self.name_pool.name_of(self.tree, self.src_bytes, a0)));
            const exp = sp.apply_vars(ap, expected);
            const st = h09_check_expr(self, ctx, a0, if (sp.is_ptr(exp)) sp.pointee(exp) else .none);
            // write access only to what could be written directly
            const mutable = places.writable(self, a0) == .ok;
            if (mutable and exp != .none and sp.tag(exp) == .ptr_mut_type) places.wrote(self, a0);
            break :blk if (st == .poison_type) st else sp.intern(.{ .ptr_type = .{ .child = st, .mutable = mutable } });
        },
        .array, .array_empty => blk: {
            const exp = sp.apply_vars(ap, expected);
            var elem = sp.array_elem(exp);
            const given = elem != .none;
            const elems = if (k == .array) self.tree.manychildren(node) else &[_]NodeId{};
            // without an expectation the elements join, literals last: `[1, -2]` is [2]i32, `[x, 300]` with u8 x [2]u32
            for (elems) |e| {
                if (!given and syntax.is_literal(self.tree, e)) continue;
                const et = h09_check_expr(self, ctx, e, elem);
                const joined = if (given or elem == .none) .none else sp.join(ap, elem, et).ty;
                if (elem == .none) elem = et else if (joined != .none) elem = joined else _ = h10_expect(self, e, et, elem);
            }
            if (!given) {
                for (elems) |e| if (syntax.is_literal(self.tree, e)) {
                    _ = h09_check_expr(self, ctx, e, .none);
                };
                if (elem == .none) elem = control.literals_type(self, elems);
                if (elem == .none and elems.len > 0) elem = self.node_type[elems[0]];
                for (elems) |e| if (syntax.is_literal(self.tree, e) and elem != .none) {
                    const j = sp.join(ap, elem, statics.literal_type(self, e, elem)).ty;
                    if (j != .none) elem = j;
                };
                for (elems) |e| if (syntax.is_literal(self.tree, e)) {
                    _ = h10_expect(self, e, self.node_type[e], elem);
                };
            }
            if (elem == .none) elem = sp.fresh_var(ap, node);
            break :blk sp.intern(.{ .array_type = .{ .len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = elems.len } }), .elem = elem } });
        },
        .as => blk: {
            const from = sp.apply_vars(ap, h09_check_expr(self, ctx, a0, .none));
            const to = types.cast_target(self, ctx, a1, from);
            const lost = to == .poison_type or from == .poison_type or sp.get(to) == .array_type and sp.get(to).array_type.len == .poison_type or sp.get(to) == .ptr_type and sp.get(sp.get(to).ptr_type.child) == .array_type and sp.get(sp.get(to).ptr_type.child).array_type.len == .poison_type;
            break :blk if (lost) .poison_type else if (sp.cast(from, to) == .invalid) self.report(.invalid_cast, node, from, to) else to;
        },
        .asbits => blk: {
            const from = sp.apply_vars(ap, h09_check_expr(self, ctx, a0, .none));
            const to = types.h07_lower_type(self, ctx, a1);
            if (from == .poison_type or to == .poison_type) break :blk .poison_type;
            break :blk if (!sp.get_tag_prop(from).has_layout or !sp.get_tag_prop(to).has_layout or sp.layout(to).size < sp.layout(from).size) self.report(.invalid_cast, node, from, to) else to;
        },
        .oftype => blk: {
            const vt = sp.deref(ap, h09_check_expr(self, ctx, a0, .none));
            const ot0 = if (ctx.interpreted) statics.deferred(self, ctx, a1) orelse .none else types.h07_lower_type(self, ctx, a1);
            const ot = if (ot0 != .none and sp.tag(ot0) == .generic) types.h07_lower_type(self, ctx, a1) else ot0;
            self.node_value[a1] = ot;
            self.node_value[node] = if (ot == .none or (ctx.interpreted and sp.tag(vt) == .meta_type)) .none else if (sp.templated(ot) != .none) (if (generics.realizes(self, vt, ot)) .bool_true else .bool_false) else if (sp.templated(vt) != .none) .none else if (vt == ot or sp.implements(vt, ot)) .bool_true else if (sp.tag(vt) == .trait_type) .none else .bool_false;
            break :blk .bool_type;
        },
        .typeof, .sizeof => blk: {
            _ = h09_check_expr(self, ctx, a0, .none);
            if (self.tree.kind(a0) == .identifier and generics.is_template(self, self.node_decl[a0])) break :blk self.report(.unrealized_template, a0, 0, 0);
            _ = statics.try_static(self, ctx, node);
            break :blk if (k == .typeof) .type_type else .u64_type;
        },
        .if_then, .if_else, .stcif_then, .stcif_else => control.h15_check_branching(self, ctx, node, expected),
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => control.h16_check_loop(self, ctx, node, expected),
        // ranges are sequences of their bound type, so `for` and slicing treat them like arrays
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => blk: {
            const exp = sp.apply_vars(ap, expected);
            const e = sp.array_elem(exp);
            var hint = if (e != .none) e else if (sp.is_numeric(exp)) exp else .none;
            const g = syntax.Range.from_node(self.tree, node);
            for ([_]NodeId{ g.lo, g.hi }) |x| if (x != 0 and hint != .none and syntax.is_literal(self.tree, x) and statics.literal_type(self, x, hint) != hint) {
                hint = .none;
            };
            const b = if (k == .gen_incl or k == .gen_excl) pair(self, ctx, node, a0, a1, hint) else operand(self, ctx, a0, hint);
            if (!sp.get_tag_prop(b).is_integer) break :blk self.mismatch(node, b, .u64_type);
            break :blk sp.intern(.{ .array_type = .{ .len = sp.fresh_var(ap, node), .elem = b } });
        },
        .match, .stcmatch => patterns.h14_check_match(self, ctx, node, expected),
        .ret => blk: {
            _ = if (ctx.ret_type == .none) h09_check_expr(self, ctx, a0, .none) else check(self, ctx, a0, ctx.ret_type);
            break :blk .never_type;
        },
        .ret_void => if (ctx.ret_type != .none and sp.coerce(ap, .unit_type, ctx.ret_type) == .incompatible) self.report(.ret_type_mismatch, node, .unit_type, ctx.ret_type) else .never_type,
        .brk, .cont => if (ctx.loop_depth > 0) blk: {
            self.jumps[@intFromBool(k == .cont)] += 1;
            if (k == .brk and self.inits.exits.head > 0) self.inits.merge(self.inits.exits.buf[self.inits.exits.head - 1], 0);
            break :blk .never_type;
        } else self.report(if (k == .brk) .brk_outside_loop else .cont_outside_loop, node, 0, 0),
        .do, .@"defer" => blk: {
            _ = h09_check_expr(self, ctx, a0, .none);
            break :blk if (k == .do) .runit_type else .unit_type;
        },
        .deinit, .inlined_defer_deinit => blk: {
            const st = h09_check_expr(self, ctx, a0, if (k == .deinit) .none else expected);
            need_deinit(self, node, st);
            // a deinitialized local has to be written again before it is read
            if (k == .deinit and self.tree.kind(a0) == .identifier and self.node_decl[a0] != .none and !self.decl_pool.flags()[@intFromEnum(self.node_decl[a0])].is_global) {
                if (self.inits.tracked_at(self.node_decl[a0])) |i| self.inits.put(0, i, true) else self.inits.track(self.node_decl[a0]);
            }
            break :blk if (k == .deinit) .unit_type else st;
        },
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => control.h17_check_unwrap(self, ctx, node, expected),
        .def_fun => blk: { // lambdas and local functions are checked on the spot and see the enclosing locals
            const d = self.decl_pool.push_decl(.empty, node, .function, .none, .{});
            self.node_decl[node] = d;
            decls.h05_ensure_signature(self, d);
            const e = sp.apply_vars(ap, expected);
            const ft = self.decl_pool.tys()[@intFromEnum(d)];
            if (e != .none and sp.tag(e) == .function_type and ft != .none and sp.tag(ft) == .function_type and std.mem.eql(StaticPool.Index, sp.get(ft).function_type.params, sp.get(e).function_type.params) and sp.tag(sp.apply_vars(ap, sp.get(ft).function_type.ret)) == .type_var) _ = sp.unify(ap, sp.get(ft).function_type.ret, sp.get(e).function_type.ret);
            decls.h06_check_body(self, d);
            break :blk self.decl_pool.tys()[@intFromEnum(d)];
        },
        // type expressions in value position: the value is a type
        else => if (syntax.props(k).type_expr or k == .unify_variants or syntax.type_kind(self.tree, node) != .variable) (if (statics.deferred(self, ctx, node)) |v| sp.type_of(v) else types.meta_of(self, node)) else .unit_type,
    };
    return self.set(node, t);
}

pub fn h10_expect(self: *Resolver, node: NodeId, actual: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    // a poisoned value settles what it was expected to infer, so the error does not spread
    if (actual == .poison_type and expected != .none and self.static_pool.has_vars(expected)) _ = self.static_pool.unify(&self.abstract_pool, expected, .poison_type);
    if (expected == .none or actual == .poison_type or expected == .poison_type) return actual;
    // literals take the expected type directly (an unbound var: their default, which then binds the var)
    const a = if (syntax.is_literal(self.tree, node)) self.set(node, statics.literal_type(self, node, expected)) else actual;
    if (self.static_pool.coerce(&self.abstract_pool, a, expected) != .incompatible) return expected;
    return self.report(if (self.static_pool.unify(&self.abstract_pool, a, expected) == .infinite) .infinite_type else .type_mismatch, node, a, expected);
}

pub fn check(self: *Resolver, ctx: *FnCtx, n: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const t = h09_check_expr(self, ctx, n, expected);
    // a case with a payload is a constructor, a value of it needs the payload
    if (t != .poison_type and self.tree.kind(n) == .member and self.static_pool.tag(t) == .variant_case_type and self.static_pool.get(t).variant_case_type.payload != .none) return self.report(.type_mismatch, n, t, expected);
    return h10_expect(self, n, t, expected);
}

fn h13_check_member(self: *Resolver, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parent = self.tree.arg(node, 0);
    const name = self.name_pool.name_of(self.tree, self.src_bytes, self.tree.arg(node, 1));
    const pt = h09_check_expr(self, ctx, parent, .none);
    if (pt == .poison_type) return pt;
    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = sp.tag(pt) == .meta_type;
    const base = if (!on_type) sp.apply_vars(&self.abstract_pool, pt) else statics.deferred(self, ctx, parent) orelse return .poison_type;
    if (base == .poison_type) return base;
    if (sp.tag(base) == .type_var) return self.report(.uninferable_type, parent, base, .none);
    if (sp.templated(base) != .none) return generics.template_member(self, node, sp.templated(base), name);
    const view = if (self.tree.kind(parent) == .identifier and self.node_decl[parent] != .none) self.decl_pool.flags()[@intFromEnum(self.node_decl[parent])].is_view else false;
    if (view and generics.source_of(self, base) != .none and generics.template_member(self, node, sp.intern(.{ .template_type = generics.source_of(self, base) }), name) == .poison_type) return .poison_type;
    return switch (sp.lookup_member(base, name)) {
        .field => |f| if (on_type) self.report(.unknown_member, node, name, base) else f.ty,
        .method => |m| method(self, node, m),
        .trait_method => |m| method(self, node, sp.method_decl(m)),
        .case => |c| c,
        .builtin_len => .u64_type,
        .builtin_tag => if (on_type) self.report(.unknown_member, node, name, base) else sp.tag_type_of(base),
        .builtin_init, .builtin_deinit => sp.intern(.{ .function_type = .{ .category = .default, .params = &.{}, .ret = if (name == .init) base else .unit_type } }),
        .none => self.report(.unknown_member, node, name, base),
    };
}

fn method(self: *Resolver, node: NodeId, m: DeclPool.Index) StaticPool.Index {
    self.node_decl[node] = m;
    return types.decl_type(self, m);
}

fn elem_ptr(self: *Resolver, t0: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (t0 == .poison_type or t0 == .none) return false;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    return sp.is_ptr(t) and sp.get(sp.pointee(t)) != .array_type;
}

fn integer(self: *Resolver, ctx: *FnCtx, n: NodeId) bool {
    const t = operand(self, ctx, n, if (self.tree.kind(n) == .neg_num) .i64_type else .u64_type);
    if (t == .poison_type or self.static_pool.get_tag_prop(t).is_integer) return true;
    _ = self.report(.type_mismatch, n, t, .u64_type);
    return false;
}

fn folded(self: *Resolver, n: NodeId) bool {
    return syntax.is_literal(self.tree, n) or self.node_value[n] != .none and switch (self.tree.kind(n)) {
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap => true,
        else => false,
    };
}

fn numeric(self: *Resolver, node: NodeId, t: StaticPool.Index, result: StaticPool.Index) StaticPool.Index {
    if (self.static_pool.is_numeric(t) or self.static_pool.tag(t) == .type_var) return if (result == .none) t else result;
    return self.mismatch(node, t, .none);
}

fn operand(self: *Resolver, ctx: *FnCtx, n: NodeId, hint: StaticPool.Index) StaticPool.Index {
    return if (syntax.is_literal(self.tree, n)) check(self, ctx, n, hint) else h09_check_expr(self, ctx, n, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn pair(self: *Resolver, ctx: *FnCtx, node: NodeId, l: NodeId, r: NodeId, hint: StaticPool.Index) StaticPool.Index {
    var neg = false;
    const swap = syntax.is_literal(self.tree, l) and (!syntax.is_literal(self.tree, r) or self.tree.kind(syntax.literal_core(self.tree, r, &neg)) == .float);
    const t1 = operand(self, ctx, if (swap) r else l, hint);
    const add = self.tree.kind(node) == .binary_add;
    if ((add or !swap and self.tree.kind(node) == .binary_sub) and elem_ptr(self, t1)) return if (integer(self, ctx, if (swap) l else r)) t1 else .poison_type;
    const t2 = operand(self, ctx, if (swap) l else r, t1);
    if (add and elem_ptr(self, t2) and self.static_pool.get_tag_prop(t1).is_integer) return t2;
    if (t1 == .poison_type or t2 == .poison_type) return .poison_type;
    if (self.static_pool.tag(t1) == .meta_type and self.static_pool.tag(t2) == .meta_type) return t1;
    var j = self.static_pool.join(&self.abstract_pool, t1, t2);
    if (j.ty == .none) j = self.static_pool.join(&self.abstract_pool, self.static_pool.deref(&self.abstract_pool, t1), self.static_pool.deref(&self.abstract_pool, t2)); // `self == Toggle.On`
    return if (j.ty == .none) self.report(.type_mismatch, node, t1, t2) else j.ty;
}

fn need_deinit(self: *Resolver, node: NodeId, t0: StaticPool.Index) void {
    const t = self.static_pool.apply_vars(&self.abstract_pool, t0);
    if (t != .poison_type and self.static_pool.lookup_member(t, .deinit) == .none)
        self.doc.h21_report(.no_deinit, node, t, 0);
}
