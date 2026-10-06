const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const Decls = @import("Decls.zig");
const NodeId = ParseTree.NodeId;

// expressions: the walk over a body, every node gets its type here or in the module of its kind
const Exprs = @This();

pub fn res(self: *Exprs) *Resolver {
    return @alignCast(@fieldParentPtr("exprs", self));
}

// the type of a node, `expected` only guides it (literals, empty arrays, lambdas)
pub fn infer(self: *Exprs, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const ap = &r.abstract_pool;
    const a0 = r.tree.arg(node, 0);
    const a1 = r.tree.arg(node, 1);
    const k = r.tree.kind(node);
    if (ctx.interpreted and r.tree.props(node).stc and !r.doc.has(node)) _ = r.report(.redundant_stc, node, 0, 0);
    const t: StaticPool.Index = switch (k) {
        .int, .float, .char, .string, .boolean_true, .boolean_false => r.statics.literal_type(node, expected),
        .identifier, .identifier_self => blk: {
            const d = r.calls.overload_for(node, r.decls.use(node), expected);
            if (d == .none) break :blk .poison_type;
            if (r.inits.unwritten(d)) r.doc.report(.use_before_initialization, node, r.decl_pool.get_name(d), 0);
            const ty = r.decl_pool.get_ty(d);
            break :blk if (ty == .none) .poison_type else ty;
        },
        .capture => self.infer(ctx, a0, expected),
        .block => blk: {
            r.scopes.push();
            defer r.scopes.pop();
            var last: StaticPool.Index = .unit_type;
            const stmts = r.tree.manychildren(node);
            // local functions are visible in their whole block
            for (stmts) |s| {
                const st = Decls.Stmt.from_node(r, s);
                if (st.kind != .function or st.assignees.len != 1 or st.type == 0 or r.tree.kind(st.type) != .type_fun) continue;
                if (r.scopes.in_scope(r.name_pool.name_of(st.assignees[0])) != .none) continue;
                const d = r.decls.declare_local(r.name_pool.name_of(st.assignees[0]), st.node, .function, .none);
                r.decl_pool.set_flags(d, st.flags);
                r.node_decl[st.assignees[0]] = d;
            }
            for (stmts, 0..) |s, i| {
                const declares = r.tree.props(s).declares;
                if (!declares) r.scopes.push();
                last = self.infer(ctx, s, if (i + 1 == stmts.len) expected else .none);
                if (!declares) r.scopes.pop();
            }
            break :blk last;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => r.decls.check_stmt(ctx, node),
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => blk: {
            const lt = r.mutability.check_assignable(ctx, a0);
            if ((k == .assign_add or k == .assign_sub) and sp.elem_ptr(ap, lt)) break :blk if (self.integer(ctx, a1)) .unit_type else .poison_type;
            _ = self.check(ctx, a1, lt);
            break :blk self.numeric(node, lt, .unit_type);
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix => blk: {
            const lt = r.mutability.check_assignable(ctx, a0);
            break :blk if (sp.elem_ptr(ap, lt)) lt else self.numeric(node, lt, lt);
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and => blk: {
            const j = self.pair(ctx, node, a0, a1, if (sp.is_numeric(expected)) expected else .none);
            const integral = switch (k) {
                .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod => false,
                else => true,
            };
            const rt = if ((k == .binary_add or k == .binary_sub) and sp.elem_ptr(ap, j)) j else if (integral and !sp.get_tag_prop(j).is_integer and sp.tag(j) != .type_var) r.mismatch(node, j, .none) else self.numeric(node, j, j);
            // arithmetic on constants is folded, a division by zero is an error as soon as it can be seen
            if (rt != .poison_type and !ctx.abstract and self.folded(a0) and self.folded(a1)) {
                _ = r.set(node, rt);
                _ = r.interpreter.eval_static(ctx, node);
            }
            break :blk rt;
        },
        .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => blk: {
            const j = self.pair(ctx, node, a0, a1, .none);
            break :blk if (j == .poison_type) j else .bool_type;
        },
        .binary_logic_or, .binary_logic_and => blk: {
            const m = r.inits.count;
            defer r.inits.release(m);
            const w = r.flow.condition(ctx, node);
            r.inits.copy(0, w[0]);
            r.inits.merge(0, w[1]);
            break :blk .bool_type;
        },
        .binary_logic_xor => blk: {
            _ = self.check(ctx, a0, .bool_type);
            _ = self.check(ctx, a1, .bool_type);
            break :blk .bool_type;
        },
        .neg_logic => blk: { // `!` is logical on bools and bitwise on integers
            const st = self.infer(ctx, a0, expected);
            break :blk if (st == .bool_type or sp.get_tag_prop(st).is_integer) st else r.mismatch(node, st, .bool_type);
        },
        .neg_num => if (r.tree.is_literal(node)) r.statics.literal_type(node, expected) else self.numeric(node, self.infer(ctx, a0, expected), .none),
        .fun_call, .with => r.calls.check_call(ctx, node),
        .member => self.check_member(ctx, node),
        .array_index => blk: {
            var st = sp.apply_vars(ap, self.infer(ctx, a0, .none));
            if (r.tree.props(a1).range) break :blk r.report(.genexpr_index, a1, 0, 0);
            const it = self.infer(ctx, a1, .none);
            if (!sp.get_tag_prop(it).is_integer) _ = r.mismatch(a1, it, .u64_type);
            if (st == .poison_type) break :blk st;
            const through_ptr = sp.is_ptr(st);
            st = sp.pointee(st);
            // pointers index like arrays (`*u8 buf; buf[i]`), arrays auto-deref once
            const elem = if (sp.get(st) == .array_type) sp.get(st).array_type.elem else if (through_ptr) st else break :blk r.report(.type_mismatch, a0, st, .none);
            // lengths of realizations and stcfun bodies are the interpreter's to check, their constant indices may be guarded
            if (!ctx.interpreted and !(ctx.decl != .none and r.generics.template_of.contains(ctx.decl)) and sp.static_len(st) != null and r.tree.is_literal(a1)) {
                const i = r.statics.static_int(ctx, a1) orelse break :blk elem;
                if (i < 0 or i >= sp.static_len(st).?) _ = r.report(.static_eval_failed, a1, 0, 0);
            }
            break :blk elem;
        },
        .dereference => blk: {
            const st = sp.apply_vars(ap, self.infer(ctx, a0, .none));
            break :blk if (sp.is_ptr(st)) sp.pointee(st) else r.mismatch(node, st, .none);
        },
        .address_of => blk: {
            if (r.tree.kind(a0) == .identifier) r.inits.written(r.scopes.lookup(&r.decl_pool, r.name_pool.name_of(a0)));
            const exp = sp.apply_vars(ap, expected);
            const st = self.infer(ctx, a0, if (sp.is_ptr(exp)) sp.pointee(exp) else .none);
            // write access only to what could be written directly
            const mutable = r.mutability.writable(a0) == .ok;
            if (mutable and exp != .none and sp.tag(exp) == .ptr_mut_type) r.mutability.wrote(a0);
            break :blk if (st == .poison_type) st else sp.ptr_of(st, mutable);
        },
        .array, .array_empty => blk: {
            const exp = sp.apply_vars(ap, expected);
            var elem = sp.array_elem(exp);
            const given = elem != .none;
            const elems = if (k == .array) r.tree.manychildren(node) else &[_]NodeId{};
            // without an expectation the elements join, literals last: `[1, -2]` is [2]i32, `[x, 300]` with u8 x [2]u32
            for (elems) |e| {
                if (!given and r.tree.is_literal(e)) continue;
                const et = self.infer(ctx, e, elem);
                const joined = if (given or elem == .none) .none else sp.join(ap, elem, et).ty;
                if (elem == .none) elem = et else if (joined != .none) elem = joined else _ = self.expect(e, et, elem);
            }
            if (!given) {
                for (elems) |e| if (r.tree.is_literal(e)) {
                    _ = self.infer(ctx, e, .none);
                };
                if (elem == .none) elem = r.flow.literals_type(elems);
                if (elem == .none and elems.len > 0) elem = r.node_type[elems[0]];
                for (elems) |e| if (r.tree.is_literal(e) and elem != .none) {
                    const j = sp.join(ap, elem, r.statics.literal_type(e, elem)).ty;
                    if (j != .none) elem = j;
                };
                for (elems) |e| if (r.tree.is_literal(e)) {
                    _ = self.expect(e, r.node_type[e], elem);
                };
            }
            if (elem == .none) elem = sp.fresh_var(ap, node);
            break :blk sp.array_of(elems.len, elem);
        },
        .as => blk: {
            const from = sp.apply_vars(ap, self.infer(ctx, a0, .none));
            const to = r.types.cast_target(ctx, a1, from);
            const lost = to == .poison_type or from == .poison_type or sp.get(to) == .array_type and sp.get(to).array_type.len == .poison_type or sp.get(to) == .ptr_type and sp.get(sp.get(to).ptr_type.child) == .array_type and sp.get(sp.get(to).ptr_type.child).array_type.len == .poison_type;
            break :blk if (lost) .poison_type else if (sp.cast(from, to) == .invalid) r.report(.invalid_cast, node, from, to) else to;
        },
        .asbits => blk: {
            const from = sp.apply_vars(ap, self.infer(ctx, a0, .none));
            const to = r.types.lower(ctx, a1);
            if (from == .poison_type or to == .poison_type) break :blk .poison_type;
            break :blk if (!sp.get_tag_prop(from).has_layout or !sp.get_tag_prop(to).has_layout or sp.layout(to).size < sp.layout(from).size) r.report(.invalid_cast, node, from, to) else to;
        },
        .oftype => blk: {
            const vt = sp.deref(ap, self.infer(ctx, a0, .none));
            const ot0 = if (ctx.interpreted) r.statics.deferred(ctx, a1) orelse .none else r.types.lower(ctx, a1);
            const ot = if (ot0 != .none and sp.tag(ot0) == .generic) r.types.lower(ctx, a1) else ot0;
            r.node_value[a1] = ot;
            r.node_value[node] = if (ot == .none or (ctx.interpreted and sp.tag(vt) == .meta_type)) .none else if (sp.templated(ot) != .none) (if (r.generics.realizes(vt, ot)) .bool_true else .bool_false) else if (sp.templated(vt) != .none) .none else if (vt == ot or sp.implements(vt, ot)) .bool_true else if (sp.tag(vt) == .trait_type) .none else .bool_false;
            break :blk .bool_type;
        },
        .typeof, .sizeof => blk: {
            _ = self.infer(ctx, a0, .none);
            if (r.tree.kind(a0) == .identifier and r.generics.is_template(r.node_decl[a0])) break :blk r.report(.unrealized_template, a0, 0, 0);
            _ = r.statics.try_static(ctx, node);
            break :blk if (k == .typeof) .type_type else .u64_type;
        },
        .if_then, .if_else, .stcif_then, .stcif_else => r.flow.check_if(ctx, node, expected),
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => r.flow.check_loop(ctx, node, expected),
        // ranges are sequences of their bound type, so `for` and slicing treat them like arrays
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => blk: {
            const exp = sp.apply_vars(ap, expected);
            const e = sp.array_elem(exp);
            var hint = if (e != .none) e else if (sp.is_numeric(exp)) exp else .none;
            const g = ParseTree.Range.from_node(r.tree, node);
            for ([_]NodeId{ g.lo, g.hi }) |x| if (x != 0 and hint != .none and r.tree.is_literal(x) and r.statics.literal_type(x, hint) != hint) {
                hint = .none;
            };
            const b = if (g.lo != 0 and g.hi != 0) self.pair(ctx, node, a0, a1, hint) else self.operand(ctx, a0, hint);
            if (!sp.get_tag_prop(b).is_integer) break :blk r.mismatch(node, b, .u64_type);
            break :blk sp.intern(.{ .array_type = .{ .len = sp.fresh_var(ap, node), .elem = b } });
        },
        .match, .stcmatch => r.patterns.check_match(ctx, node, expected),
        .ret => blk: {
            _ = if (ctx.ret_type == .none) self.infer(ctx, a0, .none) else self.check(ctx, a0, ctx.ret_type);
            break :blk .never_type;
        },
        .ret_void => if (ctx.ret_type != .none and sp.coerce(ap, .unit_type, ctx.ret_type) == .incompatible) r.report(.ret_type_mismatch, node, .unit_type, ctx.ret_type) else .never_type,
        .brk, .cont => r.flow.jump(ctx, node, k),
        .do, .@"defer" => blk: {
            _ = self.infer(ctx, a0, .none);
            break :blk if (k == .do) .runit_type else .unit_type;
        },
        .deinit, .inlined_defer_deinit => blk: {
            const st = self.infer(ctx, a0, if (k == .deinit) .none else expected);
            const dt = sp.apply_vars(ap, st);
            if (dt != .poison_type and sp.lookup_member(dt, .deinit) == .none) r.doc.report(.no_deinit, node, dt, 0);
            // a deinitialized local has to be written again before it is read
            if (k == .deinit and r.tree.kind(a0) == .identifier and r.node_decl[a0] != .none and !r.decl_pool.get_flags(r.node_decl[a0]).is_global) {
                if (r.inits.tracked_at(r.node_decl[a0])) |i| r.inits.put(0, i, true) else r.inits.track(r.node_decl[a0]);
            }
            break :blk if (k == .deinit) .unit_type else st;
        },
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => r.flow.check_unwrap(ctx, node, expected),
        .def_fun => blk: { // lambdas and local functions are checked on the spot and see the enclosing locals
            const d = r.decl_pool.push_decl(.empty, node, .function, .none, .{});
            r.node_decl[node] = d;
            r.decls.ensure_signature(d);
            const e = sp.apply_vars(ap, expected);
            const ft = r.decl_pool.get_ty(d);
            if (e != .none and sp.tag(e) == .function_type and ft != .none and sp.tag(ft) == .function_type and std.mem.eql(StaticPool.Index, sp.get(ft).function_type.params, sp.get(e).function_type.params) and sp.tag(sp.apply_vars(ap, sp.get(ft).function_type.ret)) == .type_var) _ = sp.unify(ap, sp.get(ft).function_type.ret, sp.get(e).function_type.ret);
            r.decls.check_body(d);
            break :blk r.decl_pool.get_ty(d);
        },
        // type expressions in value position: the value is a type
        else => if (r.tree.props(node).type_expr or k == .unify_variants or r.decls.type_kind(node) != .variable) (if (r.statics.deferred(ctx, node)) |v| sp.type_of(v) else r.types.meta_of(node)) else .unit_type,
    };
    return r.set(node, t);
}

pub fn expect(self: *Exprs, node: NodeId, actual: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    // a poisoned value settles what it was expected to infer, so the error does not spread
    if (actual == .poison_type and expected != .none and r.static_pool.has_vars(expected)) _ = r.static_pool.unify(&r.abstract_pool, expected, .poison_type);
    if (expected == .none or actual == .poison_type or expected == .poison_type) return actual;
    // literals take the expected type directly (an unbound var: their default, which then binds the var)
    const a = if (r.tree.is_literal(node)) r.set(node, r.statics.literal_type(node, expected)) else actual;
    if (r.static_pool.coerce(&r.abstract_pool, a, expected) != .incompatible) return expected;
    return r.report(if (r.static_pool.unify(&r.abstract_pool, a, expected) == .infinite) .infinite_type else .type_mismatch, node, a, expected);
}

// the type of a node held to `expected`
pub fn check(self: *Exprs, ctx: *FnCtx, n: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const t = self.infer(ctx, n, expected);
    // a case with a payload is a constructor, a value of it needs the payload
    if (t != .poison_type and r.tree.kind(n) == .member and r.static_pool.tag(t) == .variant_case_type and r.static_pool.get(t).variant_case_type.payload != .none) return r.report(.type_mismatch, n, t, expected);
    return self.expect(n, t, expected);
}

fn check_member(self: *Exprs, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const parent = r.tree.arg(node, 0);
    const name = r.name_pool.name_of(r.tree.arg(node, 1));
    const pt = self.infer(ctx, parent, .none);
    if (pt == .poison_type) return pt;
    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = sp.tag(pt) == .meta_type;
    const base = if (!on_type) sp.apply_vars(&r.abstract_pool, pt) else r.statics.deferred(ctx, parent) orelse return .poison_type;
    if (base == .poison_type) return base;
    if (sp.tag(base) == .type_var) return r.report(.uninferable_type, parent, base, .none);
    if (sp.templated(base) != .none) return r.generics.template_member(node, sp.templated(base), name);
    const view = if (r.tree.kind(parent) == .identifier and r.node_decl[parent] != .none) r.decl_pool.get_flags(r.node_decl[parent]).is_view else false;
    if (view and r.generics.source_of(base) != .none and r.generics.template_member(node, sp.intern(.{ .template_type = r.generics.source_of(base) }), name) == .poison_type) return .poison_type;
    return switch (sp.lookup_member(base, name)) {
        .field => |f| if (on_type) r.report(.unknown_member, node, name, base) else f.ty,
        .method => |m| self.method(node, m),
        .trait_method => |m| self.method(node, sp.method_decl(m)),
        .case => |c| c,
        .builtin_len => .u64_type,
        .builtin_tag => if (on_type) r.report(.unknown_member, node, name, base) else sp.tag_type_of(base),
        .builtin_init, .builtin_deinit => sp.intern(.{ .function_type = .{ .category = .default, .params = &.{}, .ret = if (name == .init) base else .unit_type } }),
        .none => r.report(.unknown_member, node, name, base),
    };
}

fn method(self: *Exprs, node: NodeId, m: DeclPool.Index) StaticPool.Index {
    const r = self.res();
    r.node_decl[node] = m;
    return r.types.decl_type(m);
}

fn integer(self: *Exprs, ctx: *FnCtx, n: NodeId) bool {
    const r = self.res();
    const t = self.operand(ctx, n, if (r.tree.kind(n) == .neg_num) .i64_type else .u64_type);
    if (t == .poison_type or r.static_pool.get_tag_prop(t).is_integer) return true;
    _ = r.report(.type_mismatch, n, t, .u64_type);
    return false;
}

fn folded(self: *Exprs, n: NodeId) bool {
    const r = self.res();
    return r.tree.is_literal(n) or r.node_value[n] != .none and switch (r.tree.kind(n)) {
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and => true,
        else => false,
    };
}

fn numeric(self: *Exprs, node: NodeId, t: StaticPool.Index, result: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    if (r.static_pool.is_numeric(t) or r.static_pool.tag(t) == .type_var) return if (result == .none) t else result;
    return r.mismatch(node, t, .none);
}

fn operand(self: *Exprs, ctx: *FnCtx, n: NodeId, hint: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    return if (r.tree.is_literal(n)) self.check(ctx, n, hint) else self.infer(ctx, n, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn pair(self: *Exprs, ctx: *FnCtx, node: NodeId, l: NodeId, rhs: NodeId, hint: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    var neg = false;
    const swap = r.tree.is_literal(l) and (!r.tree.is_literal(rhs) or r.tree.kind(r.tree.literal_core(rhs, &neg)) == .float);
    const t1 = self.operand(ctx, if (swap) rhs else l, hint);
    const add = r.tree.kind(node) == .binary_add;
    if ((add or !swap and r.tree.kind(node) == .binary_sub) and r.static_pool.elem_ptr(&r.abstract_pool, t1)) return if (self.integer(ctx, if (swap) l else rhs)) t1 else .poison_type;
    const t2 = self.operand(ctx, if (swap) l else rhs, t1);
    if (add and r.static_pool.elem_ptr(&r.abstract_pool, t2) and r.static_pool.get_tag_prop(t1).is_integer) return t2;
    if (t1 == .poison_type or t2 == .poison_type) return .poison_type;
    if (r.static_pool.tag(t1) == .meta_type and r.static_pool.tag(t2) == .meta_type) return t1;
    var j = r.static_pool.join(&r.abstract_pool, t1, t2);
    if (j.ty == .none) j = r.static_pool.join(&r.abstract_pool, r.static_pool.deref(&r.abstract_pool, t1), r.static_pool.deref(&r.abstract_pool, t2)); // `self == Toggle.On`
    return if (j.ty == .none) r.report(.type_mismatch, node, t1, t2) else j.ty;
}
