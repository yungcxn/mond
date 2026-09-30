const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const calls = @import("calls.zig");
const statics = @import("statics.zig");
const StaticPool = @import("../StaticPool.zig");
const Decl = Resolver.Decl;
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const class = Resolver.class;
const is_range_kind = Resolver.is_range_kind;
const meta = Resolver.meta;
const prim_types = Resolver.prim_types;
const NamePool = @import("../NamePool.zig");

pub fn meta_of(self: *Resolver, node: NodeId) StaticPool.Index {
    return meta(self.type_kind(node), if (self.nk(node) == .unify_variants) .variant_type else .type_type);
}

pub fn h07_lower_type(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(node);
    if (prim_types[@intFromEnum(k)] != .none) return prim_types[@intFromEnum(k)];
    return switch (k) {
        .capture => h07_lower_type(self, ctx, self.arg(node, 0)),
        .typeof => blk: {
            const t = self.h09_check_expr(ctx, self.arg(node, 0), .none);
            break :blk if (self.nk(self.arg(node, 0)) == .identifier_self) sp.pointee(t) else t;
        },
        .type_ptr, .type_ptrmut => sp.intern(.{ .ptr_type = .{ .child = h07_lower_type(self, ctx, self.arg(node, 0)), .mutable = k == .type_ptrmut } }),
        // an unlengthed array gets a var as its length: inferred from the value, or per call for parameters
        // record fields, `main` parameters and lengths nothing fixes become runtime-length arrays (dynify, s3)
        .type_array_unlengthed => sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = h07_lower_type(self, ctx, self.arg(node, 0)) } }),
        .type_array => blk: {
            const len = statics.deferred(self, ctx, self.arg(node, 0)) orelse .poison_type;
            const n = if (sp.tag(len) == .int_value) sp.intern(.{ .int = .{ .ty = .u64_type, .bits = sp.get(len).int.bits } }) else if (len == .poison_type) len else self.report(.not_static, self.arg(node, 0), len, 0);
            break :blk sp.intern(.{ .array_type = .{ .len = n, .elem = h07_lower_type(self, ctx, self.arg(node, 1)) } });
        },
        .def_fun_declaration => fun_type(self, ctx, node, .default, .unit_type, .none),
        else => blk: {
            const v = statics.deferred(self, ctx, node) orelse .poison_type;
            if (sp.tag(v) == .generic and sp.tag(sp.get(self.dp(.ty, sp.get(v).static_fun.decl).*).function_type.ret) == .meta_type) break :blk sp.intern(.{ .template_type = sp.get(v).static_fun.decl });
            break :blk if (v == .poison_type or sp.class(v).is_type) v else self.report(.not_a_type, node, v, .none);
        },
    };
}

pub fn static_type(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(node);
    return switch (k) {
        .unify_variants => blk: {
            var members: [64]StaticPool.Index = undefined;
            var n: usize = 0;
            for ([_]NodeId{ self.arg(node, 0), self.arg(node, 1) }) |side| {
                const t = h07_lower_type(self, ctx, side);
                if (sp.tag(t) == .variant_union_type) {
                    const m = sp.get(t).variant_union_type;
                    @memcpy(members[n..][0..m.len], m);
                    n += m.len;
                } else if (sp.tag(t) == .variant_type) {
                    members[n] = t;
                    n += 1;
                } else _ = self.mismatch(side, t, .variant_type);
            }
            break :blk sp.intern(.{ .variant_union_type = members[0..n] });
        },
        .def_type, .def_type_packed, .def_type_assertsize, .def_type_implof, .def_variant, .def_variant_unionsized, .def_variant_tagof, .def_variant_assertsize, .def_variant_implof, .def_trait, .def_trait_implof => blk: {
            const d = self.push_decl(.empty, node, self.type_kind(node), .none, .{});
            self.node_decl[node] = d;
            break :blk h19_check_type_def(self, ctx, d, node);
        },
        .def_fun => blk: {
            _ = self.h09_check_expr(ctx, node, .none);
            break :blk self.dp(.value, self.node_decl[node]).*;
        },
        else => if (class(k).type_expr) h07_lower_type(self, ctx, node) else self.report(.not_static, node, 0, 0),
    };
}

pub fn h19_check_type_def(self: *Resolver, ctx: *FnCtx, decl: Decl.Index, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const w = self.definition(node);
    const c = w.core;
    const body = w.body;
    const tagof = w.tagof;
    const ck = self.nk(c);
    const is_trait = ck == .def_trait or ck == .def_trait_implof;
    var first = self.decls.len();
    // reserved first (or already by h20), so fields can point back at the type (`*Tree`)
    if (self.dp(.value, decl).* == .none) self.dp(.value, decl).* = sp.reserve_nominal(decl);
    const ty = self.dp(.value, decl).*;
    self.dp(.ty, decl).* = meta(self.type_kind(c), .type_type);
    if (self.dp(.state, decl).* == .resolving_signature) self.dp(.state, decl).* = .signature_ready;
    self.h03_push_scope();
    defer self.h04_pop_scope();

    var traits: [32]StaticPool.Index = undefined;
    var nt: usize = 0;
    var own: StaticPool.Index = .none; // the anonymous `!{..}` body
    if (!is_trait and body != 0) {
        const impls = if (self.nk(body) == .def_trait_implof) self.kids(self.arg(body, 0)) else &[_]NodeId{};
        const members = self.arg(body, if (self.nk(body) == .def_trait_implof) 1 else 0);
        if (self.kids(members).len > 0) {
            own = trait_body(self, ctx, members, .none, ty, &.{}, decl);
            traits[0] = own;
            nt = 1;
        }
        for (impls) |t| {
            traits[nt] = h07_lower_type(self, ctx, t);
            nt += @intFromBool(traits[nt] != .poison_type);
        }
    }

    switch (ck) {
        .def_trait, .def_trait_implof => {
            var supers: [32]StaticPool.Index = undefined;
            const impls = if (ck == .def_trait_implof) self.kids(self.arg(c, 0)) else &[_]NodeId{};
            for (impls, 0..) |t, i| supers[i] = h07_lower_type(self, ctx, t);
            own = trait_body(self, ctx, self.arg(c, if (ck == .def_trait_implof) 1 else 0), ty, .none, supers[0..impls.len], decl);
        },
        .def_variant, .def_variant_unionsized => {
            const params = self.kids(self.arg(c, 0));
            var cases: [256]StaticPool.Index = undefined;
            var payload_case: ?usize = null;
            var payloads: usize = 0;
            var next_tag: u64 = 0;
            for (params, 0..) |pn, i| {
                var q = pn;
                var tag_node: NodeId = 0;
                var payload_node: NodeId = 0;
                if (self.nk(q) == .partial__variant_def_param_tagged) {
                    tag_node = self.arg(q, 1);
                    q = self.arg(q, 0);
                }
                if (self.nk(q) == .partial__variant_def_param_typed) {
                    payload_node = self.arg(q, 1);
                    q = self.arg(q, 0);
                }
                const payload = if (payload_node == 0) .none else h19_check_type_def(self, ctx, self.push_decl(.empty, payload_node, .record, .none, .{}), payload_node);
                if (payload != .none) {
                    payload_case = i;
                    payloads += 1;
                }
                const tv = if (tag_node == 0) sp.intern(.{ .int = .{ .ty = .u64_type, .bits = next_tag } }) else statics.h08_eval_static(self, ctx, tag_node);
                if (sp.tag(tv) == .int_value) next_tag = sp.get(tv).int.bits +% 1;
                cases[i] = self.set(self.arg(q, 0), sp.intern(.{ .variant_case_type = .{ .variant = ty, .case = @intCast(i), .name = self.name_of(self.arg(q, 0)), .tag = tv, .payload = payload } }));
            }
            // variants are always tagged, without tagof by the smallest tag type for their case count
            const mode: StaticPool.VariantTagMode = if (tagof != 0 and self.nk(tagof) == .identifier_self) .self else .int;
            var tag_ty: StaticPool.Index = if (tagof == 0) StaticPool.smallest_tag_type(params.len) else if (mode == .self) .none else h07_lower_type(self, ctx, tagof);
            if (mode == .self) {
                // the one payload type encodes the other cases in bit patterns it never uses
                if (payloads != 1) _ = self.report(.self_tag_without_niche, tagof, payloads, 0) else {
                    const fields = sp.get(sp.get(cases[payload_case.?]).variant_case_type.payload).custom_type.field_types;
                    tag_ty = if (fields.len == 1 and sp.class(fields[0]).is_integer) fields[0] else self.report(.self_tag_without_niche, tagof, 0, 0);
                }
            }
            if (tag_ty != .none and tag_ty != .poison_type) for (params, 0..) |pn, i| {
                const case = sp.get(cases[i]).variant_case_type;
                if ((mode == .int or case.payload == .none) and sp.tag(case.tag) == .int_value and !sp.fits(case.tag, tag_ty)) _ = self.report(.tag_overflow, pn, case.tag, tag_ty);
            };
            sp.complete_nominal(ty, .{ .variant_type = .{ .decl = decl, .tag_mode = mode, .tag_type = tag_ty, .is_unionsized = ck == .def_variant_unionsized, .cases = cases[0..params.len], .traits = traits[0..nt] } });
        },
        else => { // records: `*(..)`, `**(..)` and payload tuples
            const fields = self.fields_of_node(c);
            var names: [64]NamePool.Index = undefined;
            var types: [64]StaticPool.Index = undefined;
            for (fields, 0..) |f, i| {
                const p = self.param(f);
                types[i] = dynify(self, realized_type(self, ctx, p.ty));
                names[i] = self.name_at(p, i);
            }
            sp.complete_nominal(ty, .{ .custom_type = .{ .decl = decl, .is_packed = ck == .def_type_packed, .field_names = names[0..fields.len], .field_types = types[0..fields.len], .traits = traits[0..nt] } });
            // defaults and where-clauses see the fields by name, the snapshot's locals start at the first field
            first = self.decls.len();
            for (fields, 0..) |f, i| {
                const fd = self.h02_declare_local(names[i], f, .field, types[i]);
                self.dp(.flags, fd).is_mut = self.param(f).is_mut;
                calls.link(self, self.param(f).name, fd, types[i]);
            }
            for (fields, 0..) |f, i| {
                const p = self.param(f);
                if (p.default != 0) _ = self.check(ctx, p.default, types[i]);
                self.check_guards(ctx, p, types[i]);
            }
        },
    }
    // member bodies once the type is complete, then trait conformance
    if (own != .none) {
        const b = sp.get(own).trait_type.decl;
        for (0..sp.get(own).trait_type.member_names.len) |i| self.h06_check_body(b.member(i));
    }
    if (!is_trait) {
        for (traits[0..nt]) |t| if (t != own and sp.tag(t) == .trait_type) conform(self, ty, own, t, node);
        if (sp.layout(ty).state == .infinite) _ = self.report(.recursive_by_value_type, node, ty, .none);
        statics.snapshot(self, decl, node, first);
    }
    if (w.size != 0) {
        const v = statics.h08_eval_static(self, ctx, w.size);
        const want = if (sp.class(v).is_type) sp.layout(v).size else if (sp.tag(v) == .int_value) sp.get(v).int.bits else 0;
        if (v != .poison_type and sp.layout(ty).size != want) _ = self.report(.assertsize_failed, w.size, sp.layout(ty).size, want);
    }
    return ty;
}

// a trait body: one row for the body (its value is the self type), then one row per function member,
// contiguous, so member i is row + 1 + i. static members (`stc u32 MASK = ..`) are plain locals of the body.
fn trait_body(self: *Resolver, ctx: *FnCtx, body: NodeId, reserved: StaticPool.Index, self_ty: StaticPool.Index, supers: []const StaticPool.Index, of: Decl.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const b = self.push_decl(if (self_ty == .none) self.dp(.name, of).* else .empty, body, .trait, .trait_type, .{});
    if (self.realized_args.get(of)) |a| self.realized_args.put(self.alloc, b, a) catch @panic("OOM");
    if (self.template_of.get(of)) |g| self.template_of.put(self.alloc, b, g) catch @panic("OOM");
    const tr = if (reserved != .none) reserved else sp.reserve_nominal(b);
    self.dp(.value, b).* = if (self_ty != .none) self_ty else tr;
    var names: [64]NamePool.Index = undefined;
    var n: usize = 0;
    for (self.kids(body)) |s| {
        const m = self.statement(s);
        if (!m.is_member()) continue;
        names[n] = self.name_of(m.ids[0]);
        self.node_decl[m.ids[0]] = self.push_decl(names[n], m.node, .trait_member, .none, m.flags);
        n += 1;
    }
    for (self.kids(body)) |s| if (!self.statement(s).is_member()) {
        _ = self.h11_check_assign(ctx, s);
    };
    var types: [64]StaticPool.Index = undefined;
    for (0..n) |i| types[i] = decl_type(self, b.member(i));
    sp.complete_nominal(tr, .{ .trait_type = .{ .decl = b, .member_names = names[0..n], .member_types = types[0..n], .supers = supers } });
    return tr;
}

pub fn decl_type(self: *Resolver, d: Decl.Index) StaticPool.Index {
    self.h05_ensure_signature(d);
    const t = self.dp(.ty, d).*;
    return if (t == .none) .poison_type else t;
}

// implof: every member of the trait and its supers exists with the same signature (`typeof self` read as the type),
// members with a default implementation may be left out
fn conform(self: *Resolver, ty: StaticPool.Index, own: StaticPool.Index, trait: StaticPool.Index, node: NodeId) void {
    const sp = &self.static_pool;
    for (0..sp.get(trait).trait_type.member_names.len) |i| {
        const tt = sp.get(trait).trait_type;
        if (self.nk(self.value_node(tt.decl.member(i))) == .def_fun) continue;
        const name = tt.member_names[i];
        const want = tt.member_types[i];
        const m = if (own == .none) StaticPool.Member.none else sp.lookup_member(own, name);
        if (m != .trait_method) {
            self.doc.h21_report(.trait_member_missing, node, name, trait);
            continue;
        }
        const have = sp.apply_vars(&self.abstract_pool, sp.get(own).trait_type.member_types[m.trait_method.index]);
        const w = sp.apply_vars(&self.abstract_pool, want);
        if (!same_sig(self, have, w, trait, ty)) self.doc.h21_report(.trait_signature_mismatch, node, name, trait);
    }
    for (0..sp.get(trait).trait_type.supers.len) |i| conform(self, ty, own, sp.get(trait).trait_type.supers[i], node);
}

fn same_sig(self: *Resolver, have: StaticPool.Index, want: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (have == want or have == .poison_type or want == .poison_type) return true;
    if (sp.tag(have) != .function_type or sp.tag(want) != .function_type) return false;
    const h = sp.get(have).function_type;
    const w = sp.get(want).function_type;
    if (h.params.len != w.params.len) return false;
    for (h.params, w.params) |a, b| if (!same_as(self, a, b, trait, ty)) return false;
    return same_as(self, h.ret, w.ret, trait, ty);
}

// a == b with the trait read as the implementing type anywhere inside (pointers, arrays, function types)
fn same_as(self: *Resolver, a: StaticPool.Index, b: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (a == b or a == .poison_type or (b == trait and a == ty)) return true;
    if (sp.tag(a) != sp.tag(b)) return false;
    return switch (sp.get(a)) {
        .ptr_type => |p| p.mutable == sp.get(b).ptr_type.mutable and same_as(self, p.child, sp.get(b).ptr_type.child, trait, ty),
        .array_type => |x| x.len == sp.get(b).array_type.len and same_as(self, x.elem, sp.get(b).array_type.elem, trait, ty),
        .function_type => |f| f.params.len == sp.get(b).function_type.params.len and for (0..f.params.len) |i| {
            if (!same_as(self, sp.get(a).function_type.params[i], sp.get(b).function_type.params[i], trait, ty)) break false;
        } else same_as(self, sp.get(a).function_type.ret, sp.get(b).function_type.ret, trait, ty),
        else => false,
    };
}

pub fn fun_type(self: *Resolver, ctx: *FnCtx, v: NodeId, category: StaticPool.FunType.Category, ret: StaticPool.Index, self_param: StaticPool.Index) StaticPool.Index {
    const header = self.arg(v, 0);
    const params = self.params_of(v);
    const off = @intFromBool(self_param != .none);
    var buf: [64]StaticPool.Index = undefined;
    buf[0] = self_param;
    for (params, 0..) |p, i| {
        buf[i + off] = h07_lower_type(self, ctx, self.param(p).ty);
        if (statics.holds_template(self, buf[i + off]) and statics.templated(self, buf[i + off]) == .none) buf[i + off] = self.report(.unrealized_template, self.param(p).ty, buf[i + off], 0);
    }
    const r = if (self.nk(header) == .partial__fun_def_header_ret) realized_type(self, ctx, self.arg(header, 1)) else ret;
    return self.static_pool.intern(.{ .function_type = .{ .category = category, .params = buf[0 .. params.len + off], .ret = r } });
}

// unlengthed arrays that are not inferred per value become runtime-length arrays
pub fn dynify(self: *Resolver, t: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (t == .none or !sp.has_vars(t)) return t;
    var buf: [64]StaticPool.Index = undefined;
    return switch (sp.get(t)) {
        .array_type => |a| sp.intern(.{ .array_type = .{ .len = if (sp.tag(sp.apply_vars(&self.abstract_pool, a.len)) == .type_var) StaticPool.dyn_len else a.len, .elem = dynify(self, a.elem) } }),
        .ptr_type => |p| sp.intern(.{ .ptr_type = .{ .child = dynify(self, p.child), .mutable = p.mutable } }),
        .function_type => |f| blk: {
            const n = f.params.len;
            for (0..n) |i| buf[i] = dynify(self, sp.get(t).function_type.params[i]);
            break :blk sp.intern(.{ .function_type = .{ .category = f.category, .params = buf[0..n], .ret = dynify(self, sp.get(t).function_type.ret) } });
        },
        else => t,
    };
}

pub fn realized_type(self: *Resolver, ctx: *FnCtx, n: NodeId) StaticPool.Index {
    const t = h07_lower_type(self, ctx, n);
    return if (statics.holds_template(self, t)) self.report(.unrealized_template, n, t, 0) else t;
}

pub fn cast_target(self: *Resolver, ctx: *FnCtx, a1: NodeId, from: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const ptr = self.nk(a1) == .type_ptr or self.nk(a1) == .type_ptrmut;
    const inner = if (ptr) self.arg(a1, 0) else a1;
    if (self.nk(inner) != .type_array or !is_range_kind(self.nk(self.arg(inner, 0)))) return h07_lower_type(self, ctx, a1);
    const g = self.arg(inner, 0);
    const rg = self.range(g);
    var src = sp.pointee(from);
    if (src != .poison_type and sp.get(src) != .array_type) src = .none;
    const src_len: ?i128 = if (src != .none and src != .poison_type and sp.tag(sp.get(src).array_type.len) == .int_value) sp.get(sp.get(src).array_type.len).int.bits else null;
    const lo = if (rg.lo != 0) statics.static_int(self, ctx, rg.lo) orelse return self.report(.not_static, rg.lo, 0, 0) else 0;
    const hi = if (rg.hi == 0) src_len orelse return self.report(.not_static, g, 0, 0) else (statics.static_int(self, ctx, rg.hi) orelse return self.report(.not_static, g, 0, 0)) + @intFromBool(rg.incl);
    if (lo < 0 or hi < lo or (src_len != null and hi > src_len.?)) return self.report(.invalid_cast, g, from, .none);
    const arr = sp.intern(.{ .array_type = .{ .len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = @intCast(hi - lo) } }), .elem = h07_lower_type(self, ctx, self.arg(inner, 1)) } });
    return if (ptr) sp.intern(.{ .ptr_type = .{ .child = arr, .mutable = self.nk(a1) == .type_ptrmut } }) else arr;
}
