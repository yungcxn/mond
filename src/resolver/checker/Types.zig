const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Decls = @import("Decls.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// types: type expressions lowered to pool types, type definitions with their members, traits and conformance
const Types = @This();

const prim_types = blk: {
    var t: [256]StaticPool.Index = @splat(.none);
    for (@typeInfo(StaticPool.Index).@"enum".fields) |f| if (std.mem.endsWith(u8, f.name, "_type") and @hasField(ParseTree.Node.Kind, "type_" ++ f.name[0 .. f.name.len - 5])) {
        t[@intFromEnum(@field(ParseTree.Node.Kind, "type_" ++ f.name[0 .. f.name.len - 5]))] = @enumFromInt(f.value);
    };
    break :blk t;
};

pub fn res(self: *Types) *Resolver {
    return @alignCast(@fieldParentPtr("types", self));
}

pub fn meta_of(self: *Types, node: NodeId) StaticPool.Index {
    const r = self.res();
    return r.decls.type_kind(node).meta(if (r.tree.kind(node) == .unify_variants) .variant_type else .type_type);
}

pub fn lower(self: *Types, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const k = r.tree.kind(node);
    if (prim_types[@intFromEnum(k)] != .none) return prim_types[@intFromEnum(k)];
    return switch (k) {
        .capture => self.lower(ctx, r.tree.arg(node, 0)),
        .typeof => blk: {
            const t = r.exprs.infer(ctx, r.tree.arg(node, 0), .none);
            if (r.tree.kind(r.tree.arg(node, 0)) == .identifier and r.generics.is_template(r.node_decl[r.tree.arg(node, 0)])) break :blk r.report(.unrealized_template, r.tree.arg(node, 0), 0, 0);
            break :blk if (r.tree.kind(r.tree.arg(node, 0)) == .identifier_self) sp.pointee(t) else t;
        },
        .type_ptr, .type_ptrmut => sp.ptr_of(self.lower(ctx, r.tree.arg(node, 0)), k == .type_ptrmut),
        // an unlengthed array gets a var as its length: inferred from the value, or per call for parameters
        // record fields, `main` parameters and lengths nothing fixes become runtime-length arrays (dynify, `apply_inferred`)
        .type_array_unlengthed => sp.intern(.{ .array_type = .{ .len = sp.fresh_var(&r.abstract_pool, node), .elem = self.lower(ctx, r.tree.arg(node, 0)) } }),
        .type_array => blk: {
            const len = r.statics.deferred(ctx, r.tree.arg(node, 0)) orelse .poison_type;
            const n = if (sp.tag(len) == .int_value) sp.intern(.{ .int = .{ .ty = .u64_type, .bits = sp.get(len).int.bits } }) else if (len == .poison_type) len else r.report(.not_static, r.tree.arg(node, 0), len, 0);
            break :blk sp.intern(.{ .array_type = .{ .len = n, .elem = self.lower(ctx, r.tree.arg(node, 1)) } });
        },
        .def_fun_declaration => self.fun_type(ctx, node, .default, .unit_type, .none),
        else => blk: {
            const v = r.statics.deferred(ctx, node) orelse .poison_type;
            if (sp.tag(v) == .generic and sp.tag(sp.get(r.decl_pool.get_ty(sp.get(v).static_fun.decl)).function_type.ret) == .meta_type) break :blk sp.intern(.{ .template_type = sp.get(v).static_fun.decl });
            break :blk if (v == .poison_type or sp.get_tag_prop(v).is_type) v else r.report(.not_a_type, node, v, .none);
        },
    };
}

pub fn static_type(self: *Types, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const k = r.tree.kind(node);
    return switch (k) {
        .unify_variants => blk: {
            var members: std.ArrayList(StaticPool.Index) = .empty;
            defer members.deinit(r.alloc);
            for ([_]NodeId{ r.tree.arg(node, 0), r.tree.arg(node, 1) }) |side| {
                const t = self.lower(ctx, side);
                if (sp.tag(t) == .variant_union_type) {
                    members.appendSlice(r.alloc, sp.get(t).variant_union_type) catch @panic("OOM");
                } else if (sp.tag(t) == .variant_type) {
                    members.append(r.alloc, t) catch @panic("OOM");
                } else _ = r.mismatch(side, t, .variant_type);
            }
            break :blk sp.intern(.{ .variant_union_type = members.items });
        },
        .def_type, .def_type_packed, .def_type_assertsize, .def_type_implof, .def_variant, .def_variant_unionsized, .def_variant_tagof, .def_variant_assertsize, .def_variant_implof, .def_trait, .def_trait_implof => blk: {
            const d = r.decl_pool.push_decl(.empty, node, r.decls.type_kind(node), .none, .{});
            r.node_decl[node] = d;
            break :blk self.check_type_def(ctx, d, node);
        },
        .def_fun => blk: {
            _ = r.exprs.infer(ctx, node, .none);
            break :blk r.decl_pool.get_value(r.node_decl[node]);
        },
        else => if (r.tree.props(node).type_expr) self.lower(ctx, node) else r.report(.not_static, node, 0, 0),
    };
}

pub fn check_type_def(self: *Types, ctx: *FnCtx, decl: DeclPool.Index, node: NodeId) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const w = ParseTree.Def.from_node(r.tree, node);
    const c = w.core;
    const body = w.body;
    const tagof = w.tagof;
    const ck = r.tree.kind(c);
    const is_trait = ck == .def_trait or ck == .def_trait_implof;
    var first = r.decl_pool.entries.len();
    // reserved first (or already by `instantiate`), so fields can point back at the type (`*Tree`)
    if (r.decl_pool.get_value(decl) == .none) r.decl_pool.set_value(decl, sp.reserve_nominal(decl));
    const ty = r.decl_pool.get_value(decl);
    r.decl_pool.set_ty(decl, r.decls.type_kind(c).meta(.type_type));
    if (r.decl_pool.get_state(decl) == .resolving_signature) r.decl_pool.set_state(decl, .signature_ready);
    r.scopes.push();
    defer r.scopes.pop();

    var nt: usize = 0;
    // the anonymous `!{..}` body, completed after the type: member signatures may realize types that construct this one
    var own: StaticPool.Index = .none;
    const members = if (!is_trait and body != 0) r.tree.arg(body, if (r.tree.kind(body) == .def_trait_implof) 1 else 0) else 0;
    const traits = r.scratch(StaticPool.Index, if (members != 0 and r.tree.kind(body) == .def_trait_implof) r.tree.manychildren(r.tree.arg(body, 0)).len + 1 else 1);
    if (members != 0) {
        const impls = if (r.tree.kind(body) == .def_trait_implof) r.tree.manychildren(r.tree.arg(body, 0)) else &[_]NodeId{};
        if (r.tree.manychildren(members).len > 0) {
            own = sp.reserve_nominal(decl);
            traits[0] = own;
            nt = 1;
        }
        for (impls) |t| {
            traits[nt] = self.lower(ctx, t);
            if (traits[nt] != .poison_type and sp.tag(traits[nt]) != .trait_type) traits[nt] = r.mismatch(t, traits[nt], .trait_type);
            nt += @intFromBool(traits[nt] != .poison_type);
        }
    }

    switch (ck) {
        .def_trait, .def_trait_implof => {
            const impls = if (ck == .def_trait_implof) r.tree.manychildren(r.tree.arg(c, 0)) else &[_]NodeId{};
            const supers = r.scratch(StaticPool.Index, impls.len);
            var ns: usize = 0;
            for (impls) |t| {
                supers[ns] = self.lower(ctx, t);
                if (supers[ns] != .poison_type and sp.tag(supers[ns]) != .trait_type) supers[ns] = r.mismatch(t, supers[ns], .trait_type);
                ns += @intFromBool(supers[ns] != .poison_type);
            }
            own = self.trait_body(ctx, r.tree.arg(c, if (ck == .def_trait_implof) 1 else 0), ty, .none, supers[0..ns], decl);
        },
        .def_variant, .def_variant_unionsized => {
            const params = r.tree.manychildren(r.tree.arg(c, 0));
            const cases = r.scratch(StaticPool.Index, params.len);
            var payload_case: ?usize = null;
            var payloads: usize = 0;
            var next_tag: StaticPool.IntValue = .{ .ty = .u64_type, .bits = 0 };
            for (params, 0..) |pn, i| {
                var q = pn;
                var tag_node: NodeId = 0;
                var payload_node: NodeId = 0;
                if (r.tree.kind(q) == .partial__variant_def_param_tagged) {
                    tag_node = r.tree.arg(q, 1);
                    q = r.tree.arg(q, 0);
                }
                if (r.tree.kind(q) == .partial__variant_def_param_typed) {
                    payload_node = r.tree.arg(q, 1);
                    q = r.tree.arg(q, 0);
                }
                const payload = if (payload_node == 0) .none else self.check_type_def(ctx, r.decl_pool.push_decl(.empty, payload_node, .record, .none, .{}), payload_node);
                if (payload != .none) {
                    payload_case = i;
                    payloads += 1;
                }
                const tv = if (tag_node == 0) sp.intern(.{ .int = next_tag }) else r.interpreter.eval_static(ctx, tag_node);
                if (sp.tag(tv) == .int_value) next_tag = .{ .ty = sp.get(tv).int.ty, .bits = sp.get(tv).int.bits +% 1 } else if (tv != .poison_type) _ = r.mismatch(tag_node, sp.type_of(tv), .u64_type);
                for (cases[0..i]) |prev| if (sp.get(prev).variant_case_type.name == r.name_pool.name_of(r.tree.arg(q, 0))) r.doc.report(.duplicate_declaration, pn, r.name_pool.name_of(r.tree.arg(q, 0)), decl);
                cases[i] = r.set(r.tree.arg(q, 0), sp.intern(.{ .variant_case_type = .{ .variant = ty, .case = @intCast(i), .name = r.name_pool.name_of(r.tree.arg(q, 0)), .tag = tv, .payload = payload } }));
            }
            // variants are always tagged, without tagof by the smallest tag type for their case count
            const mode: StaticPool.VariantTagMode = if (tagof != 0 and r.tree.kind(tagof) == .identifier_self) .self else .int;
            var tag_ty: StaticPool.Index = if (tagof == 0) StaticPool.smallest_tag_type(params.len) else if (mode == .self) .none else self.lower(ctx, tagof);
            if (mode == .self) {
                // the one payload type encodes the other cases in bit patterns it never uses
                if (payloads != 1) tag_ty = r.report(.self_tag_without_niche, tagof, payloads, 0) else {
                    const fields = sp.get(sp.get(cases[payload_case.?]).variant_case_type.payload).custom_type.field_types;
                    tag_ty = if (fields.len == 1 and sp.get_tag_prop(fields[0]).is_integer) fields[0] else r.report(.self_tag_without_niche, tagof, 0, 0);
                }
            }
            if (tag_ty != .none and tag_ty != .poison_type) for (params, 0..) |pn, i| {
                const case = sp.get(cases[i]).variant_case_type;
                if ((mode == .int or case.payload == .none) and sp.tag(case.tag) == .int_value and !sp.fits(case.tag, tag_ty)) _ = r.report(.tag_overflow, pn, case.tag, tag_ty);
            };
            sp.complete_nominal(ty, .{ .variant_type = .{ .decl = decl, .tag_mode = mode, .tag_type = tag_ty, .is_unionsized = ck == .def_variant_unionsized, .cases = cases[0..params.len], .traits = traits[0..nt] } });
        },
        else => { // records: `*(..)`, `**(..)` and payload tuples
            const fields = r.tree.fields_of(c);
            const names = r.scratch(NamePool.Index, fields.len);
            const types = r.scratch(StaticPool.Index, fields.len);
            for (fields, 0..) |f, i| {
                const p = ParseTree.Param.from_node(r.tree, f);
                types[i] = self.dynify(self.realized_type(ctx, p.ty));
                names[i] = r.decls.name_at(p, i);
                if (std.mem.indexOfScalar(NamePool.Index, names[0..i], names[i]) != null) r.doc.report(.duplicate_declaration, f, names[i], decl);
            }
            sp.complete_nominal(ty, .{ .custom_type = .{ .decl = decl, .is_packed = ck == .def_type_packed, .field_names = names[0..fields.len], .field_types = types[0..fields.len], .traits = traits[0..nt] } });
        },
    }
    if (own != .none and !is_trait) _ = self.trait_body(ctx, members, own, ty, &.{}, decl);
    // member bodies once the type is complete, before the fields are names; a method calling one that writes self writes self too
    if (own != .none) {
        const b = sp.get(own).trait_type.decl;
        const n = sp.get(own).trait_type.member_names.len;
        for (0..n) |i| r.decls.check_body(b.member(i));
        r.mutability.propagate_writes(b, n);
    }
    if (sp.tag(ty) == .record_type) {
        // defaults and where-clauses see the fields by name, the snapshot's locals start at the first field
        const fields = r.tree.fields_of(c);
        first = r.decl_pool.entries.len();
        for (fields, 0..) |f, i| {
            const t = sp.field_type(ty, i);
            const fd = r.decls.declare_local(sp.get(ty).custom_type.field_names[i], f, .field, t);
            r.decl_pool.flags_ptr(fd).is_mut = ParseTree.Param.from_node(r.tree, f).is_mut;
            r.decls.link(ParseTree.Param.from_node(r.tree, f).name, fd, t);
        }
        // a default sees the fields before its own, a where-clause all of them
        const at = r.scopes.names.head - fields.len;
        const names = r.scratch(NamePool.Index, fields.len);
        @memcpy(names, r.scopes.names.buf[at..][0..fields.len]);
        @memset(r.scopes.names.buf[at..][0..fields.len], .empty);
        for (fields, 0..) |f, i| {
            const p = ParseTree.Param.from_node(r.tree, f);
            if (p.default != 0) _ = r.exprs.check(ctx, p.default, sp.field_type(ty, i));
            r.scopes.names.buf[at + i] = names[i];
        }
        for (fields, 0..) |f, i| r.decls.check_guards(ctx, ParseTree.Param.from_node(r.tree, f), sp.field_type(ty, i));
    }
    if (!is_trait) {
        for (traits[0..nt]) |t| if (t != own and sp.tag(t) == .trait_type) self.conform(ty, own, t, node);
        if (sp.layout(ty).state == .infinite) _ = r.report(.recursive_by_value_type, node, ty, .none);
        r.bodies.put(r.capture(decl, node, first));
    }
    if (w.size != 0) {
        const v = r.interpreter.eval_static(ctx, w.size);
        const want = if (sp.get_tag_prop(v).is_type) sp.layout(v).size else if (sp.tag(v) == .int_value) sp.get(v).int.bits else 0;
        if (v != .poison_type and sp.layout(ty).size != want) _ = r.report(.assertsize_failed, w.size, sp.layout(ty).size, want);
    }
    return ty;
}

// a trait body: one row for the body (its value is the self type), then one row per function member,
// contiguous, so member i is row + 1 + i. static members (`stc u32 MASK = ..`) are plain locals of the body.
fn trait_body(self: *Types, ctx: *FnCtx, body: NodeId, reserved: StaticPool.Index, self_ty: StaticPool.Index, supers: []const StaticPool.Index, of: DeclPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const b = r.decl_pool.push_decl(if (self_ty == .none) r.decl_pool.get_name(of) else .empty, body, .trait, .trait_type, .{});
    if (r.generics.realized_args.get(of)) |a| r.generics.realized_args.put(r.alloc, b, a) catch @panic("OOM");
    if (r.generics.template_of.get(of)) |g| r.generics.template_of.put(r.alloc, b, g) catch @panic("OOM");
    const tr = if (reserved != .none) reserved else sp.reserve_nominal(b);
    r.decl_pool.set_value(b, if (self_ty != .none) self_ty else tr);
    const names = r.scratch(NamePool.Index, r.tree.manychildren(body).len);
    var n: usize = 0;
    for (r.tree.manychildren(body)) |s| {
        const m = Decls.Stmt.from_node(r, s);
        if (!m.is_member()) continue;
        names[n] = r.name_pool.name_of(m.assignees[0]);
        if (std.mem.indexOfScalar(NamePool.Index, names[0..n], names[n]) != null) r.doc.report(.duplicate_declaration, m.assignees[0], names[n], of);
        r.node_decl[m.assignees[0]] = r.decl_pool.push_decl(names[n], m.node, .trait_member, .none, m.flags);
        n += 1;
    }
    for (r.tree.manychildren(body)) |s| if (!Decls.Stmt.from_node(r, s).is_member()) {
        _ = r.decls.check_stmt(ctx, s);
    };
    const types = r.scratch(StaticPool.Index, n);
    for (0..n) |i| types[i] = self.decl_type(b.member(i));
    sp.complete_nominal(tr, .{ .trait_type = .{ .decl = b, .member_names = names[0..n], .member_types = types[0..n], .supers = supers } });
    return tr;
}

pub fn decl_type(self: *Types, d: DeclPool.Index) StaticPool.Index {
    const r = self.res();
    r.decls.ensure_signature(d);
    const t = r.decl_pool.get_ty(d);
    return if (t == .none) .poison_type else t;
}

pub fn fields_of(self: *Types, rec: StaticPool.Index) []const NodeId {
    const r = self.res();
    return r.tree.fields_of(ParseTree.Def.from_node(r.tree, r.decls.value_node(r.static_pool.get(rec).custom_type.decl)).core);
}

pub fn sig(self: *Types, d: DeclPool.Index) StaticPool.FunType {
    const r = self.res();
    return r.static_pool.get(r.decl_pool.get_ty(d)).function_type;
}

// implof: every member of the trait and its supers exists with the same signature (`typeof self` read as the type),
// members with a default implementation may be left out
fn conform(self: *Types, ty: StaticPool.Index, own: StaticPool.Index, trait: StaticPool.Index, node: NodeId) void {
    const r = self.res();
    const sp = &r.static_pool;
    for (0..sp.get(trait).trait_type.member_names.len) |i| {
        const tt = sp.get(trait).trait_type;
        const name = tt.member_names[i];
        const want = tt.member_types[i];
        const m = if (own == .none) StaticPool.Member.none else sp.lookup_member(own, name);
        // members with a default may be left out, an override keeps the signature
        if (m != .trait_method) {
            if (r.tree.kind(r.decls.value_node(tt.decl.member(i))) != .def_fun) r.doc.report(.trait_member_missing, node, name, trait);
            continue;
        }
        const have = sp.apply_vars(&r.abstract_pool, sp.get(own).trait_type.member_types[m.trait_method.index]);
        const w = sp.apply_vars(&r.abstract_pool, want);
        if (!self.same_sig(have, w, trait, ty)) r.doc.report(.trait_signature_mismatch, node, name, trait);
    }
    for (0..sp.get(trait).trait_type.supers.len) |i| self.conform(ty, own, sp.get(trait).trait_type.supers[i], node);
}

fn same_sig(self: *Types, have: StaticPool.Index, want: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    if (have == want or have == .poison_type or want == .poison_type) return true;
    if (sp.tag(have) != .function_type or sp.tag(want) != .function_type) return false;
    const h = sp.get(have).function_type;
    const w = sp.get(want).function_type;
    if (h.params.len != w.params.len) return false;
    for (h.params, w.params) |a, b| if (!self.same_as(a, b, trait, ty)) return false;
    return self.same_as(h.ret, w.ret, trait, ty);
}

// a == b with the trait read as the implementing type anywhere inside (pointers, arrays, function types)
fn same_as(self: *Types, a: StaticPool.Index, b: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const r = self.res();
    const sp = &r.static_pool;
    if (a == b or a == .poison_type or (b == trait and a == ty)) return true;
    if (sp.tag(a) != sp.tag(b)) return false;
    return switch (sp.get(a)) {
        .ptr_type => |p| p.mutable == sp.get(b).ptr_type.mutable and self.same_as(p.child, sp.get(b).ptr_type.child, trait, ty),
        .array_type => |x| x.len == sp.get(b).array_type.len and self.same_as(x.elem, sp.get(b).array_type.elem, trait, ty),
        .function_type => |f| f.params.len == sp.get(b).function_type.params.len and for (0..f.params.len) |i| {
            if (!self.same_as(sp.get(a).function_type.params[i], sp.get(b).function_type.params[i], trait, ty)) break false;
        } else self.same_as(sp.get(a).function_type.ret, sp.get(b).function_type.ret, trait, ty),
        else => false,
    };
}

pub fn fun_type(self: *Types, ctx: *FnCtx, v: NodeId, category: StaticPool.FunType.Category, ret: StaticPool.Index, self_param: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const header = r.tree.arg(v, 0);
    const params = r.tree.params_of(v);
    const off = @intFromBool(self_param != .none);
    const buf = r.scratch(StaticPool.Index, params.len + off);
    if (off == 1) buf[0] = self_param;
    for (params, 0..) |p, i| {
        buf[i + off] = self.lower(ctx, ParseTree.Param.from_node(r.tree, p).ty);
        if (r.static_pool.holds_template(buf[i + off]) and r.static_pool.templated(buf[i + off]) == .none) buf[i + off] = r.report(.unrealized_template, ParseTree.Param.from_node(r.tree, p).ty, buf[i + off], 0);
    }
    const rt = if (r.tree.kind(header) == .partial__fun_def_header_ret) self.realized_type(ctx, r.tree.arg(header, 1)) else ret;
    return r.static_pool.intern(.{ .function_type = .{ .category = category, .params = buf, .ret = rt } });
}

// unlengthed arrays that are not inferred per value become runtime-length arrays
pub fn dynify(self: *Types, t: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    if (t == .none or !sp.has_vars(t)) return t;
    return switch (sp.get(t)) {
        .array_type => |a| sp.intern(.{ .array_type = .{ .len = if (sp.tag(sp.apply_vars(&r.abstract_pool, a.len)) == .type_var) StaticPool.dyn_len else a.len, .elem = self.dynify(a.elem) } }),
        .ptr_type => |p| sp.ptr_of(self.dynify(p.child), p.mutable),
        .function_type => |f| blk: {
            const buf = r.scratch(StaticPool.Index, f.params.len);
            for (buf, 0..) |*p, i| p.* = self.dynify(sp.get(t).function_type.params[i]);
            break :blk sp.intern(.{ .function_type = .{ .category = f.category, .params = buf, .ret = self.dynify(sp.get(t).function_type.ret) } });
        },
        else => t,
    };
}

pub fn realized_type(self: *Types, ctx: *FnCtx, n: NodeId) StaticPool.Index {
    const r = self.res();
    const t = self.lower(ctx, n);
    return if (r.static_pool.holds_template(t)) r.report(.unrealized_template, n, t, 0) else t;
}

pub fn cast_target(self: *Types, ctx: *FnCtx, a1: NodeId, from: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const ptr = r.tree.props(a1).pointer;
    const inner = if (ptr) r.tree.arg(a1, 0) else a1;
    if (r.tree.kind(inner) != .type_array or !r.tree.props(r.tree.arg(inner, 0)).range) return self.lower(ctx, a1);
    const g = r.tree.arg(inner, 0);
    const rg = ParseTree.Range.from_node(r.tree, g);
    const src_len: ?i128 = if (sp.static_len(sp.pointee(from))) |len| len else null;
    const lo = if (rg.lo != 0) r.statics.static_int(ctx, rg.lo) orelse return r.report(.not_static, rg.lo, 0, 0) else 0;
    const hi = if (rg.hi == 0) src_len orelse return r.report(.not_static, g, 0, 0) else (r.statics.static_int(ctx, rg.hi) orelse return r.report(.not_static, g, 0, 0)) + @intFromBool(rg.incl);
    if (lo < 0 or hi < lo or (src_len != null and hi > src_len.?)) return r.report(.invalid_cast, g, from, .none);
    const arr = sp.array_of(@intCast(hi - lo), self.lower(ctx, r.tree.arg(inner, 1)));
    return if (ptr) sp.ptr_of(arr, r.tree.kind(a1) == .type_ptrmut) else arr;
}

// type vars nothing bound: an open element type is an error, an open length a runtime length
pub fn apply_inferred(self: *Types) void {
    const r = self.res();
    if (r.abstract_pool.count() == 0) return;
    const sp = &r.static_pool;
    for (r.decl_pool.entries.sliced_field(.ty), 0..) |t, i| if (t != .none and sp.has_vars(t)) {
        const at = sp.apply_vars(&r.abstract_pool, t);
        if (sp.open_type_var(at) and !sp.length_generic(&r.abstract_pool, at)) _ = r.report(.uninferable_type, r.decl_pool.get_node(@enumFromInt(i)), at, .none);
    };
    // lengths nothing fixed are only known at runtime; a loop value then needs its element count at loop entry
    const vs = r.abstract_pool.pool.sliced();
    const group = r.alloc.alloc(ParseTree.NodeId, vs.parent.len) catch @panic("OOM");
    defer r.alloc.free(group);
    @memset(group, ParseTree.none_node);
    for (0..vs.parent.len) |i| {
        const root = @intFromEnum(r.abstract_pool.find(@enumFromInt(i)));
        if (vs.binding[root] != .none) continue;
        const origin = vs.origin[i];
        const k = r.tree.kind(origin);
        const counted = switch (k) {
            .for_seq, .for_var_in_seq => blk: {
                const seq = ParseTree.Loop.from_node(r.tree, origin).seq;
                const st = sp.deref(&r.abstract_pool, sp.apply_vars(&r.abstract_pool, r.node_type[seq]));
                break :blk if (r.tree.props(seq).range) ParseTree.Range.from_node(r.tree, seq).hi != 0 else st != .none and sp.tag(sp.pointee(st)) == .array_type;
            },
            .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => false,
            .type_array_unlengthed, .array_index, .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => true,
            else => continue,
        };
        if (group[root] == ParseTree.none_node or !counted) group[root] = if (counted) 0 else origin;
    }
    for (group, 0..) |g, i| if (g != ParseTree.none_node) {
        if (g != 0) _ = r.report(.uninferable_type, g, sp.apply_vars(&r.abstract_pool, r.node_type[g]), .none);
        r.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len);
    };
    for ([_][]StaticPool.Index{ r.node_type, r.decl_pool.entries.sliced_field(.ty) }) |ts| for (ts) |*t| if (t.* != .none and sp.has_vars(t.*)) {
        t.* = sp.apply_vars(&r.abstract_pool, t.*);
    };
}
