const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const StaticPool = @import("../StaticPool.zig");
const types = @import("types.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// static values: evaluation on demand of the checker, literals and their types

// static values: evaluation on demand of the checker, literals and their types

// static values: evaluation on demand of the checker, literals and their types

pub fn h08_eval_static(self: *Resolver, ctx: *FnCtx, node: NodeId) StaticPool.Index {
    return self.interpreter.static_value(ctx, node);
}

pub fn deferred(self: *Resolver, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    if (!ctx.interpreted) return h08_eval_static(self, ctx, node);
    const before = self.deferrals;
    const v = try_static(self, ctx, node);
    if (v != null and self.deferrals == before) return v;
    self.node_value[node] = .none;
    self.deferrals += 1;
    const s = self.tree.subtree(node);
    for (s[0]..s[1]) |i| switch (self.tree.kind(@intCast(i))) {
        .identifier, .identifier_self => {
            const d = self.scopes.h01_lookup(self.decl_pool.kinds(), self.name_pool.name_of(self.tree, self.src_bytes, @intCast(i)));
            if (d != .none) self.node_decl[i] = d;
        },
        else => {},
    };
    return null;
}

// static evaluation that leaves no diagnostics behind when the node turns out not to be static
pub fn try_static(self: *Resolver, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    const mark = self.doc.diagnostics.len();
    const ty = self.node_type[node];
    const v = h08_eval_static(self, ctx, node);
    if (self.doc.diagnostics.len() == mark and v != .poison_type) return v;
    self.doc.rewind(mark);
    self.node_type[node] = ty;
    self.node_value[node] = .none;
    self.interpreter.unwind = .none;
    return null;
}

pub fn static_of(self: *Resolver, ctx: *FnCtx, n: NodeId) StaticPool.Index {
    const c = syntax.props(self.tree.kind(n));
    return if (c.stc and c.loop and self.node_value[n] != .none) self.node_value[n] else h08_eval_static(self, ctx, n);
}

pub fn static_int(self: *Resolver, ctx: *FnCtx, n: NodeId) ?i128 {
    const sp = &self.static_pool;
    const v = try_static(self, ctx, n) orelse return null;
    if (sp.tag(v) != .int_value) return null;
    const i = sp.get(v).int;
    return if (sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed) @as(i64, @bitCast(i.bits)) else i.bits;
}

// the static value of a literal: ints as u64 (i64 when negated), floats as f64
pub fn literal_value(self: *Resolver, node: NodeId, negated: bool) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = negated;
    const n = syntax.literal_core(self.tree, node, &neg);
    var buf: [4096]u8 = undefined;
    switch (self.tree.kind(n)) {
        .boolean_true => return .bool_true,
        .boolean_false => return .bool_false,
        .string => {
            const s = self.tree.span(n);
            return sp.intern(.{ .string = unescape(self.src_bytes[s[0]..s[1]], &buf) });
        },
        .float => {
            const s = self.tree.span(n);
            const f = std.fmt.parseFloat(f64, self.src_bytes[s[0]..s[1]]) catch return if (self.doc.has(n)) .poison_type else self.report(.type_mismatch, n, .none, .none);
            return sp.intern(.{ .float = .{ .ty = .f64_type, .value = if (neg) -f else f } });
        },
        else => {
            const s = self.tree.span(n);
            const bits: u64 = if (self.tree.kind(n) == .char) unescape(self.src_bytes[s[0]..s[1]], &buf)[0] else std.fmt.parseInt(u64, self.src_bytes[s[0]..s[1]], 0) catch return if (self.doc.has(n)) .poison_type else self.report(.type_mismatch, n, .none, .u64_type);
            return sp.intern(.{ .int = if (neg) .{ .ty = .i64_type, .bits = 0 -% bits } else .{ .ty = .u64_type, .bits = bits } });
        },
    }
}

// untyped literals take the expected type when they fit, otherwise u32 / i32, then u64 / i64, floats f32
pub fn literal_type(self: *Resolver, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = false;
    const n = syntax.literal_core(self.tree, node, &neg);
    const k = self.tree.kind(n);
    if (k == .boolean_true or k == .boolean_false) return .bool_type;
    const v = literal_value(self, n, neg);
    var target = sp.apply_vars(&self.abstract_pool, expected);
    if (k == .string and target != .none and sp.tag(target) == .ptr_type and sp.get(target).ptr_type.child == .u8_type) return target;
    if (k == .string and target != .none and sp.get(target) == .array_type and sp.get(target).array_type.elem == .u8_type and
        sp.tag(sp.get(target).array_type.len) == .int_value and sp.get(sp.get(target).array_type.len).int.bits >= sp.get(v).string.len) return target;
    if (v == .poison_type) return v;
    if (k == .string) return sp.type_of(v);
    if (target != .none and sp.tag(target) == .variant_type) target = sp.single_payload(target); // `Opt8 x = 42`
    const c = if (target == .none) StaticPool.TagProperties{} else sp.get_tag_prop(target);
    if (k == .float) return if (c.is_float) target else .f32_type;
    if ((c.is_integer or c.is_float) and sp.fits(v, target)) return target;
    return if (neg) (if (sp.fits(v, .i32_type)) .i32_type else .i64_type) else if (sp.fits(v, .u32_type)) .u32_type else .u64_type;
}

pub fn retype(self: *Resolver, v: StaticPool.Index, ty: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (v == .none or ty == .none) return v;
    if ((sp.tag(v) == .int_value or sp.tag(v) == .float_value) and sp.single_payload(ty) != .none) return self.interpreter.pool(self.interpreter.coerce(.of(sp, v), ty));
    if (sp.tag(v) != .int_value) return v;
    if (sp.get_tag_prop(ty).is_integer) return sp.intern(.{ .int = .{ .ty = ty, .bits = sp.get(v).int.bits } });
    if (!sp.get_tag_prop(ty).is_float) return v;
    const i = sp.get(v).int;
    const signed = sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed;
    return sp.intern(.{ .float = .{ .ty = ty, .value = if (signed) @floatFromInt(@as(i64, @bitCast(i.bits))) else @floatFromInt(i.bits) } });
}

fn unescape(raw: []const u8, buf: []u8) []const u8 {
    if (raw.len > buf.len) return raw;
    var n: usize = 0;
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        var c = raw[i];
        if (c == '\\' and i + 1 < raw.len) {
            i += 1;
            if (raw[i] == 'x' and i + 2 < raw.len) if (std.fmt.parseInt(u8, raw[i + 1 .. i + 3], 16)) |x| {
                buf[n] = x;
                n += 1;
                i += 2;
                continue;
            } else |_| {};
            c = switch (raw[i]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => 0,
                else => raw[i],
            };
        }
        buf[n] = c;
        n += 1;
    }
    return buf[0..n];
}
