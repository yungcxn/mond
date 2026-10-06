const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// static values: evaluation on demand of the checker, literals and their types
const Statics = @This();

// static evaluations put off by an interpreted body
deferrals: u32 = 0,

pub fn res(self: *Statics) *Resolver {
    return @alignCast(@fieldParentPtr("statics", self));
}

pub fn deferred(self: *Statics, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    const r = self.res();
    if (!ctx.interpreted) return r.interpreter.eval_static(ctx, node);
    const before = self.deferrals;
    const v = self.try_static(ctx, node);
    if (v != null and self.deferrals == before) return v;
    r.node_value[node] = .none;
    self.deferrals += 1;
    const s = r.tree.subtree(node);
    for (s[0]..s[1]) |i| switch (r.tree.kind(@intCast(i))) {
        .identifier, .identifier_self => {
            const d = r.scopes.lookup(&r.decl_pool, r.name_pool.name_of(@intCast(i)));
            if (d != .none) r.node_decl[i] = d;
        },
        else => {},
    };
    return null;
}

// static evaluation that leaves no diagnostics behind when the node turns out not to be static
pub fn try_static(self: *Statics, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    const r = self.res();
    const mark = r.doc.diagnostics.len();
    const ty = r.node_type[node];
    const v = r.interpreter.eval_static(ctx, node);
    if (r.doc.diagnostics.len() == mark and v != .poison_type) return v;
    r.doc.rewind(mark);
    r.node_type[node] = ty;
    r.node_value[node] = .none;
    r.interpreter.unwind = .none;
    return null;
}

pub fn static_of(self: *Statics, ctx: *FnCtx, n: NodeId) StaticPool.Index {
    const r = self.res();
    const c = r.tree.props(n);
    return if (c.stc and c.loop and r.node_value[n] != .none) r.node_value[n] else r.interpreter.eval_static(ctx, n);
}

pub fn static_int(self: *Statics, ctx: *FnCtx, n: NodeId) ?i128 {
    const r = self.res();
    const sp = &r.static_pool;
    const v = self.try_static(ctx, n) orelse return null;
    if (sp.tag(v) != .int_value) return null;
    const i = sp.get(v).int;
    return if (sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed) @as(i64, @bitCast(i.bits)) else i.bits;
}

// the static value of a literal: ints as u64 (i64 when negated), floats as f64
pub fn literal_value(self: *Statics, node: NodeId, negated: bool) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    var neg = negated;
    const n = r.tree.literal_core(node, &neg);
    var buf: [4096]u8 = undefined;
    switch (r.tree.kind(n)) {
        .boolean_true => return .bool_true,
        .boolean_false => return .bool_false,
        .string => {
            const s = r.tree.span(n);
            return sp.intern(.{ .string = unescape(r.src_bytes[s[0]..s[1]], &buf) });
        },
        .float => {
            const s = r.tree.span(n);
            const f = std.fmt.parseFloat(f64, r.src_bytes[s[0]..s[1]]) catch return if (r.doc.has(n)) .poison_type else r.report(.type_mismatch, n, .none, .none);
            return sp.intern(.{ .float = .{ .ty = .f64_type, .value = if (neg) -f else f } });
        },
        else => {
            const s = r.tree.span(n);
            const bits: u64 = if (r.tree.kind(n) == .char) unescape(r.src_bytes[s[0]..s[1]], &buf)[0] else std.fmt.parseInt(u64, r.src_bytes[s[0]..s[1]], 0) catch return if (r.doc.has(n)) .poison_type else r.report(.type_mismatch, n, .none, .u64_type);
            return sp.intern(.{ .int = if (neg) .{ .ty = .i64_type, .bits = 0 -% bits } else .{ .ty = .u64_type, .bits = bits } });
        },
    }
}

// untyped literals take the expected type when they fit, otherwise u32 / i32, then u64 / i64, floats f32
pub fn literal_type(self: *Statics, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    var neg = false;
    const n = r.tree.literal_core(node, &neg);
    const k = r.tree.kind(n);
    if (k == .boolean_true or k == .boolean_false) return .bool_type;
    const v = self.literal_value(n, neg);
    var target = sp.apply_vars(&r.abstract_pool, expected);
    if (k == .string and target != .none and sp.tag(target) == .ptr_type and sp.get(target).ptr_type.child == .u8_type) return target;
    if (k == .string and target != .none and sp.get(target) == .array_type and sp.get(target).array_type.elem == .u8_type and
        (if (sp.static_len(target)) |len| len >= sp.get(v).string.len else false)) return target;
    if (v == .poison_type) return v;
    if (k == .string) return sp.type_of(v);
    if (target != .none and sp.tag(target) == .variant_type) target = sp.single_payload(target); // `Opt8 x = 42`
    const c = if (target == .none) StaticPool.TagProperties{} else sp.get_tag_prop(target);
    if (k == .float) return if (c.is_float) target else .f32_type;
    if ((c.is_integer or c.is_float) and sp.fits(v, target)) return target;
    return if (neg) (if (sp.fits(v, .i32_type)) .i32_type else .i64_type) else if (sp.fits(v, .u32_type)) .u32_type else .u64_type;
}

pub fn retype(self: *Statics, v: StaticPool.Index, ty: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    if (v == .none or ty == .none) return v;
    if ((sp.tag(v) == .int_value or sp.tag(v) == .float_value) and sp.single_payload(ty) != .none) return r.interpreter.pool(r.interpreter.coerce(.of(sp, v), ty));
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
