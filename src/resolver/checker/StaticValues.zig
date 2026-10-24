const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// static values: evaluation on demand of the checker, literals and their types
const StaticValues = @This();

// static evaluations put off by an interpreted body
deferrals: u32 = 0,

pub fn owning_resolver(self: *StaticValues) *Resolver {
    return @alignCast(@fieldParentPtr("static_values", self));
}

pub fn evaluate_or_defer(
    self: *StaticValues,
    context: *FunctionContext,
    node: NodeId,
) ?StaticPool.Index {
    const resolver = self.owning_resolver();
    if (!context.is_interpreted) return resolver.interpreter.evaluate_static(context, node);

    const deferrals_before = self.deferrals;
    const value = self.try_evaluate(context, node);
    if (value != null and self.deferrals == deferrals_before) return value;

    resolver.node_static_values[node] = .none;
    self.deferrals += 1;
    // a deferred node is evaluated after these scopes are closed, so its names are bound now
    const subtree = resolver.tree.subtree(node);
    for (subtree[0]..subtree[1]) |index| switch (resolver.tree.kind(@intCast(index))) {
        .identifier, .identifier_self => {
            const name = resolver.name_pool.name_of_node(@intCast(index));
            const declaration = resolver.scopes.lookup(&resolver.decl_pool, name);
            if (declaration != .none) resolver.node_declarations[index] = declaration;
        },
        else => {},
    };
    return null;
}

// static evaluation that leaves no diagnostics behind when the node turns out not to be static
pub fn try_evaluate(
    self: *StaticValues,
    context: *FunctionContext,
    node: NodeId,
) ?StaticPool.Index {
    const resolver = self.owning_resolver();
    const diagnostics_mark = resolver.doctor.diagnostics.len();
    const node_type_before = resolver.node_types[node];

    resolver.interpreter.speculative += 1;
    const value = resolver.interpreter.evaluate_static(context, node);
    resolver.interpreter.speculative -= 1;
    const is_clean = resolver.doctor.diagnostics.len() == diagnostics_mark;
    if (is_clean and value != .poison_type) return value;

    resolver.doctor.rewind(diagnostics_mark);
    resolver.node_types[node] = node_type_before;
    resolver.node_static_values[node] = .none;
    resolver.interpreter.unwind = .none;
    return null;
}

pub fn value_of(self: *StaticValues, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const properties = resolver.tree.props(node);
    const cached = resolver.node_static_values[node];
    if (properties.stc and properties.loop and cached != .none) return cached;
    return resolver.interpreter.evaluate_static(context, node);
}

pub fn static_integer(self: *StaticValues, context: *FunctionContext, node: NodeId) ?i128 {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const value = self.try_evaluate(context, node) orelse return null;
    if (static_pool.tag(value) != .int_value) return null;

    const int = static_pool.get(value).int_value;
    const is_signed = static_pool.get(int.value_type) == .int_type and
        static_pool.get(int.value_type).int_type.signedness == .signed;
    if (is_signed) return @as(i64, @bitCast(int.bits));
    return int.bits;
}

// the static value of a literal: ints as u64 (i64 when negated), floats as f64
pub fn literal_value(self: *StaticValues, node: NodeId, negated: bool) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    var is_negated = negated;
    const literal = resolver.tree.literal_core(node, &is_negated);
    const text = resolver.tree.text(literal, resolver.src_bytes);
    var buffer: [4096]u8 = undefined;

    switch (resolver.tree.kind(literal)) {
        .boolean_true => return .bool_true,
        .boolean_false => return .bool_false,
        .string => {
            // unescaping never lengthens a text, a long one gets room of its own
            const fits = text.len <= buffer.len;
            const room = if (fits) buffer[0..] else resolver.temporary_slice(u8, text.len);
            return static_pool.intern(.{ .string_value = unescape(text, room) });
        },
        .float => {
            const float = std.fmt.parseFloat(f64, text) catch {
                // the parser may already have reported the literal, one report is enough
                if (resolver.doctor.has_report_at(literal)) return .poison_type;
                return resolver.report(.type_mismatch, literal, .none, .none);
            };
            const value = if (is_negated) -float else float;
            const float_value = StaticPool.FloatValue{ .value_type = .f64_type, .value = value };
            return static_pool.intern(.{ .float_value = float_value });
        },
        else => {
            const bits = if (resolver.tree.kind(literal) == .char)
                unescape(text, &buffer)[0]
            else
                std.fmt.parseInt(u64, text, 0) catch {
                    // the parser may already have reported the literal, one report is enough
                    if (resolver.doctor.has_report_at(literal)) return .poison_type;
                    return resolver.report(.type_mismatch, literal, .none, .u64_type);
                };
            if (is_negated and bits > 1 << 63) {
                if (resolver.doctor.has_report_at(literal)) return .poison_type;
                return resolver.report(.type_mismatch, literal, .none, .i64_type);
            }
            if (is_negated) {
                const int = StaticPool.IntValue{ .value_type = .i64_type, .bits = 0 -% bits };
                return static_pool.intern(.{ .int_value = int });
            }
            return static_pool.intern(.{ .int_value = .{ .value_type = .u64_type, .bits = bits } });
        },
    }
}

// untyped literals take the expected type when they fit, else u32 / i32, then u64 / i64, floats f32
pub fn literal_type(
    self: *StaticValues,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    var is_negated = false;
    const literal = resolver.tree.literal_core(node, &is_negated);
    const kind = resolver.tree.kind(literal);
    if (kind == .boolean_true or kind == .boolean_false) return .bool_type;

    const value = self.literal_value(literal, is_negated);
    var target = static_pool.substitute_type_variables(expected);
    if (kind == .string and target != .none) {
        // a string literal is a `*u8`-like pointer or fills an u8 array at least its length
        const holds_string = blk: {
            if (static_pool.tag(target) == .pointer_type) {
                if (static_pool.get(target).pointer_type.pointee == .u8_type) break :blk true;
            }
            if (static_pool.get(target) != .array_type) break :blk false;
            if (static_pool.get(target).array_type.element != .u8_type) break :blk false;

            const length = static_pool.static_length(target) orelse break :blk false;
            break :blk length >= static_pool.get(value).string_value.len;
        };
        if (holds_string) return target;
    }
    if (value == .poison_type) return value;
    if (kind == .string) return static_pool.type_of(value);

    // a single-payload variant takes the literal as its payload (`Opt8 x = 42`), a unified variant
    // as its first number member it fits (`u8 || i64 v = -4` is an i64)
    if (target != .none and static_pool.tag(target) == .variant_type) {
        target = static_pool.single_payload(target);
    } else if (target != .none and static_pool.tag(target) == .unified_variant_type) {
        target = for (static_pool.get(target).unified_variant_type.members) |member| {
            const member_properties = static_pool.properties(member);
            if (member_properties.is_float) break member;
            if (kind == .float) continue;
            if (member_properties.is_integer and static_pool.fits(value, member)) break member;
        } else .none;
    }
    const properties = if (target == .none)
        StaticPool.TagProperties{}
    else
        static_pool.properties(target);
    if (kind == .float) return if (properties.is_float) target else .f32_type;

    const is_number = properties.is_integer or properties.is_float;
    if (is_number and static_pool.fits(value, target)) return target;
    if (is_negated) return if (static_pool.fits(value, .i32_type)) .i32_type else .i64_type;
    return if (static_pool.fits(value, .u32_type)) .u32_type else .u64_type;
}

pub fn retyped(
    self: *StaticValues,
    value: StaticPool.Index,
    target_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (value == .none or target_type == .none) return value;

    const value_tag = static_pool.tag(value);
    const is_number = value_tag == .int_value or value_tag == .float_value;
    if (is_number and static_pool.single_payload(target_type) != .none) {
        const coerced = resolver.interpreter.coerce(.of(static_pool, value), target_type);
        return resolver.interpreter.interned(coerced);
    }
    if (static_pool.tag(value) != .int_value) return value;

    const int = static_pool.get(value).int_value;
    if (static_pool.properties(target_type).is_integer) {
        const retyped_int = StaticPool.IntValue{ .value_type = target_type, .bits = int.bits };
        return static_pool.intern(.{ .int_value = retyped_int });
    }
    if (!static_pool.properties(target_type).is_float) return value;

    const is_signed = static_pool.get(int.value_type) == .int_type and
        static_pool.get(int.value_type).int_type.signedness == .signed;
    const float: f64 = if (is_signed)
        @floatFromInt(@as(i64, @bitCast(int.bits)))
    else
        @floatFromInt(int.bits);
    return static_pool.intern(.{ .float_value = .{ .value_type = target_type, .value = float } });
}

// escapes resolved into `buffer`, which holds at least `raw.len` bytes. the lexer has
// already rejected malformed escapes
fn unescape(raw: []const u8, buffer: []u8) []const u8 {
    std.debug.assert(buffer.len >= raw.len);
    var length: usize = 0;
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        var character = raw[i];
        if (character == '\\' and i + 1 < raw.len) {
            i += 1;
            if (raw[i] == 'x' and i + 2 < raw.len) {
                if (std.fmt.parseInt(u8, raw[i + 1 .. i + 3], 16)) |byte| {
                    buffer[length] = byte;
                    length += 1;
                    i += 2;
                    continue;
                } else |_| {}
            }
            character = switch (raw[i]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => 0,
                else => raw[i],
            };
        }
        buffer[length] = character;
        length += 1;
    }
    return buffer[0..length];
}
