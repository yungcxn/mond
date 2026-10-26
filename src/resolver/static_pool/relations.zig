const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const TypeVariables = @import("../TypeVariables.zig");
const Index = StaticPool.Index;
const UnifyResult = StaticPool.UnifyResult;
const CoercionKind = StaticPool.CoercionKind;
const CastKind = StaticPool.CastKind;
const JoinResult = StaticPool.JoinResult;
const dyn_len = StaticPool.dyn_len;

// relations between two types: unification, implicit coercion, joining branches and explicit casts

// follows bound type variables until a concrete type or an unbound variable
fn resolve_bound(pool: *StaticPool, index: Index) Index {
    var current = index;
    while (current != .none and pool.tag(current) == .type_variable) {
        const data = pool.items.column(.data)[@backingInt(current)];
        const variable: TypeVariables.Index = @fromBackingInt(data);
        const binding = pool.type_variables.binding_of(variable);
        if (binding == .none) return current;
        current = binding;
    }
    return current;
}

// makes the two types equal by binding type variables, structurally through compound types
pub fn unify(pool: *StaticPool, left_type: Index, right_type: Index) UnifyResult {
    const left = resolve_bound(pool, left_type);
    const right = resolve_bound(pool, right_type);
    if (left == right) return .ok;

    const left_tag = pool.tag(left);
    const right_tag = pool.tag(right);
    if (left_tag == .type_variable and right_tag == .type_variable) {
        pool.type_variables.unite(pool.get(left).type_variable, pool.get(right).type_variable);
        return .ok;
    }
    if (left_tag == .type_variable or right_tag == .type_variable) {
        const variable, const bound_type = if (left_tag == .type_variable)
            .{ pool.get(left).type_variable, right }
        else
            .{ pool.get(right).type_variable, left };
        if (pool.occurs_in(variable, bound_type)) return .infinite;
        pool.type_variables.bind(variable, bound_type);
        return .ok;
    }

    if (left == .poison_type or right == .poison_type) return .ok;
    if (left_tag != right_tag) return .mismatch;
    // equal tags, so both sides have the same composition
    return switch (pool.composition(left)) {
        .array => {
            const left_array = pool.get(left).array_type;
            const right_array = pool.get(right).array_type;
            if (pool.unify(left_array.length, right_array.length) != .ok) return .mismatch;
            return pool.unify(left_array.element, right_array.element);
        },
        .pointer => pool.unify(pool.pointee(left), pool.pointee(right)),
        .slice => pool.unify(pool.get(left).slice_type.element, pool.get(right).slice_type.element),
        .function => {
            const left_function = pool.get(left).function_type;
            const right_function = pool.get(right).function_type;
            if (left_function.category != right_function.category) return .mismatch;
            const left_parameters = left_function.parameters;
            const right_parameters = right_function.parameters;
            if (left_parameters.len != right_parameters.len) return .mismatch;
            for (left_parameters, right_parameters) |left_parameter, right_parameter| {
                const result = pool.unify(left_parameter, right_parameter);
                if (result != .ok) return result;
            }
            return pool.unify(left_function.return_type, right_function.return_type);
        },
        .unified_variants => {
            const left_members = pool.get(left).unified_variant_type.members;
            const right_members = pool.get(right).unified_variant_type.members;
            if (left_members.len != right_members.len) return .mismatch;
            for (left_members, right_members) |left_member, right_member| {
                const result = pool.unify(left_member, right_member);
                if (result != .ok) return result;
            }
            return .ok;
        },
        // two distinct leaves are distinct types (nominal ones compare by declaration),
        // trees unify only when they are the same entry
        .leaf, .tree => .mismatch,
    };
}

// how a value of type `from` may be used where `to` is expected without `as`,
// the checks run in priority order
pub fn coercion(pool: *StaticPool, from_type: Index, to_type: Index) CoercionKind {
    const from = pool.substitute_type_variables(from_type);
    const to = pool.substitute_type_variables(to_type);
    if (from == to) return .identity;
    if (from == .poison_type or to == .poison_type) return .poison;
    if (from == .never_type) return .never_to_any;
    if (from == .unit_type and to == .runit_type) return .unit_to_runit;
    if (to == .fun_type and pool.tag(from) == .function_type) return .identity;

    // trees, their pointers and lists: what they produce is checked as far as known,
    // their root when evaluated
    if (pool.tag(from) == .ast_type and pool.tag(to) == .ast_type) {
        return if (trees_fit(pool, from, to)) .identity else .incompatible;
    }
    const both_tree_pointers = pool.is_pointer(from) and pool.is_pointer(to) and
        pool.is_tree(from) and pool.is_tree(to);
    if (both_tree_pointers) {
        const keeps_writability =
            pool.tag(from) == .mutable_pointer_type or pool.tag(to) == .pointer_type;
        const fits = keeps_writability and trees_fit(pool, pool.pointee(from), pool.pointee(to));
        return if (fits) .identity else .incompatible;
    }
    if (pool.tag(from) == .array_type and pool.tag(to) == .array_type) {
        const from_array = pool.get(from).array_type;
        const to_array = pool.get(to).array_type;
        if (pool.is_tree(from_array.element) and pool.is_tree(to_array.element)) {
            const length_fits = to_array.length == dyn_len or to_array.length == from_array.length;
            const elements_fit =
                pool.coercion(from_array.element, to_array.element) != .incompatible;
            return if (length_fits and elements_fit) .identity else .incompatible;
        }
    }

    // a type still holding variables coerces when it unifies,
    // through pointers that keep or drop writability
    if (pool.has_type_variables(from) or pool.has_type_variables(to)) {
        const through_pointers = pool.is_pointer(from) and pool.is_pointer(to) and
            (pool.tag(from) == .mutable_pointer_type or pool.tag(to) == .pointer_type);
        const unified_from = if (through_pointers) pool.pointee(from) else from;
        const unified_to = if (through_pointers) pool.pointee(to) else to;
        return if (pool.unify(unified_from, unified_to) == .ok) .unified else .incompatible;
    }

    // integers widen to integers of at least their width (unsigned to wider signed),
    // floats to wider floats
    const from_key = pool.get(from);
    const to_key = pool.get(to);
    if (from_key == .int_type and to_key == .int_type) {
        const from_int = from_key.int_type;
        const to_int = to_key.int_type;
        const same_signedness = from_int.signedness == to_int.signedness;
        const to_signed = from_int.signedness == .unsigned and to_int.signedness == .signed;
        const widens = same_signedness and to_int.bits >= from_int.bits or
            to_signed and to_int.bits > from_int.bits;
        return if (widens) .int_widen else .incompatible;
    }
    if (from_key == .float_type and to_key == .float_type) {
        const widens = to_key.float_type.bits >= from_key.float_type.bits;
        return if (widens) .float_widen else .incompatible;
    }

    if (from_key == .pointer_type and to_key == .pointer_type) {
        const from_pointer = from_key.pointer_type;
        const to_pointer = to_key.pointer_type;
        const drops_writability = from_pointer.is_mutable and !to_pointer.is_mutable;
        const same_pointee = from_pointer.pointee == to_pointer.pointee;
        if (drops_writability and same_pointee) return .ptr_mut_to_ptr;
        // a subset is read as its whole or a wider subset, never written as one: that could store
        // a case it leaves out
        const reads_subset = !to_pointer.is_mutable and
            pool.tag(from_pointer.pointee) == .variant_subset_type and
            pool.coercion(from_pointer.pointee, to_pointer.pointee) == .identity;
        if (reads_subset) return if (from_pointer.is_mutable) .ptr_mut_to_ptr else .identity;
        if (from_pointer.is_mutable or !to_pointer.is_mutable) {
            const from_pointee = pool.get(from_pointer.pointee);
            const to_pointee = pool.get(to_pointer.pointee);
            const to_element = from_pointee == .array_type and
                from_pointee.array_type.element == to_pointer.pointee;
            if (to_element) {
                return .array_ptr_to_elem_ptr;
            }
            const to_runtime_length = from_pointee == .array_type and to_pointee == .array_type and
                to_pointee.array_type.length == dyn_len and
                from_pointee.array_type.element == to_pointee.array_type.element;
            if (to_runtime_length) return .to_dyn;
        }
    }
    const array_to_runtime_length = from_key == .array_type and to_key == .array_type and
        to_key.array_type.length == dyn_len and
        from_key.array_type.element == to_key.array_type.element;
    if (array_to_runtime_length) return .to_dyn;
    // an array of a static length, or a pointer to one, is a slice of its elements
    if (to_key == .slice_type) {
        const pointee = if (from_key == .pointer_type) from_key.pointer_type.pointee else from;
        const source = pool.get(pointee);
        const fits = source == .array_type and
            source.array_type.element == to_key.slice_type.element and
            pool.tag(source.array_type.length) == .int_value;
        return if (fits) .to_slice else .incompatible;
    }

    // a subset is a value of its whole, a value goes into a subset when each case it may be is one
    // the subset keeps
    if (to_key == .variant_subset_type) {
        const into_whole = pool.coercion(from, to_key.variant_subset_type.whole);
        if (into_whole == .incompatible) return .incompatible;
        const mark = pool.scratch.len;
        defer pool.scratch.len = mark;
        pool.push_units(from);
        for (pool.scratch.buffer[mark..pool.scratch.len]) |unit| {
            if (pool.is_removed(to, unit)) return .incompatible;
        }
        return into_whole;
    }
    if (from_key == .variant_subset_type) {
        return pool.coercion(from_key.variant_subset_type.whole, to);
    }

    // variants, unified variants, traits and single-payload variants (`Opt8 x = 42`)
    if (from_key == .variant_case_type) {
        const variant = from_key.variant_case_type.variant;
        const fits = variant == to or pool.coercion(variant, to) != .incompatible;
        return if (fits) .case_to_variant else .incompatible;
    }
    if (to_key == .unified_variant_type) {
        const into: CoercionKind = if (to_key.unified_variant_type.is_packed)
            .member_to_packed
        else
            .member_to_unified;
        return if (pool.is_member(to, from)) into else .incompatible;
    }
    if (to_key == .trait_type and pool.implements(from, to)) return .impl_to_trait;
    if (from_key == .pointer_type and to_key == .pointer_type) {
        const from_pointer = from_key.pointer_type;
        const to_pointer = to_key.pointer_type;
        const keeps_writability = from_pointer.is_mutable or !to_pointer.is_mutable;
        const to_trait = pool.tag(to_pointer.pointee) == .trait_type;
        const implemented = pool.implements(from_pointer.pointee, to_pointer.pointee);
        if (keeps_writability and to_trait and implemented) {
            return .impl_to_trait;
        }
        const to_packed = pool.is_parameter_only(to_pointer.pointee) and
            pool.coercion(from_pointer.pointee, to_pointer.pointee) != .incompatible;
        if (keeps_writability and to_packed) return .member_to_packed;
    }
    const payload = pool.single_payload(to);
    const wraps_payload = payload != .none and from_key != .variant_type and
        pool.coercion(from, payload) != .incompatible;
    return if (wraps_payload) .payload_to_self_tagged else .incompatible;
}

// the members of both sides, each once, a unified variant of the same kind on a side brings its
// members; a single one is just itself. a member is stored in it, or in a packed one a function is
// realized for it, so it needs a size
pub fn unified_of(
    pool: *StaticPool,
    left: Index,
    right: Index,
    is_packed: bool,
) StaticPool.UnifiedOf {
    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    // a subset unifies its whole and keeps its cases out: `A || (B -- B.x)` is `(A || B) -- B.x`,
    // with the layout and tags of `A || B`
    const has_subset = pool.tag(left) == .variant_subset_type or
        pool.tag(right) == .variant_subset_type;
    if (has_subset and !is_packed) {
        const wholes = pool.unified_of(pool.whole_of(left), pool.whole_of(right), false);
        if (wholes == .sizeless_side) return wholes;
        for ([_]Index{ left, right }) |side| {
            if (pool.tag(side) != .variant_subset_type) continue;
            pool.scratch.append(pool.get(side).variant_subset_type.removed);
        }
        return .{ .unified = without(pool, wholes.unified, mark) };
    }
    for ([_]Index{ left, right }, 0..) |side, i| {
        if (side == .poison_type) continue;
        const is_same_kind = pool.tag(side) == .unified_variant_type and
            pool.get(side).unified_variant_type.is_packed == is_packed;
        const side_members: []const Index = if (is_same_kind)
            pool.get(side).unified_variant_type.members
        else
            &.{side};
        if (!is_same_kind and pool.is_unstorable(side)) return .{ .sizeless_side = @intCast(i) };
        for (side_members) |member| {
            const known = pool.scratch.buffer[mark..pool.scratch.len];
            if (std.mem.indexOfScalar(Index, known, member) == null) pool.scratch.push(member);
        }
    }
    const members = pool.scratch.buffer[mark..pool.scratch.len];
    if (members.len == 1) return .{ .unified = members[0] };
    return .{ .unified = pool.intern(.{
        .unified_variant_type = .{ .members = members, .is_packed = is_packed },
    }) };
}

// `A -- B`: the cases of A without those of B (a case, a member, a unified variant of them or a
// subset), in the layout and tags of A's whole
pub fn difference_of(pool: *StaticPool, left: Index, right: Index) StaticPool.DifferenceOf {
    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    pool.push_units(right);
    return pool.difference_by_units(left, mark);
}

// `left` without the cases (or one-case members) on the scratch from `removing` on, each one of
// its whole, which must have tags to tell its cases apart
pub fn difference_by_units(
    pool: *StaticPool,
    left: Index,
    removing: usize,
) StaticPool.DifferenceOf {
    const whole = pool.whole_of(left);
    const is_tagged = switch (pool.get(whole)) {
        .variant_type => |variant| variant.tag_mode != .none and !variant.is_packed,
        .unified_variant_type => |unified| !unified.is_packed,
        else => false,
    };
    if (!is_tagged) return .{ .wrong_side = 0 };

    const end = pool.scratch.len;
    pool.push_units(whole);
    for (removing..end) |i| {
        const known = pool.scratch.buffer[end..pool.scratch.len];
        if (std.mem.indexOfScalar(Index, known, pool.scratch.buffer[i]) == null) {
            pool.scratch.len = end;
            return .{ .wrong_side = 1 };
        }
    }
    pool.scratch.len = end;
    if (left != whole) pool.scratch.append(pool.get(left).variant_subset_type.removed);
    return .{ .difference = without(pool, whole, removing) };
}

// `whole` without the units on the scratch from `removing` on: a subset with them sorted, the whole
// itself without any, `never` without all
fn without(pool: *StaticPool, whole: Index, removing: usize) Index {
    const end = pool.scratch.len;
    pool.push_units(whole);
    const unit_count = pool.scratch.len - end;
    pool.scratch.len = end;

    const removed = pool.scratch.buffer[removing..end];
    std.mem.sort(Index, removed, {}, struct {
        fn less(_: void, a: Index, b: Index) bool {
            return @backingInt(a) < @backingInt(b);
        }
    }.less);
    var kept: usize = 0;
    for (removed) |unit| {
        if (kept > 0 and removed[kept - 1] == unit) continue;
        removed[kept] = unit;
        kept += 1;
    }
    if (kept == 0) return whole;
    if (kept == unit_count) return .never_type;
    const subset = StaticPool.VariantSubsetType{ .whole = whole, .removed = removed[0..kept] };
    return pool.intern(.{ .variant_subset_type = subset });
}

// the variant or unified variant a value of a subset is a value of, any other type itself
pub fn whole_of(pool: *const StaticPool, type_index: Index) Index {
    if (type_index == .none or pool.tag(type_index) != .variant_subset_type) return type_index;
    return pool.get(type_index).variant_subset_type.whole;
}

// whether a subset leaves out a case or a member that is one case
pub fn is_removed(pool: *const StaticPool, subset: Index, unit: Index) bool {
    if (subset == .none or pool.tag(subset) != .variant_subset_type) return false;
    return std.mem.indexOfScalar(Index, pool.get(subset).variant_subset_type.removed, unit) != null;
}

// pushes what a value of the type may be onto the scratch: the cases of a variant, of a unified
// variant its members' cases or the members that are one case, of a subset those it keeps; a
// case or any other type is one
pub fn push_units(pool: *StaticPool, type_index: Index) void {
    switch (pool.get(type_index)) {
        .variant_type => |variant| pool.scratch.append(variant.cases),
        .unified_variant_type => |unified| for (unified.members) |member| {
            if (pool.brings_cases(member)) {
                pool.scratch.append(pool.get(member).variant_type.cases);
            } else {
                pool.scratch.push(member);
            }
        },
        .variant_subset_type => |subset| {
            const mark = pool.scratch.len;
            pool.push_units(subset.whole);
            var kept = mark;
            for (mark..pool.scratch.len) |i| {
                const unit = pool.scratch.buffer[i];
                if (std.mem.indexOfScalar(Index, subset.removed, unit) != null) continue;
                pool.scratch.buffer[kept] = unit;
                kept += 1;
            }
            pool.scratch.len = kept;
        },
        else => pool.scratch.push(type_index),
    }
}

// of what a value of `value_type` may be (see `push_units`), how much `tested` may be too: a value
// is of a type when its case or member is. `some` is known only from the value
pub fn units_covered(pool: *StaticPool, value_type: Index, tested: Index) StaticPool.Covered {
    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    pool.push_units(value_type);
    const units_end = pool.scratch.len;
    var covered: usize = 0;
    for (mark..units_end) |i| {
        if (pool.covers_unit(tested, pool.scratch.buffer[i])) covered += 1;
    }
    if (covered == 0) return .none;
    return if (covered == units_end - mark) .all else .some;
}

// whether `unit` (a case, or a member of a unified variant that is one case) is one of what a
// value of `tested` may be
pub fn covers_unit(pool: *StaticPool, tested: Index, unit: Index) bool {
    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    pool.push_units(tested);
    return std.mem.indexOfScalar(Index, pool.scratch.buffer[mark..pool.scratch.len], unit) != null;
}

// the type both branches of a choice become, and how each side gets there
pub fn join(pool: *StaticPool, left: Index, right: Index) JoinResult {
    if (left == right) return .{ .joined_type = left, .left = .identity, .right = .identity };
    if (left == .poison_type or right == .poison_type) {
        return .{ .joined_type = .poison_type, .left = .poison, .right = .poison };
    }
    if (left == .never_type or left == .runit_type) {
        const kind: CoercionKind = if (left == .never_type) .never_to_any else .unit_to_runit;
        return .{ .joined_type = right, .left = kind, .right = .identity };
    }
    if (right == .never_type or right == .runit_type) {
        const kind: CoercionKind = if (right == .never_type) .never_to_any else .unit_to_runit;
        return .{ .joined_type = left, .left = .identity, .right = kind };
    }
    if (pool.tag(left) == .variant_case_type and pool.tag(right) == .variant_case_type) {
        const variant = pool.get(left).variant_case_type.variant;
        if (variant == pool.get(right).variant_case_type.variant) {
            return .{ .joined_type = variant, .left = .case_to_variant, .right = .case_to_variant };
        }
    }
    // values of one variant without some of its cases: the variant without the cases neither
    // side may be
    const has_subset = pool.tag(left) == .variant_subset_type or
        pool.tag(right) == .variant_subset_type;
    if (has_subset) {
        // a case is of its variant
        var wholes: [2]Index = undefined;
        for ([2]Index{ left, right }, &wholes) |side, *whole| {
            const is_case = pool.tag(side) == .variant_case_type;
            const variant = if (is_case) pool.get(side).variant_case_type.variant else side;
            whole.* = pool.whole_of(variant);
        }
        const whole = wholes[0];
        if (whole == wholes[1]) {
            const mark = pool.scratch.len;
            defer pool.scratch.len = mark;
            pool.push_units(left);
            pool.push_units(right);
            const removing = pool.scratch.len;
            pool.push_units(whole);
            // the whole's units neither side may be move down to `mark`
            var kept = mark;
            for (removing..pool.scratch.len) |i| {
                const unit = pool.scratch.buffer[i];
                const known = pool.scratch.buffer[mark..removing];
                if (std.mem.indexOfScalar(Index, known, unit) != null) continue;
                pool.scratch.buffer[kept] = unit;
                kept += 1;
            }
            pool.scratch.len = kept;
            const joined = without(pool, whole, mark);
            const left_kind = pool.coercion(left, joined);
            const right_kind = pool.coercion(right, joined);
            return .{ .joined_type = joined, .left = left_kind, .right = right_kind };
        }
    }
    const right_to_left = pool.coercion(right, left);
    if (right_to_left != .incompatible) {
        return .{ .joined_type = left, .left = .identity, .right = right_to_left };
    }
    const left_to_right = pool.coercion(left, right);
    if (left_to_right != .incompatible) {
        return .{ .joined_type = right, .left = left_to_right, .right = .identity };
    }
    return .{ .joined_type = .none, .left = .incompatible, .right = .incompatible };
}

// what an explicit `as` does to a value of `from` to make it a `to`
pub fn cast_kind(pool: *StaticPool, from: Index, to: Index) CastKind {
    if (from == to or from == .poison_type or to == .poison_type) return .identity;
    // a value of a subset is one of its whole, a value of the whole only becomes one by `match`
    if (pool.tag(from) == .variant_subset_type) return pool.cast_kind(pool.whole_of(from), to);
    const from_key = pool.get(from);
    const from_int = from_key == .int_type or from == .bool_type;
    return switch (pool.get(to)) {
        .int_type => if (from_int)
            .int_resize
        else if (from_key == .float_type)
            .float_to_int
        else if (from_key == .variant_type or from_key == .variant_case_type)
            .bit_reinterpret
        else
            .invalid,
        .float_type => if (from_int)
            .int_to_float
        else if (from_key == .float_type)
            .float_resize
        else
            .invalid,
        .variant_case_type => |case| case_cast(pool, from, case),
        .pointer_type => |to_pointer| pointer_cast(pool, from, to_pointer),
        .array_type => |to_array| array_cast(pool, from, to_array),
        .slice_type => |to_slice| slice_cast(pool, from, to_slice),
        .simple_type, .meta_type, .function_type, .record_type => .invalid,
        .variant_type, .unified_variant_type, .variant_subset_type => .invalid,
        .trait_type, .static_function, .template_type, .type_variable, .ast_type => .invalid,
        .int_value, .float_value, .simple_value, .string_value, .aggregate_value => .invalid,
        .variant_value, .function_value, .tree_value => .invalid,
    };
}

fn case_cast(pool: *StaticPool, from: Index, case: StaticPool.VariantCaseType) CastKind {
    const from_key = pool.get(from);
    const same_variant = from == case.variant or
        from_key == .variant_case_type and from_key.variant_case_type.variant == case.variant;
    // the cases of a packed variant differ in size
    if (same_variant and pool.is_unstorable(case.variant)) return .invalid;
    if (same_variant) return .variant_retag;
    if (case.payload == .none) return .invalid;
    const payload_fields = pool.get(case.payload).record_type.field_types;
    const wraps = payload_fields.len == 1 and pool.cast_kind(from, payload_fields[0]) == .identity;
    if (wraps) return .payload_wrap;
    return .invalid;
}

// an array, or one behind a pointer, seen whole as a slice of its elements
fn slice_cast(pool: *StaticPool, from: Index, to_slice: StaticPool.SliceType) CastKind {
    const array = pool.get(pool.pointee(from));
    if (array != .array_type or array.array_type.element != to_slice.element) return .invalid;
    return if (pool.tag(array.array_type.length) == .int_value) .array_to_slice else .invalid;
}

fn pointer_cast(pool: *StaticPool, from: Index, to_pointer: StaticPool.PointerType) CastKind {
    const from_key = pool.get(from);
    // a slice's address of its first element, of the array it reaches into
    if (from_key == .slice_type) {
        const to_pointee = pool.get(to_pointer.pointee);
        const element = from_key.slice_type.element;
        const is_element = to_pointer.pointee == element;
        const is_array = to_pointee == .array_type and to_pointee.array_type.element == element;
        return if (is_element or is_array) .slice_to_pointer else .invalid;
    }
    if (from_key != .pointer_type) return .invalid;
    const from_pointer = from_key.pointer_type;
    if (to_pointer.is_mutable and !from_pointer.is_mutable) return .invalid;
    const to_pointee = pool.get(to_pointer.pointee);
    if (to_pointee != .array_type) return .bit_reinterpret;
    const from_pointee = pool.get(from_pointer.pointee);
    const from_element = if (from_pointee == .array_type)
        from_pointee.array_type.element
    else
        from_pointer.pointee;
    if (from_element != to_pointee.array_type.element) return .bit_reinterpret;
    // both lengths static and the target the longer one
    if (from_pointee == .array_type) {
        const from_length = from_pointee.array_type.length;
        const to_length = to_pointee.array_type.length;
        const both_static = pool.tag(from_length) == .int_value and
            pool.tag(to_length) == .int_value;
        const longer = both_static and
            pool.get(to_length).int_value.bits > pool.get(from_length).int_value.bits;
        if (longer) return .invalid;
    }
    const to_runtime_length = pool.tag(to_pointee.array_type.length) != .int_value;
    if (to_runtime_length and pool.get(from_pointer.pointee) != .array_type) return .invalid;
    return .pointer_relength;
}

fn array_cast(pool: *StaticPool, from: Index, to_array: StaticPool.ArrayType) CastKind {
    const from_key = pool.get(from);
    const source = if (from_key == .pointer_type) from_key.pointer_type.pointee else from;
    const source_has_static_length = pool.static_length(source) != null;
    const source_key = pool.get(source);
    const source_element = if (source_key == .array_type) source_key.array_type.element else source;
    if (source_element != to_array.element) return .invalid;
    if (pool.tag(to_array.length) != .int_value) return .invalid;
    if (from_key != .pointer_type and !source_has_static_length) return .invalid;
    // the target longer than a statically long source
    if (source_key == .array_type) {
        const source_length = source_key.array_type.length;
        const longer = pool.tag(source_length) == .int_value and
            pool.get(to_array.length).int_value.bits > pool.get(source_length).int_value.bits;
        if (longer) return .invalid;
    }
    return .array_narrow;
}

// the type with every bound type variable replaced by its binding
pub fn substitute_type_variables(pool: *StaticPool, index: Index) Index {
    if (index == .none or !pool.has_type_variables(index)) return index;
    const resolved = resolve_bound(pool, index);
    if (resolved != index) return pool.substitute_type_variables(resolved);

    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    return switch (pool.composition(index)) {
        .array => {
            const array = pool.get(index).array_type;
            return pool.intern(.{ .array_type = .{
                .length = pool.substitute_type_variables(array.length),
                .element = pool.substitute_type_variables(array.element),
            } });
        },
        .pointer => {
            const pointer = pool.get(index).pointer_type;
            const pointee = pool.substitute_type_variables(pointer.pointee);
            return pool.pointer_to(pointee, pointer.is_mutable);
        },
        .slice => {
            const element = pool.substitute_type_variables(pool.get(index).slice_type.element);
            return pool.slice_of(element);
        },
        .function => {
            const function = pool.get(index).function_type;
            // the scratch buffer may move while nested types are rebuilt, items are read by index
            pool.scratch.append(function.parameters);
            for (mark..pool.scratch.len) |i| {
                const substituted = pool.substitute_type_variables(pool.scratch.buffer[i]);
                pool.scratch.buffer[i] = substituted;
            }
            const return_type = pool.substitute_type_variables(function.return_type);
            return pool.intern(.{ .function_type = .{
                .category = function.category,
                .parameters = pool.scratch.buffer[mark..pool.scratch.len],
                .return_type = return_type,
            } });
        },
        .unified_variants => {
            pool.scratch.append(pool.get(index).unified_variant_type.members);
            for (mark..pool.scratch.len) |i| {
                const substituted = pool.substitute_type_variables(pool.scratch.buffer[i]);
                pool.scratch.buffer[i] = substituted;
            }
            const members_substituted = pool.scratch.buffer[mark..pool.scratch.len];
            return pool.intern(.{ .unified_variant_type = .{
                .members = members_substituted,
                .is_packed = pool.get(index).unified_variant_type.is_packed,
            } });
        },
        .tree => {
            const ast = pool.get(index).ast_type;
            return pool.intern(.{ .ast_type = .{
                .produces = pool.substitute_type_variables(ast.produces),
                .root_kind = ast.root_kind,
            } });
        },
        // nominal types and values are interned without variables
        .leaf => index,
    };
}

// a tree of one type is one of another unless both say what they produce or what their root is,
// and it differs
fn trees_fit(pool: *StaticPool, from: Index, to: Index) bool {
    const from_ast = pool.get(from).ast_type;
    const to_ast = pool.get(to).ast_type;
    const produces_fit = from_ast.produces == .none or to_ast.produces == .none or
        pool.coercion(from_ast.produces, to_ast.produces) != .incompatible;
    const roots_fit = from_ast.root_kind == 0 or to_ast.root_kind == 0 or
        from_ast.root_kind == to_ast.root_kind;
    return produces_fit and roots_fit;
}

// whether `variable` appears in `index`, which binding it would make an infinite type
pub fn occurs_in(pool: *StaticPool, variable: TypeVariables.Index, index: Index) bool {
    if (index == .none or !pool.has_type_variables(index)) return false;
    const resolved = resolve_bound(pool, index);
    if (pool.tag(resolved) == .type_variable) {
        const other = pool.get(resolved).type_variable;
        return pool.type_variables.root_of(other) == pool.type_variables.root_of(variable);
    }
    return switch (pool.composition(resolved)) {
        .array => {
            const array = pool.get(resolved).array_type;
            if (pool.occurs_in(variable, array.length)) return true;
            return pool.occurs_in(variable, array.element);
        },
        .pointer => pool.occurs_in(variable, pool.pointee(resolved)),
        .slice => pool.occurs_in(variable, pool.get(resolved).slice_type.element),
        .function => {
            const function = pool.get(resolved).function_type;
            for (function.parameters) |parameter| {
                if (pool.occurs_in(variable, parameter)) return true;
            }
            return pool.occurs_in(variable, function.return_type);
        },
        .unified_variants => {
            for (pool.get(resolved).unified_variant_type.members) |member| {
                if (pool.occurs_in(variable, member)) return true;
            }
            return false;
        },
        // the occurs check does not look into what a tree produces
        .leaf, .tree => false,
    };
}
