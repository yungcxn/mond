const std = @import("std");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const NamePool = @import("../NamePool.zig");
const Index = StaticPool.Index;
const Member = StaticPool.Member;
const dyn_len = StaticPool.dyn_len;

// questions about one type: what it holds, what its members are, what it is realized from

// a decision about one type: true or false, or null to look at the types it is built from
const ComponentTest = fn (pool: *const StaticPool, type_index: Index) ?bool;

// whether `decide` holds for the type or one it is built from: pointees, array elements
// (not lengths), parameter and return types. `decide` is comptime, the walk is a plain recursion
fn any_component(pool: *const StaticPool, type_index: Index, comptime decide: ComponentTest) bool {
    if (decide(pool, type_index)) |decided| return decided;
    return switch (pool.composition(type_index)) {
        .pointer => any_component(pool, pool.pointee(type_index), decide),
        .array => any_component(pool, pool.get(type_index).array_type.element, decide),
        .slice => any_component(pool, pool.get(type_index).slice_type.element, decide),
        .function => {
            const function = pool.get(type_index).function_type;
            for (function.parameters) |parameter| {
                if (any_component(pool, parameter, decide)) return true;
            }
            return any_component(pool, function.return_type, decide);
        },
        // the walk stops at the members of unified variants and at what a tree produces
        .leaf, .unified_variants, .tree => false,
    };
}

pub fn is_concrete(pool: *StaticPool, type_index: Index) bool {
    if (type_index == .none) return false;
    return pool.tag(pool.substitute_type_variables(type_index)) != .type_variable;
}

// a value's type looked through one pointer to a record or variant
// (`self`, `with` / `match` on such pointers)
pub fn through_pointer(pool: *StaticPool, type_index: Index) Index {
    const resolved = pool.substitute_type_variables(type_index);
    if (!pool.is_pointer(resolved)) return resolved;
    const pointee = pool.pointee(resolved);
    const properties = pool.properties(pointee);
    return if (properties.is_nominal or properties.is_variant) pointee else resolved;
}

// the template a parameter of type `T`, `*T` or `&T` is realized for, or none
pub fn template_of(pool: *const StaticPool, parameter: Index) Index {
    if (parameter == .none or parameter == .poison_type) return .none;
    const pointee = pool.pointee(parameter);
    return if (pool.tag(pointee) == .template_type) pointee else .none;
}

pub fn trait_of(pool: *const StaticPool, parameter: Index) Index {
    if (parameter == .none or parameter == .poison_type) return .none;
    const pointee = pool.pointee(parameter);
    return if (pool.tag(pointee) == .trait_type) pointee else .none;
}

// a packed variant `++(..)` or `A ||| B` as the whole parameter type, `T`, `*T` or `&T`
pub fn packed_of(pool: *const StaticPool, parameter: Index) Index {
    if (parameter == .none or parameter == .poison_type) return .none;
    const pointee = pool.pointee(parameter);
    const is_packed = switch (pool.get(pointee)) {
        .variant_type => |variant| variant.is_packed,
        .unified_variant_type => |unified| unified.is_packed,
        else => false,
    };
    return if (is_packed) pointee else .none;
}

// a template, a trait or a packed variant as the whole parameter type, `T`, `*T` or `&T`: the
// function is realized per argument type, so a trait or packed value never exists at run time
pub fn is_realized_per_type(pool: *const StaticPool, parameter: Index) bool {
    return pool.template_of(parameter) != .none or pool.trait_of(parameter) != .none or
        pool.packed_of(parameter) != .none;
}

// what a parameter realized per type is realized for: the argument's type, of a case its variant,
// but of a packed variant the case, which has a size of its own
pub fn realized_for(pool: *StaticPool, argument_type: Index) Index {
    const variant_or_type = pool.unwrapped(argument_type);
    if (pool.is_unstorable(variant_or_type)) return pool.through_pointer(argument_type);
    return variant_or_type;
}

// a type only a parameter has, `trait_of` or `packed_of` it: a value is always of one of the
// types it stands for
pub fn is_parameter_only(pool: *const StaticPool, type_index: Index) bool {
    return switch (pool.get(type_index)) {
        .trait_type => true,
        .variant_type => |variant| variant.is_packed,
        .unified_variant_type => |unified| unified.is_packed,
        else => false,
    };
}

// behind a pointer a trait, packed variant or template is opaque, and allowed
pub fn contains_parameter_only(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none or t == .poison_type) return false;
            if (p.is_pointer(t) and p.is_parameter_only(p.pointee(t))) return false;
            return if (p.is_parameter_only(t)) true else null;
        }
    }.decide);
}

pub fn contains_template(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none or t == .poison_type) return false;
            if (p.is_pointer(t) and p.tag(p.pointee(t)) == .template_type) return false;
            return if (p.tag(t) == .template_type) true else null;
        }
    }.decide);
}

// a type variable left in the type, array lengths aside
pub fn has_open_type_variable(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none or !p.has_type_variables(t)) return false;
            return if (p.tag(t) == .type_variable) true else null;
        }
    }.decide);
}

// a type without a size: a trait, a template, a packed variant, an array of a runtime length. a
// pointer to one is only an address, used after a cast
pub fn is_unstorable(pool: *const StaticPool, type_index: Index) bool {
    return switch (pool.get(type_index)) {
        .trait_type, .template_type => true,
        .variant_type => |variant| variant.is_packed,
        .unified_variant_type => |unified| unified.is_packed,
        .array_type => |array| array.length == StaticPool.dyn_len,
        else => false,
    };
}

// whether `decide` holds for the value itself: the value, an element, a field or a payload. what a
// pointer reaches is not part of it
fn any_part(pool: *const StaticPool, type_index: Index, comptime decide: PartTest) bool {
    if (type_index == .none or type_index == .poison_type) return false;
    if (decide(pool, type_index)) return true;
    return switch (pool.get(type_index)) {
        .array_type => |array| any_part(pool, array.element, decide),
        .record_type => |record| for (record.field_types) |field| {
            if (any_part(pool, field, decide)) break true;
        } else false,
        .variant_type => |variant| for (variant.cases) |case| {
            if (any_part(pool, case, decide)) break true;
        } else false,
        .variant_case_type => |case| any_part(pool, case.payload, decide),
        .unified_variant_type => |unified| for (unified.members) |member| {
            if (any_part(pool, member, decide)) break true;
        } else false,
        .variant_subset_type => |subset| any_part(pool, subset.whole, decide),
        else => false,
    };
}

const PartTest = fn (pool: *const StaticPool, type_index: Index) bool;

pub fn holds_function_value(pool: *const StaticPool, type_index: Index) bool {
    return any_part(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) bool {
            return p.tag(t) == .function_type;
        }
    }.decide);
}

// whether a value of the type may hold an address: a pointer, a slice, a runtime-length array
pub fn holds_address(pool: *const StaticPool, type_index: Index) bool {
    return any_part(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) bool {
            return switch (p.get(t)) {
                .pointer_type, .slice_type => true,
                .array_type => |array| array.length == StaticPool.dyn_len,
                else => false,
            };
        }
    }.decide);
}

// whether a type is a member of a unified variant, of any other type it is not
pub fn is_member(pool: *const StaticPool, unified: Index, member: Index) bool {
    if (unified == .none or pool.tag(unified) != .unified_variant_type) return false;
    const members = pool.get(unified).unified_variant_type.members;
    return std.mem.indexOfScalar(Index, members, member) != null;
}

// a variant or case of one without a tag (`notagtype`): nothing tells its cases apart at run time
pub fn is_untagged(pool: *const StaticPool, type_index: Index) bool {
    return switch (pool.get(type_index)) {
        .variant_type => |variant| variant.tag_mode == .none,
        .variant_case_type => |case| pool.is_untagged(case.variant),
        else => false,
    };
}

// a variant or case of one whose case nothing tells while the program runs: untagged and stored,
// a packed one is realized per case
pub fn is_untagged_at_run_time(pool: *const StaticPool, type_index: Index) bool {
    const variant = switch (pool.get(type_index)) {
        .variant_case_type => |case| case.variant,
        else => type_index,
    };
    return pool.is_untagged(variant) and !pool.is_unstorable(variant);
}

pub fn holds_untagged_variant(pool: *const StaticPool, type_index: Index) bool {
    return any_part(pool, type_index, is_untagged);
}

// the case (or one-case member) all zero bytes are: the one tagged 0, of a self-tagged variant
// the payload case unless a case has the tag 0 itself; none when no case is
pub fn zero_unit(pool: *const StaticPool, variant_or_unified: Index) Index {
    switch (pool.get(variant_or_unified)) {
        .variant_type => |variant| {
            var payload_case: Index = .none;
            for (variant.cases) |case| {
                const case_type = pool.get(case).variant_case_type;
                if (variant.tag_mode == .self and case_type.payload != .none) {
                    payload_case = case;
                    continue;
                }
                const tag_is_zero = pool.tag(case_type.tag) == .int_value and
                    pool.get(case_type.tag).int_value.bits == 0;
                if (tag_is_zero) return case;
            }
            return payload_case;
        },
        // the first member starts the tags at 0
        .unified_variant_type => |unified| {
            const first = unified.members[0];
            return if (pool.brings_cases(first)) pool.zero_unit(first) else first;
        },
        else => return .none,
    }
}

// whether zeroing the type makes a value a subset leaves out: zeroed records and arrays holding
// one are written first like scalars. a type that contains itself (an error) is not walked
pub fn holds_unzeroable(pool: *StaticPool, type_index: Index) bool {
    if (pool.layout(type_index).state != .done) return false;
    return any_part(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) bool {
            if (p.tag(t) != .variant_subset_type) return false;
            const zero = p.zero_unit(p.whole_of(t));
            return zero == .none or p.is_removed(t, zero);
        }
    }.decide);
}

// a type only static code can have: trees and what holds them
// (`[]ast`, `*ast`, functions taking or making them)
pub fn contains_trees(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none) return false;
            return if (p.tag(t) == .ast_type) true else null;
        }
    }.decide);
}

// poison or a type made of poison, through arrays (their lengths too) and pointers
pub fn is_poisoned(pool: *const StaticPool, type_index: Index) bool {
    if (type_index == .none) return false;
    if (type_index == .poison_type) return true;
    return switch (pool.get(type_index)) {
        .array_type => |array| array.length == .poison_type or pool.is_poisoned(array.element),
        .pointer_type => |pointer| pool.is_poisoned(pointer.pointee),
        else => false,
    };
}

// a function realized per call: per argument length, per `type` argument or per template
pub fn is_length_generic(pool: *StaticPool, function_type: Index) bool {
    if (function_type == .none or pool.tag(function_type) != .function_type) return false;
    const parameter_count = pool.get(function_type).function_type.parameters.len;
    for (0..parameter_count) |i| {
        // read anew: substituting may intern and move the parameter list
        const parameter = pool.get(function_type).function_type.parameters[i];
        if (pool.has_type_variables(pool.substitute_type_variables(parameter))) return true;
        if (pool.tag(parameter) == .meta_type or pool.is_realized_per_type(parameter)) return true;
    }
    return false;
}

pub fn has_only_template_parameters(pool: *const StaticPool, function_type: Index) bool {
    for (pool.get(function_type).function_type.parameters) |parameter| {
        const realized_per_value = pool.is_generic_parameter(parameter);
        if (realized_per_value and !pool.is_realized_per_type(parameter)) return false;
    }
    return true;
}

// parameters a function is realized for: unlengthed arrays (per length),
// `type` parameters (per type)
// and templates and traits (per argument type)
pub fn is_generic_parameter(pool: *const StaticPool, parameter: Index) bool {
    return pool.has_type_variables(parameter) or pool.tag(parameter) == .meta_type or
        pool.is_realized_per_type(parameter);
}

// through one pointer, and from a case to its variant
pub fn unwrapped(pool: *StaticPool, type_index: Index) Index {
    const dereferenced = pool.through_pointer(type_index);
    if (pool.tag(dereferenced) != .variant_case_type) return dereferenced;
    return pool.get(dereferenced).variant_case_type.variant;
}

// the declaration of a nominal type, also through a pointer or a case
pub fn nominal_declaration(pool: *StaticPool, type_index: Index) DeclPool.Index {
    return switch (pool.get(pool.whole_of(pool.unwrapped(type_index)))) {
        .record_type => |record| record.declaration,
        .variant_type => |variant| variant.declaration,
        .trait_type => |trait| trait.declaration,
        else => .none,
    };
}

// the static length an argument gives an unlengthed parameter (`&[5]u32` for `&[]u32`), or none
pub fn argument_length(pool: *StaticPool, argument_type: Index, parameter_type: Index) Index {
    var argument = pool.substitute_type_variables(argument_type);
    var parameter = parameter_type;
    if (argument == .poison_type) return .none;
    if (pool.get(parameter) == .pointer_type) {
        if (pool.get(argument) != .pointer_type) return .none;
        const wants_mutable = pool.get(parameter).pointer_type.is_mutable;
        if (wants_mutable and !pool.get(argument).pointer_type.is_mutable) return .none;
        argument = pool.get(argument).pointer_type.pointee;
        parameter = pool.get(parameter).pointer_type.pointee;
    }
    if (pool.get(argument) != .array_type or pool.get(parameter) != .array_type) return .none;
    const argument_element = pool.get(argument).array_type.element;
    if (argument_element != pool.get(parameter).array_type.element) return .none;
    const length = pool.get(argument).array_type.length;
    return if (pool.tag(length) == .int_value or length == dyn_len) length else .none;
}

// what `??` / `?<-` unwrap: the payload of a case, or of the first case that has one
pub fn payload_of(pool: *StaticPool, type_index: Index) Index {
    const resolved = pool.substitute_type_variables(type_index);
    const case = switch (pool.tag(resolved)) {
        .variant_case_type => resolved,
        .variant_type, .variant_subset_type, .unified_variant_type => pool.success_of(resolved),
        else => .none,
    };
    if (case == .none) return .none;
    // a member that is one case is its own payload
    if (pool.tag(case) != .variant_case_type) return case;
    const payload = pool.get(case).variant_case_type.payload;
    if (payload == .none) return .none;
    const fields = pool.get(payload).record_type.field_types;
    return if (fields.len == 1) fields[0] else payload;
}

// a pointer to one element (`*u8`), which `+` and `-` move like an array index
pub fn is_element_pointer(pool: *StaticPool, type_index: Index) bool {
    if (type_index == .poison_type or type_index == .none) return false;
    const resolved = pool.substitute_type_variables(type_index);
    return pool.is_pointer(resolved) and pool.get(pool.pointee(resolved)) != .array_type;
}

// the element type of an array type, none while it is not known
pub fn element_type(pool: *StaticPool, type_index: Index) Index {
    if (type_index == .none) return .none;
    const resolved = pool.substitute_type_variables(type_index);
    if (pool.tag(resolved) != .array_type) return .none;
    const element = pool.get(resolved).array_type.element;
    return if (pool.has_type_variables(element)) .none else element;
}

pub fn implements(pool: *const StaticPool, type_index: Index, trait: Index) bool {
    if (type_index == trait) return true;
    const traits = switch (pool.get(type_index)) {
        .record_type => |record| record.traits,
        .variant_type => |variant| variant.traits,
        .trait_type => |own_trait| own_trait.super_traits,
        .variant_case_type => |case| return pool.implements(case.variant, trait),
        .variant_subset_type => |subset| return pool.implements(subset.whole, trait),
        .pointer_type => |pointer| return pool.implements(pointer.pointee, trait),
        else => return false,
    };
    for (traits) |implemented| if (pool.implements(implemented, trait)) return true;
    return false;
}

// depth first through traits and their supers; every trait member has a declaration row right after
// the trait body's own row, so member i of a body with declaration d is declaration d + 1 + i
fn trait_member(
    pool: *const StaticPool,
    traits: []const Index,
    name: NamePool.Index,
    dynamic: bool,
) Member {
    for (traits) |trait| {
        if (pool.tag(trait) != .trait_type) continue;
        const trait_type = pool.get(trait).trait_type;
        for (trait_type.member_names, 0..) |member_name, i| {
            if (member_name != name) continue;
            if (dynamic) return .{ .trait_method = .{ .trait = trait, .index = @intCast(i) } };
            return .{ .method = trait_type.declaration.member(i) };
        }
        const inherited = trait_member(pool, trait_type.super_traits, name, dynamic);
        if (inherited != .none) return inherited;
    }
    return .none;
}

// what `tagof` gives: the tag type of a variant with tags of its own, of a case or a pointer
// through to it
pub fn tag_type_of(pool: *const StaticPool, type_index: Index) Index {
    return switch (pool.get(type_index)) {
        .variant_type => |variant| if (variant.tag_mode == .int)
            pool.stored_tag_type(type_index)
        else
            .none,
        .variant_case_type => |case| pool.tag_type_of(case.variant),
        .unified_variant_type => pool.stored_tag_type(type_index),
        .variant_subset_type => |subset| pool.tag_type_of(subset.whole),
        .pointer_type => |pointer| pool.tag_type_of(pointer.pointee),
        else => .none,
    };
}

// the type a tag is held in, a self-tagged variant's int and an untagged one's `()` too; a case's
// is its variant's
pub fn stored_tag_type(pool: *const StaticPool, type_index: Index) Index {
    return switch (pool.get(type_index)) {
        .variant_type => |variant| switch (variant.tag_type) {
            .none, .poison_type => .u8_type,
            else => variant.tag_type,
        },
        .variant_case_type => |case| pool.stored_tag_type(case.variant),
        .unified_variant_type => pool.unified_tag_type(type_index),
        .variant_subset_type => |subset| pool.stored_tag_type(subset.whole),
        else => .none,
    };
}

// what `x.name` means on a value of the type: a field, method, case or builtin,
// also through one pointer
pub fn lookup_member(pool: *StaticPool, type_index: Index, name: NamePool.Index) Member {
    const key = pool.get(type_index);
    const owner = if (key == .pointer_type) key.pointer_type.pointee else type_index;
    const found: Member = switch (pool.get(owner)) {
        .array_type => if (name == .len) .builtin_len else .none,
        .record_type => |record| for (record.field_names, 0..) |field_name, i| {
            if (field_name != name) continue;
            const field_type = record.field_types[i];
            break .{ .field = .{ .index = @intCast(i), .field_type = field_type } };
        } else trait_member(pool, record.traits, name, false),
        .variant_type => |variant| for (variant.cases) |case| {
            if (pool.get(case).variant_case_type.name == name) break .{ .case = case };
        } else trait_member(pool, variant.traits, name, false),
        .variant_case_type => |case| blk: {
            const of_payload = if (case.payload == .none)
                Member.none
            else
                pool.lookup_member(case.payload, name);
            if (of_payload != .none) break :blk of_payload;
            break :blk pool.lookup_member(case.variant, name);
        },
        .unified_variant_type => |unified| for (unified.members) |member| {
            if (!pool.brings_cases(member)) continue;
            const of_member = pool.lookup_member(member, name);
            if (of_member != .none) break of_member;
        } else .none,
        // the whole's members, without the cases it leaves out
        .variant_subset_type => |subset| switch (pool.lookup_member(subset.whole, name)) {
            .case => |case| if (pool.is_removed(owner, case)) .none else .{ .case = case },
            else => |member| member,
        },
        .trait_type => trait_member(pool, &.{owner}, name, true),
        else => .none,
    };
    if (found != .none) return found;
    const nominal = pool.tag(owner) == .record_type or pool.tag(owner) == .variant_type or
        pool.tag(owner) == .variant_subset_type;
    if (nominal and name == .init) return .builtin_init;
    if (nominal and name == .deinit) return .builtin_deinit;
    return .none;
}

// whether a static number is in the range of a number type
pub fn fits(pool: *const StaticPool, value: Index, type_index: Index) bool {
    const value_key = pool.get(value);
    const type_key = pool.get(type_index);
    if (type_key == .float_type) return value_key == .int_value or value_key == .float_value;
    if (type_key != .int_type or value_key != .int_value) return false;

    const int_value = value_key.int_value;
    const value_type = pool.get(int_value.value_type);
    const value_is_signed = value_type == .int_type and value_type.int_type.signedness == .signed;
    const number: i128 = if (value_is_signed)
        @as(i64, @bitCast(int_value.bits))
    else
        int_value.bits;
    const one: i128 = 1;
    const bits: u7 = @intCast(type_key.int_type.bits);
    if (type_key.int_type.signedness == .signed) {
        return number >= -(one << (bits - 1)) and number < one << (bits - 1);
    }
    return number >= 0 and number < one << bits;
}

pub fn niche_case(pool: *const StaticPool, case: Index, payload: Index) Index {
    const variant = pool.get(case).variant_case_type.variant;
    if (pool.tag(variant) != .variant_type) return .none;
    if (pool.get(variant).variant_type.tag_mode != .self) return .none;
    // the bits of the payload's field holding the tag, as its tag type sees them
    var field = payload;
    for (pool.get(variant).variant_type.tag_path) |index| {
        if (pool.tag(field) != .aggregate_value) return .none;
        field = pool.get(field).aggregate_value.elements[index];
    }
    const field_bits: u64 = switch (pool.get(field)) {
        .int_value => |int| int.bits,
        .simple_value => |simple| @intFromBool(simple == .bool_true),
        .float_value => |float| switch (pool.get(float.value_type).float_type.bits) {
            16 => @as(u16, @bitCast(@as(f16, @floatCast(float.value)))),
            32 => @as(u32, @bitCast(@as(f32, @floatCast(float.value)))),
            else => @as(u64, @bitCast(float.value)),
        },
        else => return .none,
    };
    for (pool.get(variant).variant_type.cases) |other| {
        const other_case = pool.get(other).variant_case_type;
        if (other_case.payload != .none or pool.tag(other_case.tag) != .int_value) continue;
        if (pool.get(other_case.tag).int_value.bits == field_bits) return other;
    }
    return .none;
}

// of a subset the first one it keeps
// a self-tagged variant (`tagtype self.f`) whose payload has more fields than the one holding the
// tag: it is laid out as that payload, the other cases are values of the field
pub fn is_field_tagged(pool: *const StaticPool, variant: Index) bool {
    if (pool.tag(variant) != .variant_type) return false;
    if (pool.get(variant).variant_type.tag_mode != .self) return false;
    const payload = pool.get(pool.first_payload_case(variant)).variant_case_type.payload;
    const path = pool.get(variant).variant_type.tag_path;
    return path.len > 1 or pool.get(payload).record_type.field_types.len > 1;
}

// what `??` and `?<-` unwrap: of the cases of a variant, or of the members of a unified variant in
// order (a member's cases, a member that is one case), the first with a payload
pub fn success_of(pool: *StaticPool, variant: Index) Index {
    const mark = pool.scratch.len;
    defer pool.scratch.len = mark;
    pool.push_units(variant);
    for (pool.scratch.buffer[mark..pool.scratch.len]) |unit| {
        if (pool.tag(unit) != .variant_case_type) return unit;
        if (pool.get(unit).variant_case_type.payload != .none) return unit;
    }
    return .none;
}

// a parameter of `unified` (`A ||| B`) realized for `member` holds its success always (the member
// is it), never, or when the member variant is in the success case
pub fn packed_unwrap(pool: *StaticPool, unified: Index, member: Index) StaticPool.PackedUnwrap {
    const success = pool.success_of(unified);
    if (pool.tag(success) != .variant_case_type) return if (success == member) .always else .never;
    const holds_case = pool.get(success).variant_case_type.variant == pool.whole_of(member);
    return if (holds_case) .tested else .never;
}

pub fn first_payload_case(pool: *const StaticPool, variant_or_subset: Index) Index {
    const variant = pool.whole_of(variant_or_subset);
    if (pool.tag(variant) != .variant_type) return .none;
    for (pool.get(variant).variant_type.cases) |case| {
        if (pool.is_removed(variant_or_subset, case)) continue;
        if (pool.get(case).variant_case_type.payload != .none) return case;
    }
    return .none;
}

// the case a failed bare `x??` returns of a variant result: one without payload, else the failing
// case when it is one of the result's, else any; tagged 0 or else smallest first. a member of a
// unified variant that is one case is itself, a result without tag has none
pub fn fallback_case(pool: *const StaticPool, result: Index, failing: Index) Index {
    var search: FallbackSearch = .{ .pool = pool, .result = result, .failing = failing };
    switch (pool.get(pool.whole_of(result))) {
        .variant_case_type => return result,
        .variant_type => |variant| {
            if (variant.tag_mode == .none) return .none;
            for (variant.cases) |case| search.consider(case);
        },
        .unified_variant_type => |unified| for (unified.members) |member| {
            if (!pool.brings_cases(member)) {
                search.consider(member);
                continue;
            }
            for (pool.get(member).variant_type.cases) |case| search.consider(case);
        },
        else => return .none,
    }
    if (search.payload_less != .none) return search.payload_less;
    return if (search.holds_failing) failing else search.any;
}

const FallbackSearch = struct {
    pool: *const StaticPool,
    result: Index,
    failing: Index,
    holds_failing: bool = false,
    payload_less: Index = .none,
    payload_less_tag: i128 = 0,
    any: Index = .none,
    any_tag: i128 = 0,

    fn consider(search: *FallbackSearch, entry: Index) void {
        const pool = search.pool;
        // a subset's result keeps the tags of its whole, without the cases it leaves out
        if (pool.is_removed(search.result, entry)) return;
        const tag = if (pool.tag(pool.whole_of(search.result)) == .unified_variant_type)
            pool.tag_in(pool.whole_of(search.result), entry)
        else
            signed_tag(pool, pool.get(entry).variant_case_type.tag);
        if (entry == search.failing) search.holds_failing = true;
        if (search.any == .none or comes_first(tag, search.any_tag)) {
            search.any = entry;
            search.any_tag = tag;
        }
        const is_case = pool.tag(entry) == .variant_case_type;
        if (!is_case or pool.get(entry).variant_case_type.payload != .none) return;
        if (search.payload_less == .none or comes_first(tag, search.payload_less_tag)) {
            search.payload_less = entry;
            search.payload_less_tag = tag;
        }
    }

    fn comes_first(tag: i128, other: i128) bool {
        if (tag == 0 or other == 0) return tag == 0 and other != 0;
        return tag < other;
    }

    fn signed_tag(pool: *const StaticPool, tag: Index) i128 {
        if (pool.tag(tag) != .int_value) return 0;
        const int = pool.get(tag).int_value;
        const is_signed = pool.tag(int.value_type) == .int_type and
            pool.get(int.value_type).int_type.signedness == .signed;
        return if (is_signed) @as(i64, @bitCast(int.bits)) else int.bits;
    }
};

// the single payload field of a variant with exactly one payload case (`Opt8.Some(u8)`), or none
pub fn single_payload(pool: *const StaticPool, variant: Index) Index {
    if (pool.tag(variant) != .variant_type) return .none;
    var found: Index = .none;
    for (pool.get(variant).variant_type.cases) |case| {
        const payload = pool.get(case).variant_case_type.payload;
        if (payload == .none) continue;
        if (found != .none) return .none;
        const fields = pool.get(payload).record_type.field_types;
        found = if (fields.len == 1) fields[0] else payload;
    }
    return found;
}

pub fn ast_type_of(pool: *StaticPool, produces: Index, root_kind: u16) Index {
    return pool.intern(.{ .ast_type = .{ .produces = produces, .root_kind = root_kind } });
}

// `ast(..)`, also behind a pointer
pub fn is_tree(pool: *const StaticPool, type_index: Index) bool {
    return type_index != .none and pool.tag(pool.pointee(type_index)) == .ast_type;
}
