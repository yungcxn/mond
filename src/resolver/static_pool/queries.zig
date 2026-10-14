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
        .function => {
            const function = pool.get(type_index).function_type;
            for (function.parameters) |parameter| {
                if (any_component(pool, parameter, decide)) return true;
            }
            return any_component(pool, function.return_type, decide);
        },
        // the walk stops at the members of unions and at what a tree produces
        .leaf, .union_of_variants, .tree => false,
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

// a template or a trait as the whole parameter type, `T`, `*T` or `&T`: the function is realized
// per argument type, so a trait value never exists at run time
pub fn is_realized_per_type(pool: *const StaticPool, parameter: Index) bool {
    return pool.template_of(parameter) != .none or pool.trait_of(parameter) != .none;
}

pub fn contains_trait(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none or t == .poison_type) return false;
            return if (p.tag(t) == .trait_type) true else null;
        }
    }.decide);
}

pub fn contains_template(pool: *const StaticPool, type_index: Index) bool {
    return any_component(pool, type_index, struct {
        fn decide(p: *const StaticPool, t: Index) ?bool {
            if (t == .none or t == .poison_type) return false;
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
    return switch (pool.get(pool.unwrapped(type_index))) {
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
        .variant_type => pool.first_payload_case(resolved),
        else => .none,
    };
    if (case == .none) return .none;
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

pub fn tag_type_of(pool: *const StaticPool, type_index: Index) Index {
    return switch (pool.get(type_index)) {
        .variant_type => |variant| if (variant.tag_mode == .self)
            .none
        else if (variant.tag_type == .none or variant.tag_type == .poison_type)
            .u8_type
        else
            variant.tag_type,
        .variant_case_type => |case| pool.tag_type_of(case.variant),
        .variant_union_type => pool.union_tag_type(type_index),
        .pointer_type => |pointer| pool.tag_type_of(pointer.pointee),
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
        .variant_union_type => |members| for (members) |member| {
            const of_member = pool.lookup_member(member, name);
            if (of_member != .none) break of_member;
        } else .none,
        .trait_type => trait_member(pool, &.{owner}, name, true),
        else => .none,
    };
    if (found != .none) return found;
    if (name == .tag and pool.tag_type_of(owner) != .none) return .builtin_tag;
    const nominal = pool.tag(owner) == .record_type or pool.tag(owner) == .variant_type;
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

pub fn first_payload_case(pool: *const StaticPool, variant: Index) Index {
    for (pool.get(variant).variant_type.cases) |case| {
        if (pool.get(case).variant_case_type.payload != .none) return case;
    }
    return .none;
}

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
