const std = @import("std");

// This realizes the plans on the type system and that "everything is an expression".
// -> It checks the unification of types and validity of applications

// Types are just an index in the type table
// This is not a "type" as in "custom struct definition", but rather from u8 up to traits
const TypeId = u32;
// also just an index in the function table
const FunctionId = u32;

// disregards "static" fully
const BaseType = enum(u8) {
    unsigned_int8,
    unsigned_int16,
    unsigned_int32,
    unsigned_int64,

    signed_int8,
    signed_int16,
    signed_int32,
    signed_int64,

    float16,
    float32,
    float64,

    boolean,

    unit,
    runit, // compiler helper, wrapper where combining `unit` and others is illegal

    fn size(self: @This()) u32 {
        return switch (self) {
            .unsigned_int8 => 8,
            .unsigned_int16 => 16,
            .unsigned_int32 => 32,
            .unsigned_int64 => 64,

            .signed_int8 => 8,
            .signed_int16 => 16,
            .signed_int32 => 32,
            .signed_int64 => 64,

            .float16 => 16,
            .float32 => 32,
            .float64 => 64,

            .boolean => 1,

            .unit => 0,
            .runit => 0,
        };
    }
};

const StaticType = enum {
    type_type,
    type_fun,
    type_trait,
    type_variant,
};

// everything here gets its own TypeId in the type registry when compiling
const ComplexType = union(enum) {
    array: Array,
    ptr: Pointer,
    ptrmut: Pointer,

    function: Function,

    type: Type,
    variant,
    trait: Trait,

    optional: Optional,
    errored: Errored,

    tagged_type: TaggedType, // compiler helper, created by defining a variant

    incompl_type: IncompleteType, // compiler helper, created by defining `stcfun` returning a type
    incompl_trait: IncompleteTrait, // same as above for trait
    incompl_variant: IncompleteVariant, // same as above for variant
    incompl_tagged_type: IncompleteTaggedType, // same as above for tagged type

    const Array = struct {
        length: u32,
        type: TypeId,
    };

    const Pointer = struct {
        child_type: TypeId,
    };

    const Optional = struct {
        child_type: TypeId,
        none_value: *const anyopaque, // in size of child type
    };

    const Errored = struct {
        child_type: TypeId,
        error_values: []const *const anyopaque, // in size of child type
    };

    const Function = struct {
        category: Category,
        // the default value, where-else clause is not part of the function type.
        params: []const TypeId,
        return_type: TypeId,

        const Category = enum(u8) {
            default,
            static,
            inlined,
        };
    };

    const Type = struct {
        is_packed: bool,
        // mutability, default value, where-else clause etc. is not part of the type representation
        params: []const TypeId,
        own_trait: TypeId,
        implemented_traits: []const TypeId,
    };

    const Trait = struct {
        // unlike any other fields / parameters is here the name of the funcs important
        decl_names: []const u8,
        funcs: []const FunctionId,
    };

    const Variant = struct {
        tag_int_type: BaseType,
        subtypes: []const TypeId,
    };

    const TaggedType = struct {
        tag_int_type: BaseType,
        tag_value: i128,
        mother_variant: TypeId,
        child_type: TypeId,
    };

    // mimics type, but certain parameters could have types that are templates through static functions
    // - same for implemented traits
    const IncompleteType = struct {
        is_packed: bool,
        params: []const ?TypeId,
        own_trait: TypeId,
        implemented_traits: []const ?TypeId,
    };

    // mimics trait. Only Complete methods can be used. Complete is only that which has nothing templated
    const IncompleteTrait = struct {
        decl_names: []const u8,
        funcs: []const ?FunctionId, // none if a function has templated parameters or a templ. return type
    };

    // mimics variant. Only complete subtypes can be used.
    // A complete
    const IncompleteVariant = struct {
        // none: the tag may be none or of arbitrary size
        tag_int_type: ?BaseType,

        // case by case:
        // - non-none: could be typeid of a complete type, OR of an incomplete type
        //   -> this means, either type is complete or it has some fields with templated types.
        // - none: the subtypes type ("payload") is templated, which is something like:
        //   `@(SomeTag = 0 | TagWithPayload of TemplatedType = 1 | ...)` and `TemplatedType` is not known
        subtypes: []const ?TypeId,
    };

    const IncompleteTaggedType = struct {
        tag_int_type: ?BaseType,
        tag_value: ?i128,
        mother_variant: TypeId,
        child_type: ?TypeId,
    };
};
