const std = @import("std");
const ParseTree = @import("../ParseTree.zig");
const StructOfArrays = @import("../containers.zig").StructOfArrays;
const NamePool = @import("./NamePool.zig");
const StaticPool = @import("./StaticPool.zig");

const DeclPool = @This();

// one row per declaration: globals, locals, parameters, fields, binders
// struct-of-arrays, so a lookup reads only `name` and a use only `kind`, `flags`, `value_type`
pub const Entry = struct {
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: Kind,
    flags: Flags,
    state: State,
    value_type: StaticPool.Index,
    static_value: StaticPool.Index,
    next_overload: Index,

    pub const Field = std.meta.FieldEnum(Entry);

    pub fn FieldType(comptime field: Field) type {
        return @FieldType(Entry, @tagName(field));
    }

    pub const Kind = enum(u8) {
        variable,
        parameter,
        static_parameter,
        field,
        function,
        static_function,
        inlined_function,
        type_alias,
        record,
        variant,
        variant_case,
        trait,
        trait_member,
        pattern_binder,
        arrow_binder,
        loop_variable,
        self,
        autoins_arg,
        autoins_it,

        pub fn is_function(kind: Kind) bool {
            return properties.get(kind).is_function;
        }

        pub fn is_type_declaration(kind: Kind) bool {
            return properties.get(kind).is_type_declaration;
        }

        // a runtime value of a body, which closures capture from the bodies around them
        pub fn is_runtime_local(kind: Kind) bool {
            return properties.get(kind).is_runtime_local;
        }

        // the type of a type declared with this kind, `other` for every other kind
        pub fn meta_type(kind: Kind, other: StaticPool.Index) StaticPool.Index {
            const declared = properties.get(kind).declared_meta_type;
            return if (declared != .none) declared else other;
        }

        const Properties = struct {
            is_function: bool = false,
            is_type_declaration: bool = false,
            is_runtime_local: bool = false,
            declared_meta_type: StaticPool.Index = .none,
        };

        // one row per kind, `init` refuses to compile while a kind has no row
        const properties = std.EnumArray(Kind, Properties).init(.{
            .variable = .{ .is_runtime_local = true },
            .parameter = .{ .is_runtime_local = true },
            .static_parameter = .{},
            .field = .{},
            .function = .{ .is_function = true },
            .static_function = .{ .is_function = true },
            .inlined_function = .{ .is_function = true },
            .type_alias = .{ .is_type_declaration = true },
            .record = .{ .is_type_declaration = true, .declared_meta_type = .type_type },
            .variant = .{ .is_type_declaration = true, .declared_meta_type = .variant_type },
            .variant_case = .{},
            .trait = .{ .is_type_declaration = true, .declared_meta_type = .trait_type },
            .trait_member = .{ .is_function = true },
            .pattern_binder = .{ .is_runtime_local = true },
            .arrow_binder = .{ .is_runtime_local = true },
            .loop_variable = .{ .is_runtime_local = true },
            .self = .{ .is_runtime_local = true },
            .autoins_arg = .{ .is_runtime_local = true },
            .autoins_it = .{ .is_runtime_local = true },
        });
    };

    pub const Flags = packed struct(u8) {
        is_pub: bool = false,
        is_mut: bool = false,
        is_stc: bool = false,
        is_global: bool = false,
        is_view: bool = false,
        // methods: the body writes through `self`, the `self` local: something writes through it
        writes: bool = false,
        _pad: u2 = 0,

        pub fn any(flags: Flags) bool {
            return @as(u8, @bitCast(flags)) != 0;
        }
    };

    // unresolved -> resolving_signature -> signature_ready -> checking_body -> done (or failed)
    // signature_ready precedes the body, so (mutually) recursive calls see an induced type variable
    // meeting a declaration in resolving_signature again is a real cycle and an error
    pub const State = enum(u8) {
        unresolved,
        resolving_signature,
        signature_ready,
        checking_body,
        done,
        failed,
    };
};

pub const Index = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    // members are pushed right after the declaration that owns them
    pub fn member(owner: Index, i: usize) Index {
        return @enumFromInt(@intFromEnum(owner) + 1 + i);
    }
};

alloc: std.mem.Allocator,
entries: StructOfArrays(Entry),

pub inline fn init(alloc: std.mem.Allocator, initial_capacity: usize) DeclPool {
    return .{ .alloc = alloc, .entries = StructOfArrays(Entry).init(alloc, initial_capacity) };
}

pub inline fn deinit(self: *DeclPool) void {
    self.entries.deinit();
}

pub fn push(
    self: *DeclPool,
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: DeclPool.Entry.Kind,
    value_type: StaticPool.Index,
    flags: DeclPool.Entry.Flags,
) DeclPool.Index {
    const declaration: DeclPool.Index = @enumFromInt(self.entries.len());
    // globals, functions and types are resolved on first use, everything else when declared
    const lazy = flags.is_global or kind.is_function() or kind.is_type_declaration();

    self.entries.push(.{
        .name = name,
        .node = node,
        .kind = kind,
        .flags = flags,
        .state = if (lazy) .unresolved else .done,
        .value_type = value_type,
        .static_value = .none,
        .next_overload = .none,
    });

    return declaration;
}

pub fn get(
    self: *const DeclPool,
    declaration: Index,
    comptime field: Entry.Field,
) Entry.FieldType(field) {
    return self.entries.column(field)[@intFromEnum(declaration)];
}

pub fn set(
    self: *DeclPool,
    declaration: Index,
    comptime field: Entry.Field,
    value: Entry.FieldType(field),
) void {
    self.entries.column(field)[@intFromEnum(declaration)] = value;
}

pub fn pointer(
    self: *DeclPool,
    declaration: Index,
    comptime field: Entry.Field,
) *Entry.FieldType(field) {
    return &self.entries.column(field)[@intFromEnum(declaration)];
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
pub fn implicit_self_count(self: *const DeclPool, declaration: Index) usize {
    const is_method = self.get(declaration, .kind) == .trait_member;
    return @intFromBool(is_method and self.get(declaration, .name) != .init);
}
