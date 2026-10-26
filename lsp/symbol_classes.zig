const mond = @import("mond");
const Resolver = mond.Resolver;
const DeclPool = mond.DeclPool;
const Analysis = @import("Analysis.zig");
const Type = Analysis.Type;
const Modifier = Analysis.Modifier;

// what a declaration is to the reader: its class and modifiers when highlighted, its outline kind

pub fn class_of_kind(kind: DeclPool.Entry.Kind) Type {
    return switch (kind) {
        .parameter, .static_parameter => .parameter,
        .field => .property,
        .function, .static_function, .inlined_function => .function,
        .trait_member => .method,
        .type_alias => .type,
        .record => .@"struct",
        .variant => .@"enum",
        .variant_case => .enumMember,
        .trait => .interface,
        .variable,
        .pattern_binder,
        .arrow_binder,
        .loop_variable,
        .self,
        .autoins_arg,
        .autoins_it,
        => .variable,
    };
}

pub fn declaration_modifiers(resolver: *Resolver, declaration: usize) u32 {
    const declarations = resolver.decl_pool.entries.columns();
    const class = class_of_kind(declarations.kind[declaration]);
    return modifiers(class, declarations.flags[declaration]);
}

// a value that cannot be written is readonly, one known at compile-time static
pub fn modifiers(class: Type, flags: DeclPool.Entry.Flags) u32 {
    const is_value = class == .variable or class == .parameter or class == .property;
    const readonly = modifier_bit(.readonly, is_value and !flags.is_mut);
    return readonly | modifier_bit(.static, flags.is_stc);
}

pub fn modifier_bit(modifier: Modifier, on: bool) u32 {
    return @as(u32, @intFromBool(on)) << @backingInt(modifier);
}

// lsp numbers the kinds of symbols
pub fn symbol_kind(class: Type) u8 {
    return switch (class) {
        .method => 6,
        .property => 8,
        .@"enum" => 10,
        .interface => 11,
        .function => 12,
        .enumMember => 22,
        .@"struct" => 23,
        .type => 26,
        .namespace => 3,
        .comment,
        .keyword,
        .operator,
        .string,
        .number,
        .variable,
        .parameter,
        .macro,
        => 13,
    };
}

pub fn is_type(resolver: *Resolver, node: u32) bool {
    const node_type = resolver.node_types[node];
    return node_type != .none and resolver.static_pool.tag(node_type) == .meta_type;
}
