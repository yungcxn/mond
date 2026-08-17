const std = @import("std");

const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const Parser = @import("Parser.zig");
const ParseTree = @import("ParseTree.zig");

const SimpleType = struct {
    pub const id_u8: u32 = 0xFFFFFFFF;
    pub const id_u32: u32 = 0xFFFFFFFE;
    pub const id_f32: u32 = 0xFFFFFFFD;
    pub const id_bool: u32 = 0xFFFFFFFC;
};

const ComposedType = union {};

const Symbol = packed struct {
    kind: Kind,

    const Kind = enum(u8) {
        variable,
        constant,
        function,

        structure,
        enumeration,

        typealias,
        funcalias,
    };
};

const Scope = packed struct {
    parent_scope_idx: u32,
    symbolref: packed struct { start_idx: u32, count: u32 },
};

node_type_idx: []u32, // node_type[node_idx] = type_idx -> types[type_idx] => type with id "type_idx"
type_name_table: std.StringHashMap(u32), // type_table.get("typename") => type_idx
types: DynBuf(ComposedType),

symbols: []const Lexer.TextSpan,

scopes: SoD(Scope),

// TODO: all templates must be concrete for a clear and concrete High-IR
