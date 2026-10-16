// the front end as the module `mond`: lexing up to `HighIr`, without llvm, for the compiler in
// main.zig and the tools in lsp/ and stats/
pub const Lexer = @import("Lexer.zig");
pub const Parser = @import("Parser.zig");
pub const ParseTree = @import("ParseTree.zig");
pub const Resolver = @import("Resolver.zig");
pub const HighLowerer = @import("HighLowerer.zig");
pub const HighIr = @import("high_lowerer/HighIr.zig");
pub const StaticPool = @import("resolver/StaticPool.zig");
pub const DeclPool = @import("resolver/DeclPool.zig");
pub const NamePool = @import("resolver/NamePool.zig");
pub const Doctor = @import("resolver/Doctor.zig");
pub const constructs = @import("language/constructs.zig");
pub const DynamicBuffer = @import("containers.zig").DynamicBuffer;
pub const dbg = @import("debug.zig");

// what programs are built for: the machine mond runs on
pub const target: struct { pointer_bits: u8, os: []const u8, arch: []const u8 } = .{
    .pointer_bits = 64,
    .os = @tagName(@import("builtin").os.tag),
    .arch = @tagName(@import("builtin").cpu.arch),
};
