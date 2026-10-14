const std = @import("std");
const llvm = @import("llvm_c");
const mond = @import("mond");
const ParseTree = mond.ParseTree;
const Metadata = llvm.LLVMMetadataRef;

// dwarf for a debugger: the source file, a subprogram per function and the line and column of
// every instruction, from the tree node it was lowered from (`HighIr.Inst.origin`)
const DebugInfo = @This();

allocator: std.mem.Allocator,
context: llvm.LLVMContextRef,
builder: llvm.LLVMDIBuilderRef,
file: Metadata,
// every function is typed the same, a debugger reads names and lines from it
function_type: Metadata,
tree: *const ParseTree,
source: []const u8,
// the byte offset where each line starts
line_starts: []u32,
// the function being lowered, and the origin of the location set last
scope: Metadata = null,
function_line: u32 = 0,
last_origin: u32 = std.math.maxInt(u32),

pub fn init(
    allocator: std.mem.Allocator,
    module: llvm.LLVMModuleRef,
    tree: *const ParseTree,
    source: []const u8,
    absolute_path: []const u8,
    optimized: bool,
) DebugInfo {
    const context = llvm.LLVMGetModuleContext(module);
    add_flag(module, "Debug Info Version", llvm.LLVMDebugMetadataVersion());
    add_flag(module, "Dwarf Version", 4);

    const builder = llvm.LLVMCreateDIBuilder(module);
    const directory = std.fs.path.dirname(absolute_path) orelse "/";
    const name = std.fs.path.basename(absolute_path);
    const file = llvm.LLVMDIBuilderCreateFile(
        builder,
        name.ptr,
        name.len,
        directory.ptr,
        directory.len,
    );
    const producer = "mond";
    _ = llvm.LLVMDIBuilderCreateCompileUnit(
        builder,
        llvm.LLVMDWARFSourceLanguageC,
        file,
        producer,
        producer.len,
        @intFromBool(optimized),
        "",
        0,
        0,
        "",
        0,
        llvm.LLVMDWARFEmissionFull,
        0,
        0,
        0,
        "",
        0,
        "",
        0,
    );

    var line_starts: std.ArrayList(u32) = .empty;
    line_starts.append(allocator, 0) catch @panic("OOM");
    for (source, 0..) |character, i| {
        if (character == '\n') line_starts.append(allocator, @intCast(i + 1)) catch @panic("OOM");
    }
    return .{
        .allocator = allocator,
        .context = context,
        .builder = builder,
        .file = file,
        .function_type = llvm.LLVMDIBuilderCreateSubroutineType(builder, file, null, 0, 0),
        .tree = tree,
        .source = source,
        .line_starts = line_starts.toOwnedSlice(allocator) catch @panic("OOM"),
    };
}

pub fn deinit(self: *DebugInfo) void {
    llvm.LLVMDisposeDIBuilder(self.builder);
    self.allocator.free(self.line_starts);
}

// resolves what the functions left open, before the module is optimized or emitted
pub fn finish(self: *DebugInfo) void {
    llvm.LLVMDIBuilderFinalize(self.builder);
}

fn add_flag(module: llvm.LLVMModuleRef, key: []const u8, value: u64) void {
    const context = llvm.LLVMGetModuleContext(module);
    const constant = llvm.LLVMConstInt(llvm.LLVMInt32TypeInContext(context), value, 0);
    llvm.LLVMAddModuleFlag(
        module,
        llvm.LLVMModuleFlagBehaviorWarning,
        key.ptr,
        key.len,
        llvm.LLVMValueAsMetadata(constant),
    );
}

// the function's instructions are placed in it from now on
pub fn enter_function(
    self: *DebugInfo,
    function: llvm.LLVMValueRef,
    name: []const u8,
    origin: u32,
    optimized: bool,
) void {
    const line = self.position(origin)[0];
    self.scope = llvm.LLVMDIBuilderCreateFunction(
        self.builder,
        self.file,
        name.ptr,
        name.len,
        name.ptr,
        name.len,
        self.file,
        line,
        self.function_type,
        1,
        1,
        line,
        llvm.LLVMDIFlagZero,
        @intFromBool(optimized),
    );
    llvm.LLVMSetSubprogram(function, self.scope);
    self.function_line = line;
    self.last_origin = std.math.maxInt(u32);
}

// a function without a source of its own (a thunk, `main` of c) is built without locations
pub fn leave_function(self: *DebugInfo, builder: llvm.LLVMBuilderRef) void {
    self.scope = null;
    llvm.LLVMSetCurrentDebugLocation2(builder, null);
}

// what `builder` makes next comes from `origin`, the function's own line when that is 0
pub fn locate(self: *DebugInfo, builder: llvm.LLVMBuilderRef, origin: u32) void {
    if (self.scope == null or origin == self.last_origin) return;
    self.last_origin = origin;
    const line, const column = if (origin == 0)
        .{ self.function_line, 0 }
    else
        self.position(origin);
    const location = llvm.LLVMDIBuilderCreateDebugLocation(
        self.context,
        line,
        column,
        self.scope,
        null,
    );
    llvm.LLVMSetCurrentDebugLocation2(builder, location);
}

// one-based line and column of a node
fn position(self: *DebugInfo, node: u32) [2]u32 {
    const span = mond.dbg.node_span(self.tree, self.source, node) orelse return .{ 1, 1 };
    const at: u32 = @intCast(span[0]);
    var low: usize = 0;
    var high: usize = self.line_starts.len;
    while (high - low > 1) {
        const middle = (low + high) / 2;
        if (self.line_starts[middle] <= at) low = middle else high = middle;
    }
    return .{ @intCast(low + 1), at - self.line_starts[low] + 1 };
}
