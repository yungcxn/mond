const std = @import("std");
const llvm = @import("llvm_c");
const mond = @import("mond");
const StaticPool = mond.StaticPool;
const NamePool = mond.NamePool;
const Index = StaticPool.Index;
const Type = llvm.LLVMTypeRef;

// the llvm type of every pool type, memoized. llvm lays out structs in c order with natural
// alignment like `StaticPool.layout`, so the sizes agree. records, arrays and tagged variants live
// in memory (`is_in_memory`), their values are pointers to them (`value_of`):
// - bool is `i1`, `()` and static-only types are `{}`
// - a pointer is `ptr`, so is a runtime-length array: the address of its first element
// - a function value is `{ptr fn, ptr env}`, see the thunks in LLVMLowerer.zig
// - a variant is `{tag, [n x iA]}`: the payload room of the widest case, in units of its
//   alignment, so the payloads start where the layout puts them. a `tagof self` variant is its int
const Types = @This();

allocator: std.mem.Allocator,
context: llvm.LLVMContextRef,
pool: *StaticPool,
names: *const NamePool,
// per pool entry, null until lowered: the pool is complete once the backend runs
memo: []Type,
pointer: Type,
// a function value: the function taking the environment first, and the environment
closure: Type,
unit: Type,
length: Type,

// the room of the payloads of a variant or unified variant
pub const PayloadRoom = struct { size: u64, align_log2: u8 };

pub fn init(
    allocator: std.mem.Allocator,
    context: llvm.LLVMContextRef,
    pool: *StaticPool,
    names: *const NamePool,
) Types {
    const pointer = llvm.LLVMPointerTypeInContext(context, 0);
    const length = llvm.LLVMInt64TypeInContext(context);
    const memo = allocator.alloc(Type, pool.items.len()) catch @panic("OOM");
    @memset(memo, null);
    return .{
        .allocator = allocator,
        .context = context,
        .pool = pool,
        .names = names,
        .memo = memo,
        .pointer = pointer,
        .closure = llvm.LLVMStructTypeInContext(
            context,
            @constCast(&[_]Type{ pointer, pointer }),
            2,
            0,
        ),
        .unit = llvm.LLVMStructTypeInContext(context, null, 0, 0),
        .length = length,
    };
}

pub fn deinit(self: *Types) void {
    self.allocator.free(self.memo);
}

pub fn of(self: *Types, type_index: Index) Type {
    if (type_index == .none) return self.unit;
    const i = @intFromEnum(type_index);
    if (self.memo[i] == null) self.memo[i] = self.lower(type_index);
    return self.memo[i];
}

// whether values of the type exist at run time: functions returning none of them return void
// a value of the type is the address of an immutable copy of it: llvm promotes small copies to
// registers, and large ones never become values too big for its instruction selection
pub fn is_in_memory(self: *const Types, type_index: Index) bool {
    if (type_index == .none) return false;
    return switch (self.pool.get(type_index)) {
        .record_type, .unified_variant_type => true,
        .array_type => |array| array.length != StaticPool.dyn_len,
        .variant_type => |variant| variant.tag_mode != .self,
        .variant_case_type => |case| self.is_in_memory(case.variant),
        else => false,
    };
}

// how a value of the type is held in a register
pub fn value_of(self: *Types, type_index: Index) Type {
    if (self.is_in_memory(type_index)) return self.pointer;
    return self.of(type_index);
}

pub fn has_value(type_index: Index) bool {
    return switch (type_index) {
        .none, .unit_type, .runit_type, .never_type, .poison_type => false,
        else => true,
    };
}

pub fn is_runtime_array(self: *const Types, type_index: Index) bool {
    return switch (self.pool.get(type_index)) {
        .array_type => |array| array.length == StaticPool.dyn_len,
        else => false,
    };
}

pub fn is_self_tagged(self: *const Types, type_index: Index) bool {
    const variant = self.declaring_variant(type_index);
    return self.pool.tag(variant) == .variant_type and
        self.pool.get(variant).variant_type.tag_mode == .self;
}

// the variant a case or variant type stands for, unified variants stay themselves and a case of a
// packed variant too: it has a size of its own
pub fn variant_of(self: *const Types, type_index: Index) Index {
    const declaring = self.declaring_variant(type_index);
    if (declaring == type_index or self.pool.get(declaring).variant_type.is_packed) {
        return type_index;
    }
    return declaring;
}

fn declaring_variant(self: *const Types, type_index: Index) Index {
    if (self.pool.tag(type_index) != .variant_case_type) return type_index;
    return self.pool.get(type_index).variant_case_type.variant;
}

pub fn tag_type(self: *const Types, variant_or_unified: Index) Index {
    const pool = self.pool;
    const variant = self.variant_of(variant_or_unified);
    if (pool.tag(variant) == .unified_variant_type) return pool.unified_tag_type(variant);
    const declared = pool.get(self.declaring_variant(variant)).variant_type.tag_type;
    if (declared == .none or declared == .poison_type) return .u8_type;
    return declared;
}

pub fn payload_room(self: *Types, variant_or_unified: Index) PayloadRoom {
    const pool = self.pool;
    var room: PayloadRoom = .{ .size = 0, .align_log2 = 0 };
    const variant = self.variant_of(variant_or_unified);
    // a case of a packed variant has a room for its own payload only
    if (pool.tag(variant) == .variant_case_type) {
        const payload = pool.get(variant).variant_case_type.payload;
        if (payload == .none) return room;
        const payload_layout = pool.layout(payload);
        return .{ .size = payload_layout.size, .align_log2 = payload_layout.align_log2 };
    }
    const is_unified = pool.tag(variant) == .unified_variant_type;
    const members: []const Index = if (is_unified)
        pool.get(variant).unified_variant_type.members
    else
        &.{variant};
    for (members) |member| {
        // a member that is one case fills the room itself
        if (is_unified and !pool.brings_cases(member)) {
            const member_layout = pool.layout(member);
            room.size = @max(room.size, member_layout.size);
            room.align_log2 = @max(room.align_log2, member_layout.align_log2);
            continue;
        }
        for (pool.get(member).variant_type.cases) |case| {
            const payload = pool.get(case).variant_case_type.payload;
            if (payload == .none) continue;
            const payload_layout = pool.layout(payload);
            room.size = @max(room.size, payload_layout.size);
            room.align_log2 = @max(room.align_log2, payload_layout.align_log2);
        }
    }
    return room;
}

fn lower(self: *Types, type_index: Index) Type {
    const pool = self.pool;
    const context = self.context;
    return switch (pool.get(type_index)) {
        .int_type => |int| llvm.LLVMIntTypeInContext(context, int.bits),
        .float_type => |float| switch (float.bits) {
            16 => llvm.LLVMHalfTypeInContext(context),
            32 => llvm.LLVMFloatTypeInContext(context),
            else => llvm.LLVMDoubleTypeInContext(context),
        },
        .simple_type => |simple| if (simple == .bool)
            llvm.LLVMInt1TypeInContext(context)
        else
            self.unit,
        .pointer_type => self.pointer,
        .array_type => |array| blk: {
            if (array.length == StaticPool.dyn_len) break :blk self.pointer;
            const length = pool.static_length(type_index) orelse 0;
            break :blk llvm.LLVMArrayType2(self.of(array.element), length);
        },
        .function_type => self.closure,
        .record_type => |record| blk: {
            const named = self.named_struct(type_index);
            self.memo[@intFromEnum(type_index)] = named;
            const fields = self.allocator.alloc(Type, record.field_types.len) catch @panic("OOM");
            defer self.allocator.free(fields);
            for (record.field_types, fields) |field_type, *field| field.* = self.of(field_type);
            const is_packed: c_int = @intFromBool(record.is_packed);
            llvm.LLVMStructSetBody(named, fields.ptr, @intCast(fields.len), is_packed);
            break :blk named;
        },
        .variant_type => |variant| if (variant.tag_mode == .self)
            self.of(variant.tag_type)
        else
            self.tagged(type_index),
        .variant_case_type => |case| if (self.variant_of(type_index) != type_index)
            self.of(case.variant)
        else if (self.is_self_tagged(type_index))
            self.of(self.tag_type(type_index))
        else
            self.tagged(type_index),
        .unified_variant_type => self.tagged(type_index),
        .meta_type, .trait_type, .static_function, .template_type, .type_variable => self.unit,
        .ast_type => self.unit,
        .int_value, .float_value, .simple_value, .string_value, .aggregate_value => self.unit,
        .variant_value, .function_value, .tree_value => self.unit,
    };
}

// `{tag, [n x iA]}` with A the payloads' alignment
fn tagged(self: *Types, variant_or_unified: Index) Type {
    const room = self.payload_room(variant_or_unified);
    const unit_bytes = @as(u64, 1) << @intCast(room.align_log2);
    const unit = llvm.LLVMIntTypeInContext(self.context, @intCast(unit_bytes * 8));
    const room_type = llvm.LLVMArrayType2(
        unit,
        std.math.divCeil(u64, room.size, unit_bytes) catch 0,
    );
    const named = self.named_struct(variant_or_unified);
    var fields = [_]Type{ self.of(self.tag_type(variant_or_unified)), room_type };
    llvm.LLVMStructSetBody(named, &fields, fields.len, 0);
    return named;
}

// named after the type as a program writes it, so the llvm ir reads like the source
fn named_struct(self: *Types, type_index: Index) Type {
    var buffer: [256]u8 = undefined;
    var writer = std.Io.Writer.fixed(buffer[0 .. buffer.len - 1]);
    self.pool.format(self.names, type_index, &writer) catch {};
    buffer[writer.end] = 0;
    return llvm.LLVMStructCreateNamed(self.context, &buffer);
}
