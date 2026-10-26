const std = @import("std");

// a growable array of `T`: `buffer[0..len]` holds the elements, the rest is spare capacity
pub fn DynamicBuffer(T: type) type {
    return struct {
        const Self = @This();
        pub const Element = T;

        allocator: std.mem.Allocator,
        buffer: []T,
        len: u32 = 0,
        capacity: u32,

        pub fn init(allocator: std.mem.Allocator, initial_capacity: u32) Self {
            if (initial_capacity == 0) @panic("a dynamic buffer needs a capacity above zero");
            return .{
                .allocator = allocator,
                .buffer = allocator.alloc(T, initial_capacity) catch @panic("OOM"),
                .capacity = initial_capacity,
            };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.buffer);
        }

        inline fn ensure_capacity(self: *Self, needed: u32) void {
            if (needed <= self.capacity) return;
            // doubled in 64 bits, a u32 capacity past 2^31 would wrap to zero and never grow
            var grown: u64 = self.capacity;
            while (needed > grown) grown *= 2;
            self.capacity = @intCast(@min(grown, std.math.maxInt(u32)));
            self.buffer = self.allocator.realloc(self.buffer, self.capacity) catch @panic("OOM");
        }

        pub inline fn get(self: *const Self, index: u32) ?T {
            if (index >= self.len) return null;
            return self.buffer[index];
        }

        pub inline fn last(self: *const Self) ?T {
            if (self.len == 0) return null;
            return self.buffer[self.len - 1];
        }

        pub inline fn push(self: *Self, value: T) void {
            self.ensure_capacity(self.len + 1);
            self.buffer[self.len] = value;
            self.len += 1;
        }

        pub inline fn push_repeated(self: *Self, count: u32, value: T) void {
            const new_length = self.len + count;
            self.ensure_capacity(new_length);
            @memset(self.buffer[self.len..new_length], value);
            self.len = new_length;
        }

        pub inline fn append(self: *Self, values: []const T) void {
            const new_length = self.len + @as(u32, @intCast(values.len));
            self.ensure_capacity(new_length);
            @memcpy(self.buffer[self.len..new_length], values);
            self.len = new_length;
        }

        pub inline fn items(self: *const Self) []T {
            return self.buffer[0..self.len];
        }
    };
}

// a growable struct of arrays: one `DynamicBuffer` per field of `Row`, all of the same length,
// so a pass reading one field of every row touches only that field's memory
pub fn StructOfArrays(Row: type) type {
    const info = @typeInfo(Row).@"struct";

    return struct {
        const Self = @This();
        pub const Field = std.meta.FieldEnum(Row);

        pub const Buffers = blk: {
            var names: [info.field_names.len][]const u8 = undefined;
            var types: [info.field_types.len]type = undefined;
            for (info.field_names, info.field_types, 0..) |fname, ftype, i| {
                names[i] = fname;
                types[i] = DynamicBuffer(ftype);
            }
            break :blk @Struct(.auto, null, &names, &types, &@splat(.{}));
        };

        pub const Columns = blk: {
            var names: [info.field_names.len][]const u8 = undefined;
            var types: [info.field_types.len]type = undefined;
            for (info.field_names, info.field_types, 0..) |fname, ftype, i| {
                names[i] = fname;
                types[i] = []ftype;
            }
            break :blk @Struct(.auto, null, &names, &types, &@splat(.{}));
        };

        buffers: Buffers,

        pub fn init(allocator: std.mem.Allocator, initial_capacity: u32) Self {
            var buffers: Buffers = undefined;
            inline for (info.field_names) |fname| {
                @field(buffers, fname) = .init(allocator, initial_capacity);
            }
            return .{ .buffers = buffers };
        }

        pub fn deinit(self: *Self) void {
            inline for (info.field_names) |fname| @field(self.buffers, fname).deinit();
        }

        pub fn len(self: *const Self) u32 {
            return @field(self.buffers, info.field_names[0]).len;
        }

        pub fn push(self: *Self, row: Row) void {
            inline for (info.field_names) |fname| {
                @field(self.buffers, fname).push(@field(row, fname));
            }
        }

        pub fn get(self: *const Self, index: u32) ?Row {
            if (index >= self.len()) return null;
            var row: Row = undefined;
            inline for (info.field_names) |fname| {
                @field(row, fname) = @field(self.buffers, fname).buffer[index];
            }
            return row;
        }

        pub fn get_field(
            self: *const Self,
            comptime field: Field,
            index: u32,
        ) ?@FieldType(Row, @tagName(field)) {
            return @field(self.buffers, @tagName(field)).get(index);
        }

        pub fn last(self: *const Self) ?Row {
            if (self.len() == 0) return null;
            return self.get(self.len() - 1);
        }

        pub fn truncate(self: *Self, new_length: u32) void {
            std.debug.assert(new_length <= self.len());
            inline for (info.field_names) |fname| @field(self.buffers, fname).len = new_length;
        }

        pub fn column(self: *const Self, comptime field: Field) []@FieldType(Row, @tagName(field)) {
            return @field(self.buffers, @tagName(field)).items();
        }

        pub fn columns(self: *const Self) Columns {
            var result: Columns = undefined;
            inline for (info.field_names) |fname| {
                @field(result, fname) = @field(self.buffers, fname).items();
            }
            return result;
        }
    };
}
