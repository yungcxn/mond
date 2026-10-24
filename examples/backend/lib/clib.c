// the c side of examples/backend/c_interop.mn: one function per way a value crosses into c
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct { int32_t x, y; } Pair;
typedef struct { double x, y; } Point;
typedef struct { int64_t a, b, c; } Triple;
typedef struct { float r, g, b; } Color;
typedef struct { uint8_t tag; int32_t value; } Tagged;

int8_t clib_negate8(int8_t value) { return (int8_t)-value; }
uint16_t clib_double16(uint16_t value) { return (uint16_t)(value * 2); }
bool clib_is_even(uint32_t value) { return value % 2 == 0; }

int64_t clib_sum_pair(Pair pair) { return pair.x + pair.y; }
Pair clib_make_pair(int32_t x, int32_t y) { return (Pair){x, y}; }
double clib_length2(Point point) { return point.x * point.x + point.y * point.y; }
Point clib_scale(Point point, double factor) { return (Point){point.x * factor, point.y * factor}; }
int64_t clib_sum_triple(Triple triple) { return triple.a + triple.b + triple.c; }
Triple clib_make_triple(int64_t base) { return (Triple){base, base + 1, base + 2}; }
float clib_brightness(Color color) { return color.r + color.g + color.b; }
Color clib_gray(float level) { return (Color){level, level, level}; }
int32_t clib_tagged(Tagged tagged) { return tagged.tag * 1000 + tagged.value; }

size_t clib_count(const uint8_t *bytes, size_t length, uint8_t wanted) {
    size_t count = 0;
    for (size_t i = 0; i < length; i++) count += bytes[i] == wanted;
    return count;
}

void clib_fill(int32_t *out, int32_t count) {
    for (int32_t i = 0; i < count; i++) out[i] = i * i;
}

int64_t clib_apply(int64_t (*function)(int64_t), int64_t value) { return function(value); }

int64_t clib_sum(int32_t count, ...) {
    va_list arguments;
    va_start(arguments, count);
    int64_t sum = 0;
    for (int32_t i = 0; i < count; i++) sum += va_arg(arguments, int);
    va_end(arguments);
    return sum;
}

double clib_average(int32_t count, ...) {
    va_list arguments;
    va_start(arguments, count);
    double sum = 0;
    for (int32_t i = 0; i < count; i++) sum += va_arg(arguments, double);
    va_end(arguments);
    return sum / count;
}

// slices cross as a record of the address of the first element and the length
typedef struct { uint8_t *bytes; uint64_t length; } Bytes;
uint64_t clib_slice_sum(Bytes s) {
    uint64_t total = 0;
    for (uint64_t i = 0; i < s.length; i++) total += s.bytes[i];
    return total;
}
Bytes clib_slice_tail(Bytes s) { return (Bytes){s.bytes + 1, s.length - 1}; }
void clib_slice_fill(Bytes s, uint8_t value) {
    for (uint64_t i = 0; i < s.length; i++) s.bytes[i] = value;
}
