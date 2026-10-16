// the c side of examples/backend/c_abi_shapes.mn: records that the calling conventions classify
// differently (mixed int and float eightbytes, homogeneous float aggregates of 2 to 4, too large
// ones, odd sizes), arguments past the registers, narrow ints, and calls back into mond
#include <stdbool.h>
#include <stdint.h>

typedef struct { float f; int32_t i; } FloatInt;
typedef struct { int64_t i; double d; } IntDouble;
typedef struct { double a, b, c, d; } Quad;
typedef struct { float a, b, c, d, e; } Five;
typedef struct { uint8_t a, b, c; } Three;
typedef struct { uint16_t v[3]; } Shorts;
typedef struct { bool flag; int8_t small; int16_t mid; } Narrow;
typedef struct { char c; double d; } CharDouble;

int64_t abi_float_int(FloatInt x) { return (int64_t)(x.f * 10) + x.i; }
FloatInt abi_make_float_int(int32_t i) { return (FloatInt){i * 0.5f, -i}; }
int64_t abi_int_double(IntDouble x) { return x.i + (int64_t)(x.d * 100); }
IntDouble abi_make_int_double(int64_t i) { return (IntDouble){i * 2, i / 4.0}; }
double abi_quad(Quad q) { return q.a + q.b * 10 + q.c * 100 + q.d * 1000; }
Quad abi_make_quad(double base) { return (Quad){base, base + 1, base + 2, base + 3}; }
double abi_five(Five f) { return f.a + f.b + f.c + f.d + f.e * 100; }
Five abi_make_five(float x) { return (Five){x, x, x, x, -x}; }
uint32_t abi_three(Three t) { return t.a * 10000u + t.b * 100u + t.c; }
Three abi_make_three(uint8_t x) { return (Three){x, (uint8_t)(x + 1), (uint8_t)(x + 2)}; }
uint32_t abi_shorts(Shorts s) { return s.v[0] + s.v[1] * 1000u + s.v[2] * 1000000u; }
int32_t abi_narrow(Narrow n) { return (n.flag ? 100000 : 0) + n.small * 100 + n.mid; }
double abi_char_double(CharDouble x) { return x.c + x.d; }

// fourteen arguments: past the eight integer and eight float registers
int64_t abi_many(int64_t a, double b, int64_t c, double d, int64_t e, double f, int64_t g,
                 double h, int64_t i, double j, int64_t k, double l, int64_t m, double n,
                 int32_t o, float p, int8_t q, uint16_t r) {
    return a + c + e + g + i + k + m + o + q + r + (int64_t)(b + d + f + h + j + l + n + p);
}

// narrow results: the caller must extend them as signed or unsigned
int8_t abi_minus_one8(void) { return -1; }
uint8_t abi_max8(void) { return 255; }
int16_t abi_min16(void) { return -32768; }
uint16_t abi_max16(void) { return 65535; }
bool abi_not(bool b) { return !b; }
int32_t abi_narrow_args(int8_t a, uint8_t b, int16_t c, uint16_t d) { return a + b + c + d; }

// mond functions called by c
int64_t abi_fold(int64_t (*f)(int64_t, int64_t), int64_t count) {
    int64_t acc = 0;
    for (int64_t i = 1; i <= count; i++) acc = f(acc, i);
    return acc;
}
double abi_call_float(double (*f)(double, float), double x) { return f(x, 0.5f); }
int64_t abi_call_record(int64_t (*f)(IntDouble), int64_t x) { return f((IntDouble){x, 0.25}); }
int32_t abi_sort3(int32_t *xs, int32_t (*less)(const int32_t *, const int32_t *)) {
    for (int i = 0; i < 3; i++)
        for (int j = 0; j + 1 < 3 - i; j++)
            if (less(&xs[j + 1], &xs[j])) { int32_t t = xs[j]; xs[j] = xs[j + 1]; xs[j + 1] = t; }
    return xs[0] * 100 + xs[1] * 10 + xs[2];
}
int64_t abi_call_maker(IntDouble (*f)(int64_t), int64_t x) {
    IntDouble r = f(x);
    return r.i * 100 + (int64_t)(r.d * 100);
}
double abi_call_quad(Quad (*f)(double, Quad), double x) {
    Quad q = f(x, (Quad){1, 2, 3, 4});
    return q.a + q.b * 10 + q.c * 100 + q.d * 1000;
}

// narrow results and arguments cut from wider values: only some calling conventions extend them
uint8_t abi_low_byte(uint32_t x) { return (uint8_t)x; }
int8_t abi_low_signed(uint32_t x) { return (int8_t)x; }
uint32_t abi_call_narrow(uint32_t (*f)(uint8_t), uint32_t x) { return f((uint8_t)x); }
typedef struct { int64_t a, b, c; } Longs;
int64_t abi_call_triple(Longs (*f)(int64_t), int64_t x) {
    Longs t = f(x);
    return t.a + t.b * 10 + t.c * 100;
}
