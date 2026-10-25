/* Janus NEON harvest corpus: saturating arithmetic, multiply-high, rounding
 * shifts and bit tricks (prefix nx_). */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))
#define RS restrict
#define NR

__extension__ typedef unsigned __int128 u128;

#define BIN(nm, T, R, expr)                                                   \
  NI void nx_##nm(T *R a, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i], y = c[i];                                                   \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
#define UN(nm, T, R, expr)                                                    \
  NI void nx_##nm(T *R a, const T *R b, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i];                                                             \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
#define ACC1(nm, T, R, expr)                                                  \
  NI void nx_##nm(T *R a, const T *R b, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      T z = a[i], x = b[i];                                                   \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }

static inline uint32_t bitrev32(uint32_t v) {
  v = ((v >> 1) & 0x55555555u) | ((v & 0x55555555u) << 1);
  v = ((v >> 2) & 0x33333333u) | ((v & 0x33333333u) << 2);
  v = ((v >> 4) & 0x0f0f0f0fu) | ((v & 0x0f0f0f0fu) << 4);
  return __builtin_bswap32(v);
}
static inline int32_t absdiff32(int32_t x, int32_t y) {
  int32_t d = (int32_t)((uint32_t)x - (uint32_t)y), m = d >> 31;
  return (d ^ m) - m;
}
static inline uint32_t xorshift32(uint32_t v) {
  v ^= v << 13; v ^= v >> 17; v ^= v << 5;
  return v;
}
static inline uint64_t mix64(uint64_t v) {
  v ^= v >> 33; v *= 0xff51afd7ed558ccdull; v ^= v >> 33;
  return v;
}

/* ---- saturating add / sub, written the usual C ways ---- */
BIN(uqadd_u8, uint8_t, RS, (unsigned)x + y > 255 ? 255 : x + y)
BIN(uqadd_u16, uint16_t, NR, (unsigned)x + y > 65535 ? 65535 : x + y)
BIN(uqadd_u32, uint32_t, RS, x + y < x ? UINT32_MAX : x + y)
BIN(uqadd_u64, uint64_t, NR, x + y < x ? UINT64_MAX : x + y)
BIN(sqadd_i8, int8_t, NR, x + y > 127 ? 127 : (x + y < -128 ? -128 : x + y))
BIN(sqadd_i16, int16_t, RS, x + y > 32767 ? 32767 : (x + y < -32768 ? -32768 : x + y))
BIN(sqadd_i32, int32_t, NR,
    (int64_t)x + y > INT32_MAX ? INT32_MAX : ((int64_t)x + y < INT32_MIN ? INT32_MIN : x + (int64_t)y))
BIN(uqsub_u8, uint8_t, RS, x > y ? x - y : 0)
BIN(uqsub_u16, uint16_t, NR, x >= y ? x - y : 0)
BIN(uqsub_u32, uint32_t, RS, x > y ? x - y : 0)
BIN(sqsub_i8, int8_t, RS, x - y > 127 ? 127 : (x - y < -128 ? -128 : x - y))
BIN(sqsub_i16, int16_t, NR, x - y > 32767 ? 32767 : (x - y < -32768 ? -32768 : x - y))
UN(sqabs_i8, int8_t, NR, x == -128 ? 127 : (x < 0 ? -x : x))
UN(sqneg_i16, int16_t, RS, x == -32768 ? 32767 : -x)
UN(sqshl_u8, uint8_t, RS, x > 63 ? 255 : x << 2)
NI void nx_sat_accum_u8(uint8_t *restrict a, const uint8_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    unsigned s = a[i] + b[i];
    a[i] = (uint8_t)(s > 255 ? 255 : s);
  }
}
NI void nx_sat_mix_i16(int16_t *a, const int16_t *b, const int16_t *c, size_t n) {
  for (size_t i = 0; i < n; i++) {
    int s = (b[i] + c[i]) >> 1;
    s += b[i];
    a[i] = (int16_t)(s > 32767 ? 32767 : (s < -32768 ? -32768 : s));
  }
}

/* ---- multiply high / fixed-point multiplies ---- */
BIN(mulh_i32, int32_t, RS, ((int64_t)x * y) >> 32)
BIN(mulh_u32, uint32_t, NR, ((uint64_t)x * y) >> 32)
BIN(mulh_i16, int16_t, NR, ((int32_t)x * y) >> 16)
BIN(mulh_u16, uint16_t, RS, ((uint32_t)x * y) >> 16)
BIN(mulh_u8, uint8_t, RS, ((unsigned)x * y) >> 8)
BIN(q15_mul, int16_t, NR, ((int32_t)x * y) >> 15)
BIN(q15_rmul, int16_t, RS, ((int32_t)x * y + (1 << 14)) >> 15)
BIN(sqdmulh_i16, int16_t, RS,
    (((int32_t)x * y) >> 15) > 32767 ? 32767 : (((int32_t)x * y) >> 15))
BIN(q31_mul, int32_t, NR, ((int64_t)x * y) >> 31)
BIN(mulh_u64, uint64_t, NR, (uint64_t)(((u128)x * y) >> 64))
UN(div_const_u32, uint32_t, RS, x / 7)
UN(div_const_i16, int16_t, NR, x / 10)
UN(mod_const_u16, uint16_t, RS, x % 3)

/* ---- rounding shifts ---- */
UN(urshr_u16, uint16_t, RS, (x + 8) >> 4)
UN(srshr_i32, int32_t, NR, (x + (1 << 9)) >> 10)
UN(urshr_u8, uint8_t, NR, (x + 2) >> 2)
ACC1(ursra_u32, uint32_t, RS, z + ((x + 16) >> 5))
ACC1(srsra_i16, int16_t, NR, z + ((x + 4) >> 3))

/* ---- clz / ctz / bit reversal / other bit tricks ---- */
UN(clz_u32, uint32_t, RS, x ? (uint32_t)__builtin_clz(x) : 32)
UN(clz_u16, uint16_t, NR, x ? __builtin_clz(x) - 16 : 16)
UN(clz_u8, uint8_t, RS, x ? __builtin_clz(x) - 24 : 8)
UN(cls_i32, int32_t, NR, __builtin_clrsb(x))
UN(ctz_u32, uint32_t, NR, x ? (uint32_t)__builtin_ctz(x) : 32)
UN(ctz_u64, uint64_t, RS, x ? (uint64_t)__builtin_ctzll(x) : 64)
UN(bitrev_u8, uint8_t, NR,
   ((x * 0x0802u & 0x22110u) | (x * 0x8020u & 0x88440u)) * 0x10101u >> 16)
UN(bitrev_u32, uint32_t, RS, bitrev32(x))
UN(bitrev_nib_u8, uint8_t, NR, (uint8_t)((x << 4) | (x >> 4)))
UN(lowbit_u32, uint32_t, RS, x & -x)
UN(clear_lowbit_u64, uint64_t, NR, x & (x - 1))
UN(gray_u16, uint16_t, RS, x ^ (x >> 1))
UN(sign_i32, int32_t, NR, (x > 0) - (x < 0))
UN(sign_i8, int8_t, RS, (x > 0) - (x < 0))
UN(ispow2_u32, uint32_t, NR, x && !(x & (x - 1)))
UN(mask_from_bit_u32, uint32_t, RS, (uint32_t)-(int32_t)((x >> 5) & 1))
UN(nibble_popcnt_u8, uint8_t, NR,
   ((x & 0x55) + ((x >> 1) & 0x55)))
UN(parity_u32, uint32_t, RS, __builtin_parity(x))
BIN(bitmerge_u16, uint16_t, RS, (x & 0x5555) | (y & 0xaaaa))
BIN(avg_floor_bits_u32, uint32_t, NR, (x & y) + ((x ^ y) >> 1))
BIN(avg_ceil_bits_u32, uint32_t, RS, (x | y) - ((x ^ y) >> 1))
BIN(abs_diff_bits_i32, int32_t, NR, absdiff32(x, y))
UN(xorshift_u32, uint32_t, RS, xorshift32(x))
UN(hash_mix_u64, uint64_t, NR, mix64(x))
