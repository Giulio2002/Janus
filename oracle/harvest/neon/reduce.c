/* Janus NEON harvest corpus: reductions (prefix nr_).
 * Sums (incl. widening), dot products, min/max, any/all, match counts,
 * horizontal logic, float sums via explicit partial sums (no -ffast-math
 * needed), popcounts and sums of absolute differences. */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))

/* R acc = init; acc = f(acc, x = s[i]) */
#define RED(nm, R, S, init, expr)                                             \
  NI R nr_##nm(const S *s, size_t n) {                                        \
    R acc = (init);                                                           \
    for (size_t i = 0; i < n; i++) {                                          \
      S x = s[i];                                                             \
      acc = (R)(expr);                                                        \
    }                                                                         \
    return acc;                                                               \
  }
#define RED2(nm, R, S, init, expr)                                            \
  NI R nr_##nm(const S *restrict a, const S *restrict b, size_t n) {          \
    R acc = (init);                                                           \
    for (size_t i = 0; i < n; i++) {                                          \
      S x = a[i], y = b[i];                                                   \
      acc = (R)(expr);                                                        \
    }                                                                         \
    return acc;                                                               \
  }

/* ---- sums ---- */
RED(sum_u8_u32, uint32_t, uint8_t, 0, acc + x)
RED(sum_i8_i32, int32_t, int8_t, 0, acc + x)
RED(sum_u8_u16, uint16_t, uint8_t, 0, acc + x)
RED(sum_u16_u32, uint32_t, uint16_t, 0, acc + x)
RED(sum_i16_i64, int64_t, int16_t, 0, acc + x)
RED(sum_i32, int32_t, int32_t, 0, acc + x)
RED(sum_u32_u64, uint64_t, uint32_t, 0, acc + x)
RED(sum_i64, int64_t, int64_t, 0, acc + x)
RED(sum_u8, uint8_t, uint8_t, 0, acc + x)
RED(sumsq_i16_i32, int32_t, int16_t, 0, acc + x * x)
RED(sum_abs_i32, int32_t, int32_t, 0, acc + (x < 0 ? -x : x))

/* ---- dot products ---- */
RED2(dot_i8_i32, int32_t, int8_t, 0, acc + x * y)
RED2(dot_u8_u32, uint32_t, uint8_t, 0, acc + (uint32_t)x * y)
RED2(dot_i16_i32, int32_t, int16_t, 0, acc + x * y)
RED2(dot_i16_i64, int64_t, int16_t, 0, acc + (int64_t)x * y)
RED2(dot_i32, int32_t, int32_t, 0, acc + x * y)
RED2(dot_i32_i64, int64_t, int32_t, 0, acc + (int64_t)x * y)
RED2(dot_u32_u64, uint64_t, uint32_t, 0, acc + (uint64_t)x * y)

/* ---- min / max ---- */
RED(maxv_u8, uint8_t, uint8_t, 0, x > acc ? x : acc)
RED(minv_u8, uint8_t, uint8_t, 255, x < acc ? x : acc)
RED(maxv_i8, int8_t, int8_t, -128, x > acc ? x : acc)
RED(minv_i16, int16_t, int16_t, 32767, x < acc ? x : acc)
RED(maxv_u16, uint16_t, uint16_t, 0, x > acc ? x : acc)
RED(maxv_i32, int32_t, int32_t, INT32_MIN, x > acc ? x : acc)
RED(minv_u32, uint32_t, uint32_t, UINT32_MAX, x < acc ? x : acc)
RED(maxv_u64, uint64_t, uint64_t, 0, x > acc ? x : acc)
RED(fmaxnmv_f32, float, float, -1e30f, __builtin_fmaxf(acc, x))
RED(fminnmv_f64, double, double, 1e300, __builtin_fmin(acc, x))

/* ---- any / all / count ---- */
RED(any_zero_u8, int, uint8_t, 0, acc | (x == 0))
RED(all_pos_i32, int, int32_t, 1, acc & (x > 0))
RED(count_eq_u8, uint32_t, uint8_t, 0, acc + (x == 'a'))
RED(count_gt_i16, int32_t, int16_t, 0, acc + (x > 100))
RED(count_nz_u32, uint32_t, uint32_t, 0, acc + (x != 0))
RED2(count_match_u8, uint32_t, uint8_t, 0, acc + (x == y))
RED(count_lt_f32, int32_t, float, 0, acc + (x < 0.5f))

/* ---- horizontal logic ---- */
RED(xor_u8, uint8_t, uint8_t, 0, acc ^ x)
RED(xor_u32, uint32_t, uint32_t, 0, acc ^ x)
RED(or_u16, uint16_t, uint16_t, 0, acc | x)
RED(or_u64, uint64_t, uint64_t, 0, acc | x)
RED(and_u32, uint32_t, uint32_t, 0xffffffffu, acc & x)
RED(and_u8, uint8_t, uint8_t, 0xff, acc & x)

/* ---- integer sum without widening, two arrays ---- */
RED2(sad_u8_u32, uint32_t, uint8_t, 0, acc + (x > y ? x - y : y - x))
RED2(sad_u8_u16, uint16_t, uint8_t, 0, acc + (x > y ? x - y : y - x))
RED2(sad_i16_i32, int32_t, int16_t, 0, acc + (x > y ? x - y : y - x))
RED2(ssd_u8_u32, uint32_t, uint8_t, 0, acc + (uint32_t)((x - y) * (x - y)))

/* ---- popcount ---- */
RED(popcnt_u8, uint32_t, uint8_t, 0, acc + (uint32_t)__builtin_popcount(x))
RED(popcnt_u32, uint32_t, uint32_t, 0, acc + (uint32_t)__builtin_popcount(x))
RED(popcnt_u64, uint64_t, uint64_t, 0, acc + (uint64_t)__builtin_popcountll(x))
RED2(hamming_u64, uint64_t, uint64_t, 0, acc + (uint64_t)__builtin_popcountll(x ^ y))
NI void nr_popcnt_each_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint8_t)__builtin_popcount(s[i]);
}
NI void nr_popcnt_each_u16(uint16_t *d, const uint16_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint16_t)__builtin_popcount(s[i]);
}

/* ---- float sums / dots with explicit partial sums (exact w/o fast-math) ---- */
NI float nr_fsum4_f32(const float *s, size_t n) {
  float p0 = 0, p1 = 0, p2 = 0, p3 = 0;
  for (size_t i = 0; i + 4 <= n; i += 4) {
    p0 += s[i]; p1 += s[i + 1]; p2 += s[i + 2]; p3 += s[i + 3];
  }
  return (p0 + p1) + (p2 + p3);
}
NI float nr_fdot8_f32(const float *restrict a, const float *restrict b, size_t n) {
  float p[8] = {0};
  for (size_t i = 0; i + 8 <= n; i += 8)
    for (int k = 0; k < 8; k++) p[k] += a[i + k] * b[i + k];
  return ((p[0] + p[4]) + (p[1] + p[5])) + ((p[2] + p[6]) + (p[3] + p[7]));
}
NI double nr_dsum2_f64(const double *s, size_t n) {
  double p0 = 0, p1 = 0;
  for (size_t i = 0; i + 2 <= n; i += 2) { p0 += s[i]; p1 += s[i + 1]; }
  return p0 + p1;
}
NI double nr_ddot4_f64(const double *a, const double *b, size_t n) {
  double p0 = 0, p1 = 0, p2 = 0, p3 = 0;
  for (size_t i = 0; i + 4 <= n; i += 4) {
    p0 += a[i] * b[i]; p1 += a[i + 1] * b[i + 1];
    p2 += a[i + 2] * b[i + 2]; p3 += a[i + 3] * b[i + 3];
  }
  return (p0 + p2) + (p1 + p3);
}
NI float nr_fmax4_f32(const float *s, size_t n) {
  float m0 = s[0], m1 = s[1], m2 = s[2], m3 = s[3];
  for (size_t i = 4; i + 4 <= n; i += 4) {
    m0 = __builtin_fmaxf(m0, s[i]); m1 = __builtin_fmaxf(m1, s[i + 1]);
    m2 = __builtin_fmaxf(m2, s[i + 2]); m3 = __builtin_fmaxf(m3, s[i + 3]);
  }
  return __builtin_fmaxf(__builtin_fmaxf(m0, m1), __builtin_fmaxf(m2, m3));
}
NI float nr_fsum_inorder_f32(const float *s, size_t n) {
  float acc = 0;
  for (size_t i = 0; i < n; i++) acc += s[i];
  return acc;
}
NI void nr_pairwise_add_f32(float *restrict d, const float *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[2 * i] + s[2 * i + 1];
}
NI void nr_pairwise_add_u16_u32(uint32_t *restrict d, const uint16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint32_t)s[2 * i] + s[2 * i + 1];
}
NI void nr_pairwise_max_i32(int32_t *d, const int32_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[2 * i] > s[2 * i + 1] ? s[2 * i] : s[2 * i + 1];
}

/* ---- signed pairwise widening, abs()-style SAD ---- */
NI void nr_pairsum_i8_i16(int16_t *restrict d, const int8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (int16_t)(s[2 * i] + s[2 * i + 1]);
}
NI void nr_pairacc_i16_i32(int32_t *d, const int16_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] += s[2 * i] + s[2 * i + 1];
}
RED(sum_i16_i32, int32_t, int16_t, 0, acc + x)
RED(sum_i8_i16, int16_t, int8_t, 0, acc + x)
RED2(sad_abs_u8, uint32_t, uint8_t, 0, acc + (uint32_t)__builtin_abs((int)x - (int)y))
RED2(sad_abs_u16, uint32_t, uint16_t, 0, acc + (uint32_t)__builtin_abs((int)x - (int)y))
NI void nr_uabal_abs_u8(uint16_t *restrict d, const uint8_t *restrict a,
                        const uint8_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint16_t)(d[i] + __builtin_abs((int)a[i] - (int)b[i]));
}
NI void nr_uabal_abs_u16(uint32_t *d, const uint16_t *a, const uint16_t *b, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] += (uint32_t)__builtin_abs((int)a[i] - (int)b[i]);
}
