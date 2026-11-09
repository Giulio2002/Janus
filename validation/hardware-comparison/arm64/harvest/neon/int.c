/* Janus NEON harvest corpus: element-wise integer loops (prefix ni_).
 * Plain C11, no intrinsics: every AdvSIMD instruction comes from the
 * auto-vectoriser.  RS = restrict-qualified (no runtime alias versioning),
 * NR = plain pointers (the compiler must version or prove no overlap). */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))
#define RS restrict
#define NR

/* a[i] = f(x = b[i], y = c[i]) */
#define BIN(nm, T, R, expr)                                                   \
  NI void ni_##nm(T *R a, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i], y = c[i];                                                   \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
/* a[i] = f(z = a[i], x = b[i], y = c[i]) */
#define ACC(nm, T, R, expr)                                                   \
  NI void ni_##nm(T *R a, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T z = a[i], x = b[i], y = c[i];                                         \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
/* a[i] = f(z = a[i], x = b[i]) */
#define ACC1(nm, T, R, expr)                                                  \
  NI void ni_##nm(T *R a, const T *R b, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      T z = a[i], x = b[i];                                                   \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
/* a[i] = f(x = b[i]) */
#define UN(nm, T, R, expr)                                                    \
  NI void ni_##nm(T *R a, const T *R b, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i];                                                             \
      a[i] = (T)(expr);                                                       \
    }                                                                         \
  }
/* a[i] = b[i] OP c[i] ? d[i] : e[i] */
#define SEL(nm, T, R, op)                                                     \
  NI void ni_##nm(T *R a, const T *R b, const T *R c, const T *R d,           \
                  const T *R e, int n) {                                      \
    for (int i = 0; i < n; i++) a[i] = b[i] op c[i] ? d[i] : e[i];            \
  }

/* ---- sign-agnostic arithmetic / logic, spread over the widths ---- */
BIN(add_i8, int8_t, RS, x + y)
BIN(add_u16, uint16_t, NR, x + y)
BIN(add_i32, int32_t, RS, x + y)
BIN(add_u64, uint64_t, NR, x + y)
BIN(sub_u8, uint8_t, NR, x - y)
BIN(sub_i16, int16_t, RS, x - y)
BIN(sub_u32, uint32_t, NR, x - y)
BIN(sub_i64, int64_t, RS, x - y)
BIN(mul_u8, uint8_t, RS, x * y)
BIN(mul_i16, int16_t, NR, x * y)
BIN(mul_i32, int32_t, RS, x * y)
BIN(mul_u64, uint64_t, NR, x * y)
ACC(mla_i8, int8_t, NR, z + x * y)
ACC(mla_u16, uint16_t, RS, z + x * y)
ACC(mla_i32, int32_t, NR, z + x * y)
ACC(mls_u8, uint8_t, RS, z - x * y)
ACC(mls_i16, int16_t, NR, z - x * y)
ACC(mls_u32, uint32_t, RS, z - x * y)
BIN(and_u8, uint8_t, RS, x & y)
BIN(orr_u16, uint16_t, NR, x | y)
BIN(eor_u32, uint32_t, RS, x ^ y)
BIN(bic_u64, uint64_t, NR, x & ~y)
BIN(orn_u32, uint32_t, RS, x | ~y)
UN(not_u8, uint8_t, NR, ~x)
BIN(bsl_u32, uint32_t, RS, (x & 0x0f0f0f0fu) | (y & 0xf0f0f0f0u))
ACC(bitsel_u8, uint8_t, NR, (z & x) | (~z & y))
ACC(bitsel_u64, uint64_t, RS, (x & z) | (y & ~z))

/* ---- negate / abs ---- */
UN(neg_i8, int8_t, RS, -x)
UN(neg_i16, int16_t, NR, -x)
UN(neg_i32, int32_t, RS, -x)
UN(neg_i64, int64_t, NR, -x)
UN(abs_i8, int8_t, NR, x < 0 ? -x : x)
UN(abs_i16, int16_t, RS, x < 0 ? -x : x)
UN(abs_i32, int32_t, NR, x < 0 ? -x : x)
UN(abs_i64, int64_t, RS, x < 0 ? -x : x)

/* ---- min / max (both signednesses) ---- */
BIN(min_i8, int8_t, RS, x < y ? x : y)
BIN(max_u8, uint8_t, NR, x > y ? x : y)
BIN(max_i16, int16_t, NR, x > y ? x : y)
BIN(min_u16, uint16_t, RS, x < y ? x : y)
BIN(min_i32, int32_t, NR, x < y ? x : y)
BIN(max_u32, uint32_t, RS, x > y ? x : y)
BIN(max_i64, int64_t, RS, x > y ? x : y)
BIN(min_u64, uint64_t, NR, x < y ? x : y)

/* ---- compare -> mask, compare -> select ---- */
BIN(cmeq_u8, uint8_t, RS, x == y ? 0xff : 0)
BIN(cmgt_i16, int16_t, NR, x > y ? -1 : 0)
BIN(cmhi_u16, uint16_t, RS, x > y ? 0xffff : 0)
BIN(cmge_i32, int32_t, NR, x >= y ? -1 : 0)
BIN(cmhs_u32, uint32_t, RS, x >= y ? 0xffffffffu : 0)
BIN(cmgt_i64, int64_t, NR, x > y ? -1 : 0)
BIN(cmtst_u8, uint8_t, NR, (x & y) ? 0xff : 0)
BIN(cmtst_u32, uint32_t, RS, (x & y) ? 0xffffffffu : 0)
UN(cmlt0_i8, int8_t, RS, x < 0 ? -1 : 0)
UN(cmeq0_i32, int32_t, NR, x == 0 ? -1 : 0)
UN(cmle0_i16, int16_t, RS, x <= 0 ? 1 : 0)
SEL(sel_gt_i8, int8_t, RS, >)
SEL(sel_gt_u8, uint8_t, NR, >)
SEL(sel_ge_i16, int16_t, NR, >=)
SEL(sel_lt_u16, uint16_t, RS, <)
SEL(sel_gt_i32, int32_t, RS, >)
SEL(sel_ne_u32, uint32_t, NR, !=)
SEL(sel_gt_u64, uint64_t, RS, >)
SEL(sel_eq_i64, int64_t, NR, ==)

/* ---- shifts by constant ---- */
UN(shl_u8, uint8_t, RS, x << 3)
UN(shl_i16, int16_t, NR, x << 5)
UN(shl_u32, uint32_t, RS, x << 7)
UN(shl_i64, int64_t, NR, (uint64_t)x << 13)
UN(ushr_u8, uint8_t, NR, x >> 2)
UN(ushr_u16, uint16_t, RS, x >> 9)
UN(ushr_u32, uint32_t, NR, x >> 11)
UN(ushr_u64, uint64_t, RS, x >> 40)
UN(sshr_i8, int8_t, RS, x >> 3)
UN(sshr_i16, int16_t, NR, x >> 4)
UN(sshr_i32, int32_t, RS, x >> 17)
UN(sshr_i64, int64_t, NR, x >> 33)

/* ---- shifts by variable amounts ---- */
BIN(ushl_u8, uint8_t, NR, x << (y & 7))
BIN(sshl_i16, int16_t, RS, (uint16_t)x << (y & 15))
BIN(ushl_u32, uint32_t, RS, x << (y & 31))
BIN(ushl_u64, uint64_t, NR, x << (y & 63))
BIN(ushrv_u16, uint16_t, NR, x >> (y & 15))
BIN(ushrv_u32, uint32_t, RS, x >> (y & 31))
BIN(sshrv_i32, int32_t, NR, x >> (y & 31))
BIN(sshrv_i64, int64_t, RS, x >> (y & 63))
BIN(sshrv_i8, int8_t, RS, x >> (y & 7))

/* ---- shift-accumulate, shift-insert, rotate ---- */
ACC1(usra_u8, uint8_t, RS, z + (x >> 3))
ACC1(usra_u32, uint32_t, NR, z + (x >> 7))
ACC1(ssra_i16, int16_t, RS, z + (x >> 2))
ACC1(ssra_i64, int64_t, NR, z + (x >> 20))
ACC1(sli_u16, uint16_t, RS, (z & 0x00ff) | (uint16_t)(x << 8))
ACC1(sri_u32, uint32_t, NR, (z & 0xff000000u) | (x >> 8))
UN(rol_u32, uint32_t, RS, (x << 7) | (x >> 25))
UN(ror_u64, uint64_t, NR, (x >> 17) | (x << 47))
UN(rol_u16, uint16_t, NR, (uint16_t)(x << 3) | (x >> 13))
UN(rol_u8, uint8_t, RS, (uint8_t)(x << 1) | (x >> 7))
BIN(rolv_u32, uint32_t, RS, (x << (y & 31)) | (x >> ((32 - y) & 31)))

/* ---- averaging ---- */
BIN(urhadd_u8, uint8_t, RS, (x + y + 1) >> 1)
BIN(uhadd_u8, uint8_t, NR, (x + y) >> 1)
BIN(urhadd_u16, uint16_t, NR, (x + y + 1) >> 1)
BIN(uhadd_u16, uint16_t, RS, (x + y) >> 1)
BIN(srhadd_i8, int8_t, NR, (x + y + 1) >> 1)
BIN(shadd_i16, int16_t, RS, (x + y) >> 1)
BIN(uhadd_u32, uint32_t, RS, ((uint64_t)x + y) >> 1)
BIN(urhadd_u32, uint32_t, NR, ((uint64_t)x + y + 1) >> 1)

/* ---- absolute difference, abs-diff-accumulate ---- */
BIN(uabd_u8, uint8_t, RS, x > y ? x - y : y - x)
BIN(sabd_i8, int8_t, NR, x > y ? x - y : y - x)
BIN(uabd_u16, uint16_t, NR, x > y ? x - y : y - x)
BIN(sabd_i16, int16_t, RS, x > y ? x - y : y - x)
BIN(sabd_i32, int32_t, RS, x > y ? x - y : y - x)
BIN(uabd_u32, uint32_t, NR, x > y ? x - y : y - x)
ACC(uaba_u8, uint8_t, NR, z + (x > y ? x - y : y - x))
ACC(saba_i16, int16_t, RS, z + (x > y ? x - y : y - x))

/* ---- clamp to range ---- */
UN(clamp_i8, int8_t, RS, x < -100 ? -100 : (x > 100 ? 100 : x))
UN(clamp_u8, uint8_t, NR, x < 16 ? 16 : (x > 235 ? 235 : x))
UN(clamp_i16, int16_t, NR, x < -1000 ? -1000 : (x > 1000 ? 1000 : x))
UN(clamp_u16, uint16_t, RS, x > 4095 ? 4095 : x)
UN(clamp_i32, int32_t, RS, x < 0 ? 0 : (x > 65535 ? 65535 : x))
UN(clamp_u32, uint32_t, NR, x < 10 ? 10 : (x > 1000000 ? 1000000 : x))

/* ---- broadcast scalar / immediate operands ---- */
NI void ni_add_scalar_i16(int16_t *restrict a, const int16_t *restrict b,
                          int16_t s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = (int16_t)(b[i] + s);
}
NI void ni_mul_scalar_u32(uint32_t *a, const uint32_t *b, uint32_t s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] * s;
}
NI void ni_mla_scalar_i32(int32_t *restrict a, const int32_t *restrict b,
                          int32_t s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] += b[i] * s;
}
NI void ni_and_imm_u16(uint16_t *a, const uint16_t *b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] & 0xff00;
}
NI void ni_orr_imm_u32(uint32_t *restrict a, const uint32_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] | 0x00ff0000u;
}
NI void ni_bic_imm_u32(uint32_t *a, const uint32_t *b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] & 0xffff00ffu;
}
NI void ni_add_iota_i32(int32_t *restrict a, const int32_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] + (int32_t)i;
}
NI void ni_mvni_u32(uint32_t *a, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = 0xfffeffffu ^ (uint32_t)i;
}
NI void ni_shift_by_scalar_u32(uint32_t *restrict a, const uint32_t *restrict b,
                               unsigned s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] << (s & 31);
}
NI void ni_sshr_by_scalar_i16(int16_t *a, const int16_t *b, unsigned s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = (int16_t)(b[i] >> (s & 15));
}
