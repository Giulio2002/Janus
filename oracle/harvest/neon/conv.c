/* Janus NEON harvest corpus: conversions, widening and narrowing (prefix nc_).
 * int<->fp, fp<->fp, rounding builtins, fixed point, widening multiply and
 * add (int8*int8 -> int16 ...), truncating / shifting / saturating narrowing. */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))
#define RS restrict
#define NR

/* d[i] = f(x = s[i]) with differing element types */
#define CV(nm, D, S, R, expr)                                                 \
  NI void nc_##nm(D *R d, const S *R s, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      S x = s[i];                                                             \
      d[i] = (D)(expr);                                                       \
    }                                                                         \
  }
/* d[i] = f(x = b[i], y = c[i]) widening/narrowing two-input */
#define CV2(nm, D, S, R, expr)                                                \
  NI void nc_##nm(D *R d, const S *R b, const S *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      S x = b[i], y = c[i];                                                   \
      d[i] = (D)(expr);                                                       \
    }                                                                         \
  }
/* d[i] += f(x = b[i], y = c[i]) mixed-width accumulate */
#define WACC(nm, D, S, R, expr)                                               \
  NI void nc_##nm(D *R d, const S *R b, const S *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      S x = b[i], y = c[i];                                                   \
      d[i] += (D)(expr);                                                      \
    }                                                                         \
  }

/* ---- int <-> fp ---- */
CV(scvtf_i32_f32, float, int32_t, RS, x)
CV(ucvtf_u32_f32, float, uint32_t, NR, x)
CV(scvtf_i64_f64, double, int64_t, NR, x)
CV(ucvtf_u64_f64, double, uint64_t, RS, x)
CV(fcvtzs_f32_i32, int32_t, float, RS, x)
CV(fcvtzu_f32_u32, uint32_t, float, NR, x)
CV(fcvtzs_f64_i64, int64_t, double, NR, x)
CV(fcvtzu_f64_u64, uint64_t, double, RS, x)
CV(scvtf_i32_f64, double, int32_t, RS, x)
CV(fcvtzs_f64_i32, int32_t, double, NR, x)
CV(scvtf_i16_f32, float, int16_t, NR, x)
CV(ucvtf_u8_f32, float, uint8_t, RS, x)
CV(fcvt_f32_u8_clamp, uint8_t, float, RS, x < 0.0f ? 0.0f : (x > 255.0f ? 255.0f : x))
CV(fcvt_f32_i16, int16_t, float, NR, x)

/* ---- fp <-> fp ---- */
CV(fcvtl_f32_f64, double, float, RS, x)
CV(fcvtn_f64_f32, float, double, NR, x)
CV(fcvtl_mul_f32_f64, double, float, NR, (double)x * 3.0)

/* ---- rounding builtins ---- */
CV(frintm_f32, float, float, RS, __builtin_floorf(x))
CV(frintp_f32, float, float, NR, __builtin_ceilf(x))
CV(frintz_f32, float, float, RS, __builtin_truncf(x))
CV(frintx_f32, float, float, NR, __builtin_rintf(x))
CV(frinti_f32, float, float, RS, __builtin_nearbyintf(x))
CV(frinta_f32, float, float, NR, __builtin_roundf(x))
CV(frintm_f64, double, double, NR, __builtin_floor(x))
CV(frintp_f64, double, double, RS, __builtin_ceil(x))
CV(frintz_f64, double, double, NR, __builtin_trunc(x))
CV(frintx_f64, double, double, RS, __builtin_rint(x))
CV(frinti_f64, double, double, NR, __builtin_nearbyint(x))
CV(frinta_f64, double, double, RS, __builtin_round(x))
CV(lround_f64, long, double, RS, __builtin_lround(x))
CV(lrint_f64, long, double, NR, __builtin_lrint(x))
CV(lroundf_i32, int32_t, float, NR, __builtin_lroundf(x))
CV(floor_to_i32, int32_t, float, RS, __builtin_floorf(x))
CV(ceil_to_i64, int64_t, double, NR, __builtin_ceil(x))

/* ---- fixed point ---- */
CV(fix16_from_f32, int32_t, float, RS, x * 65536.0f)
CV(fix16_to_f32, float, int32_t, NR, (float)x * (1.0f / 65536.0f))
CV(fix8_u16_to_f32, float, uint16_t, RS, (float)x / 256.0f)
CV(q31_from_f64, int64_t, double, NR, x * 2147483648.0)

/* ---- widening ---- */
CV(sxtl_i8_i16, int16_t, int8_t, RS, x)
CV(uxtl_u8_u16, uint16_t, uint8_t, NR, x)
CV(sxtl_i16_i32, int32_t, int16_t, NR, x)
CV(uxtl_u16_u32, uint32_t, uint16_t, RS, x)
CV(sxtl_i32_i64, int64_t, int32_t, RS, x)
CV(uxtl_u32_u64, uint64_t, uint32_t, NR, x)
CV(uxtl_u8_u32, uint32_t, uint8_t, RS, x)
CV(sxtl_i8_i64, int64_t, int8_t, NR, x)
CV(ushll_u8_u16, uint16_t, uint8_t, NR, (uint16_t)x << 4)
CV(sshll_i16_i32, int32_t, int16_t, RS, (int32_t)x * 256)
CV2(smull_i8_i16, int16_t, int8_t, RS, (int16_t)x * y)
CV2(umull_u8_u16, uint16_t, uint8_t, NR, (uint16_t)x * y)
CV2(smull_i16_i32, int32_t, int16_t, NR, (int32_t)x * y)
CV2(umull_u16_u32, uint32_t, uint16_t, RS, (uint32_t)x * y)
CV2(smull_i32_i64, int64_t, int32_t, RS, (int64_t)x * y)
CV2(umull_u32_u64, uint64_t, uint32_t, NR, (uint64_t)x * y)
CV2(uaddl_u16_u32, uint32_t, uint16_t, NR, (uint32_t)x + y)
CV2(saddl_i8_i16, int16_t, int8_t, RS, (int16_t)x + y)
CV2(usubl_u8_u16, uint16_t, uint8_t, RS, (uint16_t)((uint16_t)x - y))
CV2(ssubl_i32_i64, int64_t, int32_t, NR, (int64_t)x - y)
CV2(uabdl_u8_u16, uint16_t, uint8_t, NR, x > y ? x - y : y - x)
CV2(sabdl_i16_i32, int32_t, int16_t, RS, x > y ? x - y : y - x)
WACC(smlal_i8_i16, int16_t, int8_t, RS, (int16_t)x * y)
WACC(umlal_u8_u16, uint16_t, uint8_t, NR, (uint16_t)x * y)
WACC(smlal_i16_i32, int32_t, int16_t, NR, (int32_t)x * y)
WACC(umlal_u16_u32, uint32_t, uint16_t, RS, (uint32_t)x * y)
WACC(smlal_i32_i64, int64_t, int32_t, RS, (int64_t)x * y)
WACC(umlsl_u16_u32, uint32_t, uint16_t, NR, -((uint32_t)x * y))
WACC(uabal_u8_u16, uint16_t, uint8_t, RS, x > y ? x - y : y - x)

NI void nc_uaddw_u32_u16(uint32_t *restrict d, const uint16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] += s[i];
}
NI void nc_saddw_i16_i8(int16_t *d, const int8_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (int16_t)(d[i] + s[i]);
}
NI void nc_usubw_u64_u32(uint64_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] -= s[i];
}
NI void nc_count_u8_u32(uint32_t *restrict hist, const uint8_t *restrict b,
                        const uint8_t *restrict c, size_t n) {
  for (size_t i = 0; i < n; i++) hist[i] += (b[i] == c[i]);
}

/* ---- narrowing ---- */
CV(xtn_i32_i16, int16_t, int32_t, RS, x)
CV(xtn_u32_u8, uint8_t, uint32_t, NR, x)
CV(xtn_u64_u32, uint32_t, uint64_t, NR, x)
CV(xtn_u16_u8, uint8_t, uint16_t, RS, x)
CV(shrn_u16_u8, uint8_t, uint16_t, NR, x >> 8)
CV(shrn_i32_i16, int16_t, int32_t, RS, x >> 16)
CV(shrn_u64_u32, uint32_t, uint64_t, RS, x >> 32)
CV(shrn3_u16_u8, uint8_t, uint16_t, NR, x >> 3)
CV(rshrn_u16_u8, uint8_t, uint16_t, RS, (x + 128) >> 8)
CV(sqxtn_i32_i16, int16_t, int32_t, NR, x < -32768 ? -32768 : (x > 32767 ? 32767 : x))
CV(sqxtn_i16_i8, int8_t, int16_t, RS, x < -128 ? -128 : (x > 127 ? 127 : x))
CV(uqxtn_u32_u16, uint16_t, uint32_t, RS, x > 65535 ? 65535 : x)
CV(uqxtn_u16_u8, uint8_t, uint16_t, NR, x > 255 ? 255 : x)
CV(sqxtun_i16_u8, uint8_t, int16_t, NR, x < 0 ? 0 : (x > 255 ? 255 : x))
CV(sqxtun_i32_u16, uint16_t, int32_t, RS, x < 0 ? 0 : (x > 65535 ? 65535 : x))
CV(sqxtn_i64_i32, int32_t, int64_t, NR, x < INT32_MIN ? INT32_MIN : (x > INT32_MAX ? INT32_MAX : x))
CV(sqshrn_i32_i16, int16_t, int32_t, RS, (x >> 4) < -32768 ? -32768 : ((x >> 4) > 32767 ? 32767 : (x >> 4)))
CV2(addhn_u16_u8, uint8_t, uint16_t, NR, (uint16_t)(x + y) >> 8)
CV2(narrow_avg_i32_i16, int16_t, int32_t, RS, (x + y) >> 1)
