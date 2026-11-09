/* Janus NEON harvest corpus: memory idioms (prefix nm_).
 * Interleaved structs (LD2/LD3/LD4/ST2/ST3/ST4), strided gathers, reverse
 * copies, byte swaps, scans, fills/copies, broadcasts, permutes, transposes. */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))

struct pair8 { uint8_t a, b; };
struct pair16 { int16_t a, b; };
struct pair32 { uint32_t a, b; };
struct rgb { uint8_t r, g, b; };
struct rgba { uint8_t r, g, b, a; };
struct v3f { float x, y, z; };
struct v4i16 { int16_t x, y, z, w; };
struct cplxf { float re, im; };
struct cplxd { double re, im; };

/* ---- 2-field structs ---- */
NI void nm_ld2_sum_u8(uint8_t *restrict d, const struct pair8 *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint8_t)(s[i].a + s[i].b);
}
NI void nm_ld2_diff_i16(int16_t *d, const struct pair16 *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (int16_t)(s[i].a - s[i].b);
}
NI void nm_st2_merge_u32(struct pair32 *restrict d, const uint32_t *restrict a,
                         const uint32_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) { d[i].a = a[i]; d[i].b = b[i]; }
}
NI void nm_ld2st2_swap_u8(struct pair8 *d, const struct pair8 *s, size_t n) {
  for (size_t i = 0; i < n; i++) { uint8_t t = s[i].a; d[i].a = s[i].b; d[i].b = t; }
}
NI void nm_split2_i16(int16_t *restrict lo, int16_t *restrict hi,
                      const int16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) { lo[i] = s[2 * i]; hi[i] = s[2 * i + 1]; }
}
NI void nm_interleave2_u8(uint8_t *restrict d, const uint8_t *restrict a,
                          const uint8_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) { d[2 * i] = a[i]; d[2 * i + 1] = b[i]; }
}

/* ---- 3-field structs / RGB ---- */
NI void nm_rgb_to_gray(uint8_t *restrict d, const struct rgb *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++)
    d[i] = (uint8_t)((s[i].r * 77 + s[i].g * 150 + s[i].b * 29) >> 8);
}
NI void nm_rgb_swap_rb(struct rgb *d, const struct rgb *s, size_t n) {
  for (size_t i = 0; i < n; i++) { d[i].r = s[i].b; d[i].g = s[i].g; d[i].b = s[i].r; }
}
NI void nm_rgb_planar(uint8_t *restrict r, uint8_t *restrict g, uint8_t *restrict b,
                      const struct rgb *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) { r[i] = s[i].r; g[i] = s[i].g; b[i] = s[i].b; }
}
NI void nm_planar_rgb(struct rgb *restrict d, const uint8_t *restrict r,
                      const uint8_t *restrict g, const uint8_t *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) { d[i].r = r[i]; d[i].g = g[i]; d[i].b = b[i]; }
}
NI void nm_v3f_scale(struct v3f *d, const struct v3f *s, float k, size_t n) {
  for (size_t i = 0; i < n; i++) { d[i].x = s[i].x * k; d[i].y = s[i].y * k; d[i].z = s[i].z * 2.0f; }
}
NI void nm_v3f_dot(float *restrict d, const struct v3f *restrict a,
                   const struct v3f *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = a[i].x * b[i].x + a[i].y * b[i].y + a[i].z * b[i].z;
}

/* ---- 4-field structs / RGBA ---- */
NI void nm_rgba_premul(struct rgba *restrict d, const struct rgba *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) {
    unsigned a = s[i].a;
    d[i].r = (uint8_t)((s[i].r * a) >> 8);
    d[i].g = (uint8_t)((s[i].g * a) >> 8);
    d[i].b = (uint8_t)((s[i].b * a) >> 8);
    d[i].a = (uint8_t)a;
  }
}
NI void nm_rgba_to_bgra(struct rgba *d, const struct rgba *s, size_t n) {
  for (size_t i = 0; i < n; i++) {
    struct rgba p = s[i];
    d[i].r = p.b; d[i].g = p.g; d[i].b = p.r; d[i].a = p.a;
  }
}
NI void nm_rgba_alpha(uint8_t *restrict d, const struct rgba *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i].a;
}
NI void nm_rgba_blend(struct rgba *restrict d, const struct rgba *restrict a,
                      const struct rgba *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    d[i].r = (uint8_t)((a[i].r + b[i].r + 1) >> 1);
    d[i].g = (uint8_t)((a[i].g + b[i].g + 1) >> 1);
    d[i].b = (uint8_t)((a[i].b + b[i].b + 1) >> 1);
    d[i].a = 255;
  }
}
NI void nm_v4i16_add(struct v4i16 *d, const struct v4i16 *a, const struct v4i16 *b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    d[i].x = (int16_t)(a[i].x + b[i].x); d[i].y = (int16_t)(a[i].y - b[i].y);
    d[i].z = (int16_t)(a[i].z * b[i].z); d[i].w = (int16_t)(a[i].w ^ b[i].w);
  }
}

/* ---- complex numbers ---- */
NI void nm_cmul_f32(struct cplxf *restrict d, const struct cplxf *restrict a,
                    const struct cplxf *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    float ar = a[i].re, ai = a[i].im, br = b[i].re, bi = b[i].im;
    d[i].re = ar * br - ai * bi;
    d[i].im = ar * bi + ai * br;
  }
}
NI void nm_cmul_f64(struct cplxd *d, const struct cplxd *a, const struct cplxd *b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    double ar = a[i].re, ai = a[i].im, br = b[i].re, bi = b[i].im;
    d[i].re = ar * br - ai * bi;
    d[i].im = ar * bi + ai * br;
  }
}
NI void nm_cabs2_f32(float *restrict d, const struct cplxf *restrict a, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = a[i].re * a[i].re + a[i].im * a[i].im;
}
NI void nm_conj_f64(struct cplxd *restrict d, const struct cplxd *restrict a, size_t n) {
  for (size_t i = 0; i < n; i++) { d[i].re = a[i].re; d[i].im = -a[i].im; }
}

/* ---- strided gathers ---- */
NI void nm_stride2_u32(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[2 * i];
}
NI void nm_stride3_i16(int16_t *d, const int16_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[3 * i + 1];
}
NI void nm_stride4_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[4 * i + 3];
}
NI void nm_stride4_f32(float *d, const float *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[4 * i] + s[4 * i + 2];
}
NI void nm_scatter2_f64(double *restrict d, const double *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[2 * i + 1] = s[i] * 2.0;
}

/* ---- reverse copies ---- */
NI void nm_rev_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[n - 1 - i];
}
NI void nm_rev_u16(uint16_t *d, const uint16_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[n - 1 - i];
}
NI void nm_rev_u32(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[n - 1 - i];
}
NI void nm_rev_f64(double *d, const double *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[n - 1 - i];
}
NI void nm_rev_inplace_i32(int32_t *a, size_t n) {
  for (size_t i = 0; i < n / 2; i++) { int32_t t = a[i]; a[i] = a[n - 1 - i]; a[n - 1 - i] = t; }
}

/* ---- byte swaps ---- */
NI void nm_bswap16(uint16_t *restrict d, const uint16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = __builtin_bswap16(s[i]);
}
NI void nm_bswap32(uint32_t *d, const uint32_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = __builtin_bswap32(s[i]);
}
NI void nm_bswap64(uint64_t *restrict d, const uint64_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = __builtin_bswap64(s[i]);
}
NI void nm_bswap16_shift(uint16_t *d, const uint16_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint16_t)((s[i] << 8) | (s[i] >> 8));
}
NI void nm_hswap32(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (s[i] << 16) | (s[i] >> 16);
}

/* ---- scans (early exit) ---- */
NI size_t nm_memchr_like(const uint8_t *s, uint8_t c, size_t n) {
  for (size_t i = 0; i < n; i++)
    if (s[i] == c) return i;
  return n;
}
NI size_t nm_strlen_like(const char *s) {
  size_t i = 0;
  while (s[i]) i++;
  return i;
}
NI size_t nm_find_u32(const uint32_t *s, uint32_t v, size_t n) {
  for (size_t i = 0; i < n; i++)
    if (s[i] == v) return i;
  return n;
}
NI size_t nm_mismatch_u8(const uint8_t *a, const uint8_t *b, size_t n) {
  for (size_t i = 0; i < n; i++)
    if (a[i] != b[i]) return i;
  return n;
}
NI int nm_find_gt_i16(const int16_t *s, int16_t lim, int n) {
  for (int i = 0; i < n; i++)
    if (s[i] > lim) return i;
  return -1;
}

/* ---- fills / copies ---- */
NI void nm_fill_u32(uint32_t *d, uint32_t v, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = v;
}
NI void nm_fill_pattern_u16(uint16_t *restrict d, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = 0x1234;
}
NI void nm_fill_f64(double *d, double v, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = v;
}
NI void nm_fill_alt_u8(uint8_t *restrict d, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (i & 1) ? 0xaa : 0x55;
}
NI void nm_copy_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i];
}
NI void nm_copy_overlap_i32(int32_t *d, const int32_t *s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i] + 0;
}
NI void nm_copy_and_add_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint8_t)(s[i] + 1);
}
NI void nm_bcast_mem_i32(int32_t *restrict d, const int32_t *restrict s,
                         const int32_t *restrict p, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i] + *p;
}
NI void nm_bcast_mem_f64(double *d, const double *s, const double *p, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i] * p[0];
}
NI void nm_window_sum_i32(int32_t *restrict d, const int32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i] + s[i + 1] + s[i + 2];
}
NI void nm_diff_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint8_t)(s[i + 1] - s[i]);
}

/* ---- small-table lookups ---- */
NI void nm_lut16_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  static const uint8_t hex[16] = {'0', '1', '2', '3', '4', '5', '6', '7',
                                  '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};
  for (size_t i = 0; i < n; i++) d[i] = hex[s[i] & 15];
}
NI void nm_lut_tab_u8(uint8_t *d, const uint8_t *s, const uint8_t *tab, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = tab[s[i] & 7];
}
NI void nm_hexenc(char *restrict d, const uint8_t *restrict s, size_t n) {
  static const char hex[17] = "0123456789abcdef";
  for (size_t i = 0; i < n; i++) { d[2 * i] = hex[s[i] >> 4]; d[2 * i + 1] = hex[s[i] & 15]; }
}

/* ---- fixed permutes / transposes ---- */
NI void nm_perm4_u32(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i += 4) {
    d[i] = s[i + 2]; d[i + 1] = s[i + 0]; d[i + 2] = s[i + 3]; d[i + 3] = s[i + 1];
  }
}
NI void nm_perm8_u8(uint8_t *restrict d, const uint8_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i += 8) {
    d[i + 0] = s[i + 3]; d[i + 1] = s[i + 6]; d[i + 2] = s[i + 1]; d[i + 3] = s[i + 0];
    d[i + 4] = s[i + 7]; d[i + 5] = s[i + 2]; d[i + 6] = s[i + 5]; d[i + 7] = s[i + 4];
  }
}
NI void nm_rot_u32x4(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i += 4) {
    d[i] = s[i + 1]; d[i + 1] = s[i + 2]; d[i + 2] = s[i + 3]; d[i + 3] = s[i];
  }
}
NI void nm_transpose4x4_i32(int32_t *restrict d, const int32_t *restrict s) {
  for (int r = 0; r < 4; r++)
    for (int c = 0; c < 4; c++) d[c * 4 + r] = s[r * 4 + c];
}
NI void nm_transpose4x4_f32(float *d, const float *s) {
  float t[16];
  for (int r = 0; r < 4; r++)
    for (int c = 0; c < 4; c++) t[c * 4 + r] = s[r * 4 + c];
  for (int k = 0; k < 16; k++) d[k] = t[k];
}
NI void nm_transpose8x8_u8(uint8_t *restrict d, const uint8_t *restrict s) {
  for (int r = 0; r < 8; r++)
    for (int c = 0; c < 8; c++) d[c * 8 + r] = s[r * 8 + c];
}
NI void nm_transpose2x2_f64(double *restrict d, const double *restrict s, size_t n) {
  for (size_t i = 0; i < n; i += 4) {
    d[i] = s[i]; d[i + 1] = s[i + 2]; d[i + 2] = s[i + 1]; d[i + 3] = s[i + 3];
  }
}
NI void nm_matmul4_f32(float *restrict c, const float *restrict a, const float *restrict b) {
  for (int i = 0; i < 4; i++)
    for (int j = 0; j < 4; j++) {
      float s = 0.0f;
      for (int k = 0; k < 4; k++) s += a[i * 4 + k] * b[k * 4 + j];
      c[i * 4 + j] = s;
    }
}
NI void nm_matvec4_f32(float *restrict y, const float *restrict m, const float *restrict x,
                       size_t n) {
  for (size_t v = 0; v < n; v++)
    for (int j = 0; j < 4; j++)
      y[4 * v + j] = m[j] * x[4 * v] + m[4 + j] * x[4 * v + 1] + m[8 + j] * x[4 * v + 2] +
                     m[12 + j] * x[4 * v + 3];
}
NI void nm_zip_lo_hi_u16(uint16_t *restrict d, const uint16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) { d[2 * i] = s[i]; d[2 * i + 1] = s[n + i]; }
}

/* ---- index gathers, odd strides, 2x2 element transposes ---- */
NI void nm_gather_idx_f32(float *restrict d, const float *restrict s,
                          const uint32_t *restrict idx, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[idx[i]];
}
NI void nm_gather_idx_i64(int64_t *d, const int64_t *s, const int32_t *idx, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[idx[i]] + 1;
}
NI void nm_stride5_u32(uint32_t *restrict d, const uint32_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[5 * i] + s[5 * i + 1];
}
NI void nm_trn_u32(uint32_t *restrict d, uint32_t *restrict e, const uint32_t *restrict a,
                   const uint32_t *restrict b, size_t n) {
  for (size_t i = 0; i + 2 <= n; i += 2) {
    d[i] = a[i]; d[i + 1] = b[i];
    e[i] = a[i + 1]; e[i + 1] = b[i + 1];
  }
}
NI void nm_trn_u16(uint16_t *restrict d, const uint16_t *restrict a,
                   const uint16_t *restrict b, size_t n) {
  for (size_t i = 0; i + 2 <= n; i += 2) { d[i] = a[i]; d[i + 1] = b[i]; }
}
NI void nm_trn2_u8(uint8_t *restrict d, const uint8_t *restrict a,
                   const uint8_t *restrict b, size_t n) {
  for (size_t i = 0; i + 2 <= n; i += 2) { d[i] = a[i + 1]; d[i + 1] = b[i + 1]; }
}
NI void nm_pack2_f32(float *restrict d, const float *restrict p, const float *restrict q) {
  d[0] = p[0] * 2.0f; d[1] = q[0] * 2.0f; d[2] = p[1] * 3.0f; d[3] = q[1] * 3.0f;
}
NI void nm_insert_lane_i32(int32_t *restrict d, const int32_t *restrict s, int32_t v, size_t n) {
  for (size_t i = 0; i < n; i += 4) {
    d[i] = s[i] + v; d[i + 1] = s[i + 1] + 1; d[i + 2] = s[i + 2] + v; d[i + 3] = s[i + 3] + 2;
  }
}
NI void nm_stride7_u16(uint16_t *restrict d, const uint16_t *restrict s, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = (uint16_t)(s[7 * i] + 3);
}
NI void nm_stride_var_f32(float *d, const float *s, size_t k, size_t n) {
  for (size_t i = 0; i < n; i++) d[i] = s[i * k] * 2.0f;
}
