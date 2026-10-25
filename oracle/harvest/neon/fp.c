/* Janus NEON harvest corpus: element-wise floating-point loops (prefix nf_).
 * Plain C11 + GNU builtins, no intrinsics.  Only operations that are exact
 * without -ffast-math are used, so the vectoriser can work at plain -O2/-O3
 * (fma contraction is the compiler default for GNU C). */
#include <stddef.h>
#include <stdint.h>

#define NI __attribute__((noinline))
#define RS restrict
#define NR

#define BIN(nm, T, R, expr)                                                   \
  NI void nf_##nm(T *R a, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i], y = c[i];                                                   \
      a[i] = (expr);                                                          \
    }                                                                         \
  }
#define ACC(nm, T, R, expr)                                                   \
  NI void nf_##nm(T *R a, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T z = a[i], x = b[i], y = c[i];                                         \
      a[i] = (expr);                                                          \
    }                                                                         \
  }
#define UN(nm, T, R, expr)                                                    \
  NI void nf_##nm(T *R a, const T *R b, size_t n) {                           \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i];                                                             \
      a[i] = (expr);                                                          \
    }                                                                         \
  }
/* compare two FP arrays into an integer mask array */
#define CMP(nm, T, M, R, expr)                                                \
  NI void nf_##nm(M *R m, const T *R b, const T *R c, size_t n) {             \
    for (size_t i = 0; i < n; i++) {                                          \
      T x = b[i], y = c[i];                                                   \
      m[i] = (expr) ? (M)-1 : 0;                                              \
    }                                                                         \
  }

BIN(fadd_f32, float, RS, x + y)
BIN(fadd_f64, double, NR, x + y)
BIN(fsub_f32, float, NR, x - y)
BIN(fsub_f64, double, RS, x - y)
BIN(fmul_f32, float, RS, x * y)
BIN(fmul_f64, double, NR, x * y)
BIN(fdiv_f32, float, NR, x / y)
BIN(fdiv_f64, double, RS, x / y)
ACC(fmla_f32, float, RS, z + x * y)
ACC(fmla_f64, double, NR, z + x * y)
ACC(fmls_f32, float, NR, z - x * y)
ACC(fmls_f64, double, RS, z - x * y)
ACC(fma_builtin_f32, float, RS, __builtin_fmaf(x, y, z))
ACC(fma_builtin_f64, double, NR, __builtin_fma(x, y, z))
ACC(fnmla_f32, float, NR, -(z + x * y))
UN(fneg_f32, float, RS, -x)
UN(fneg_f64, double, NR, -x)
UN(fabs_f32, float, NR, __builtin_fabsf(x))
UN(fabs_f64, double, RS, __builtin_fabs(x))
BIN(fabd_f32, float, RS, __builtin_fabsf(x - y))
BIN(fabd_f64, double, NR, __builtin_fabs(x - y))
UN(fsqrt_f32, float, RS, x >= 0.0f ? __builtin_sqrtf(x) : 0.0f)
UN(fsqrt_f64, double, NR, x >= 0.0 ? __builtin_sqrt(x) : 0.0)
UN(frecip_f32, float, NR, 1.0f / x)
UN(frecip_f64, double, RS, 1.0 / x)
BIN(fminnm_f32, float, RS, __builtin_fminf(x, y))
BIN(fmaxnm_f32, float, NR, __builtin_fmaxf(x, y))
BIN(fminnm_f64, double, NR, __builtin_fmin(x, y))
BIN(fmaxnm_f64, double, RS, __builtin_fmax(x, y))
BIN(fmin_tern_f32, float, RS, x < y ? x : y)
BIN(fmax_tern_f64, double, NR, x > y ? x : y)
BIN(copysign_f32, float, NR, __builtin_copysignf(x, y))
BIN(copysign_f64, double, RS, __builtin_copysign(x, y))
UN(fclamp_f32, float, RS, __builtin_fminf(__builtin_fmaxf(x, -1.0f), 1.0f))
UN(fclamp_tern_f64, double, NR, x < 0.0 ? 0.0 : (x > 255.0 ? 255.0 : x))
CMP(fcmgt_f32, float, int32_t, RS, x > y)
CMP(fcmge_f32, float, int32_t, NR, x >= y)
CMP(fcmeq_f32, float, int32_t, RS, x == y)
CMP(fcmgt_f64, double, int64_t, NR, x > y)
CMP(fcmeq_f64, double, int64_t, RS, x == y)
CMP(fcmlt0_f32, float, int32_t, NR, x < 0.0f && y == y)
CMP(facgt_f32, float, int32_t, RS, __builtin_fabsf(x) > __builtin_fabsf(y))
CMP(fcmuo_f32, float, int32_t, NR, x != x || y != y)

NI void nf_sel_gt_f32(float *restrict a, const float *restrict b,
                      const float *restrict c, const float *restrict d,
                      const float *restrict e, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] > c[i] ? d[i] : e[i];
}
NI void nf_sel_lt_f64(double *a, const double *b, const double *c, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] < c[i] ? 0.0 : b[i] - c[i];
}
NI void nf_relu_f32(float *a, const float *b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] > 0.0f ? b[i] : 0.0f;
}
NI void nf_scale_f32(float *restrict a, const float *restrict b, float s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] * s;
}
NI void nf_scale_f64(double *a, const double *b, double s, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] * s;
}
NI void nf_saxpy(float *restrict y, const float *restrict x, float a, size_t n) {
  for (size_t i = 0; i < n; i++) y[i] += a * x[i];
}
NI void nf_daxpy(double *y, const double *x, double a, size_t n) {
  for (size_t i = 0; i < n; i++) y[i] += a * x[i];
}
NI void nf_axpy_mem_f32(float *restrict y, const float *restrict x,
                        const float *restrict ap, size_t n) {
  for (size_t i = 0; i < n; i++) y[i] = y[i] + ap[0] * x[i];
}
NI void nf_lerp_f32(float *a, const float *b, const float *c, float t, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] + t * (c[i] - b[i]);
}
NI void nf_horner_f32(float *restrict a, const float *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    float x = b[i];
    a[i] = ((0.5f * x + 0.25f) * x - 0.125f) * x + 1.0f;
  }
}
NI void nf_horner_f64(double *a, const double *b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    double x = b[i];
    a[i] = ((1.5 * x - 2.0) * x + 3.0) * x - 4.0;
  }
}
NI void nf_add_const_f32(float *restrict a, const float *restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] + 2.0f;
}
NI void nf_half_f64(double *a, const double *b, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = b[i] * 0.5;
}
NI void nf_mag2_f32(float *restrict a, const float *restrict x,
                    const float *restrict y, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = __builtin_sqrtf(x[i] * x[i] + y[i] * y[i]);
}
NI void nf_norm_div_f32(float *a, const float *b, const float *c, size_t n) {
  for (size_t i = 0; i < n; i++) a[i] = (b[i] - c[i]) / (b[i] + c[i] + 1.0f);
}
