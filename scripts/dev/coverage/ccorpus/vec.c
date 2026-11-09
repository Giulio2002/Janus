/* Loops gcc/clang auto-vectorise at -O2 (gcc >= 12, clang) and -O3. */
#include <stdint.h>
#include <stddef.h>

uint64_t v_sum64(const uint64_t *p, size_t n) { uint64_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
uint32_t v_sum32(const uint32_t *p, size_t n) { uint32_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
uint64_t v_sum8(const uint8_t *p, size_t n) { uint64_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
void v_add(uint32_t *restrict z, const uint32_t *x, const uint32_t *y, size_t n) { for (size_t i = 0; i < n; i++) z[i] = x[i] + y[i]; }
void v_xor(uint8_t *restrict z, const uint8_t *x, const uint8_t *y, size_t n) { for (size_t i = 0; i < n; i++) z[i] = x[i] ^ y[i]; }
void v_saxpy(float *restrict y, const float *x, float a, size_t n) { for (size_t i = 0; i < n; i++) y[i] += a * x[i]; }
double v_dot(const double *x, const double *y, size_t n) { double s = 0; for (size_t i = 0; i < n; i++) s += x[i] * y[i]; return s; }
int64_t v_max(const int64_t *p, size_t n) { int64_t m = INT64_MIN; for (size_t i = 0; i < n; i++) m = p[i] > m ? p[i] : m; return m; }
size_t v_count(const uint8_t *p, size_t n, uint8_t c) { size_t k = 0; for (size_t i = 0; i < n; i++) k += p[i] == c; return k; }
void v_copy(uint64_t *restrict d, const uint64_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
void v_zero(uint32_t *d, size_t n) { for (size_t i = 0; i < n; i++) d[i] = 0; }
void v_reverse(uint32_t *restrict d, const uint32_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = s[n - 1 - i]; }
void v_widen(uint32_t *restrict d, const uint16_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (uint32_t)s[i] * 3u; }
void v_narrow(uint8_t *restrict d, const uint32_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (uint8_t)(s[i] >> 4); }
void v_mul64(uint64_t *restrict z, const uint64_t *x, const uint64_t *y, size_t n) { for (size_t i = 0; i < n; i++) z[i] = x[i] * y[i]; }
void v_shift(uint32_t *restrict z, const uint32_t *x, size_t n) { for (size_t i = 0; i < n; i++) z[i] = (x[i] << 7) | (x[i] >> 25); }
void v_cond(int32_t *restrict z, const int32_t *x, size_t n) { for (size_t i = 0; i < n; i++) z[i] = x[i] < 0 ? -x[i] : x[i] * 2; }
void v_tolower(char *restrict d, const char *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (s[i] >= 'A' && s[i] <= 'Z') ? s[i] + 32 : s[i]; }
void v_i2f(double *restrict d, const int32_t *s, size_t n) { for (size_t i = 0; i < n; i++) d[i] = (double)s[i]; }
size_t v_strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }
void v_matmul4(float *restrict c, const float *a, const float *b) {
	for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { float s = 0; for (int k = 0; k < 4; k++) s += a[4*i+k] * b[4*k+j]; c[4*i+j] = s; }
}
