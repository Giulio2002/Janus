#include <stdint.h>

/* The C ABI examples of Janus (docs/FFI.md, section 5): one function per argument/result
   class of the C calling conventions. */

struct k_pt { double x, y; };            /* AAPCS64 HFA of two doubles; System V: SSE, SSE */
struct k_mix { double s; int64_t n; };     /* AAPCS64: X0, X1; System V: SSE, INTEGER (XMM0, RAX) */
struct k_big { int64_t a, b, c, d; };    /* 32 bytes: returned through X8 / the hidden RDI pointer */

int64_t k_stack10(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g,
                  int64_t h, int32_t i, int64_t j);
double k_fp(double a, float b, double c);
struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n);
struct k_big k_big(int64_t x, int64_t y);
int64_t k_vsum(int n, ...);
int64_t k_vsum8(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g,
                int64_t h);
