/* C ABI features beyond integer register arguments. */
#include <stdint.h>
#include <stdarg.h>
#include <setjmp.h>
#include <string.h>
#include <stdlib.h>
#include <alloca.h>
#include <complex.h>

struct small { int64_t a, b; };          /* returned in two registers */
struct big { int64_t a[6]; };            /* returned through a hidden pointer (X8 / RDI sret) */
struct mixed { double x; int32_t k; };   /* SSE + INTEGER classes */
struct hfa { float a, b, c, d; };        /* AAPCS64 homogeneous float aggregate */

int64_t a_varargs(int n, ...) { va_list ap; va_start(ap, n); int64_t s = 0; for (int i = 0; i < n; i++) s += va_arg(ap, int64_t); va_end(ap); return s; }
double a_varargs_f(int n, ...) { va_list ap; va_start(ap, n); double s = 0; for (int i = 0; i < n; i++) s += va_arg(ap, double); va_end(ap); return s; }
struct small a_small(int64_t x) { struct small r = { x, x * 2 }; return r; }
int64_t a_small_arg(struct small s) { return s.a - s.b; }
struct big a_big(int64_t x) { struct big r; for (int i = 0; i < 6; i++) r.a[i] = x + i; return r; }
int64_t a_big_arg(struct big b) { int64_t s = 0; for (int i = 0; i < 6; i++) s += b.a[i]; return s; }
double a_mixed(struct mixed m) { return m.x * m.k; }
float a_hfa(struct hfa h) { return h.a + h.b + h.c + h.d; }
int64_t a_stackargs(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g, int64_t h, int64_t i, int64_t j) { return a + b * c - d + e * f - g + h * i - j; }
double a_fargs(double a, float b, double c, int64_t k) { return a * b + c - (double)k; }
int64_t a_callback(int64_t (*f)(int64_t, void *), void *ctx, int64_t n) { int64_t s = 0; for (int64_t i = 0; i < n; i++) s += f(i, ctx); return s; }

int64_t a_global = 42;
static int64_t a_static_counter;
const int64_t a_table[4] = { 1, 10, 100, 1000 };
extern int64_t a_extern_global;
int64_t a_globals(int k) { a_static_counter++; return a_global + a_table[k & 3] + a_static_counter + a_extern_global; }
__thread int64_t a_tls;
int64_t a_use_tls(int64_t x) { a_tls += x; return a_tls; }

static jmp_buf a_env;
static void a_thrower(int v) { if (v) longjmp(a_env, v); }
int a_setjmp(int v) { if (setjmp(a_env)) return 1; a_thrower(v); return 0; }
int64_t a_alloca(size_t n) { int64_t *p = alloca(n * sizeof *p + 8); for (size_t i = 0; i < n; i++) p[i] = (int64_t)i; int64_t s = 0; for (size_t i = 0; i < n; i++) s += p[i]; return s; }
int64_t a_libc(const char *s, char *d) { size_t n = strlen(s); memcpy(d, s, n + 1); char *m = malloc(n + 1); if (!m) return -1; memcpy(m, s, n); free(m); return (int64_t)n; }
long double a_ldouble(long double x, long double y) { return x * y + 1.0L; }
double complex a_complex(double complex a, double complex b) { return a * b; }
unsigned __int128 a_u128(unsigned __int128 a, unsigned __int128 b) { return a * b + (a >> 3); }
struct bits { unsigned a : 3, b : 5, c : 12; int d : 7; };
int a_bitfield(struct bits *p) { p->b++; return p->a + p->c + p->d; }
int64_t a_recursive(int64_t n) { return n < 2 ? n : a_recursive(n - 1) + a_recursive(n - 2); }
