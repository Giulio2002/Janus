/* x87 harvest corpus for scripts/oracle-amd64.sh x87: long double code as gcc and clang emit it
 * (-O0/-O2/-O3, with and without -march=x86-64-v3: FISTTP), together with the C corpus's abi.c.
 * Only the instructions are harvested; nothing here is run. */
#include <math.h>
#include <stdint.h>
long double ld_mul(long double a, long double b) { return a * b; }
long double ld_add(long double a, long double b) { return a + b; }
long double ld_sub(long double a, long double b) { return a - b; }
long double ld_div(long double a, long double b) { return a / b; }
long double ld_rdiv(long double a, long double b) { return b / a; }
long double ld_neg(long double a) { return -a; }
long double ld_abs(long double a) { return __builtin_fabsl(a); }
long double ld_sqrt(long double a) { return __builtin_sqrtl(a); }
int ld_lt(long double a, long double b) { return a < b; }
int ld_le(long double a, long double b) { return a <= b; }
int ld_eq(long double a, long double b) { return a == b; }
int ld_ne(long double a, long double b) { return a != b; }
int ld_un(long double a, long double b) { return __builtin_isunordered(a, b); }
int ld_signbit(long double a) { return __builtin_signbit(a); }
int ld_isinf(long double a) { return __builtin_isinf(a); }
int ld_class(long double a) { return __builtin_fpclassify(0, 1, 2, 3, 4, a); }
long double ld_fromi(int x) { return x; }
long double ld_froms(short x) { return x; }
long double ld_froml(long x) { return x; }
long double ld_fromu(unsigned long x) { return x; }
long ld_toi(long double x) { return x; }
int ld_toi32(long double x) { return x; }
short ld_toi16(long double x) { return x; }
unsigned long ld_tou(long double x) { return x; }
long ld_lrint(long double x) { return __builtin_lrintl(x); }
double ld_tod(long double x) { return x; }
float ld_tof(long double x) { return x; }
long double ld_fromd(double x) { return x; }
long double ld_fromf(float x) { return x; }
void ld_ptr(long double *r, const long double *a, const long double *b) { *r = *a * *b + 1.0L; }
long double ld_poly(long double x) { return ((x * 3.0L + 2.0L) * x - 1.5L) * x + 0.25L; }
long double ld_zero(void) { return 0.0L; }
long double ld_one(void) { return 1.0L; }
long double ld_max(long double a, long double b) { return a > b ? a : b; }
long double ld_min(long double a, long double b) { return a < b ? a : b; }
long double ld_sum(const long double *a, int n) {
	long double s = 0;
	for (int i = 0; i < n; i++) s += a[i];
	return s;
}
long double ld_dot(const long double *a, const long double *b, int n) {
	long double s = 0;
	for (int i = 0; i < n; i++) s += a[i] * b[i];
	return s;
}
long double ld_mixed(long double a, double b, float c, int d) { return a * b - c / d; }
long double ld_iadd(long double a, int i) { return a + i; }
long double ld_imul(long double a, short i) { return a * i; }
long double ld_horner(const long double *c, int n, long double x) {
	long double r = 0;
	for (int i = n - 1; i >= 0; i--) r = r * x + c[i];
	return r;
}
int main(void) { return 0; }
