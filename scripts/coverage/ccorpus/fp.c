/* Scalar floating point as C compilers emit it (libm calls stay calls). */
#include <stdint.h>
#include <math.h>

double f_poly(double x) { return ((3.0 * x + 2.0) * x - 7.5) * x + 0.25; }
float f_mix(float a, double b) { return (float)(a * b) + a; }
int64_t f_trunc(double x) { return (int64_t)x; }
uint64_t f_utrunc(double x) { return (uint64_t)x; }
double f_fromu(uint64_t x) { return (double)x; }
int f_cmp(double a, double b) { return (a < b) - (a > b) + 2 * (a != a); }
double f_sqrt(double x) { return sqrt(x); }
double f_fma(double a, double b, double c) { return fma(a, b, c); }
double f_floor(double x) { return floor(x) + ceil(x) + trunc(x) + round(x); }
double f_abs(double x, double y) { return fabs(x) + copysign(y, x); }
double f_minmax(double a, double b) { return fmin(a, b) * fmax(a, b); }
float f_recip(float x) { return 1.0f / x; }
double f_libm(double x) { return sin(x) + exp(x) + log(x); }
