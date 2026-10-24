#include <stdarg.h>
#include "kabi.h"

/* Ten arguments: eight in registers on AAPCS64 (X0-X7) and six on System V (RDI RSI RDX RCX R8
   R9); the rest on the stack, each in an 8-byte slot (the 32-bit `i` in the low half of its
   slot). Every argument has its own weight, so a swapped slot changes the result. */
int64_t k_stack10(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g,
                  int64_t h, int32_t i, int64_t j) {
	return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * (int64_t)i + 10 * j;
}

/* Floating-point arguments and result: D0, S1, D2 -> D0 (AAPCS64); XMM0, XMM1, XMM2 -> XMM0
   (System V). */
double k_fp(double a, float b, double c) { return (a - b) * c; }

/* Structs by value. `struct k_pt` is an AAPCS64 homogeneous floating-point aggregate (HFA) of two
   doubles, passed in D0-D1 and D2-D3, and two SSE eightbytes on System V, passed in XMM0-XMM1 and
   XMM2-XMM3; `n` goes in X0 / RDI. The 16-byte result `struct k_mix` is not an HFA on AAPCS64
   (X0 = the bits of `s`, X1 = `n`); on System V its eightbytes are SSE and INTEGER (XMM0, RAX). */
struct k_mix k_pmix(struct k_pt a, struct k_pt b, int64_t n) {
	struct k_mix r = { (a.x + b.x) * (a.y - b.y), n + 1 };
	return r;
}

/* A 32-byte result: written through X8 (AAPCS64) / the hidden first argument RDI, which is also
   returned in RAX (System V, class MEMORY). */
struct k_big k_big(int64_t x, int64_t y) {
	struct k_big r = { x + y, x - y, x * y, x ^ y };
	return r;
}

/* The sum of n 64-bit variadic arguments (va_arg over the register save area, then the
   overflow area). */
int64_t k_vsum(int n, ...) {
	va_list ap;
	va_start(ap, n);
	int64_t s = 0;
	for (int i = 0; i < n; i++)
		s += va_arg(ap, int64_t);
	va_end(ap);
	return s;
}
