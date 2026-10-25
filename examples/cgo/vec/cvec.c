#include "cvec.h"

/* Return the sum, modulo 2^32, of the n 32-bit integers at p. clang -O2 vectorises the loop:
   8 elements per iteration in two PADDD accumulators, a PSHUFD/PADDD reduction, then a scalar
   loop for the remaining n mod 8 elements. */
int32_t c_sum32(const int32_t *p, uint64_t n) {
	int32_t s = 0;
	for (uint64_t i = 0; i < n; i++)
		s += p[i];
	return s;
}
