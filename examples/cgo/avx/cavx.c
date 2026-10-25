#include "cavx.h"

/* Return the dot product, modulo 2^32, of the n 32-bit words at a and at b. clang -O3
   -march=x86-64-v3 vectorises the loop with AVX2: 32 products per iteration (VPMULLD) into four
   YMM accumulators (VPADDD), a VEXTRACTI128/VPSHUFD/VPADDD reduction; then 4 products per
   iteration on XMM for the remaining n mod 32 words, and a scalar loop for the last n mod 4. */
uint32_t c_dot32(const uint32_t *a, const uint32_t *b, uint64_t n) {
	uint32_t s = 0;
	for (uint64_t i = 0; i < n; i++)
		s += a[i] * b[i];
	return s;
}
