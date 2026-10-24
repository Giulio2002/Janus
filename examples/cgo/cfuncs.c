#include "cfuncs.h"

/* Return a + b modulo 2^64. */
uint64_t c_add(uint64_t a, uint64_t b) { return a + b; }

/* Return the sum, modulo 2^64, of the n words at p. */
uint64_t c_sum(const uint64_t *p, uint64_t n) {
	uint64_t s = 0;
	for (uint64_t i = 0; i < n; i++)
		s += p[i];
	return s;
}

/* Store v at *p. */
void c_store(uint64_t *p, uint64_t v) { *p = v; }
