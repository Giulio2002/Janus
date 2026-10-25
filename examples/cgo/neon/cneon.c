#include "cneon.h"

/* Return the number of the n bytes at p that equal c. At cgo's default -O2, gcc vectorises the
   loop (CMEQ, ZIP1/ZIP2, UADDW/UADDW2, ADDP on arm64; scripts/coverage/ccorpus/vec.c:v_count). */
uint64_t c_count(const uint8_t *p, uint64_t n, uint8_t c) {
	uint64_t k = 0;
	for (uint64_t i = 0; i < n; i++)
		k += p[i] == c;
	return k;
}
