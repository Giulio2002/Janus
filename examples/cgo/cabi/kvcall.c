#include "kabi.h"

/* A variadic call with eight variadic arguments (its own translation unit, so the call is not
   inlined): on AAPCS64 `n` and seven of them go in X0-X7 and the last on the stack; on System V
   `n` and five go in registers, three on the stack, and AL = 0 (no vector registers). */
int64_t k_vsum8(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g,
                int64_t h) {
	return k_vsum(8, a, b, c, d, e, f, g, h);
}
