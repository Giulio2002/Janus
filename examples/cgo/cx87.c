/* The amd64 C-specific encodings of WP-J: x87 long double arithmetic and a CET jump table.
 * See docs/FFI.md and examples/proofs-cgo/amd64/{CLdMul,GoLdMul,CSwitch}.lean. */
#include "cx87.h"

/* a * b in long double: both arguments arrive on the stack (System V class X87, 16 bytes
 * each), the result in ST(0). gcc -O2: fldt; fldt; fmulp; ret. Not inlined, so that the
 * long doubles cross the C calling convention. */
__attribute__((noinline)) long double ld_mul(long double a, long double b) { return a * b; }

/* *r = *a * *b, through ld_mul (fstpt stores the 10 bytes of the result). */
void c_ldmul(const ld16 *a, const ld16 *b, ld16 *r) {
	*(long double *)r = ld_mul(*(const long double *)a, *(const long double *)b);
}

/* A dense switch: gcc -O2 compiles it to a bounds check and a jump through a table of 32-bit
 * offsets in .rodata, dispatched with `notrack jmp *%rax` (3E FF E0) under -fcf-protection. */
uint64_t c_switch(uint64_t k, uint64_t x) {
	switch (k) {
	case 0: return x + 1;
	case 1: return x * 3;
	case 2: return x ^ 0x55;
	case 3: return x - 7;
	case 4: return x << 2;
	case 5: return x >> 1;
	case 6: return ~x;
	case 7: return x * x;
	default: return k + x;
	}
}
