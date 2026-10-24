/* Model-coverage corpus: C functions written to make gcc emit the integer instructions that
 * Go code does not (conditional selects, bitfield moves, multiply-add, 64-bit immediates,
 * frame-pointer prologues with LEAVE, ...). They are linked into the example binary but not
 * called from Go; `janus blockers` and the differential oracles run over them. See
 * docs/FFI.md ("Model coverage"). */
#include <stdint.h>

uint64_t cc_max(uint64_t a, uint64_t b) { return a > b ? a : b; }
int64_t cc_clamp(int64_t x, int64_t lo, int64_t hi) { return x < lo ? lo : (x > hi ? hi : x); }
uint64_t cc_select(uint64_t c, uint64_t a, uint64_t b) { return c ? a + 1 : -b; }
uint64_t cc_selinv(uint64_t c, uint64_t a, uint64_t b) { return c == 7 ? ~a : b; }
int cc_cmp(int64_t a, int64_t b) { return (a > b) - (a < b); }
int64_t cc_mask(int64_t a, int64_t b) { return a < b ? -1 : 0; }
uint64_t cc_bitfield(uint64_t x) { return ((x & 0xff) << 3) | ((x >> 7) & 0x3f); }
int64_t cc_sbitfield(int64_t x) { return (int64_t)(int8_t)(x >> 5) << 4; }
uint64_t cc_madd(uint64_t a, uint64_t b, uint64_t c) { return a * b + c; }
uint64_t cc_msub(uint64_t a, uint64_t b, uint64_t c) { return c - a * b; }
uint64_t cc_mulhi(uint64_t a, uint64_t b) { return (uint64_t)(((unsigned __int128)a * b) >> 64); }
int64_t cc_smulhi(int64_t a, int64_t b) { return (int64_t)(((__int128)a * b) >> 64); }
uint64_t cc_const(void) { return 0x123456789abcdef0ull; }
uint64_t cc_lea(uint64_t a, uint64_t b) { return a * 9 + b * 4 + 12345; }
uint32_t cc_w32(uint32_t a, uint32_t b) { return (a << (b & 31)) ^ (a >> 3) ^ (b * 5u); }
int64_t cc_sext(int32_t a, int16_t b, int8_t c) { return (int64_t)a + b + c; }
uint64_t cc_zext(uint32_t a, uint16_t b, uint8_t c) { return (uint64_t)a * 3 + b + c; }
uint64_t cc_rot(uint64_t a, unsigned n) { return (a >> (n & 63)) | (a << ((64 - n) & 63)); }
uint64_t cc_bswap(uint64_t a) { return __builtin_bswap64(a); }
uint64_t cc_div(uint64_t a, uint64_t b) { return b ? a / b + a % b : 0; }
int64_t cc_sdiv(int64_t a, int64_t b) { return b ? a / b : 0; }
int64_t cc_abs(int64_t a) { return a < 0 ? -a : a; }
uint64_t cc_clz(uint64_t a) { return a ? (uint64_t)__builtin_clzll(a) : 64; }
uint64_t cc_shifts(uint64_t a, uint64_t s) { return (a << (s & 63)) + ((int64_t)a >> (s & 63)) + (a >> (s & 63)); }
uint64_t cc_bool(uint64_t a, uint64_t b) { return (a == b) + 2 * (a < b) + 4 * ((int64_t)a < (int64_t)b); }

/* A variable-length array forces a frame pointer, so the epilogue restores the stack with
 * LEAVE (amd64) or MOV SP, X29 (arm64). */
uint64_t cc_vla(uint64_t n) {
	uint64_t buf[n + 1];
	for (uint64_t i = 0; i <= n; i++)
		buf[i] = i * i;
	uint64_t s = 0;
	for (uint64_t i = 0; i <= n; i++)
		s += buf[i];
	return s;
}

/* Calls between C functions: callee-saved registers are pushed and popped. */
uint64_t cc_calls(uint64_t a, uint64_t b, uint64_t c) {
	uint64_t x = cc_madd(a, b, c);
	uint64_t y = cc_max(x, c);
	return cc_lea(x, y) ^ a ^ b ^ c;
}

/* Byte and halfword memory accesses, with pre-indexed pointer arithmetic. */
uint64_t cc_bytes(const uint8_t *p, const uint16_t *q, uint32_t *r, uint64_t n) {
	uint64_t s = 0;
	for (uint64_t i = 0; i < n; i++) {
		s += p[i] + q[i];
		r[i] = (uint32_t)s;
	}
	return s;
}
