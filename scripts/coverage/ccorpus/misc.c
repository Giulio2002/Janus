/* Integer idioms: hashing, CRC, bit manipulation, string loops, memory builtins. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>

static uint32_t crc_table[256];
void m_crc_init(void) { for (uint32_t i = 0; i < 256; i++) { uint32_t c = i; for (int k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320u ^ (c >> 1) : c >> 1; crc_table[i] = c; } }
uint32_t m_crc(const uint8_t *p, size_t n) { uint32_t c = ~0u; for (size_t i = 0; i < n; i++) c = crc_table[(c ^ p[i]) & 0xff] ^ (c >> 8); return ~c; }
uint64_t m_fnv(const uint8_t *p, size_t n) { uint64_t h = 1469598103934665603ull; for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ull; } return h; }
int m_popcount(uint64_t x) { return __builtin_popcountll(x); }
int m_ctz(uint64_t x) { return x ? __builtin_ctzll(x) : 64; }
uint64_t m_pdep_like(uint64_t x, uint64_t m) { uint64_t r = 0; for (uint64_t b = 1; m; b += b) { if (x & b) r |= m & -m; m &= m - 1; } return r; }
uint32_t m_sha_round(uint32_t a, uint32_t b, uint32_t c, uint32_t d, uint32_t e, uint32_t w) {
	uint32_t s1 = ((e >> 6) | (e << 26)) ^ ((e >> 11) | (e << 21)) ^ ((e >> 25) | (e << 7));
	uint32_t ch = (e & a) ^ (~e & b);
	return d + s1 + ch + w + c;
}
int m_strcmp(const char *a, const char *b) { while (*a && *a == *b) { a++; b++; } return (unsigned char)*a - (unsigned char)*b; }
void m_memset(void *p, size_t n) { memset(p, 0, n); }
void m_memcpy(void *d, const void *s, size_t n) { memcpy(d, s, n); }
struct blob { int64_t x[16]; };
void m_blobcopy(struct blob *d, const struct blob *s) { *d = *s; }
int m_memcmp(const void *a, const void *b, size_t n) { return memcmp(a, b, n); }
uint64_t m_mulhi(uint64_t a, uint64_t b) { return (uint64_t)(((unsigned __int128)a * b) >> 64); }
int64_t m_divconst(int64_t x) { return x / 7 + x % 13; }
uint64_t m_bswap(uint64_t x) { return __builtin_bswap64(x) ^ __builtin_bswap32((uint32_t)x); }
int m_atomic_inc(int *p) { return __atomic_add_fetch(p, 1, __ATOMIC_SEQ_CST); }
int m_cas(int *p, int o, int n) { return __atomic_compare_exchange_n(p, &o, n, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); }
