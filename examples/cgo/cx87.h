#include <stdint.h>

/* A C long double as cgo can pass it: 16 bytes, the x87 double-extended value in the low 10
 * (cgo has no Go type for long double). */
typedef struct { unsigned char b[16]; } ld16;

long double ld_mul(long double a, long double b);
void c_ldmul(const ld16 *a, const ld16 *b, ld16 *r);
uint64_t c_switch(uint64_t k, uint64_t x);
