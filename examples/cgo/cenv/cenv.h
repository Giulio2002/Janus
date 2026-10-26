#include <stddef.h>
#include <stdint.h>

/* The C environment examples of Janus (docs/FFI.md, sections 2-4): C functions that use what a
   C program gets from its environment rather than from its arguments. */

extern int64_t e_counter;           /* writable, .bss */
extern int64_t e_scale;             /* writable, .data */
int64_t e_bump(int64_t x);          /* e_counter += x * e_scale */

int64_t e_tls_add(int64_t x);       /* a __thread variable, local-exec model */
int64_t e_tls_ie_add(int64_t x);    /* a __thread variable, initial-exec model */

typedef int (*e_cmp_fn)(const void *, const void *);
size_t e_argmin(const int64_t *a, size_t n, e_cmp_fn cmp); /* qsort-style comparator */
int e_cmp_i64(const void *x, const void *y);
size_t e_argmin_i64(const int64_t *a, size_t n);           /* e_argmin(a, n, e_cmp_i64) */

int64_t e_libc(const char *s, char *d);  /* strlen, malloc, memcpy, free through the PLT */
int e_setjmp(int v);                     /* setjmp / longjmp */
int64_t e_alloca(size_t n);              /* alloca */
uint32_t e_atomic_inc(uint32_t *p);      /* GCC __atomic (arm64: the outline-atomics helper) */
int64_t e_callgo(int64_t x);             /* calls the exported Go function GoTwice */
int64_t e_callbox(int64_t x);          /* calls the exported Go function GoBox (allocates) */
int64_t e_calllarge(int64_t x);        /* calls the exported Go function GoLarge (a 4.8 KB frame) */
char *e_env_at(size_t i);              /* environ[i]: a GOT slot with a dynamic relocation */
