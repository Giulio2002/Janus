#include <alloca.h>
#include <setjmp.h>
#include <stdlib.h>
#include <string.h>
extern char **environ;

#include "cenv.h"
#include "_cgo_export.h"

int64_t e_counter;
int64_t e_scale = 3;

/* Add x * e_scale to e_counter and return the new value. */
int64_t e_bump(int64_t x) { e_counter += x * e_scale; return e_counter; }

static __thread int64_t e_tls;
static __thread int64_t e_tls_ie __attribute__((tls_model("initial-exec")));

/* Add x to this thread's e_tls and return the new value. */
int64_t e_tls_add(int64_t x) { e_tls += x; return e_tls; }
int64_t e_tls_ie_add(int64_t x) { e_tls_ie += x; return e_tls_ie; }

/* The index of the first minimum of a[0..n) under cmp (0 if n = 0). */
size_t e_argmin(const int64_t *a, size_t n, e_cmp_fn cmp) {
	size_t best = 0;
	for (size_t i = 1; i < n; i++)
		if (cmp(&a[i], &a[best]) < 0)
			best = i;
	return best;
}

/* -1, 0 or 1 as *x <, = or > *y (signed). */
int e_cmp_i64(const void *x, const void *y) {
	int64_t a = *(const int64_t *)x, b = *(const int64_t *)y;
	return (a > b) - (a < b);
}

size_t e_argmin_i64(const int64_t *a, size_t n) { return e_argmin(a, n, e_cmp_i64); }

/* Duplicate the string s on the C heap, copy the duplicate to d and free it; return the
   length of s (-1, and d untouched, if malloc fails). */
int64_t e_libc(const char *s, char *d) {
	size_t n = strlen(s);
	char *m = malloc(n + 1);
	if (!m)
		return -1;
	memcpy(m, s, n + 1);
	memcpy(d, m, n + 1);
	free(m);
	return (int64_t)n;
}

static jmp_buf e_env;
static void __attribute__((noinline)) e_thrower(int v) { if (v) longjmp(e_env, v); }

/* 1 if v != 0 (e_thrower jumps back to the setjmp), 0 otherwise. */
int e_setjmp(int v) {
	if (setjmp(e_env))
		return 1;
	e_thrower(v);
	return 0;
}

/* 0 + 1 + ... + (n - 1), through an alloca'd array. */
int64_t e_alloca(size_t n) {
	int64_t *p = alloca(n * sizeof *p + 8);
	for (size_t i = 0; i < n; i++)
		p[i] = (int64_t)i;
	int64_t s = 0;
	for (size_t i = 0; i < n; i++)
		s += p[i];
	return s;
}

/* Atomically increment *p and return the new value. */
uint32_t e_atomic_inc(uint32_t *p) { return __atomic_add_fetch(p, 1, __ATOMIC_ACQ_REL); }

/* GoTwice(x) + 1: calls back into Go. */
int64_t e_callgo(int64_t x) { return GoTwice(x) + 1; }

/* GoBox(x): calls back into Go, whose code calls a Go function that allocates. */
int64_t e_callbox(int64_t x) { return GoBox(x); }

/* GoLarge(x): calls back into Go, whose frame is over 4096 bytes. */
int64_t e_calllarge(int64_t x) { return GoLarge(x); }

/* environ[i]: a libc variable, read through a GOT slot the dynamic linker fills. */
char *e_env_at(size_t i) { return environ[i]; }
