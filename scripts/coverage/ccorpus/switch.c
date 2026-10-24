/* Switches that become jump tables, binary-search trees or bit tests; a computed goto. */
#include <stdint.h>

int s_dense(int op, int a, int b) {
	switch (op) {
	case 0: return a + b; case 1: return a - b; case 2: return a * b; case 3: return b ? a / b : 0;
	case 4: return a & b; case 5: return a | b; case 6: return a ^ b; case 7: return a << (b & 31);
	case 8: return a >> (b & 31); case 9: return a < b; case 10: return a == b; case 11: return ~a;
	default: return -1;
	}
}
const char *s_name(unsigned k) {
	switch (k) {
	case 0: return "zero"; case 1: return "one"; case 2: return "two"; case 3: return "three";
	case 4: return "four"; case 5: return "five"; case 6: return "six"; case 7: return "seven";
	}
	return "many";
}
int s_sparse(int x) {
	switch (x) {
	case 3: return 10; case 100: return 20; case 1000: return 30; case 77777: return 40;
	case -5: return 50; case 123456789: return 60;
	}
	return 0;
}
int s_class(char c) {
	switch (c) {
	case ' ': case '\t': case '\n': case '\r': return 1;
	case '0' ... '9': return 2;
	case 'a' ... 'z': case 'A' ... 'Z': case '_': return 3;
	case '(': case ')': case '[': case ']': case '{': case '}': return 4;
	}
	return 0;
}
/* A small lexer state machine: switch inside a loop. */
int s_lex(const char *p) {
	int st = 0, n = 0;
	for (; *p; p++) {
		switch (st) {
		case 0: if (*p == '"') st = 1; else if (*p == '/') st = 3; else n++; break;
		case 1: if (*p == '\\') st = 2; else if (*p == '"') st = 0; break;
		case 2: st = 1; break;
		case 3: st = *p == '/' ? 4 : 0; break;
		case 4: if (*p == '\n') st = 0; break;
		}
	}
	return n * 8 + st;
}
/* GNU computed goto (threaded interpreter). */
int64_t s_interp(const uint8_t *code, int64_t acc) {
	static const void *tab[] = { &&op_end, &&op_inc, &&op_dbl, &&op_neg };
	const uint8_t *pc = code;
	goto *tab[*pc & 3];
op_inc: acc++; pc++; goto *tab[*pc & 3];
op_dbl: acc *= 2; pc++; goto *tab[*pc & 3];
op_neg: acc = -acc; pc++; goto *tab[*pc & 3];
op_end: return acc;
}
