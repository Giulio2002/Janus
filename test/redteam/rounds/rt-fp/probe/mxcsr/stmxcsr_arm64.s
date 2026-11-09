#include "textflag.h"

// func stmxcsr() uint32: on arm64, FPCR (bits 31:0) | FPSR << 32 is not needed; FPCR only.
TEXT ·stmxcsr(SB), NOSPLIT, $0-4
	MRS FPCR, R0
	MOVW R0, ret+0(FP)
	RET
