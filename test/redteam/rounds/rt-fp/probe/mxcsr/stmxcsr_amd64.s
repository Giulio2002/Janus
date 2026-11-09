#include "textflag.h"

// func stmxcsr() uint32
TEXT ·stmxcsr(SB), NOSPLIT, $8-4
	STMXCSR 0(SP)
	MOVL 0(SP), AX
	MOVL AX, ret+0(FP)
	RET
