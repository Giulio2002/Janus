#include "textflag.h"

// func fpsr() uint32
TEXT ·fpsr(SB), NOSPLIT, $0-4
	MRS FPSR, R0
	MOVW R0, ret+0(FP)
	RET
