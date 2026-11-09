#include "textflag.h"

// func getg() uintptr: the current g (R28), for the in-process MCacheOK probe.
TEXT ·getg(SB),NOSPLIT,$0-8
	MOVD	g, R0
	MOVD	R0, ret+0(FP)
	RET
