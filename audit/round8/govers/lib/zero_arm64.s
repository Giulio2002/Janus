#include "textflag.h"

// Round 8 G3: an ordinary function of package lib that returns normally, under the name of a
// runtime panic stub that exists in go1.26 but not in go1.25 (runtime.panicSimdImm). Linked by
// go1.25 it is the only definition of that name, so it gets the name unmangled.
TEXT runtime·panicSimdImm(SB),NOSPLIT|NOFRAME,$0-0
	MOVD	$0, R0
	RET

TEXT ·Zero(SB),NOSPLIT,$0-8
	MOVD	R30, R3
	BL	runtime·panicSimdImm(SB)
	MOVD	R3, R30
	MOVD	R0, ret+0(FP)
	RET
