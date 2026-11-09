#include "textflag.h"

// An ordinary function of package lib that returns normally, but whose symbol is in the
// runtime namespace and starts with "runtime.panic".
TEXT runtime·panicJanusR7(SB),NOSPLIT|NOFRAME,$0-0
	MOVD	$0, R0
	RET

TEXT ·Zero(SB),NOSPLIT,$0-8
	MOVD	R30, R3
	BL	runtime·panicJanusR7(SB)
	MOVD	R3, R30
	MOVD	R0, ret+0(FP)
	RET

// An ordinary function of package lib that panics (it calls lib.boom), but whose symbol is in
// the runtime namespace and starts with "runtime.morestack".
TEXT runtime·morestackJanusR7(SB),0,$16-0
	CALL	·boom(SB)
	RET

TEXT ·Boom(SB),NOSPLIT,$0-8
	MOVD	R30, R3
	BL	runtime·morestackJanusR7(SB)
	MOVD	R3, R30
	MOVD	$0, R0
	MOVD	R0, ret+0(FP)
	RET

