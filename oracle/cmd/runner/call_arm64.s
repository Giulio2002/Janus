#include "textflag.h"

// func callPage(entry uintptr)
// Branches-with-link to the trampoline entry. The trampoline saves x19..x30 and SP in the
// context page and the resume sequence restores them, so to Go this is an ordinary call
// that clobbers every caller-saved register.
TEXT ·callPage(SB),NOSPLIT,$16-8
	MOVD	entry+0(FP), R1
	CALL	(R1)
	RET
