#include "textflag.h"

// func AddAsm(x, y uint64) uint64
TEXT ·AddAsm(SB), NOSPLIT, $0-24
	MOVQ	x+0(FP), AX
	MOVQ	y+8(FP), BX
	ADDQ	BX, AX
	MOVQ	AX, ret+16(FP)
	RET

// func XorSlice(xs []uint64) uint64
TEXT ·XorSlice(SB), NOSPLIT, $0-32
	MOVQ	xs_base+0(FP), SI
	MOVQ	xs_len+8(FP), CX
	XORQ	AX, AX
loop:
	TESTQ	CX, CX
	JZ	done
	XORQ	(SI), AX
	ADDQ	$8, SI
	DECQ	CX
	JMP	loop
done:
	MOVQ	AX, ret+24(FP)
	RET

// func Twice(x uint64) uint64
TEXT ·Twice(SB), NOSPLIT, $16-16
	MOVQ	x+0(FP), AX
	MOVQ	AX, 0(SP)
	CALL	·double(SB)
	MOVQ	8(SP), AX
	INCQ	AX
	MOVQ	AX, ret+8(FP)
	RET
