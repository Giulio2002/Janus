#include "textflag.h"

// func AddAsm(x, y uint64) uint64
TEXT ·AddAsm(SB), NOSPLIT, $0-24
	MOVD	x+0(FP), R0
	MOVD	y+8(FP), R1
	ADD	R1, R0, R0
	MOVD	R0, ret+16(FP)
	RET

// func XorSlice(xs []uint64) uint64
TEXT ·XorSlice(SB), NOSPLIT, $0-32
	MOVD	xs_base+0(FP), R0
	MOVD	xs_len+8(FP), R1
	MOVD	$0, R2
loop:
	CBZ	R1, done
	MOVD.P	8(R0), R3
	EOR	R3, R2, R2
	SUB	$1, R1, R1
	B	loop
done:
	MOVD	R2, ret+24(FP)
	RET

// func Twice(x uint64) uint64
TEXT ·Twice(SB), NOSPLIT, $16-16
	MOVD	x+0(FP), R0
	MOVD	R0, 8(RSP)
	CALL	·double(SB)
	MOVD	16(RSP), R0
	ADD	$1, R0, R0
	MOVD	R0, ret+8(FP)
	RET
