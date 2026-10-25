#include "textflag.h"

// func indexByte32(p *[32]byte, c byte) int
TEXT ·indexByte32(SB), NOSPLIT, $0-24
	MOVQ	p+0(FP), SI
	MOVBLZX	c+8(FP), AX
	MOVQ	AX, X0
	PUNPCKLBW	X0, X0
	PSHUFLW	$0, X0, X0
	PUNPCKLQDQ	X0, X0
	MOVOU	(SI), X2
	MOVOU	16(SI), X3
	PCMPEQB	X0, X2
	PCMPEQB	X0, X3
	PMOVMSKB	X2, AX
	PMOVMSKB	X3, BX
	SHLQ	$16, BX
	ORQ	BX, AX
	BTSQ	$32, AX
	BSFQ	AX, AX
	MOVQ	AX, ret+16(FP)
	RET

// func crc32cBlock(crc uint32, p *[16]byte) uint32
TEXT ·crc32cBlock(SB), NOSPLIT, $0-20
	MOVL	crc+0(FP), AX
	MOVQ	p+8(FP), SI
	CRC32Q	(SI), AX
	CRC32Q	8(SI), AX
	MOVL	AX, ret+16(FP)
	RET
