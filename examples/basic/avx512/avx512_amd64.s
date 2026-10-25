#include "textflag.h"

// func search64(p *byte, nq int, c byte) int
TEXT ·search64(SB), NOSPLIT, $0-32
	MOVQ	p+0(FP), SI
	MOVQ	nq+8(FP), CX
	MOVBLZX	c+16(FP), AX
	MOVL	$1, BX
	SHLL	CX, BX
	DECL	BX
	KMOVB	BX, K1
	VMOVDQU64.Z	(SI), K1, Z0
	VPBROADCASTB	AX, Z1
	SHLQ	$3, CX
	MOVQ	$-1, DX
	BZHIQ	CX, DX, DX
	KMOVQ	DX, K3
	VPCMPEQB	Z1, Z0, K3, K2
	KMOVQ	K2, AX
	TZCNTQ	AX, AX
	VZEROUPPER
	MOVQ	AX, ret+24(FP)
	RET
