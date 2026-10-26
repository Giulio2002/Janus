#include "textflag.h"

// CtxPage = layout.CtxPage = 0x10_0000_0000 - 0x10_0000. Offsets: layout.Ctx*.
#define CTX $0xFFFF00000
// Ctx2Page = layout.Ctx2Page = CtxPage + 0x1000 (the AVX-512 state). Offsets: layout.Ctx2*.
#define CTX2 $0xFFFF01000

// func callPage()
// Saves the host's callee state and FS base in the context page, sets the case's FS base,
// loads YMM0-15 (XMM halves with MOVUPS, then bits 255:128 with VINSERTI128), the case's MXCSR
// (LDMXCSR) and every GPR of the case, and enters the instruction under test with IRETQ (frame at CtxFrame: rip, cs,
// rflags with TF set, rsp, ss), so that exactly one instruction executes before the
// single-step trap. From WRFSBASE until ·resume restores the host FS base nothing here may
// touch the Go runtime's TLS (no Go code runs in between).
// Control comes back through ·resume, which the signal handler plants as the saved RIP.
TEXT ·callPage(SB),NOSPLIT,$0-0
	MOVQ	CTX, AX
	MOVQ	BX, 32(AX)
	MOVQ	BP, 40(AX)
	MOVQ	R12, 48(AX)
	MOVQ	R13, 56(AX)
	MOVQ	R14, 64(AX)
	MOVQ	R15, 72(AX)
	MOVQ	SP, 80(AX)
	RDFSBASEQ	BX
	MOVQ	BX, 2056(AX)
	MOVQ	2064(AX), BX
	WRFSBASEQ	BX
	MOVQ	AX, R15
	MOVUPS	232(R15), X0
	MOVUPS	248(R15), X1
	MOVUPS	264(R15), X2
	MOVUPS	280(R15), X3
	MOVUPS	296(R15), X4
	MOVUPS	312(R15), X5
	MOVUPS	328(R15), X6
	MOVUPS	344(R15), X7
	MOVUPS	360(R15), X8
	MOVUPS	376(R15), X9
	MOVUPS	392(R15), X10
	MOVUPS	408(R15), X11
	MOVUPS	424(R15), X12
	MOVUPS	440(R15), X13
	MOVUPS	456(R15), X14
	MOVUPS	472(R15), X15
	// the case's x87 state: FXRSTOR64 of the image at CtxInX87 (which repeats the XMM
	// registers and MXCSR of the case), if the case has one
	CMPQ	2088(R15), $0
	JEQ	nox87
	FXRSTOR64	2112(R15)
nox87:
	VINSERTI128	$1, 1536(R15), Y0, Y0
	VINSERTI128	$1, 1552(R15), Y1, Y1
	VINSERTI128	$1, 1568(R15), Y2, Y2
	VINSERTI128	$1, 1584(R15), Y3, Y3
	VINSERTI128	$1, 1600(R15), Y4, Y4
	VINSERTI128	$1, 1616(R15), Y5, Y5
	VINSERTI128	$1, 1632(R15), Y6, Y6
	VINSERTI128	$1, 1648(R15), Y7, Y7
	VINSERTI128	$1, 1664(R15), Y8, Y8
	VINSERTI128	$1, 1680(R15), Y9, Y9
	VINSERTI128	$1, 1696(R15), Y10, Y10
	VINSERTI128	$1, 1712(R15), Y11, Y11
	VINSERTI128	$1, 1728(R15), Y12, Y12
	VINSERTI128	$1, 1744(R15), Y13, Y13
	VINSERTI128	$1, 1760(R15), Y14, Y14
	VINSERTI128	$1, 1776(R15), Y15, Y15
	// AVX-512 (WP-G, when the host has it: Ctx2Use512): bits 511:256 of ZMM0-15 (VINSERTI64X4,
	// after the VEX VINSERTI128 above, which zeroes them), ZMM16-31 and K0-K7
	MOVQ	CTX2, R14
	CMPQ	3648(R14), $0
	JEQ	no512
	VINSERTI64X4	$1, 0(R14), Z0, Z0
	VINSERTI64X4	$1, 32(R14), Z1, Z1
	VINSERTI64X4	$1, 64(R14), Z2, Z2
	VINSERTI64X4	$1, 96(R14), Z3, Z3
	VINSERTI64X4	$1, 128(R14), Z4, Z4
	VINSERTI64X4	$1, 160(R14), Z5, Z5
	VINSERTI64X4	$1, 192(R14), Z6, Z6
	VINSERTI64X4	$1, 224(R14), Z7, Z7
	VINSERTI64X4	$1, 256(R14), Z8, Z8
	VINSERTI64X4	$1, 288(R14), Z9, Z9
	VINSERTI64X4	$1, 320(R14), Z10, Z10
	VINSERTI64X4	$1, 352(R14), Z11, Z11
	VINSERTI64X4	$1, 384(R14), Z12, Z12
	VINSERTI64X4	$1, 416(R14), Z13, Z13
	VINSERTI64X4	$1, 448(R14), Z14, Z14
	VINSERTI64X4	$1, 480(R14), Z15, Z15
	VMOVDQU64	512(R14), Z16
	VMOVDQU64	576(R14), Z17
	VMOVDQU64	640(R14), Z18
	VMOVDQU64	704(R14), Z19
	VMOVDQU64	768(R14), Z20
	VMOVDQU64	832(R14), Z21
	VMOVDQU64	896(R14), Z22
	VMOVDQU64	960(R14), Z23
	VMOVDQU64	1024(R14), Z24
	VMOVDQU64	1088(R14), Z25
	VMOVDQU64	1152(R14), Z26
	VMOVDQU64	1216(R14), Z27
	VMOVDQU64	1280(R14), Z28
	VMOVDQU64	1344(R14), Z29
	VMOVDQU64	1408(R14), Z30
	VMOVDQU64	1472(R14), Z31
	KMOVQ	1536(R14), K0
	KMOVQ	1544(R14), K1
	KMOVQ	1552(R14), K2
	KMOVQ	1560(R14), K3
	KMOVQ	1568(R14), K4
	KMOVQ	1576(R14), K5
	KMOVQ	1584(R14), K6
	KMOVQ	1592(R14), K7
no512:
	// the case's MXCSR: from here to the instruction under test only integer moves and
	// IRETQ execute, so no SSE floating-point exception can be raised before TestPC
	LDMXCSR	2072(R15)
	MOVQ	104(R15), AX
	MOVQ	112(R15), CX
	MOVQ	120(R15), DX
	MOVQ	128(R15), BX
	MOVQ	144(R15), BP
	MOVQ	152(R15), SI
	MOVQ	160(R15), DI
	MOVQ	168(R15), R8
	MOVQ	176(R15), R9
	MOVQ	184(R15), R10
	MOVQ	192(R15), R11
	MOVQ	200(R15), R12
	MOVQ	208(R15), R13
	MOVQ	216(R15), R14
	LEAQ	1024(R15), SP
	MOVQ	224(R15), R15
	IRETQ

// Signal handler, entered by the kernel (SysV): DI = signo, SI = siginfo*, DX = ucontext*.
// Runs on the thread's sigaltstack. If a case is in flight it records the signal and the
// interrupted context, resets the x87/SSE control state in the frame, clears TF/DF/AC in the
// saved RFLAGS and redirects the saved RIP to ·resume. Otherwise: SIGALRM is ignored and any
// other signal (a fault of the harness itself) exits with status 97.
TEXT ·handler(SB),NOSPLIT|NOFRAME,$0
	MOVQ	CTX, AX
	MOVQ	0(AX), BX
	TESTQ	BX, BX
	JZ	notours
	MOVQ	DI, 8(AX)
	MOVQ	16(SI), BX
	MOVQ	BX, 16(AX)
	MOVLQSX	8(SI), BX
	MOVQ	BX, 24(AX)
	LEAQ	40(DX), SI
	LEAQ	512(AX), DI
	MOVQ	$23, CX
gloop:
	MOVQ	(SI), BX
	MOVQ	BX, (DI)
	ADDQ	$8, SI
	ADDQ	$8, DI
	DECQ	CX
	JNZ	gloop
	MOVQ	$0, 960(AX)
	MOVQ	$-1, 2080(AX)
	MOVQ	224(DX), SI
	TESTQ	SI, SI
	JZ	nofp
	MOVQ	$1, 960(AX)
	MOVL	24(SI), BX      // MXCSR at the time of the signal (fxsave offset 24)
	MOVL	BX, 2080(AX)
	LEAQ	160(SI), R8
	LEAQ	704(AX), DI
	MOVQ	$32, CX
xloop:
	MOVQ	(R8), BX
	MOVQ	BX, (DI)
	ADDQ	$8, R8
	ADDQ	$8, DI
	DECQ	CX
	JNZ	xloop
	// the x87 part of the fxsave area (FCW FSW FTW FOP FIP FDP MXCSR, ST0-ST7): 160 bytes
	LEAQ	2624(AX), DI
	MOVQ	SI, R8
	MOVQ	$20, CX
floop:
	MOVQ	(R8), BX
	MOVQ	BX, (DI)
	ADDQ	$8, R8
	ADDQ	$8, DI
	DECQ	CX
	JNZ	floop
	// YMM bits 255:128: the YMM_Hi128 component of the XSAVE area (standard format, offset
	// layout.XsaveYMMHOffset), if the frame has one (sw_reserved.magic1 = FP_XSTATE_MAGIC1)
	MOVQ	$-1, 2048(AX)
	MOVL	464(SI), BX
	CMPL	BX, $0x46505853
	JNE	noxsave
	MOVQ	512(SI), BX     // XSTATE_BV
	MOVQ	BX, 2048(AX)
	LEAQ	576(SI), R8
	LEAQ	1792(AX), DI
	MOVQ	$32, CX
yloop:
	MOVQ	(R8), BX
	MOVQ	BX, (DI)
	ADDQ	$8, R8
	ADDQ	$8, DI
	DECQ	CX
	JNZ	yloop
	// AVX-512: the opmask, ZMM_Hi256 and Hi16_ZMM components (standard offsets 1088, 1152,
	// 1664, checked at start-up), when the runner uses them (Ctx2Use512)
	MOVQ	CTX2, DI
	CMPQ	3648(DI), $0
	JEQ	noxsave
	LEAQ	1088(SI), R8
	LEAQ	3584(DI), R9
	MOVQ	$8, CX
kloop:
	MOVQ	(R8), BX
	MOVQ	BX, (R9)
	ADDQ	$8, R8
	ADDQ	$8, R9
	DECQ	CX
	JNZ	kloop
	LEAQ	1152(SI), R8
	LEAQ	2048(DI), R9
	MOVQ	$192, CX
zloop:
	MOVQ	(R8), BX
	MOVQ	BX, (R9)
	ADDQ	$8, R8
	ADDQ	$8, R9
	DECQ	CX
	JNZ	zloop
noxsave:
	MOVW	$0x37F, 0(SI)   // FCW: default
	MOVW	$0, 2(SI)       // FSW
	MOVW	$0, 4(SI)       // abridged FTW: x87 stack empty
	MOVL	$0x1F80, 24(SI) // MXCSR: default (the host's: Go runs with 0x1F80; sigreturn restores it)
nofp:
	LEAQ	·resume(SB), BX
	MOVQ	BX, 168(DX)     // saved RIP
	MOVQ	176(DX), BX
	ANDQ	$~0x40500, BX   // clear TF (0x100), DF (0x400), AC (0x40000)
	MOVQ	BX, 176(DX)
	MOVQ	$0, 0(AX)
	RET
notours:
	CMPQ	DI, $14
	JEQ	plain
	MOVQ	$97, DI
	MOVQ	$231, AX // exit_group
	SYSCALL
plain:
	RET

TEXT ·restorer(SB),NOSPLIT|NOFRAME,$0
	MOVQ	$15, AX // rt_sigreturn
	SYSCALL
	INT	$3

// Resume after the signal: restore the host FS base and the state saved by callPage and
// return to its caller (with clean upper YMM state).
TEXT ·resume(SB),NOSPLIT|NOFRAME,$0
	MOVQ	CTX, AX
	MOVQ	2056(AX), BX
	WRFSBASEQ	BX
	MOVQ	80(AX), SP
	MOVQ	32(AX), BX
	MOVQ	40(AX), BP
	MOVQ	48(AX), R12
	MOVQ	56(AX), R13
	MOVQ	64(AX), R14
	MOVQ	72(AX), R15
	CLD
	VZEROUPPER
	XORPS	X15, X15
	RET

// func addrs() (handler, restorer uintptr)
TEXT ·addrs(SB),NOSPLIT,$0-16
	LEAQ	·handler(SB), AX
	MOVQ	AX, handler+0(FP)
	LEAQ	·restorer(SB), AX
	MOVQ	AX, restorer+8(FP)
	RET

// func xgetbv0() uint64 (XCR0)
TEXT ·xgetbv0(SB),NOSPLIT,$0-8
	MOVL	$0, CX
	XGETBV
	SHLQ	$32, DX
	ORQ	DX, AX
	MOVQ	AX, ret+0(FP)
	RET

// func cpuid(eax, ecx uint32) (a, b, c, d uint32)
TEXT ·cpuid(SB),NOSPLIT,$0-24
	MOVL	eax+0(FP), AX
	MOVL	ecx+4(FP), CX
	CPUID
	MOVL	AX, a+8(FP)
	MOVL	BX, b+12(FP)
	MOVL	CX, c+16(FP)
	MOVL	DX, d+20(FP)
	RET
