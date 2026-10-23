#include "textflag.h"

// CtxPage = layout.CtxPage = 0x10_0000_0000 - 0x10_0000. Offsets: layout.Ctx*.
#define CTX $0xFFFF00000

// func callPage()
// Saves the host's callee state in the context page, loads XMM0-15 and every GPR of the case,
// and enters the instruction under test with IRETQ (frame at CtxFrame: rip, cs, rflags with
// TF set, rsp, ss), so that exactly one instruction executes before the single-step trap.
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
	MOVQ	224(DX), SI
	TESTQ	SI, SI
	JZ	nofp
	MOVQ	$1, 960(AX)
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
	MOVW	$0x37F, 0(SI)   // FCW: default
	MOVW	$0, 2(SI)       // FSW
	MOVW	$0, 4(SI)       // abridged FTW: x87 stack empty
	MOVL	$0x1F80, 24(SI) // MXCSR: default
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

// Resume after the signal: restore the host state saved by callPage and return to its caller.
TEXT ·resume(SB),NOSPLIT|NOFRAME,$0
	MOVQ	CTX, AX
	MOVQ	80(AX), SP
	MOVQ	32(AX), BX
	MOVQ	40(AX), BP
	MOVQ	48(AX), R12
	MOVQ	56(AX), R13
	MOVQ	64(AX), R14
	MOVQ	72(AX), R15
	CLD
	XORPS	X15, X15
	RET

// func addrs() (handler, restorer uintptr)
TEXT ·addrs(SB),NOSPLIT,$0-16
	LEAQ	·handler(SB), AX
	MOVQ	AX, handler+0(FP)
	LEAQ	·restorer(SB), AX
	MOVQ	AX, restorer+8(FP)
	RET
