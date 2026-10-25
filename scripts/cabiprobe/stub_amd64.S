// The probe's machine-code helpers for System V AMD64 (compiled with the fixed driver compiler).
//
// probe_dump: the callee of every caller test. Saves RDI RSI RDX RCX R8 R9 RAX, XMM0-XMM7, RSP
// at entry and the 1024 bytes of the argument area (from RSP + 8) into probe_dumparea, calls
// probe_capture (C), and returns.
//
// probe_load(block, fn): calls fn with the registers, AL and the argument-area bytes from block
// (laid out by the Go harness from Janus's classification) and stores RAX, RDX, XMM0, XMM1 and,
// when block says the result is on the x87 stack, ST0 (and ST1).
	.text
	.globl probe_dump
	.type probe_dump, @function
probe_dump:
	movq %rdi, probe_dumparea+0(%rip)
	movq %rsi, probe_dumparea+8(%rip)
	movq %rdx, probe_dumparea+16(%rip)
	movq %rcx, probe_dumparea+24(%rip)
	movq %r8, probe_dumparea+32(%rip)
	movq %r9, probe_dumparea+40(%rip)
	movq %rax, probe_dumparea+48(%rip)
	movdqu %xmm0, probe_dumparea+80(%rip)
	movdqu %xmm1, probe_dumparea+96(%rip)
	movdqu %xmm2, probe_dumparea+112(%rip)
	movdqu %xmm3, probe_dumparea+128(%rip)
	movdqu %xmm4, probe_dumparea+144(%rip)
	movdqu %xmm5, probe_dumparea+160(%rip)
	movdqu %xmm6, probe_dumparea+176(%rip)
	movdqu %xmm7, probe_dumparea+192(%rip)
	movq %rsp, probe_dumparea+208(%rip)
	leaq 8(%rsp), %rsi
	leaq probe_dumparea+224(%rip), %rdi
	movl $1024, %ecx
	rep movsb
	subq $8, %rsp
	call probe_capture
	addq $8, %rsp
	ret
	.size probe_dump, .-probe_dump

	.globl probe_load
	.type probe_load, @function
probe_load:
	pushq %rbp
	movq %rsp, %rbp
	pushq %rbx
	pushq %r12
	movq %rdi, %rbx
	movq %rsi, %r12
	movq 208(%rbx), %rcx
	subq %rcx, %rsp
	leaq 352(%rbx), %rsi
	movq %rsp, %rdi
	rep movsb
	movq %rsp, 216(%rbx)
	movdqu 80(%rbx), %xmm0
	movdqu 96(%rbx), %xmm1
	movdqu 112(%rbx), %xmm2
	movdqu 128(%rbx), %xmm3
	movdqu 144(%rbx), %xmm4
	movdqu 160(%rbx), %xmm5
	movdqu 176(%rbx), %xmm6
	movdqu 192(%rbx), %xmm7
	movq 0(%rbx), %rdi
	movq 8(%rbx), %rsi
	movq 16(%rbx), %rdx
	movq 24(%rbx), %rcx
	movq 32(%rbx), %r8
	movq 40(%rbx), %r9
	movq 48(%rbx), %rax
	call *%r12
	movq %rax, 232(%rbx)
	movq %rdx, 240(%rbx)
	movdqu %xmm0, 256(%rbx)
	movdqu %xmm1, 272(%rbx)
	cmpq $0, 224(%rbx)
	je 1f
	fstpt 320(%rbx)
	cmpq $1, 224(%rbx)
	je 1f
	fstpt 336(%rbx)
1:	fninit
	leaq -16(%rbp), %rsp
	popq %r12
	popq %rbx
	popq %rbp
	ret
	.size probe_load, .-probe_load
	.section .note.GNU-stack,"",@progbits
