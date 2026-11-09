// The probe's machine-code helpers for AAPCS64 (compiled with the fixed driver compiler).
//
// probe_dump: the callee of every caller test. Saves X0-X8, Q0-Q7, SP and the 1024 bytes above
// SP into probe_dumparea, calls probe_capture (C) to copy the memory any saved value points to
// on the stack, and returns.
//
// probe_load(block, fn): calls fn with X0-X8, Q0-Q7 and the stacked-argument bytes from block
// (laid out by the Go harness from Janus's classification), and stores X0, X1, Q0-Q3 after the
// return.
	.text
	.globl probe_dump
	.type probe_dump, %function
probe_dump:
	adrp x9, probe_dumparea
	add x9, x9, :lo12:probe_dumparea
	stp x0, x1, [x9, #0]
	stp x2, x3, [x9, #16]
	stp x4, x5, [x9, #32]
	stp x6, x7, [x9, #48]
	str x8, [x9, #64]
	stp q0, q1, [x9, #80]
	stp q2, q3, [x9, #112]
	stp q4, q5, [x9, #144]
	stp q6, q7, [x9, #176]
	mov x10, sp
	str x10, [x9, #208]
	add x11, x9, #224
	mov x12, #0
1:	ldr x13, [x10, x12]
	str x13, [x11, x12]
	add x12, x12, #8
	cmp x12, #1024
	b.ne 1b
	stp x29, x30, [sp, #-16]!
	mov x29, sp
	bl probe_capture
	ldp x29, x30, [sp], #16
	ret
	.size probe_dump, .-probe_dump

	.globl probe_load
	.type probe_load, %function
probe_load:
	stp x29, x30, [sp, #-32]!
	mov x29, sp
	stp x19, x20, [sp, #16]
	mov x19, x0
	mov x20, x1
	ldr x9, [x19, #208]
	sub sp, sp, x9
	add x10, x19, #352
	mov x11, sp
	mov x12, #0
1:	cmp x12, x9
	b.eq 2f
	ldr x13, [x10, x12]
	str x13, [x11, x12]
	add x12, x12, #8
	b 1b
2:	mov x13, sp
	str x13, [x19, #216]
	ldp q0, q1, [x19, #80]
	ldp q2, q3, [x19, #112]
	ldp q4, q5, [x19, #144]
	ldp q6, q7, [x19, #176]
	ldp x0, x1, [x19, #0]
	ldp x2, x3, [x19, #16]
	ldp x4, x5, [x19, #32]
	ldp x6, x7, [x19, #48]
	ldr x8, [x19, #64]
	blr x20
	stp x0, x1, [x19, #232]
	stp q0, q1, [x19, #256]
	stp q2, q3, [x19, #288]
	mov sp, x29
	ldp x19, x20, [sp, #16]
	ldp x29, x30, [sp], #32
	ret
	.size probe_load, .-probe_load
	.section .note.GNU-stack,"",%progbits
