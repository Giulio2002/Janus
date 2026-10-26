// Model engine (placed at E = 0x300000). Priv base B = 0x10000.
// frame (msp): +0 Fsp, +8 bound, +16 resume, +24 mode, +32 phase, +40 ba, +48 sa, +56 x18, +64 lr, +72 x29
        .text
gopanic:
        movz x6, #0x1, lsl #16
        ldr x7, [x6]
        add x8, x6, #0x100
        add x8, x8, x7, lsl #5
        str x0, [x8]
        str x1, [x8, #8]
        mov x9, sp
        str x9, [x8, #16]
        str xzr, [x8, #24]
        add x7, x7, #1
        str x7, [x6]
        mov x10, #0
        b lookup
goexit:
        movz x6, #0x1, lsl #16
        ldr x7, [x6]
        add x8, x6, #0x100
        add x8, x8, x7, lsl #5
        str xzr, [x8]
        str xzr, [x8, #8]
        mov x9, sp
        str x9, [x8, #16]
        mov x9, #1
        str x9, [x8, #24]
        add x7, x7, #1
        str x7, [x6]
        mov x10, #1
        b lookup
deferreturn:
        movz x6, #0x1, lsl #16
        mov x9, sp
        ldr x5, [x6, #0x10]
        ldr x14, [x6, #0x18]
        ldr x15, [x6, #0x20]
        str xzr, [x6, #0x10]
        sub sp, x9, #96
        str x9, [sp]
        str x9, [sp, #8]
        str xzr, [sp, #16]
        mov x10, #2
        str x10, [sp, #24]
        str x5, [sp, #32]
        str x14, [sp, #40]
        str x15, [sp, #48]
        str x18, [sp, #56]
        str x30, [sp, #64]
        str x29, [sp, #72]
        b LH
gorecover:
        movz x6, #0x1, lsl #16
        ldr x7, [x6]
        cbz x7, 1f
        sub x7, x7, #1
        add x8, x6, #0x100
        add x8, x8, x7, lsl #5
        ldr x0, [x8, #24]
        and x0, x0, #3
        cbnz x0, 1f
        ldr x1, [x29, #8]
        adr x2, RP
        cmp x1, x2
        b.ne 1f
        mov x0, #2
        str x0, [x8, #24]
        ldr x0, [x8]
        ldr x1, [x8, #8]
        ret
1:      mov x0, #0
        mov x1, #0
        ret
deferproc:
        movz x6, #0x1, lsl #16
        ldr x7, [x6, #8]
        mov x9, #96
        mul x8, x7, x9
        add x8, x8, x6
        add x8, x8, #0x200
        mov x10, sp
        str x10, [x8]
        str xzr, [x8, #8]
        str xzr, [x8, #16]
        mov x11, #1
        str x11, [x8, #24]
        str x0, [x8, #32]
        add x7, x7, #1
        str x7, [x6, #8]
        ret
deferprocStack:
        ldr x0, [x0, #24]
        movz x6, #0x1, lsl #16
        ldr x7, [x6, #8]
        mov x9, #96
        mul x8, x7, x9
        add x8, x8, x6
        add x8, x8, #0x200
        mov x10, sp
        str x10, [x8]
        str xzr, [x8, #8]
        str xzr, [x8, #16]
        mov x11, #1
        str x11, [x8, #24]
        str x0, [x8, #32]
        add x7, x7, #1
        str x7, [x6, #8]
        ret
deferrangefunc:
        movz x6, #0x1, lsl #16
        ldr x7, [x6, #8]
        mov x9, #96
        mul x8, x7, x9
        add x8, x8, x6
        add x8, x8, #0x200
        mov x10, sp
        str x10, [x8]
        str x8, [x8, #8]
        str xzr, [x8, #16]
        str xzr, [x8, #24]
        add x7, x7, #1
        str x7, [x6, #8]
        mov x0, #1
        mov x1, x8
        ret
deferprocat:
        movz x6, #0x1, lsl #16
        ldr x7, [x6, #8]
        sub x7, x7, #1
        mov x9, #96
        mul x8, x7, x9
        add x8, x8, x6
        add x8, x8, #0x200
        ldr x10, [x8, #24]
        add x11, x8, #32
        str x0, [x11, x10, lsl #3]
        add x10, x10, #1
        str x10, [x8, #24]
        ret
lookup:                         // x30 = pc in F, x10 = mode, sp = Fsp
        movz x6, #0x1, lsl #16
        ldr x7, [x6, #0x28]     // ntab
        add x8, x6, #0x500
L1:     cbz x7, NOTFOUND
        ldr x0, [x8]
        cmp x30, x0
        b.lo NEXT
        ldr x1, [x8, #8]
        add x1, x0, x1
        cmp x30, x1
        b.lo FOUND
NEXT:   add x8, x8, #56
        sub x7, x7, #1
        b L1
NOTFOUND: b NOTFOUND
FOUND:  mov x9, sp
        ldr x1, [x8, #16]
        add x2, x9, x1          // bound
        ldr x3, [x8, #24]
        add x3, x0, x3          // resume
        ldr x4, [x8, #32]       // hasOpen
        mov x5, #0
        mov x14, #0
        mov x15, #0
        cbz x4, SETUP
        sub x12, x2, #8         // varp
        ldr x13, [x8, #40]
        sub x14, x12, x13       // ba
        ldr x13, [x8, #48]
        sub x15, x12, x13       // sa
        ldrb w13, [x14]
        cbz w13, SETUP
        mov x5, #1
SETUP:  sub sp, x9, #96
        str x9, [sp]
        str x2, [sp, #8]
        str x3, [sp, #16]
        str x10, [sp, #24]
        str x5, [sp, #32]
        str x14, [sp, #40]
        str x15, [sp, #48]
        str x18, [sp, #56]
LH:     ldr x0, [sp, #32]
        cbz x0, REC
        ldr x1, [sp, #40]
        ldrb w2, [x1]
        cbz w2, TOREC
        clz w3, w2
        mov w4, #31
        sub w3, w4, w3
        mov w4, #1
        lsl w4, w4, w3
        bic w2, w2, w4
        strb w2, [x1]
        ldr x5, [sp, #48]
        ldr x26, [x5, x3, lsl #3]
        b CALL
TOREC:  str xzr, [sp, #32]
REC:    movz x6, #0x1, lsl #16
        ldr x7, [x6, #8]
        cbz x7, FIN
        sub x8, x7, #1
        mov x0, #96
        mul x8, x8, x0
        add x8, x8, x6
        add x8, x8, #0x200
        ldr x0, [x8]
        ldr x1, [sp]
        cmp x0, x1
        b.ne FIN
        mov x0, #1
        str x0, [x8, #16]
        ldr x0, [x8, #24]
        cbz x0, POPREC
        sub x0, x0, #1
        str x0, [x8, #24]
        add x2, x8, #32
        ldr x26, [x2, x0, lsl #3]
        cbnz x0, CALL
        sub x7, x7, #1
        str x7, [x6, #8]
        b CALL
POPREC: sub x7, x7, #1
        str x7, [x6, #8]
        b LH
CALL:   ldr x9, [x26]
        sub x29, sp, #8
        blr x9
RP:     ldr x18, [sp, #56]
        ldr x0, [sp, #24]
        cbnz x0, LH
        movz x6, #0x1, lsl #16
        ldr x7, [x6]
        sub x7, x7, #1
        add x8, x6, #0x100
        add x8, x8, x7, lsl #5
        ldr x0, [x8, #24]
        tbz x0, #1, LH
        ldr x1, [sp]            // recovery: Fsp
DROP:   ldr x7, [x6]
        cbz x7, DROPPED
        sub x7, x7, #1
        add x8, x6, #0x100
        add x8, x8, x7, lsl #5
        ldr x0, [x8, #16]
        cmp x0, x1
        b.hi DROPPED
        str x7, [x6]
        b DROP
DROPPED: str xzr, [x6, #0x10]
        ldr x0, [sp, #32]
        cbz x0, RESUME
        ldr x2, [sp, #40]
        ldrb w3, [x2]
        cbz w3, RESUME
        mov x0, #1
        str x0, [x6, #0x10]
        str x2, [x6, #0x18]
        ldr x3, [sp, #48]
        str x3, [x6, #0x20]
RESUME: ldr x0, [sp, #16]
        mov sp, x1
        sub x29, sp, #8
        br x0
FIN:    ldr x0, [sp, #24]
        cmp x0, #2
        b.eq RETFIN
        ldr x1, [sp, #8]
        mov sp, x1
        adr x0, RP
        br x0
RETFIN: ldr x30, [sp, #64]
        ldr x29, [sp, #72]
        ldr x1, [sp]
        mov sp, x1
        ret
