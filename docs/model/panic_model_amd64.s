// Model engine for the amd64 panic contracts (placed at E = 0x300000). Priv base B = 0x10000.
// The same engine as panic_model_arm64.s, in x86-64: the entry RSP points at the return address,
// the frame's SP (Fsp) is RSP + 8; the engine frame (msp) is 96 bytes below the entry RSP:
// +0 Fsp, +8 bound, +16 resume, +24 mode, +32 phase, +40 ba, +48 sa, +56 unused.
        .intel_syntax noprefix
        .text
gopanic:
        mov     r8d, 0x10000
        mov     r9, [r8]
        lea     r10, [r8+0x100]
        mov     r11, r9
        shl     r11, 5
        add     r10, r11
        mov     [r10], rax
        mov     [r10+8], rbx
        lea     r11, [rsp+8]
        mov     [r10+16], r11
        mov     qword ptr [r10+24], 0
        add     r9, 1
        mov     [r8], r9
        xor     edi, edi
        jmp     lookup
goexit:
        mov     r8d, 0x10000
        mov     r9, [r8]
        lea     r10, [r8+0x100]
        mov     r11, r9
        shl     r11, 5
        add     r10, r11
        mov     qword ptr [r10], 0
        mov     qword ptr [r10+8], 0
        lea     r11, [rsp+8]
        mov     [r10+16], r11
        mov     qword ptr [r10+24], 1
        add     r9, 1
        mov     [r8], r9
        mov     edi, 1
        jmp     lookup
deferreturn:
        mov     r8d, 0x10000
        lea     r11, [rsp+8]
        mov     rsi, [r8+0x10]
        mov     r12, [r8+0x18]
        mov     r13, [r8+0x20]
        mov     qword ptr [r8+0x10], 0
        sub     rsp, 96
        mov     [rsp], r11
        mov     [rsp+8], r11
        mov     qword ptr [rsp+16], 0
        mov     qword ptr [rsp+24], 2
        mov     [rsp+32], rsi
        mov     [rsp+40], r12
        mov     [rsp+48], r13
        mov     qword ptr [rsp+56], 0
        jmp     LH
gorecover:
        mov     r8d, 0x10000
        mov     r9, [r8]
        test    r9, r9
        jz      NIL
        sub     r9, 1
        lea     r10, [r8+0x100]
        mov     r11, r9
        shl     r11, 5
        add     r10, r11
        mov     rax, [r10+24]
        and     eax, 3
        jnz     NIL
        mov     rcx, [rbp+8]
        lea     rdx, [rip+RP]
        cmp     rcx, rdx
        jne     NIL
        mov     qword ptr [r10+24], 2
        mov     rax, [r10]
        mov     rbx, [r10+8]
        ret
NIL:    xor     eax, eax
        xor     ebx, ebx
        ret
deferproc:
        mov     r8d, 0x10000
        mov     r9, [r8+8]
        imul    r10, r9, 96
        lea     r10, [r10+r8+0x200]
        lea     r11, [rsp+8]
        mov     [r10], r11
        mov     qword ptr [r10+8], 0
        mov     qword ptr [r10+16], 0
        mov     qword ptr [r10+24], 1
        mov     [r10+32], rax
        add     r9, 1
        mov     [r8+8], r9
        ret
deferprocStack:
        mov     rax, [rax+24]
        mov     r8d, 0x10000
        mov     r9, [r8+8]
        imul    r10, r9, 96
        lea     r10, [r10+r8+0x200]
        lea     r11, [rsp+8]
        mov     [r10], r11
        mov     qword ptr [r10+8], 0
        mov     qword ptr [r10+16], 0
        mov     qword ptr [r10+24], 1
        mov     [r10+32], rax
        add     r9, 1
        mov     [r8+8], r9
        ret
deferrangefunc:
        mov     r8d, 0x10000
        mov     r9, [r8+8]
        imul    r10, r9, 96
        lea     r10, [r10+r8+0x200]
        lea     r11, [rsp+8]
        mov     [r10], r11
        mov     [r10+8], r10
        mov     qword ptr [r10+16], 0
        mov     qword ptr [r10+24], 0
        add     r9, 1
        mov     [r8+8], r9
        mov     eax, 1
        mov     rbx, r10
        ret
deferprocat:
        mov     r8d, 0x10000
        mov     r9, [r8+8]
        sub     r9, 1
        imul    r10, r9, 96
        lea     r10, [r10+r8+0x200]
        mov     r11, [r10+24]
        mov     [r10+r11*8+32], rax
        add     r11, 1
        mov     [r10+24], r11
        ret
lookup:
        mov     rcx, [rsp]
        mov     r8d, 0x10000
        mov     r9, [r8+0x28]
        lea     r10, [r8+0x500]
L1:     test    r9, r9
        jz      NOTFOUND
        mov     rax, [r10]
        cmp     rcx, rax
        jb      NEXT
        mov     rdx, [r10+8]
        add     rdx, rax
        cmp     rcx, rdx
        jb      FOUND
NEXT:   add     r10, 56
        sub     r9, 1
        jmp     L1
NOTFOUND: jmp   NOTFOUND
FOUND:  lea     r11, [rsp+8]
        mov     rdx, [r10+16]
        add     rdx, r11
        mov     rsi, [r10+24]
        add     rsi, rax
        mov     r9, [r10+32]
        xor     r12d, r12d
        xor     r13d, r13d
        xor     r15d, r15d
        test    r9, r9
        jz      SETUP
        lea     rax, [rdx-8]
        mov     rcx, [r10+40]
        mov     r13, rax
        sub     r13, rcx
        mov     rcx, [r10+48]
        mov     r15, rax
        sub     r15, rcx
        movzx   ecx, byte ptr [r13]
        test    ecx, ecx
        jz      SETUP
        mov     r12d, 1
SETUP:  sub     rsp, 96
        mov     [rsp], r11
        mov     [rsp+8], rdx
        mov     [rsp+16], rsi
        mov     [rsp+24], rdi
        mov     [rsp+32], r12
        mov     [rsp+40], r13
        mov     [rsp+48], r15
        mov     qword ptr [rsp+56], 0
LH:     mov     rax, [rsp+32]
        test    rax, rax
        jz      REC
        mov     rcx, [rsp+40]
        movzx   edx, byte ptr [rcx]
        test    edx, edx
        jz      TOREC
        bsr     esi, edx
        btr     edx, esi
        mov     [rcx], dl
        mov     r8, [rsp+48]
        mov     rdx, [r8+rsi*8]
        jmp     CALL
TOREC:  mov     qword ptr [rsp+32], 0
        jmp     LH
REC:    mov     r8d, 0x10000
        mov     r9, [r8+8]
        test    r9, r9
        jz      FIN
        lea     r10, [r9-1]
        imul    r10, r10, 96
        lea     r10, [r10+r8+0x200]
        mov     rax, [r10]
        cmp     rax, [rsp]
        jne     FIN
        mov     qword ptr [r10+16], 1
        mov     rax, [r10+24]
        test    rax, rax
        jz      POPREC
        sub     rax, 1
        mov     [r10+24], rax
        mov     rdx, [r10+rax*8+32]
        test    rax, rax
        jnz     CALL
        sub     r9, 1
        mov     [r8+8], r9
        jmp     CALL
POPREC: sub     r9, 1
        mov     [r8+8], r9
        jmp     LH
CALL:   mov     r9, [rdx]
        call    r9
RP:     mov     rax, [rsp+24]
        test    rax, rax
        jnz     LH
        mov     r8d, 0x10000
        mov     r9, [r8]
        sub     r9, 1
        lea     r10, [r8+0x100]
        mov     r11, r9
        shl     r11, 5
        add     r10, r11
        mov     rax, [r10+24]
        test    eax, 2
        jz      LH
        mov     rsi, [rsp]
DROP:   mov     r9, [r8]
        test    r9, r9
        jz      DROPPED
        sub     r9, 1
        lea     r10, [r8+0x100]
        mov     r11, r9
        shl     r11, 5
        add     r10, r11
        mov     rax, [r10+16]
        cmp     rax, rsi
        ja      DROPPED
        mov     [r8], r9
        jmp     DROP
DROPPED: mov    qword ptr [r8+0x10], 0
        mov     rax, [rsp+32]
        test    rax, rax
        jz      RESUME
        mov     rcx, [rsp+40]
        movzx   edx, byte ptr [rcx]
        test    edx, edx
        jz      RESUME
        mov     qword ptr [r8+0x10], 1
        mov     [r8+0x18], rcx
        mov     rdx, [rsp+48]
        mov     [r8+0x20], rdx
RESUME: mov     rax, [rsp+16]
        mov     rdx, [rsp+8]
        sub     rdx, 8
        mov     rsp, rsi
        mov     rbp, rdx
        jmp     rax
FIN:    mov     rax, [rsp+24]
        cmp     rax, 2
        je      RETFIN
        mov     rcx, [rsp+8]
        mov     rsp, rcx
        lea     rax, [rip+RP]
        jmp     rax
RETFIN: add     rsp, 96
        ret
