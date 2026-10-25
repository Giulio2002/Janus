#include "textflag.h"

// func vCount(p *byte, n uint64, c byte) uint64
//
// ABI0 shim: loads the arguments into the AAPCS64 argument registers (X0 = p, X1 = n,
// W2 = c), calls vCountC, and stores its X0 result.
TEXT ·vCount(SB), NOSPLIT, $16-32
	MOVD	p+0(FP), R0
	MOVD	n+8(FP), R1
	MOVBU	c+16(FP), R2
	BL	·vCountC(SB)
	MOVD	R0, ret+24(FP)
	RET

// vCountC is, word for word, what gcc 15.2.0 (Ubuntu 15.2.0-16ubuntu1, aarch64-linux-gnu)
// emits at cgo's default -O2 (with -fPIC -pthread -g) for
//
//	size_t v_count(const uint8_t *p, size_t n, uint8_t c)
//	{ size_t k = 0; for (size_t i = 0; i < n; i++) k += p[i] == c; return k; }
//
// (scripts/coverage/ccorpus/vec.c). The comments are objdump's disassembly, offsets from the
// start of vCountC. The vectoriser turns the loop into a 16-byte loop
// (CMEQ, AND with 1, ZIP1/ZIP2 widening to 64-bit lanes, UADDW/UADDW2 accumulation, ADDP)
// followed by a scalar loop over the last n mod 16 bytes. Every branch in it is PC-relative
// and internal, so the words run unchanged here; they follow the AAPCS64 (arguments in
// X0-X2, result in X0, X30 the return address).
TEXT ·vCountC(SB), NOSPLIT|NOFRAME, $0-0
	WORD	$0x4f00041d	//    0: movi   v29.4s, #0x0
	WORD	$0xaa0003e5	//    4: mov    x5, x0
	WORD	$0x12001c42	//    8: and    w2, w2, #0xff
	WORD	$0xb40005a1	//    c: cbz    x1, c0 <v_count+0xc0>
	WORD	$0xd1000420	//   10: sub    x0, x1, #0x1
	WORD	$0xf100381f	//   14: cmp    x0, #0xe
	WORD	$0x54000589	//   18: b.ls   c8 <v_count+0xc8>
	WORD	$0x927cec23	//   1c: and    x3, x1, #0xfffffffffffffff0
	WORD	$0x4e010c57	//   20: dup    v23.16b, w2
	WORD	$0x4f00041a	//   24: movi   v26.4s, #0x0
	WORD	$0xaa0503e4	//   28: mov    x4, x5
	WORD	$0x4f00e438	//   2c: movi   v24.16b, #0x1
	WORD	$0x8b0300a0	//   30: add    x0, x5, x3
	WORD	$0xd503201f	//   34: nop    
	WORD	$0xd503201f	//   38: nop    
	WORD	$0xd503201f	//   3c: nop    
	WORD	$0x3cc1049f	//   40: ldr    q31, [x4], #16
	WORD	$0x6e378fff	//   44: cmeq   v31.16b, v31.16b, v23.16b
	WORD	$0x4e381fff	//   48: and    v31.16b, v31.16b, v24.16b
	WORD	$0x4e1d3bfb	//   4c: zip1   v27.16b, v31.16b, v29.16b
	WORD	$0x4e1d7bff	//   50: zip2   v31.16b, v31.16b, v29.16b
	WORD	$0x4e5d3b7c	//   54: zip1   v28.8h, v27.8h, v29.8h
	WORD	$0x4e5d7b7b	//   58: zip2   v27.8h, v27.8h, v29.8h
	WORD	$0x4e5d3bf9	//   5c: zip1   v25.8h, v31.8h, v29.8h
	WORD	$0x4e5d7bff	//   60: zip2   v31.8h, v31.8h, v29.8h
	WORD	$0x4e9d7b9e	//   64: zip2   v30.4s, v28.4s, v29.4s
	WORD	$0x2ebc13de	//   68: uaddw  v30.2d, v30.2d, v28.2s
	WORD	$0x4e9d7b7c	//   6c: zip2   v28.4s, v27.4s, v29.4s
	WORD	$0x2eb913de	//   70: uaddw  v30.2d, v30.2d, v25.2s
	WORD	$0x2ebb139c	//   74: uaddw  v28.2d, v28.2d, v27.2s
	WORD	$0x2ebf13de	//   78: uaddw  v30.2d, v30.2d, v31.2s
	WORD	$0x6eb9139c	//   7c: uaddw2 v28.2d, v28.2d, v25.4s
	WORD	$0x6ebf139f	//   80: uaddw2 v31.2d, v28.2d, v31.4s
	WORD	$0x4eff87df	//   84: add    v31.2d, v30.2d, v31.2d
	WORD	$0x4eff875a	//   88: add    v26.2d, v26.2d, v31.2d
	WORD	$0xeb00009f	//   8c: cmp    x4, x0
	WORD	$0x54fffd81	//   90: b.ne   40 <v_count+0x40>
	WORD	$0x5ef1bb5f	//   94: addp   d31, v26.2d
	WORD	$0x9e6603e0	//   98: fmov   x0, d31
	WORD	$0xeb01007f	//   9c: cmp    x3, x1
	WORD	$0x540000e0	//   a0: b.eq   bc <v_count+0xbc>
	WORD	$0x386368a4	//   a4: ldrb   w4, [x5, x3]
	WORD	$0x91000463	//   a8: add    x3, x3, #0x1
	WORD	$0x6b02009f	//   ac: cmp    w4, w2
	WORD	$0x9a801400	//   b0: cinc   x0, x0, eq
	WORD	$0xeb03003f	//   b4: cmp    x1, x3
	WORD	$0x54ffff68	//   b8: b.hi   a4 <v_count+0xa4>
	WORD	$0xd65f03c0	//   bc: ret    
	WORD	$0xd2800000	//   c0: mov    x0, #0x0                   
	WORD	$0xd65f03c0	//   c4: ret    
	WORD	$0xd2800003	//   c8: mov    x3, #0x0                   
	WORD	$0xd2800000	//   cc: mov    x0, #0x0                   
	WORD	$0x17fffff5	//   d0: b      a4 <v_count+0xa4>
