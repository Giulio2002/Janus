/-!
# x86-64 SSE packed instructions: the AST (WP-D)

The legacy-encoded (non-VEX) SSE2, SSE3, SSSE3, SSE4.1 and SSE4.2 instructions on `XMM` that
`Janus.Amd64.DecodeSSE` decodes and `Janus.Amd64.ExecSSE` executes, as one constructor of
`Janus.Amd64.Instr` (`Instr.sse`). The instructions that existed before (`MOVUPS`..., `PXOR`,
`PAND`, `POR`, `PCMPEQB`, `PUNPCKLBW`, `PSHUFB`, `PSIGNB`, `PSHUFD`, `PSHUFLW`, `PMOVMSKB`,
`MOVD`/`MOVQ`, the scalar floating point, `ANDPS`/`ANDNPS`/`ORPS`/`XORPS`, `ROUNDSD/SS`) keep
their constructors in `Instr`; a few new encodings with the same meaning decode to those
(`MOVNTDQ`/`MOVNTPS`/`MOVNTPD` and `MOVNTDQA` are aligned `sseMov`, `LDDQU` is an unaligned
one).

Conventions (as in `Instr`): `XMMn` is register `n ∈ 0..15`; a source operand is an `XLoc`
(register or memory operand); vector values are naturals `< 2^128` with element `i` of width
`e` at bits `e*(i+1)-1 : e*i` (`Janus.Arm64.elem`). Element widths `e` are bits (`8 16 32 64`).
Every instruction here is legacy SSE: it writes bits 127:0 of its `XMM` destination and
preserves bits 255:128 (`ymmHi`).

**Memory operands.** A 128-bit memory operand must be 16-byte aligned (`#GP` otherwise,
`Fault.misaligned`), except for the SSE4.2 string instructions (`PCMPESTRI`...), which do not
check alignment. Narrower memory operands (`m64` of `CVTDQ2PD`/`CVTPS2PD`/`MOVDDUP`/`MOVLPS`...,
the `PMOVSX`/`PMOVZX` sources, `PINSR*`/`PEXTR*`, `INSERTPS m32`) have no alignment requirement.
-/

namespace Janus.Amd64

/-- Packed-integer (and bitwise) two-operand operations, `XMM[dst] ← op(XMM[dst], src)`.
`e` is the element width in bits. -/
inductive PIntOp where
  /-- `PADDB/W/D/Q` (wrapping). -/
  | add (e : Nat)
  /-- `PSUBB/W/D/Q` (wrapping). -/
  | sub (e : Nat)
  /-- `PADDSB/W` (signed saturation). -/
  | adds (e : Nat)
  /-- `PADDUSB/W` (unsigned saturation). -/
  | addus (e : Nat)
  /-- `PSUBSB/W`. -/
  | subs (e : Nat)
  /-- `PSUBUSB/W`. -/
  | subus (e : Nat)
  /-- `PMULLW` (low 16 bits of the product), `PMULLD` (`e = 32`, low 32 bits). -/
  | mull (e : Nat)
  /-- `PMULHW` (signed) / `PMULHUW` (`unsigned`): the high 16 bits of the 32-bit product. -/
  | mulh (unsigned : Bool)
  /-- `PMULUDQ` / `PMULDQ` (`signed`, SSE4.1): the 64-bit products of the even dwords. -/
  | muldq (signed : Bool)
  /-- `PMADDWD`: the sums of adjacent signed word products, as dwords (wrapping). -/
  | maddwd
  /-- `PMADDUBSW` (SSSE3): unsigned destination bytes times signed source bytes, adjacent pairs
  added with signed word saturation. -/
  | maddubsw
  /-- `PMULHRSW` (SSSE3): `((a * b >> 14) + 1) >> 1` of signed words. -/
  | mulhrsw
  /-- `PCMPEQB/W/D/Q`: all ones where equal. -/
  | cmpeq (e : Nat)
  /-- `PCMPGTB/W/D/Q`: all ones where the destination element is greater (signed). -/
  | cmpgt (e : Nat)
  /-- `PANDN`, `ANDNPS`: `NOT dst AND src`. -/
  | andn
  /-- `PUNPCKLBW/WD/DQ/QDQ`, `UNPCKLPS` (`32`), `UNPCKLPD` and `MOVLHPS` (`64`): interleave the
  low halves, destination element first. -/
  | unpckl (e : Nat)
  /-- `PUNPCKHBW/WD/DQ/QDQ`, `UNPCKHPS`, `UNPCKHPD`: interleave the high halves. -/
  | unpckh (e : Nat)
  /-- `PACKSSWB` (`e = 16`) / `PACKSSDW` (`32`): signed saturation of the destination's, then
  the source's, `e`-bit elements to `e/2` bits. -/
  | packss (e : Nat)
  /-- `PACKUSWB` (`16`) / `PACKUSDW` (`32`, SSE4.1): unsigned saturation of signed elements. -/
  | packus (e : Nat)
  /-- `PMINUB`, `PMINUW`, `PMINUD` (unsigned minimum). -/
  | minu (e : Nat)
  /-- `PMINSB`, `PMINSW`, `PMINSD` (signed minimum). -/
  | mins (e : Nat)
  /-- `PMAXUB`, `PMAXUW`, `PMAXUD`. -/
  | maxu (e : Nat)
  /-- `PMAXSB`, `PMAXSW`, `PMAXSD`. -/
  | maxs (e : Nat)
  /-- `PSADBW`: per 64-bit half, the sum of the absolute byte differences (in its low 16 bits). -/
  | sadbw
  /-- `PAVGB/W`: `(a + b + 1) >> 1`, unsigned. -/
  | avg (e : Nat)
  /-- `PSLLW/D/Q xmm, xmm/m128`: shift left by the low 64 bits of the source (≥ `e`: zero). -/
  | sll (e : Nat)
  /-- `PSRLW/D/Q xmm, xmm/m128` (logical). -/
  | srl (e : Nat)
  /-- `PSRAW/D xmm, xmm/m128` (arithmetic; a count ≥ `e` fills with the sign). -/
  | sra (e : Nat)
  /-- `PHADDW/D` (SSSE3): adjacent pairs of the destination, then of the source, added. -/
  | hadd (e : Nat)
  /-- `PHSUBW/D`: `even - odd` of adjacent pairs. -/
  | hsub (e : Nat)
  /-- `PHADDSW`: as `hadd 16` with signed saturation. -/
  | hadds
  /-- `PHSUBSW`. -/
  | hsubs
  /-- `PSIGNW/D` (SSSE3; `PSIGNB` is `SseOp.psignb`). -/
  | sign (e : Nat)
  /-- `PABSB/W/D` (SSSE3): the absolute value of each source element (the destination is not
  read). -/
  | abs (e : Nat)
  /-- `MOVHLPS xmm, xmm`: the low quadword becomes the source's high quadword. -/
  | movhl
deriving Repr, DecidableEq, Inhabited

/-- Shifts of a register by an immediate (group 12/13/14, `66 0F 71/72/73`). -/
inductive PShiftOp where
  /-- `PSLLW/D/Q xmm, imm8`. -/
  | sll
  /-- `PSRLW/D/Q xmm, imm8`. -/
  | srl
  /-- `PSRAW/D xmm, imm8`. -/
  | sra
  /-- `PSLLDQ xmm, imm8`: the whole register left by `imm8` bytes (`> 15`: zero). -/
  | slldq
  /-- `PSRLDQ xmm, imm8`. -/
  | srldq
deriving Repr, DecidableEq, Inhabited

/-- Two-operand operations with an immediate, `XMM[dst] ← op(XMM[dst], src, imm8)`. -/
inductive PImmOp where
  /-- `SHUFPS`: dwords 0, 1 from the destination, 2, 3 from the source, selected by `imm8`. -/
  | shufps
  /-- `SHUFPD`: quadword 0 from the destination (`imm8<0>`), 1 from the source (`imm8<1>`). -/
  | shufpd
  /-- `PALIGNR` (SSSE3): bytes `imm8 ..` of the 32-byte concatenation `dst:src`. -/
  | palignr
  /-- `PBLENDW` (SSE4.1): word `i` from the source iff `imm8<i>`. -/
  | pblendw
  /-- `BLENDPS` (SSE4.1): dword `i` from the source iff `imm8<i>` (`imm8<7:4>` ignored). -/
  | blendps
  /-- `BLENDPD`: quadword `i` from the source iff `imm8<i>` (`imm8<7:2>` ignored). -/
  | blendpd
  /-- `PSHUFHW` (`F3 0F 70`): the low quadword of the source, then its high words selected. -/
  | pshufhw
  /-- `MPSADBW` (SSE4.1): eight sums of absolute differences of 4-byte blocks. -/
  | mpsadbw
  /-- `INSERTPS` (SSE4.1) register form: dword `imm8<7:6>` of the source into dword
  `imm8<5:4>`, then the dwords of `imm8<3:0>` zeroed. -/
  | insertps
deriving Repr, DecidableEq, Inhabited

/-- Packed conversions. -/
inductive CvtOp where
  /-- `CVTDQ2PS`: four `int32` to `binary32` (rounded by `MXCSR.RC`). -/
  | dq2ps
  /-- `CVTPS2DQ` (`MXCSR.RC`) / `CVTTPS2DQ` (`trunc`): four `binary32` to `int32`. -/
  | ps2dq (trunc : Bool)
  /-- `CVTDQ2PD`: the low two `int32` (an `m64` source) to `binary64` (exact). -/
  | dq2pd
  /-- `CVTPD2DQ` / `CVTTPD2DQ`: two `binary64` to `int32`, the upper quadword zeroed. -/
  | pd2dq (trunc : Bool)
  /-- `CVTPS2PD`: the low two `binary32` (an `m64` source) to `binary64`. -/
  | ps2pd
  /-- `CVTPD2PS`: two `binary64` to `binary32`, the upper quadword zeroed. -/
  | pd2ps
deriving Repr, DecidableEq, Inhabited

/-- Duplicating moves (SSE3). -/
inductive DupOp where
  /-- `MOVDDUP xmm, xmm/m64`: the low quadword in both halves. -/
  | ddup
  /-- `MOVSLDUP`: dwords `0 0 2 2` of the source. -/
  | sldup
  /-- `MOVSHDUP`: dwords `1 1 3 3`. -/
  | shdup
deriving Repr, DecidableEq, Inhabited

/-- The packed floating-point arithmetic operations (`ADDPS` ... `SQRTPD`). -/
inductive PFOp where
  | add | sub | mul | div | min | max | sqrt
deriving Repr, DecidableEq, Inhabited

/-- The legacy-SSE packed instructions of WP-D, over the operand types of `Instr` (`X = XLoc`,
`L = Loc`, `A = Addr`; the parameters only break the import cycle with `Janus.Amd64.Instr`, which
uses `SseI XLoc Loc Addr`). `w` is the floating-point element width (`32` for the `PS` forms,
`64` for `PD`). -/
inductive SseI (X L A : Type) where
  /-- `XMM[dst] ← op(XMM[dst], src)`, `src` an aligned `m128` or a register. -/
  | pint (op : PIntOp) (dst : Nat) (src : X)
  /-- `PSLLW/D/Q`, `PSRLW/D/Q`, `PSRAW/D xmm, imm8` (element width `e`) and `PSLLDQ`/`PSRLDQ`
  (`e = 128`): register only. -/
  | pshift (op : PShiftOp) (e : Nat) (dst : Nat) (imm : Nat)
  /-- `XMM[dst] ← op(XMM[dst], src, imm8)`, `src` an aligned `m128` or a register. -/
  | pimm (op : PImmOp) (dst : Nat) (src : X) (imm : Nat)
  /-- `INSERTPS xmm, m32, imm8`: the memory dword into dword `imm8<5:4>`, then `imm8<3:0>`
  zeroed (`imm8<7:6>` ignored). -/
  | insertpsM (dst : Nat) (a : A) (imm : Nat)
  /-- `PBLENDVB` (`e = 8`), `BLENDVPS` (`32`), `BLENDVPD` (`64`) `xmm, xmm/m128, <XMM0>`: element
  `i` from the source iff the top bit of element `i` of `XMM0` is set. -/
  | blendv (e : Nat) (dst : Nat) (src : X)
  /-- `PMOVSX` (`signed`) / `PMOVZX` (SSE4.1) from `f`-bit to `t`-bit elements: the `128/t`
  low elements of the source (`m(16·f/t)` or a register) extended. -/
  | pmovx (signed : Bool) (f t : Nat) (dst : Nat) (src : X)
  /-- `PINSRB` (`e = 8`), `PINSRW` (`16`), `PINSRD` (`32`), `PINSRQ` (`64`) `xmm, r/m, imm8`:
  element `imm8 mod (128/e)` becomes the low `e` bits of the general register or the `e/8`
  bytes of memory. -/
  | pinsr (e : Nat) (dst : Nat) (src : L) (imm : Nat)
  /-- `PEXTRB/W/D/Q` and `EXTRACTPS` (`e = 32`) `r/m, xmm, imm8`: element `imm8 mod (128/e)` of
  `XMM[src]`, zero-extended into a 64-bit register or stored as `e/8` bytes. -/
  | pextr (e : Nat) (dst : L) (src : Nat) (imm : Nat)
  /-- `MOVMSKPS` (`e = 32`) / `MOVMSKPD` (`64`) `r, xmm`: bit `i` is the sign of element `i`,
  zero-extended. -/
  | movmsk (e : Nat) (dst : Nat) (src : Nat)
  /-- `PTEST xmm, xmm/m128` (SSE4.1): `ZF = (a AND b = 0)`, `CF = (b AND NOT a = 0)`, `AF OF PF
  SF` cleared. -/
  | ptest (a : Nat) (b : X)
  /-- `MOVLPS`/`MOVLPD` (`hi = false`) and `MOVHPS`/`MOVHPD` (`hi`): `load` replaces that
  quadword of `XMM[x]` with the `m64`, else the quadword is stored. -/
  | movHalf (hi load : Bool) (x : Nat) (a : A)
  /-- `MOVDDUP`, `MOVSLDUP`, `MOVSHDUP` (SSE3). -/
  | movdup (op : DupOp) (dst : Nat) (src : X)
  /-- `MOVNTI m32/m64, r` (`0F C3`): store the low `w` bits of the register (the non-temporal
  hint does not change the single-threaded result). -/
  | movnti (w : Nat) (a : A) (r : Nat)
  /-- `PHMINPOSUW` (SSE4.1): the minimum unsigned word of the source and the lowest index
  holding it, in bits 15:0 and 18:16; the rest zeroed. -/
  | phminposuw (dst : Nat) (src : X)
  /-- `CRC32 r32/r64, r/m8/16/32/64` (SSE4.2): `dst` (its low 32 bits) updated with the `w`
  bits of `src` by CRC-32C (Castagnoli polynomial `11EDC6F41H`, bit-reflected), the result
  zero-extended to 64 bits. -/
  | crc32 (w : Nat) (dst : Nat) (src : L)
  /-- `PCMPESTRI` (`expl`, `index`), `PCMPESTRM` (`expl`), `PCMPISTRI` (`index`),
  `PCMPISTRM` `xmm1, xmm2/m128, imm8` (SSE4.2, no alignment requirement). `w64` is `REX.W`:
  the explicit lengths come from `RAX`/`RDX` instead of `EAX`/`EDX`. The index goes to `ECX`
  (zero-extended), the mask to `XMM0`. -/
  | pcmpstr (expl index w64 : Bool) (a : Nat) (b : X) (imm : Nat)
  -- packed floating point (on the IEEE core, `Janus.Amd64.FP`)
  /-- `ADDPS/PD SUBPS/PD MULPS/PD DIVPS/PD MINPS/PD MAXPS/PD SQRTPS/PD xmm, xmm/m128`. -/
  | fpArith (op : PFOp) (w : Nat) (dst : Nat) (src : X)
  /-- `CMPPS/PD xmm, xmm/m128, pred` (`pred < 8`). -/
  | fpCmp (w : Nat) (dst : Nat) (src : X) (pred : Nat)
  /-- `ROUNDPS/PD xmm, xmm/m128, imm8` (SSE4.1, `imm8 < 16`). -/
  | fpRound (w : Nat) (dst : Nat) (src : X) (imm : Nat)
  /-- `HADDPS/PD` (`sub = false`) and `HSUBPS/PD` (SSE3): adjacent pairs of the destination,
  then of the source. -/
  | fpHorz (sub : Bool) (w : Nat) (dst : Nat) (src : X)
  /-- `ADDSUBPS/PD` (SSE3): even elements subtracted, odd elements added. -/
  | fpAddsub (w : Nat) (dst : Nat) (src : X)
  /-- The packed conversions. -/
  | cvt (op : CvtOp) (dst : Nat) (src : X)
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64
