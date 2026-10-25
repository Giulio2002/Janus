import Janus.Amd64.InstrSSE

/-!
# x86-64 AVX / AVX2 / FMA3 instructions: the AST (WP-F)

The VEX-encoded (`C4`/`C5`) vector instructions that `Janus.Amd64.DecodeAVX` decodes and
`Janus.Amd64.ExecAVX` executes, as one constructor of `Janus.Amd64.Instr` (`Instr.avx`), beyond
the moves and compares `memmove` and `internal/bytealg` use (`Instr.vmov`, `Instr.vop`,
`Instr.vptest`, `Instr.pmovmskb`, `Instr.vpbroadcastb`, `Instr.vzeroupper`, which keep their
constructors), the BMI1/BMI2 instructions and the scalar FMA3 forms (`Instr.vfmas`). Several VEX
encodings have exactly the meaning of an existing instruction and decode to it: the VEX moves
`VMOVUPS VMOVAPS VMOVUPD VMOVAPD VMOVNTPS VMOVNTPD VMOVNTDQA VLDDQU` are `Instr.vmov`;
`VANDPS/PD VORPS/PD VXORPS/PD` are `Instr.vop` (`VPAND`...) and `VPSHUFB`/`VPSIGNB` are
`Instr.vop .pshufb`/`.psignb` (already in-lane at 256 bits); and the forms that only write a
general register, the flags or memory are the legacy instruction (`VUCOMISS/SD`, `VCOMISS/SD`,
`VCVT(T)SS/SD2SI`, `VPEXTRB/W/D/Q`, `VEXTRACTPS`, `VMOVD/VMOVQ r/m, xmm`, `VMOVQ m64, xmm`,
`VMOVSS/SD m, xmm`, `VMOVLPS/HPS/LPD/HPD m64, xmm`, `VPCMPESTRI`/`VPCMPISTRI`).

Conventions (as in `Instr` and `InstrSSE`):

* `l` is the vector length in bits, `128` (`VEX.L0`, `XMM`) or `256` (`VEX.L1`, `YMM`).
* A VEX instruction writes the whole 256-bit register: a 128-bit result zeroes bits 255:128 of
  its destination (the **VEX.128 zero-upper rule**, SDM Vol. 1 §14.1.3), unlike legacy SSE,
  which preserves them (`Janus.Amd64.ExecAVX.setV`).
* The three-operand forms compute `dst ← op(src1, src2)`: `src1` is the `VEX.vvvv` register,
  `src2` the ModRM `r/m` operand (register or memory). Unless a constructor says otherwise, the
  256-bit form applies the 128-bit operation of WP-D (`Janus.Amd64.ExecSSE`) to each 128-bit lane
  (the SDM's in-lane definition of the AVX2 integer and shuffle instructions).
* A memory operand of a VEX instruction has no alignment requirement, except for the aligned
  moves (`Instr.vmov`).
* `e` is an element width in bits, `w` a floating-point element width (`32` = `PS`/`SS`,
  `64` = `PD`/`SD`).
-/

namespace Janus.Amd64

/-- Two-operand shuffles with an immediate, `dst ← op(src, imm8)`, in each 128-bit lane with
the same immediate (`VPERMILPD` uses bits `2j+1:2j` in lane `j`). -/
inductive VShufOp where
  /-- `VPSHUFD`. -/
  | pshufd
  /-- `VPSHUFLW`: words 0–3 selected, the high quadword copied. -/
  | pshuflw
  /-- `VPSHUFHW`: the low quadword copied, words 4–7 selected. -/
  | pshufhw
  /-- `VPERMILPS ..., imm8`: as `VPSHUFD`. -/
  | permilps
  /-- `VPERMILPD ..., imm8`: quadword `i` of lane `j` is quadword `imm8<2j+i>` of that lane. -/
  | permilpd
deriving Repr, DecidableEq, Inhabited

/-- The AVX2 variable shifts `VPSLLV`, `VPSRLV`, `VPSRAV`. -/
inductive VShiftOp where
  | sll | srl | sra
deriving Repr, DecidableEq, Inhabited

/-- The AVX/AVX2/FMA3 instructions of WP-F, over the operand types of `Instr` (`X = XLoc`,
`L = Loc`, `A = Addr`, as for `SseI`). -/
inductive AvxI (X L A : Type) where
  -- VEX forms of the WP-D packed integer instructions
  /-- `VPADDB ... VPMAXUD`, `VPUNPCK*`, `VPACK*`, `VPHADD*`, `VPSADBW`, `VPMADD*`, `VPAVG*`,
  `VPSIGNW/D`, `VPABS*` (`src1` unused), `VPANDN`, `VANDNPS/PD`, `VUNPCK*PS/PD`, `VMOVHLPS`/`VMOVLHPS`
  (128-bit register forms): `dst ← op(src1, src2)` per 128-bit lane. The shifts by a vector
  count (`VPSLLW/D/Q`, `VPSRLW/D/Q`, `VPSRAW/D ..., xmm/m128`) read a 128-bit count operand,
  which applies to both lanes. -/
  | pint (op : PIntOp) (l dst src1 : Nat) (src2 : X)
  /-- `VPSLLW/D/Q`, `VPSRLW/D/Q`, `VPSRAW/D`, `VPSLLDQ`, `VPSRLDQ (e = 128) dst, src, imm8`
  (`dst` is `VEX.vvvv`, `src` the ModRM register), per 128-bit lane. -/
  | pshift (op : PShiftOp) (e l dst src imm : Nat)
  /-- `VSHUFPS VSHUFPD VPALIGNR VPBLENDW VBLENDPS VBLENDPD VPBLENDD VMPSADBW` and the register
  form of `VINSERTPS` (128 only): `dst ← op(src1, src2, imm8)` per 128-bit lane. Lane `j` of the
  256-bit form reads the immediate bits the SDM assigns to it (`ExecAVX.laneImm`): `VSHUFPD`
  and `VBLENDPD` bits `2j+1:2j`, `VBLENDPS`/`VPBLENDD` bits `4j+3:4j`, `VMPSADBW` bits
  `3j+2:3j`; the others the same `imm8` in both lanes. -/
  | pimm (op : PImmOp) (l dst src1 : Nat) (src2 : X) (imm : Nat)
  /-- `VPSHUFD VPSHUFLW VPSHUFHW VPERMILPS VPERMILPD dst, src, imm8`. -/
  | shuf (op : VShufOp) (l dst : Nat) (src : X) (imm : Nat)
  /-- `VINSERTPS xmm1, xmm2, m32, imm8`: `src1` with the memory dword in dword `imm8<5:4>`, then
  the dwords of `imm8<3:0>` zeroed. -/
  | insertpsM (dst src1 : Nat) (a : A) (imm : Nat)
  /-- `VPBLENDVB` (`e = 8`), `VBLENDVPS` (`32`), `VBLENDVPD` (`64`) `dst, src1, src2, mask`
  (`mask` from `imm8<7:4>`): element `i` from `src2` iff the top bit of element `i` of `mask`. -/
  | blendv (e l dst src1 : Nat) (src2 : X) (mask : Nat)
  /-- `VPMOVSX` (`signed`) / `VPMOVZX` from `f`-bit to `t`-bit elements: the `l/t` low elements of
  the source (`m(l·f/t)` or a register) extended. -/
  | pmovx (signed : Bool) (f t l dst : Nat) (src : X)
  /-- `VPINSRB/W/D/Q dst, src1, r/m, imm8` (128 only): `src1` with element `imm8 mod (128/e)`
  replaced by the low `e` bits of the general operand. -/
  | pinsr (e dst src1 : Nat) (src : L) (imm : Nat)
  /-- `VMOVMSKPS` (`e = 32`) / `VMOVMSKPD` (`64`) `r, xmm/ymm`. -/
  | movmsk (e l dst src : Nat)
  /-- `VTESTPS` (`e = 32`) / `VTESTPD` (`64`) `a, b`: `ZF` = no element of `a AND b` has its
  sign bit set, `CF` = none of `b AND NOT a`; `AF OF PF SF` cleared. -/
  | vtest (e l a : Nat) (b : X)
  /-- `VMOVLPS/VMOVLPD` (`hi = false`) and `VMOVHPS/VMOVHPD` (`hi`) `xmm1, xmm2, m64`: `src1` with
  that quadword replaced by the memory quadword. -/
  | movHalfL (hi : Bool) (dst src1 : Nat) (a : A)
  /-- `VMOVDDUP` (in each lane), `VMOVSLDUP`, `VMOVSHDUP`. `VMOVDDUP xmm` reads an `m64`. -/
  | movdup (op : DupOp) (l dst : Nat) (src : X)
  /-- `VPHMINPOSUW xmm, xmm/m128`. -/
  | phminposuw (dst : Nat) (src : X)
  /-- `VPCMPESTRM` (`expl`) / `VPCMPISTRM xmm1, xmm2/m128, imm8`: the mask to `XMM0` (bits
  255:128 zeroed), the flags as `PCMPESTRM`. -/
  | pcmpstrm (expl w64 : Bool) (a : Nat) (b : X) (imm : Nat)
  -- packed floating point
  /-- `VADDPS ... VSQRTPD` (`sqrt`: `src1` unused). -/
  | fpArith (op : PFOp) (w l dst src1 : Nat) (src2 : X)
  /-- `VCMPPS/PD dst, src1, src2, pred` with the 32 VEX predicates (`pred < 32`). -/
  | fpCmp (w l dst src1 : Nat) (src2 : X) (pred : Nat)
  /-- `VROUNDPS/PD dst, src, imm8` (`imm8 < 16`). -/
  | fpRound (w l dst : Nat) (src : X) (imm : Nat)
  /-- `VHADDPS/PD` (`sub = false`), `VHSUBPS/PD`: adjacent pairs of `src1`, then of `src2`, in each
  128-bit lane. -/
  | fpHorz (sub : Bool) (w l dst src1 : Nat) (src2 : X)
  /-- `VADDSUBPS/PD`. -/
  | fpAddsub (w l dst src1 : Nat) (src2 : X)
  /-- The packed conversions at width `l`: `VCVTDQ2PS VCVT(T)PS2DQ` (`l` bits to `l` bits),
  `VCVTDQ2PD VCVTPS2PD` (`l/2` bits, a register or `m(l/2)`, to `l`), `VCVT(T)PD2DQ VCVTPD2PS`
  (`l` bits to `l/2` bits, written as a 128-bit result). -/
  | cvt (op : CvtOp) (l dst : Nat) (src : X)
  /-- Packed FMA3 `VFMADD/VFMSUB/VFNMADD/VFNMSUB/VFMADDSUB/VFMSUBADD 132/213/231 PS/PD`: per
  element as the scalar `Instr.vfmas` (`form`, the negations), single rounding (`FP.fma`).
  `alt = 0`: every element as `negC`; `alt = 1` (`FMADDSUB`): even elements subtract the addend,
  odd ones add it; `alt = 2` (`FMSUBADD`): even ones add, odd ones subtract. -/
  | fma (form : Nat) (negP negC : Bool) (alt : Nat) (w l dst src2 : Nat) (src3 : X)
  -- scalar floating point (VEX: `dst ← src1` with the low element replaced, bits 255:128 zeroed)
  /-- `VADDSD ... VSQRTSD` and the `SS` forms `dst, src1, src2` (`SQRT`: `√src2`). -/
  | sArith (op : PFOp) (w dst src1 : Nat) (src2 : X)
  /-- `VCMPSD/SS dst, src1, src2, pred` (`pred < 32`). -/
  | sCmp (w dst src1 : Nat) (src2 : X) (pred : Nat)
  /-- `VCVTSI2SD/SS dst, src1, r/m32` (`iw = 32`) or `r/m64` (`iw = 64`). -/
  | cvtsi2f (w iw dst src1 : Nat) (src : L)
  /-- `VCVTSD2SS` (`w = 64`, the source width) / `VCVTSS2SD` (`w = 32`) `dst, src1, src2`. -/
  | cvtff (w dst src1 : Nat) (src2 : X)
  /-- `VROUNDSD/SS dst, src1, src2, imm8` (`imm8 < 16`). -/
  | sRound (w dst src1 : Nat) (src2 : X) (imm : Nat)
  /-- `VMOVSD`/`VMOVSS xmm1, xmm2, xmm3`: `src1` with its low `w` bits from `src2`. -/
  | movsRR (w dst src1 src2 : Nat)
  /-- The zero-extending loads `VMOVSS`/`VMOVSD xmm, m` (`k = 4`/`8` bytes), `VMOVQ xmm,
  xmm/m64` (`k = 8`), `VMOVD xmm, m32`: the low `8k` bits of the source, zero-extended to 256. -/
  | vload (k dst : Nat) (src : X)
  /-- `VMOVD`/`VMOVQ xmm, r/m32/64` (`w = 32/64`): zero-extended to 256 bits. -/
  | movdG (w dst : Nat) (src : L)
  -- AVX2 permutes, broadcasts, masked moves, variable shifts, gathers
  /-- `VPERM2I128`/`VPERM2F128 ymm1, ymm2, ymm3/m256, imm8`: lane `j` of the result is lane
  `imm8<4j+1:4j>` of `src2:src1` (0, 1 from `src1`, 2, 3 from `src2`), or zero if `imm8<4j+3>`. -/
  | perm2 (dst src1 : Nat) (src2 : X) (imm : Nat)
  /-- `VPERMD`/`VPERMPS ymm1, ymm2, ymm3/m256`: dword `i` of the result is dword `idx[i] mod 8`
  of `src` (`idx` is `VEX.vvvv`). -/
  | permd (dst idx : Nat) (src : X)
  /-- `VPERMQ`/`VPERMPD ymm1, ymm2/m256, imm8`: quadword `i` is quadword `imm8<2i+1:2i>`. -/
  | permq (dst : Nat) (src : X) (imm : Nat)
  /-- `VPERMILPS` (`e = 32`) / `VPERMILPD` (`64`) `dst, src1, ctl` (variable form): element `i` is
  the element of `src1`'s lane selected by bits 1:0 (`PS`) or bit 1 (`PD`) of `ctl[i]`. -/
  | permilv (e l dst src1 : Nat) (ctl : X)
  /-- `VINSERTI128`/`VINSERTF128 ymm1, ymm2, xmm3/m128, imm8`: `src1` with lane `imm8<0>`
  replaced. -/
  | insert128 (dst src1 : Nat) (src2 : X) (imm : Nat)
  /-- `VEXTRACTI128`/`VEXTRACTF128 xmm1/m128, ymm2, imm8`: lane `imm8<0>` of `src`. -/
  | extract128 (dst : X) (src imm : Nat)
  /-- `VPBROADCASTB/W/D/Q`, `VBROADCASTSS/SD` (`e = 32/64`), `VBROADCASTI128/F128` (`e = 128`,
  memory only): the low `e` bits of `src` in every element. -/
  | bcast (e l dst : Nat) (src : X)
  /-- `VPMASKMOVD/Q` (`e = 32/64`), `VMASKMOVPS/PD`: with `load`, `x ← ` the elements of the
  memory operand whose `mask` element has its top bit set, the others zero; otherwise those
  elements of `x` are stored. Only the selected elements are accessed (and checked); the whole
  operand must lie in the canonical lower half (`< 2^47`), else the model faults. -/
  | maskmov (e l : Nat) (load : Bool) (x mask : Nat) (a : A)
  /-- `VPSLLVD/Q` (`sll`), `VPSRLVD/Q` (`srl`), `VPSRAVD` (`sra`) `dst, src1, src2`: element `i`
  of `src1` shifted by element `i` of `src2` (a count `≥ e`: zero, or the sign for `SRAV`). -/
  | shiftv (op : VShiftOp) (e l dst src1 : Nat) (src2 : X)
  /-- `VPGATHERDD/DQ/QD/QQ`, `VGATHERDPS/DPD/QPS/QPD dst, [base + idx·scale + disp], mask`:
  `e` the data and `ie` the index element width, `a` the VSIB operand (`a.index` is the vector
  index register). Element `j < n = l / max e ie` is loaded from `base + sext(idx[j]) · 2^scale +
  disp` iff the top bit of `mask[j]`; then the mask register is zeroed. -/
  | gather (e ie l dst mask : Nat) (a : A)
  /-- F16C `VCVTPH2PS xmm/ymm, xmm/m64/m128`: the `l/32` low binary16 elements of `src` to
  binary32 (exact). -/
  | cvtph2ps (l dst : Nat) (src : X)
  /-- F16C `VCVTPS2PH xmm/m64/m128, xmm/ymm, imm8`: the `l/32` binary32 elements of `src` to
  binary16, rounded by `imm8<1:0>` or, if `imm8<2>`, `MXCSR.RC`. -/
  | cvtps2ph (l : Nat) (dst : X) (src imm : Nat)
  /-- `VZEROALL`: `YMM0`–`YMM15` become 0. -/
  | vzeroall
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64
