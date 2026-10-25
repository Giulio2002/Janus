import Janus.Amd64.InstrAVX

/-!
# x86-64 AVX-512 instructions: the AST (WP-G)

The EVEX-encoded (`62`) vector instructions that `Janus.Amd64.DecodeEVEX` decodes and
`Janus.Amd64.ExecEVEX` executes, the VEX-encoded opmask instructions (`KMOV*`, `KAND*`, ...) and
the VEX forms of `VPCLMULQDQ` and the GFNI instructions, as one constructor of
`Janus.Amd64.Instr` (`Instr.evex`).

Conventions (as in `Instr`, `InstrSSE` and `InstrAVX`):

* Vector registers are numbered `0..31` (`ZMM0`–`ZMM31`; `16..31` only reachable with EVEX).
  `l` is the vector length in bits, `128`, `256` or `512` (`EVEX.L'L`). An EVEX instruction writes
  bits `l-1:0` of its destination and **zeroes bits 511:`l`** (the EVEX zero-upper rule, as for
  VEX; `ExecEVEX.setZ`).
* `k` is the write-mask register (`EVEX.aaa`): `0` means no masking, `1..7` the opmask registers
  `K1`–`K7`. `z` is zeroing-masking (`{z}`): a masked-off element is zeroed; otherwise
  (merging-masking) it keeps the destination's old value. `e` is the masking granularity (the
  element width in bits): element `i` of the destination is written iff bit `i` of `K[k]` is set.
* `bc` is embedded broadcast (`EVEX.b` with a memory operand, `{1toN}`): `0` for none, otherwise
  the width in bits of the one memory element that is replicated to every element of the
  operand.
* The three-operand forms compute `dst ← op(src1, src2)` with `src1` the `EVEX.vvvv` register
  (`EVEX.V'` its fifth bit) and `src2` the ModRM `r/m` operand.
* Memory operands are unaligned except for the aligned moves (`VMOVDQA32/64`, `VMOVAPS/PD`:
  `l/8`-byte aligned, whatever the mask). Element-wise instructions with a write mask access
  only the selected elements of a full-width memory operand (**fault suppression**, SDM Vol. 2
  §2.8: exception classes `E2`, `E4` and the moves); the others (`E4NF`, the shuffles, permutes,
  `VPCLMULQDQ`, GFNI, inserts, extracts) access the whole operand (`EOp.suppress`).
-/

namespace Janus.Amd64

/-- The bitwise operations of `VPANDD/Q`, `VPANDND/Q`, `VPORD/Q`, `VPXORD/Q` (and the `PS`/`PD`
forms of AVX512DQ). `andn` is `NOT src1 AND src2`. -/
inductive ELogic where
  | and | andn | or | xor
deriving Repr, DecidableEq, Inhabited

/-- The operations of `EvexI.op`: `dst ← op(old dst, src1, src2)` element by element (or 128-bit
lane by lane), then masked. -/
inductive EOp where
  /-- WP-D's packed integer operation on each 128-bit lane (`ExecSSE.pintOp`): `VPADD*`, `VPSUB*`,
  saturating, `VPMIN*`/`VPMAX*` (also at 64 bits: `VPMINUQ`...), `VPMULL*` (`VPMULLQ`), `VPMULH*`,
  `VPMULUDQ`/`VPMULDQ`, `VPMADD*`, `VPSADBW`, `VPAVG*`, `VPUNPCK*`, `VPACK*`, `VPABS*` (`src1`
  unused), the shifts by an `xmm/m128` count (`VPSLLW ..., VPSRAQ`, the count applying to every
  lane). -/
  | pint (op : PIntOp)
  /-- `VPANDD/Q`... -/
  | logic (op : ELogic)
  /-- `VPSHUFB` (in each 128-bit lane). -/
  | shufb
  /-- `VPTERNLOGD/Q`: bit `j` of the result is bit `4·dst_j + 2·src1_j + src2_j` of `imm8`. -/
  | ternlog (imm : Nat)
  /-- `VPERMB/W/D/Q dst, idx, src`: element `i` is element `idx[i] mod n` of `src2` (`src1` is the
  index vector). -/
  | perm
  /-- `VPERMI2B/W/D/Q`: the destination holds the indices; element `i` is element `idx mod 2n` of
  the table `src2:src1` (`src1` low). Merging-masking keeps the index. -/
  | permi2
  /-- `VPERMT2B/W/D/Q`: `src1` holds the indices; the table is `src2:dst` (`dst` low).
  Merging-masking keeps the table. -/
  | permt2
  /-- `VGF2P8AFFINEQB` / `VGF2P8AFFINEINVQB` (`inv`): byte `b` of quadword `j` is the affine
  transformation, by the 8×8 bit matrix quadword `j` of `src2`, of byte `b` of `src1` (or of its
  inverse in GF(2⁸) for `inv`), `XOR imm8`. -/
  | gfaffine (inv : Bool) (imm : Nat)
  /-- `VGF2P8MULB`: the bytes multiplied in GF(2⁸) modulo `x⁸ + x⁴ + x³ + x + 1`. -/
  | gfmul
  /-- `VPOPCNTB/W/D/Q`: the number of one bits of each element of `src2` (`src1` unused). -/
  | popcnt
  /-- `VPSLLVW/D/Q`, `VPSRLVW/D/Q`, `VPSRAVW/D/Q`. -/
  | shiftv (op : VShiftOp)
  /-- `VPROLVD/Q` (`left`), `VPRORVD/Q`: element `i` of `src1` rotated by element `i` of `src2`
  modulo `e`. -/
  | rotv (left : Bool)
  /-- `VPALIGNR`: in each 128-bit lane, bytes `imm8 .. imm8+15` of `src1:src2` (`src2` low). -/
  | alignr (imm : Nat)
  /-- `VALIGND/Q`: elements `imm8 mod n .. +n-1` of `src1:src2` (`src2` low), across the whole
  vector. -/
  | align (imm : Nat)
  /-- `VSHUFI32X4/64X2`, `VSHUFF32X4/64X2`: 128-bit chunk `j` of the result is chunk `sel_j` of
  `src1` for the low half of the chunks and of `src2` for the high half (`sel_j` the 1 or 2 bits
  of `imm8` for chunk `j`). -/
  | shuf128 (imm : Nat)
  /-- `VPCLMULQDQ` (EVEX and VEX): in each 128-bit lane, the carry-less product of quadword
  `imm8<0>` of `src1` and quadword `imm8<4>` of `src2`. Never masked. -/
  | clmul (imm : Nat)
deriving Repr, DecidableEq, Inhabited

/-- The one-source operations with an immediate of `EvexI.uop`: `dst ← op(src, imm8)`. -/
inductive EUOp where
  /-- `VPSLLW/D/Q`, `VPSRLW/D/Q`, `VPSRAW/D/Q ..., imm8` and `VPSLLDQ`/`VPSRLDQ` per 128-bit lane
  (WP-D's `ExecSSE.pshiftOp`; `dst` is `EVEX.vvvv`, the source the `r/m` operand). -/
  | shift (op : PShiftOp)
  /-- `VPROLD/Q` (`left`), `VPRORD/Q ..., imm8`: every element rotated by `imm8 mod e`. -/
  | rot (left : Bool)
  /-- `VPSHUFD`, `VPSHUFLW`, `VPSHUFHW` per 128-bit lane (`ExecAVX.shufLane`). -/
  | shuf (op : VShufOp)
  /-- `VPERMQ`/`VPERMPD ..., imm8`: in each 256-bit half, quadword `i` is quadword `imm8<2i+1:2i>`
  of that half. -/
  | permq
deriving Repr, DecidableEq, Inhabited

/-- The comparisons into a mask register of `EvexI.cmp`. -/
inductive ECmp where
  /-- `VPCMPB/W/D/Q` (`signed`) and `VPCMPUB/UW/UD/UQ` with predicate `imm8<2:0>` (`EQ LT LE
  FALSE NE NLT NLE TRUE`); `VPCMPEQ*` is predicate 0 and `VPCMPGT*` signed predicate 6. -/
  | int (signed : Bool) (pred : Nat)
  /-- `VPTESTMB/W/D/Q` (`neg = false`: `src1 AND src2 ≠ 0`) and `VPTESTNM*` (`= 0`). -/
  | test (neg : Bool)
  /-- `VCMPPS/PD` with the 32 predicates (`ExecAVX.vcmp`), `sae`: `{sae}` (no flags, no traps). -/
  | fp (pred : Nat) (sae : Bool)
deriving Repr, DecidableEq, Inhabited

/-- The binary opmask operations (`KANDB/W/D/Q`...). `andn` is `NOT src1 AND src2`. -/
inductive KOp where
  | and | andn | or | xor | xnor | add
deriving Repr, DecidableEq, Inhabited

/-- An opmask operand of `KMOV*`: a mask register, a general register (low `w` bits) or memory. -/
inductive KLoc (A : Type) where
  | k (n : Nat)
  | gpr (r : Nat)
  | mem (a : A)
deriving Repr, DecidableEq, Inhabited

/-- The AVX-512 instructions of WP-G, over the operand types of `Instr` (`X = XLoc`, `L = Loc`,
`A = Addr`, as for `SseI` and `AvxI`). -/
inductive EvexI (X L A : Type) where
  /-- `VMOVDQU8/16/32/64`, `VMOVDQA32/64` (`al`), `VMOVUPS/PD`, `VMOVAPS/PD` (`al`): register to
  register, load (`src` memory) or store (`dst` memory; only the selected elements are written,
  `z = false`). -/
  | mov (e l : Nat) (al : Bool) (dst src : X) (k : Nat) (z : Bool)
  /-- `dst ← op(dst, src1, src2)` (`EOp`), masked at `e` bits. -/
  | op (o : EOp) (e l d s1 : Nat) (src2 : X) (bc k : Nat) (z : Bool)
  /-- `dst ← op(src, imm8)` (`EUOp`), masked at `e` bits. -/
  | uop (o : EUOp) (e l d : Nat) (src : X) (bc imm k : Nat) (z : Bool)
  /-- `VPBLENDMB/W/D/Q`, `VBLENDMPS/PD`: element `i` is `src2`'s where `K[k]` (or no mask) selects
  it, otherwise `src1`'s (or zero, `z`). -/
  | blendm (e l d s1 : Nat) (src2 : X) (bc k : Nat) (z : Bool)
  /-- A comparison into the mask register `kd`: bit `i < l/e` is the comparison of element `i`
  ANDed with bit `i` of `K[k]` (`k ≠ 0`); bits 63:`l/e` are zeroed. -/
  | cmp (c : ECmp) (e l kd s1 : Nat) (src2 : X) (bc k : Nat)
  /-- `VPCOMPRESSB/W/D/Q dst, src`: the selected elements of `src`, packed into the low elements of
  `dst`; in a register the rest is zeroed (`z`) or kept, in memory only the packed elements are
  written. -/
  | compress (e l : Nat) (dst : X) (src k : Nat) (z : Bool)
  /-- `VPEXPANDB/W/D/Q dst, src`: the consecutive low elements of `src` (only as many as are
  selected are read from memory) to the selected elements of `dst`. -/
  | expand (e l d : Nat) (src : X) (k : Nat) (z : Bool)
  /-- `VEXTRACTF/I32X4/64X2/32X8/64X4 dst, src, imm8`: the `c`-bit chunk `imm8 mod (l/c)` of `src`,
  masked at `e` bits, to an `xmm`/`ymm` register (bits 511:`c` zeroed) or to memory. -/
  | extract (e l c : Nat) (dst : X) (src imm k : Nat) (z : Bool)
  /-- `VINSERTF/I32X4/64X2/32X8/64X4 dst, src1, src2, imm8`: `src1` with the `c`-bit chunk
  `imm8 mod (l/c)` replaced by `src2`. -/
  | insert (e l c d s1 : Nat) (src2 : X) (imm k : Nat) (z : Bool)
  /-- `VPBROADCASTB/W/D/Q`, `VBROADCASTSS/SD` (`c = e`), `VBROADCASTI32X4/64X2/32X8/64X4` (`c` =
  128 or 256, memory only): the low `c` bits of `src` repeated, masked at `e` bits. -/
  | bcast (e c l d : Nat) (src : X) (k : Nat) (z : Bool)
  /-- `VPBROADCASTB/W/D/Q dst, r32/r64`: the low `e` bits of general register `src` in every
  element. -/
  | bcastG (e l d src k : Nat) (z : Bool)
  /-- `VPMOVSX` (`signed`) / `VPMOVZX` from `f`-bit to `t`-bit elements (`l/t` of them). -/
  | pmovx (signed : Bool) (f t l d : Nat) (src : X) (k : Nat) (z : Bool)
  /-- `VADDPS/PD`, `VSUBPS/PD`, `VMULPS/PD`, `VDIVPS/PD`, `VMINPS/PD`, `VMAXPS/PD`, `VSQRTPS/PD`
  (`src1` unused) at element width `w`. `rc`: `0` the `MXCSR` rounding with exceptions as usual,
  `1..4` embedded rounding `{rn-sae}`, `{rd-sae}`, `{ru-sae}`, `{rz-sae}`, `5` `{sae}` (both
  suppress every floating-point exception: no flags, no `#XM`). -/
  | fp (op : PFOp) (w l d s1 : Nat) (src2 : X) (bc rc k : Nat) (z : Bool)
  /-- `KMOVB/W/D/Q dst, src` (`w` bits, zero-extended into a mask or general register). -/
  | kmov (w : Nat) (dst src : KLoc A)
  /-- `KANDB/W/D/Q`... `kd ← op(k1, k2)` on the low `w` bits, zero-extended. -/
  | klogic (op : KOp) (w kd k1 k2 : Nat)
  /-- `KNOTB/W/D/Q kd, ks`. -/
  | knot (w kd ks : Nat)
  /-- `KSHIFTLB/W/D/Q` (`left`), `KSHIFTRB/W/D/Q kd, ks, imm8`. -/
  | kshift (left : Bool) (w kd ks imm : Nat)
  /-- `KORTESTB/W/D/Q k1, k2`: `ZF` = the `OR` is zero, `CF` = it is all ones; `OF SF AF PF`
  cleared. -/
  | kortest (w k1 k2 : Nat)
  /-- `KTESTB/W/D/Q k1, k2`: `ZF` = `k1 AND k2` is zero, `CF` = `NOT k1 AND k2` is zero; `OF SF
  AF PF` cleared. -/
  | ktest (w k1 k2 : Nat)
  /-- `KUNPCKBW` (`w = 8`), `KUNPCKWD` (`16`), `KUNPCKDQ` (`32`) `kd, k1, k2`: the low `w` bits of
  `k2` below the low `w` bits of `k1`. -/
  | kunpck (w kd k1 k2 : Nat)
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64
