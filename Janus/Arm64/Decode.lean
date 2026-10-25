import Janus.Arm64.Instr
import Janus.Arm64.Bits
import Janus.Arm64.DecodeFloat
import Janus.Arm64.DecodeSys
import Janus.Arm64.DecodeNeon
import Janus.Arm64.DecodeCrypto

/-!
# A64 decoder for the supported subset

`decode w` maps a 32-bit instruction word to an `Instr`, or `none` when the word is outside
the subset **or** is a reserved / unallocated / UNDEFINED / CONSTRAINED UNPREDICTABLE encoding
within it. Rejecting is always safe (execution stops with `Fault.undecodable`); accepting an
encoding the hardware treats differently would be unsound, so every fixed field, every
should-be-one/zero field we know of, and every "UNDEFINED" / "UNPREDICTABLE" condition in
the ARM ARM decode pseudocode of a supported instruction is checked.

The structure follows the ARM ARM top-level decode table (`op0 = w<28:25>`) and then the
class tables. Only `Nat` arithmetic and `if` are used, so `decide`, `rfl` and
`simp [decode, decodeDPImm, decodeBranchSys, decodeLdSt, decodeLdStV, decodeExclusive,
decodeAtomic, decodeDPReg, decodeSimdDP, bits, bit, ...]`
evaluate the decoder on literal words.
-/

namespace Janus.Arm64

namespace ShiftType
/-- The 2-bit `shift` field. -/
def ofBits (n : Nat) : ShiftType :=
  if n = 0 then .lsl else if n = 1 then .lsr else if n = 2 then .asr else .ror
end ShiftType

namespace ExtendType
/-- The 3-bit `option` field. -/
def ofBits (n : Nat) : ExtendType :=
  if n = 0 then .uxtb else if n = 1 then .uxth else if n = 2 then .uxtw else
  if n = 3 then .uxtx else if n = 4 then .sxtb else if n = 5 then .sxth else
  if n = 6 then .sxtw else .sxtx
end ExtendType

namespace LogicOp
/-- The 2-bit `opc` field of the logical instructions. -/
def ofBits (n : Nat) : LogicOp :=
  if n = 0 then .and else if n = 1 then .orr else if n = 2 then .eor else .ands
end LogicOp

/-- Data processing -- immediate (`op0 = 100x`); class selected by `w<25:23>`. -/
def decodeDPImm (w : Nat) : Option Instr :=
  let sf := bit w 31
  let rd := bits w 4 0
  let rn := bits w 9 5
  let op := bits w 25 23
  if op / 2 = 0 then
    -- PC-rel addressing: op<31> immlo<30:29> 10000 immhi<23:5> Rd
    some (.adr (bit w 31) (bits w 30 29) (bits w 23 5) rd)
  else if op = 0b010 then
    -- Add/subtract (immediate): sf op S 100010 sh imm12 Rn Rd
    some (.addSubImm sf (bit w 30) (bit w 29) (bit w 22) (bits w 21 10) rn rd)
  else if op = 0b100 then
    -- Logical (immediate): sf opc 100100 N immr imms Rn Rd
    let N := bit w 22
    let immr := bits w 21 16
    let imms := bits w 15 10
    if !sf && N then none else
    match decodeBitMasks N imms immr true (if sf then 64 else 32) with
    | none => none
    | some _ => some (.logicalImm sf (LogicOp.ofBits (bits w 30 29)) N immr imms rn rd)
  else if op = 0b101 then
    -- Move wide (immediate): sf opc 100101 hw imm16 Rd
    let opc := bits w 30 29
    let hw := bits w 22 21
    if opc = 1 then none else
    if !sf && hw ≥ 2 then none else
    let mop := if opc = 0 then MoveWideOp.movn else if opc = 2 then .movz else .movk
    some (.moveWide sf mop hw (bits w 20 5) rd)
  else if op = 0b110 then
    -- Bitfield: sf opc 100110 N immr imms Rn Rd
    let opc := bits w 30 29
    let N := bit w 22
    let immr := bits w 21 16
    let imms := bits w 15 10
    if opc = 3 then none else
    -- `if sf == '1' && N != '1' then UNDEFINED;`
    -- `if sf == '0' && (N != '0' || immr<5> != '0' || imms<5> != '0') then UNDEFINED;`
    if sf != N then none else
    if !sf && (immr ≥ 32 || imms ≥ 32) then none else
    match decodeBitMasks N imms immr false (if sf then 64 else 32) with
    | none => none
    | some _ =>
      let bop := if opc = 0 then BitfieldOp.sbfm else if opc = 1 then .bfm else .ubfm
      some (.bitfield sf bop N immr imms rn rd)
  else if op = 0b111 then
    -- Extract: sf op21 100111 N o0 Rm imms Rn Rd; only op21 = 00, o0 = 0 is EXTR.
    let N := bit w 22
    let imms := bits w 15 10
    if bits w 30 29 ≠ 0 || bit w 21 then none else
    if sf != N then none else
    if !sf && imms ≥ 32 then none else
    some (.extr sf N (bits w 20 16) imms rn rd)
  else
    -- 011: add/subtract (immediate, with tags), min/max (immediate): not supported.
    none

/-- Hints executed as no-ops in this model, by `CRm:op2`. Everything else in the hint space
is rejected: the pointer-authentication hints (PACIASP, AUTIASP, XPACLRI, ...) and
CHKFEAT modify registers when the feature is implemented, ESB/PSB/TSB/GCSB/CLRBHB/... are
feature-dependent, WFE/WFI may block, and unallocated hints may be allocated by future
features. Accepted: NOP (0), YIELD (1), SEV (4), SEVL (5), DGH (6), CSDB (0b0010100), and
BTI / BTI c / BTI j / BTI jc (0b0100xx0; branch-target enforcement needs PROT_BTI pages,
which Go binaries do not use). -/
def noOpHint (crmOp2 : Nat) : Bool :=
  crmOp2 = 0 || crmOp2 = 1 || crmOp2 = 4 || crmOp2 = 5 || crmOp2 = 6 || crmOp2 = 0b0010100 ||
  crmOp2 = 0b0100000 || crmOp2 = 0b0100010 || crmOp2 = 0b0100100 || crmOp2 = 0b0100110

/-- Branches, exception generating and system instructions (`op0 = 101x`). -/
def decodeBranchSys (w : Nat) : Option Instr :=
  if bits w 30 26 = 0b00101 then
    -- Unconditional branch (immediate): op 00101 imm26
    some (.b (bit w 31) (bits w 25 0))
  else if bits w 30 25 = 0b011010 then
    -- Compare and branch: sf 011010 op imm19 Rt
    some (.cb (bit w 31) (bit w 24) (bits w 23 5) (bits w 4 0))
  else if bits w 30 25 = 0b011011 then
    -- Test and branch: b5 011011 op b40 imm14 Rt
    some (.tb (bit w 31) (bit w 24) (bits w 23 19) (bits w 18 5) (bits w 4 0))
  else if bits w 31 24 = 0b01010100 then
    -- Conditional branch: 0101010 o1=0 imm19 o0 cond. o0 = 1 is BC.cond (FEAT_HBC): rejected.
    if bit w 4 then none else some (.bcond (bits w 23 5) (bits w 3 0))
  else if w &&& 0xFFFFF01F = 0xD503201F then
    -- HINT: 1101010100 0 00 011 0010 CRm op2 11111
    if noOpHint (bits w 11 5) then some (.hint (bits w 11 8) (bits w 7 5)) else none
  else if w &&& 0xFFFFF01F = 0xD503301F then
    -- Barriers: 1101010100 0 00 011 0011 CRm op2 11111.
    -- op2 = 100 DSB, 101 DMB, 110 ISB (every CRm value is a valid or "execute as SY" option);
    -- CLREX, SB, DSB nXS, TCOMMIT, ... are rejected.
    -- op2 = 010 CLREX (every CRm value is allowed: the immediate is ignored).
    let op2 := bits w 7 5
    if op2 = 4 || op2 = 5 || op2 = 6 then some (.barrier (bits w 11 8) op2)
    else if op2 = 2 then some (.clrex (bits w 11 8))
    else none
  else if w &&& 0xFFFFFC1F = 0xD61F0000 then
    -- Unconditional branch (register): 1101011 opc op2=11111 op3=000000 Rn op4=00000
    some (.br (bits w 9 5))
  else if w &&& 0xFFFFFC1F = 0xD63F0000 then
    some (.blr (bits w 9 5))
  else if w &&& 0xFFFFFC1F = 0xD65F0000 then
    some (.ret (bits w 9 5))
  else if w &&& 0xFFFFFFE0 = 0xD53B00E0 then
    -- MRS Xt, DCZID_EL0: 1101010100 1 1 op0=11 op1=011 CRn=0000 CRm=0000 op2=111 Rt.
    -- No other system register is readable in this model (TPIDR_EL0 below).
    some (.mrsDczid (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD53BD040 then
    -- MRS Xt, TPIDR_EL0: op0=11 op1=011 CRn=1101 CRm=0000 op2=010 Rt.
    some (.mrsTpidr (bits w 4 0))
  else if w &&& 0xFFFFFFE0 = 0xD50B7420 then
    -- DC ZVA, Xt = SYS #3, C7, C4, #1, Xt: 1101010100 0 01 011 0111 0100 001 Rt.
    -- No other cache-maintenance or SYS operation is accepted.
    some (.dcZva (bits w 4 0))
  else decodeSys w  -- SVC #0, BRK, MRS/MSR of the environment registers (`Janus.Arm64.DecodeSys`)

/-- Valid `(size, opc)` combinations of the single-register integer load/store classes:
opc 00 store / 01 load for every size; 10 (signed to 64) for B/H/W (LDRSB/LDRSH/LDRSW);
11 (signed to 32) for B/H. `size = 11, opc = 10` is PRFM/PRFUM (or unallocated) and the
other combinations are unallocated. -/
def validSizeOpc (size opc : Nat) : Bool :=
  opc ≤ 1 || (opc = 2 && size ≤ 2) || (opc = 3 && size ≤ 1)

/-- LSE atomic memory operations by `opc` (bits 14:12) with `o3 = 0`. -/
def AtomicOp.ofBits (n : Nat) : AtomicOp :=
  if n = 0 then .add else if n = 1 then .clr else if n = 2 then .eor else if n = 3 then .set
  else if n = 4 then .smax else if n = 5 then .smin else if n = 6 then .umax else .umin

/-- Load/store exclusive, ordered, and compare-and-swap (`size 001000 o2 L o1 Rs o0 Rt2 Rn Rt`).

* `o2 o1 = 1 1`: CAS{A}{L}{B,H} (`Rt2 = 11111`; other values are unallocated).
* `o2 o1 = 1 0`: LDAR/STLR (`o0 = 1`, `Rs` and `Rt2` should-be-one; any other value is
  CONSTRAINED UNPREDICTABLE and rejected). `o0 = 0` is LDLAR/STLLR (FEAT_LOR), rejected.
* `o2 o1 = 0 1`: CASP{A}{L} for `size = 0x` (`Rt2 = 11111`, `Rs` and `Rt` even, else
  UNDEFINED); LDXP/STXP/... for `size = 1x`, rejected.
* `o2 o1 = 0 0`: LDXR/LDAXR (`L = 1`, `Rs` and `Rt2` should-be-one). STXR/STLXR (`L = 0`) are
  **rejected**: a store-exclusive may fail spuriously on hardware, and a deterministic model
  of it would be unsound (see `docs/SOUNDNESS.md`). -/
def decodeExclusive (w : Nat) : Option Instr :=
  let rt := bits w 4 0
  let rn := bits w 9 5
  let size := bits w 31 30
  let o2 := bit w 23
  let L := bit w 22
  let o1 := bit w 21
  let rs := bits w 20 16
  let o0 := bit w 15
  if bits w 14 10 ≠ 31 then none else
  if o2 && o1 then some (.cas size L o0 rs rn rt)
  else if o2 then
    if !o0 || rs ≠ 31 then none else some (.ldstOrdered size L false rn rt)
  else if o1 then
    if size ≥ 2 then none else
    if rs % 2 = 1 || rt % 2 = 1 then none else
    some (.casp (size = 1) L o0 rs rn rt)
  else
    if !L || rs ≠ 31 then none else some (.ldExcl size o0 rn rt)

/-- Atomic memory operations (`size 111 0 00 A R 1 Rs o3 opc 00 Rn Rt`): LD<op>{A}{L}
(`o3 = 0`, every `opc`), SWP{A}{L} (`o3 = 1, opc = 000`) and LDAPR (`o3 = 1, opc = 100`,
`A = 1, R = 0`, `Rs` should-be-one). Everything else (ST64B*, LD64B, RCW*, ...) is rejected. -/
def decodeAtomic (w : Nat) : Option Instr :=
  let rt := bits w 4 0
  let rn := bits w 9 5
  let size := bits w 31 30
  let A := bit w 23
  let R := bit w 22
  let rs := bits w 20 16
  let opc := bits w 14 12
  if !bit w 15 then some (.atomic size A R rs (AtomicOp.ofBits opc) rn rt)
  else if opc = 0 then some (.atomic size A R rs .swp rn rt)
  else if opc = 4 && A && !R && rs == 31 then some (.ldstOrdered size true true rn rt)
  else none

/-- The element layout of a single-structure load/store (`opcode`, `S`, `size`, `Q` fields, `L`):
`(esize in bytes, lane index, replicate)`, or `none` where the decode pseudocode is UNDEFINED
(`scale = opcode<2:1>`; `3`: replicate, needs `L = 1, S = 0`; `0`: byte lane `Q:S:size`;
`1`: halfword lane `Q:S:size<1>`, `size<0> = 0`; `2`: word lane `Q:S` for `size = 00`, doubleword
lane `Q` for `size = 01, S = 0`, otherwise UNDEFINED). -/
def vSingleLayout (Q : Bool) (opcode : Nat) (S : Bool) (size : Nat) (L : Bool) : Option (Nat × Nat × Bool) :=
  let scale := opcode / 2
  if scale = 3 then (if L && !S then some (2 ^ size, 0, true) else none)
  else if scale = 0 then some (1, Q.toNat * 8 + S.toNat * 4 + size, false)
  else if scale = 1 then (if size % 2 = 1 then none else some (2, Q.toNat * 4 + S.toNat * 2 + size / 2, false))
  else if size / 2 = 1 then none
  else if size = 0 then some (4, Q.toNat * 2 + S.toNat, false)
  else if S then none
  else some (8, Q.toNat, false)

/-- SIMD&FP loads and stores (`op0 = x1x0`, `V = 1`): LD1/ST1 (multiple structures), and
LD1–LD4/ST1–ST4 (single structure), LD1R–LD4R, LDR/STR/LDUR/STUR/LDP/STP and LDR (literal) of
B/H/S/D/Q registers. Rejected: LD2–LD4/ST2–ST4 (multiple structures), LDNP/STNP, LDAPUR/STLUR (SIMD&FP), and every reserved
size (`opc<1>:size > 4`, `opc = 11` for pairs and literals). -/
def decodeLdStV (w : Nat) : Option Instr :=
  let rt := bits w 4 0
  let rn := bits w 9 5
  let cls := bits w 29 27
  if w &&& 0xBFBF0000 = 0x0C000000 || w &&& 0xBFA00000 = 0x0C800000 then
    -- Load/store multiple structures: 0 Q 0011000 L 000000 opcode size Rn Rt (no offset),
    -- 0 Q 0011001 L 0 Rm opcode size Rn Rt (post-index). LD1/ST1: opcode 0111 (1 register),
    -- 1010 (2), 0110 (3), 0010 (4).
    let opcode := bits w 15 12
    if opcode = 0b0111 || opcode = 0b1010 || opcode = 0b0110 || opcode = 0b0010 then
      some (.vldstMulti (bit w 30) (bit w 22) opcode (bits w 11 10) (bit w 23) (bits w 20 16) rn rt)
    else none
  else if w &&& 0xBF9F0000 = 0x0D000000 || w &&& 0xBF800000 = 0x0D800000 then
    -- Load/store single structure: 0 Q 0011010 L R 00000 opcode S size Rn Rt (no offset),
    -- 0 Q 0011011 L R Rm opcode S size Rn Rt (post-index).
    match vSingleLayout (bit w 30) (bits w 15 13) (bit w 12) (bits w 11 10) (bit w 22) with
    | none => none
    | some _ =>
      some (.vldstSingle (bit w 30) (bit w 22) (bit w 21) (bits w 15 13) (bit w 12) (bits w 11 10)
        (bit w 23) (bits w 20 16) rn rt)
  else if cls = 0b011 then
    -- Load register (literal): opc 011 1 00 imm19 Rt
    if bit w 24 then none else
    let opc := bits w 31 30
    if opc = 3 then none else some (.vldrLit opc (bits w 23 5) rt)
  else if cls = 0b101 then
    -- Load/store register pair: opc 101 1 0 idx L imm7 Rt2 Rn Rt
    let opc := bits w 31 30
    let L := bit w 22
    let rt2 := bits w 14 10
    let idx := bits w 24 23
    if idx = 0 then none else  -- LDNP/STNP: not supported
    if opc = 3 then none else
    -- `if memop == MemOp_LOAD && t == t2 then CONSTRAINED UNPREDICTABLE`
    if L && rt == rt2 then none else
    let mode := if idx = 1 then PairMode.post else if idx = 2 then .offset else .pre
    some (.vldstPair opc mode L (bits w 21 15) rt2 rn rt)
  else if cls = 0b111 then
    let size := bits w 31 30
    let opc := bits w 23 22
    -- `scale = UInt(opc<1>:size); if scale > 4 then UNDEFINED`
    if opc / 2 * 4 + size > 4 then none else
    if bit w 24 then some (.vldstUImm size opc (bits w 21 10) rn rt)
    else if !bit w 21 then
      let op4 := bits w 11 10
      if op4 = 2 then none else
      let mode := if op4 = 0 then Imm9Mode.unscaled else if op4 = 1 then .post else .pre
      some (.vldstImm9 size opc mode (bits w 20 12) rn rt)
    else if bits w 11 10 = 2 then
      let option := bits w 15 13
      if option / 2 % 2 = 0 then none else  -- `if option<1> == '0' then UNDEFINED`
      some (.vldstReg size opc (bits w 20 16) (ExtendType.ofBits option) (bit w 12) rn rt)
    else none
  else none

/-- Loads and stores (`op0 = x1x0`); `V = 1` goes to `decodeLdStV`. -/
def decodeLdSt (w : Nat) : Option Instr :=
  let rt := bits w 4 0
  let rn := bits w 9 5
  if bit w 26 then decodeLdStV w else
  let cls := bits w 29 27
  if cls = 0b001 then
    -- Exclusive / ordered / compare-and-swap: size 001000 ... (w<24> = 1: other classes)
    if bit w 24 then none else decodeExclusive w
  else if cls = 0b011 then
    -- Load register (literal): opc 011 V 0 0 imm19 Rt (w<24> = 1 is another class)
    if bit w 24 then none else
    let opc := bits w 31 30
    if opc = 3 then some (.prefetch rt) else  -- PRFM (literal)
    some (.ldrLit opc (bits w 23 5) rt)
  else if cls = 0b101 then
    -- Load/store register pair: opc 101 V 0 idx L imm7 Rt2 Rn Rt
    let opc := bits w 31 30
    let L := bit w 22
    let rt2 := bits w 14 10
    let idx := bits w 24 23
    if idx = 0 then none else  -- LDNP/STNP: not supported
    let mode := if idx = 1 then PairMode.post else if idx = 2 then .offset else .pre
    if opc = 3 then none else
    if opc = 1 && !L then none else  -- STGP (FEAT_MTE)
    -- `if memop == MemOp_LOAD && t == t2 then CONSTRAINED UNPREDICTABLE`
    if L && rt == rt2 then none else
    -- `if wback && (t == n || t2 == n) && n != 31 then CONSTRAINED UNPREDICTABLE`
    if idx ≠ 2 && (rt == rn || rt2 == rn) && rn ≠ 31 then none else
    some (.ldstPair opc mode L (bits w 21 15) rt2 rn rt)
  else if cls = 0b111 then
    let size := bits w 31 30
    let opc := bits w 23 22
    -- `size = 11, opc = 10` is PRFM (immediate, register) / PRFUM: a hint with no effect.
    let prfm := size = 3 && opc = 2
    if bit w 24 then
      -- Load/store register (unsigned immediate): size 111 V 01 opc imm12 Rn Rt
      if prfm then some (.prefetch rt) else
      if !validSizeOpc size opc then none else
      some (.ldstUImm size opc (bits w 21 10) rn rt)
    else if !bit w 21 then
      -- size 111 V 00 opc 0 imm9 op4 Rn Rt; op4: 00 unscaled, 01 post, 10 unprivileged, 11 pre
      let op4 := bits w 11 10
      if prfm then (if op4 = 0 then some (.prefetch rt) else none) else  -- PRFUM
      if !validSizeOpc size opc then none else
      if op4 = 2 then none else
      let mode := if op4 = 0 then Imm9Mode.unscaled else if op4 = 1 then .post else .pre
      -- `if wback && n == t && n != 31 then CONSTRAINED UNPREDICTABLE` (loads and stores)
      if op4 ≠ 0 && rn == rt && rn ≠ 31 then none else
      some (.ldstImm9 size opc mode (bits w 20 12) rn rt)
    else if bits w 11 10 = 2 then
      -- Load/store register (register offset): size 111 V 00 opc 1 Rm option S 10 Rn Rt
      let option := bits w 15 13
      if option / 2 % 2 = 0 then none else  -- `if option<1> == '0' then UNDEFINED`
      if prfm then some (.prefetch rt) else
      if !validSizeOpc size opc then none else
      some (.ldstReg size opc (bits w 20 16) (ExtendType.ofBits option) (bit w 12) rn rt)
    else if bits w 11 10 = 0 then
      -- Atomic memory operations: size 111 V 00 A R 1 Rs o3 opc 00 Rn Rt
      decodeAtomic w
    else none  -- LDRAA/LDRAB, ...
  else none  -- MOPS, tags, RCpc unscaled, ...

/-- Data processing -- register (`op0 = x101`). -/
def decodeDPReg (w : Nat) : Option Instr :=
  let sf := bit w 31
  let rd := bits w 4 0
  let rn := bits w 9 5
  let rm := bits w 20 16
  if !bit w 28 then
    if !bit w 24 then
      -- Logical (shifted register): sf opc 01010 shift N Rm imm6 Rn Rd
      let imm6 := bits w 15 10
      if !sf && imm6 ≥ 32 then none else
      some (.logicalShifted sf (LogicOp.ofBits (bits w 30 29)) (ShiftType.ofBits (bits w 23 22))
        (bit w 21) rm imm6 rn rd)
    else if !bit w 21 then
      -- Add/subtract (shifted register): sf op S 01011 shift 0 Rm imm6 Rn Rd
      let shift := bits w 23 22
      let imm6 := bits w 15 10
      if shift = 3 then none else
      if !sf && imm6 ≥ 32 then none else
      some (.addSubShifted sf (bit w 30) (bit w 29) (ShiftType.ofBits shift) rm imm6 rn rd)
    else
      -- Add/subtract (extended register): sf op S 01011 opt=00 1 Rm option imm3 Rn Rd
      let imm3 := bits w 12 10
      if bits w 23 22 ≠ 0 then none else
      if imm3 > 4 then none else
      some (.addSubExt sf (bit w 30) (bit w 29) rm (ExtendType.ofBits (bits w 15 13)) imm3 rn rd)
  else
    let op2 := bits w 24 21
    if op2 = 0b0000 then
      -- Add/subtract (with carry): sf op S 11010000 Rm 000000 Rn Rd
      if bits w 15 10 ≠ 0 then none else
      some (.addSubCarry sf (bit w 30) (bit w 29) rm rn rd)
    else if op2 = 0b0010 then
      -- Conditional compare: sf op S=1 11010010 Rm|imm5 cond imm o2=0 Rn o3=0 nzcv
      if !bit w 29 || bit w 10 || bit w 4 then none else
      if bit w 11 then
        some (.condCmpImm sf (bit w 30) rm (bits w 15 12) rn (bits w 3 0))
      else
        some (.condCmpReg sf (bit w 30) rm (bits w 15 12) rn (bits w 3 0))
    else if op2 = 0b0100 then
      -- Conditional select: sf op S=0 11010100 Rm cond op2 Rn Rd, op2 = 0x
      if bit w 29 || bit w 11 then none else
      some (.condSel sf (bit w 30) rm (bits w 15 12) (bit w 10) rn rd)
    else if op2 = 0b0110 then
      if bit w 29 then none else  -- S = 1: unallocated
      if !bit w 30 then
        -- Data-processing (2 source): sf 0 0 11010110 Rm opcode Rn Rd
        let opcode := bits w 15 10
        if opcode = 0b000010 then some (.div sf false rm rn rd)
        else if opcode = 0b000011 then some (.div sf true rm rn rd)
        else if opcode = 0b001000 then some (.shiftV sf .lsl rm rn rd)
        else if opcode = 0b001001 then some (.shiftV sf .lsr rm rn rd)
        else if opcode = 0b001010 then some (.shiftV sf .asr rm rn rd)
        else if opcode = 0b001011 then some (.shiftV sf .ror rm rn rd)
        else (decodeCrc32 w).map .crypto  -- CRC32 (`Janus.Arm64.DecodeCrypto`); PAC, MTE, ...: none
      else
        -- Data-processing (1 source): sf 1 0 11010110 opcode2 opcode Rn Rd
        let opcode := bits w 15 10
        if bits w 20 16 ≠ 0 then none
        else if opcode = 0 then some (.rbit sf rn rd)
        else if opcode = 1 then some (.rev sf 1 rn rd)
        else if opcode = 2 then some (.rev sf 2 rn rd)
        else if opcode = 3 then (if sf then some (.rev sf 3 rn rd) else none)
        else if opcode = 4 then some (.clz sf rn rd)
        else if opcode = 5 then some (.cls sf rn rd)
        else none  -- CTZ/CNT/ABS (FEAT_CSSC), PAC, ...
    else if op2 / 8 = 1 then
      -- Data-processing (3 source): sf op54=00 11011 op31 Rm o0 Ra Rn Rd
      if bits w 30 29 ≠ 0 then none else
      let op31 := bits w 23 21
      let o0 := bit w 15
      let ra := bits w 14 10
      if op31 = 0 then some (.madd sf o0 rm ra rn rd)
      else if !sf then none
      else if op31 = 0b001 then some (.maddl false o0 rm ra rn rd)
      else if op31 = 0b101 then some (.maddl true o0 rm ra rn rd)
      -- SMULH/UMULH: o0 = 0 and Ra is a should-be-one field (11111).
      else if op31 = 0b010 && !o0 && ra == 31 then some (.mulh false rm rn rd)
      else if op31 = 0b110 && !o0 && ra == 31 then some (.mulh true rm rn rd)
      else none
    else none


/-- `LowestSetBit` of a 5-bit field (5 when it is zero). -/
def lowestSetBit5 (v : Nat) : Nat :=
  if v % 2 = 1 then 0 else if v / 2 % 2 = 1 then 1 else if v / 4 % 2 = 1 then 2 else
  if v / 8 % 2 = 1 then 3 else if v / 16 % 2 = 1 then 4 else 5

/-- `HighestSetBit` of the 4-bit `immh` field (`immh ≠ 0`). -/
def highestSetBit4 (v : Nat) : Nat :=
  if v ≥ 8 then 3 else if v ≥ 4 then 2 else if v ≥ 2 then 1 else 0

/-- Scalar floating-point and Advanced SIMD data processing (`op0 = x111`): the Advanced SIMD
integer and move instructions (see `Instr`), and the scalar single/double floating-point classes
(`decodeFloat`, `decodeFpCvtInt` in `Janus.Arm64.DecodeFloat`), and the crypto, PMULL, permute
and scalar DUP classes (`decodeCrypto` in `Janus.Arm64.DecodeCrypto`). Advanced SIMD floating
point, half precision, conversions to and from fixed point, SM3/SM4, saturating,
rounding, widening/narrowing arithmetic other than XTN/SHRN/SSHLL/USHLL/PMULL, and every
reserved or unallocated encoding within the accepted classes are rejected. -/
def decodeSimdDP (w : Nat) : Option Instr :=
  let rd := bits w 4 0
  let rn := bits w 9 5
  let rm := bits w 20 16
  let Q := bit w 30
  let U := bit w 29
  let size := bits w 23 22
  if w &&& 0xFFFFCC00 = 0x4E284800 then
    -- Crypto AES: 01001110 00 10100 opcode 10 Rn Rd, opcode 001xx (AESE/AESD/AESMC/AESIMC).
    some (.vAes (bits w 16 12) rn rd)
  else if w &&& 0x9F200400 = 0x0E200400 then
    -- Three same: 0 Q U 01110 size 1 Rm opcode 1 Rn Rd
    let opcode := bits w 15 11
    let reservedQ := size = 3 && !Q   -- `if size:Q == '110' then UNDEFINED`
    if opcode = 0b00011 then some (.vThreeSame Q U size rm opcode rn rd)
    else if opcode = 0b10000 || opcode = 0b10001 || opcode = 0b00110 || opcode = 0b00111 ||
        (opcode = 0b10111 && !U) then
      if reservedQ then none else some (.vThreeSame Q U size rm opcode rn rd)
    else if opcode = 0b01100 || opcode = 0b01101 || opcode = 0b10100 || opcode = 0b10101 then
      if size = 3 then none else some (.vThreeSame Q U size rm opcode rn rd)
    else none
  else if w &&& 0xDF200400 = 0x5E200400 then
    -- Scalar three same: 01 U 11110 size 1 Rm opcode 1 Rn Rd (D registers only)
    let opcode := bits w 15 11
    if size ≠ 3 then none else
    if opcode = 0b10000 || opcode = 0b10001 || opcode = 0b00110 || opcode = 0b00111 then
      some (.vScalarThreeSame U size rm opcode rn rd)
    else none
  else if w &&& 0x9FE08400 = 0x0E000400 then
    -- Copy: 0 Q op 01110000 imm5 0 imm4 1 Rn Rd
    let imm5 := bits w 20 16
    let imm4 := bits w 14 11
    let sz := lowestSetBit5 imm5
    if sz > 3 then none else
    if U then (if Q then some (.vCopy Q U imm5 imm4 rn rd) else none)  -- INS (element)
    else if imm4 = 0 || imm4 = 1 then
      if sz = 3 && !Q then none else some (.vCopy Q U imm5 imm4 rn rd)  -- DUP
    else if imm4 = 3 then (if Q then some (.vCopy Q U imm5 imm4 rn rd) else none)  -- INS
    else if imm4 = 5 then  -- SMOV: B/H to W, B/H/S to X
      if sz ≤ 1 || (Q && sz = 2) then some (.vCopy Q U imm5 imm4 rn rd) else none
    else if imm4 = 7 then  -- UMOV: B/H/S to W, D to X
      if (!Q && sz ≤ 2) || (Q && sz = 3) then some (.vCopy Q U imm5 imm4 rn rd) else none
    else none
  else if w &&& 0x9F3E0C00 = 0x0E300800 then
    -- Across lanes: 0 Q U 01110 size 11000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    if size = 3 || (size = 2 && !Q) then none else
    if opcode = 0b00011 || opcode = 0b01010 || opcode = 0b11010 || (opcode = 0b11011 && !U) then
      some (.vAcross Q U size opcode rn rd)
    else none
  else if w &&& 0x9F3E0C00 = 0x0E200800 then
    -- Two-register miscellaneous: 0 Q U 01110 size 10000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    let ok :=
      if opcode = 0b00000 then (if U then size ≤ 1 else size ≤ 2)          -- REV32 / REV64
      else if opcode = 0b00001 then !U && size = 0                          -- REV16
      else if opcode = 0b00101 then (if U then size ≤ 1 else size = 0)      -- NOT, RBIT / CNT
      else if opcode = 0b01000 || opcode = 0b01001 || opcode = 0b01011 then !(size = 3 && !Q)
      else if opcode = 0b01010 then !U && !(size = 3 && !Q)                 -- CMLT #0
      else if opcode = 0b10010 then !U && size ≠ 3                          -- XTN
      else false
    if ok then some (.vTwoMisc Q U size opcode rn rd) else none
  else if w &&& 0x9F800400 = 0x0F000400 then
    let immh := bits w 22 19
    if immh = 0 then
      -- Modified immediate: 0 Q op 0111100000 a b c cmode o2 1 d e f g h Rd
      let cmode := bits w 15 12
      if bit w 11 then none else  -- o2 = 1: FMOV (half precision, FEAT_FP16) / unallocated
      if cmode = 15 && U && !Q then none else
      some (.vModImm Q U cmode (bits w 18 16 * 32 + bits w 9 5) rd)
    else
      -- Shift by immediate: 0 Q U 011110 immh immb opcode 1 Rn Rd
      let opcode := bits w 15 11
      let wide := immh ≥ 8   -- immh<3>
      let ok :=
        if opcode = 0b00000 || opcode = 0b00010 then !(wide && !Q)            -- SSHR/USHR/SSRA/USRA
        else if opcode = 0b01010 then !(wide && !Q)                           -- SHL / SLI
        else if opcode = 0b01000 then U && !(wide && !Q)                      -- SRI
        else if opcode = 0b10000 then !U && !wide                             -- SHRN
        else if opcode = 0b10100 then !wide                                   -- SSHLL/USHLL
        else false
      if ok then some (.vShiftImm Q U immh (bits w 18 16) opcode rn rd) else none
  else if w &&& 0xBFE08400 = 0x2E000000 then
    -- EXT: 0 Q 101110 00 0 Rm 0 imm4 0 Rn Rd
    let imm4 := bits w 14 11
    if !Q && imm4 ≥ 8 then none else some (.vExt Q rm imm4 rn rd)
  else if w &&& 0xBFE08C00 = 0x0E000000 then
    -- TBL/TBX: 0 Q 001110 00 0 Rm 0 len op 00 Rn Rd
    some (.vTbl Q rm (bits w 14 13) (bit w 12) rn rd)
  else if w &&& 0x7F20FC00 = 0x1E200000 then
    -- Conversion between FP and integer: sf 0 0 11110 ftype 1 rmode opcode 000000 Rn Rd;
    -- the FMOV bit moves (opcode 110/111): W<->S, X<->D, X<->V.D[1]; the arithmetic
    -- conversions are `decodeFpCvtInt` (`Janus.Arm64.DecodeFloat`).
    let sf := bit w 31
    let ftype := bits w 23 22
    let rmode := bits w 20 19
    let opcode := bits w 18 16
    if opcode ≠ 6 && opcode ≠ 7 then decodeFpCvtInt w
    else if (!sf && ftype = 0 && rmode = 0) || (sf && ftype = 1 && rmode = 0) ||
        (sf && ftype = 2 && rmode = 1) then
      some (.fmovGen sf ftype rmode opcode rn rd)
    else none
  else
    -- crypto extension, PMULL, permutes, scalar DUP (`Janus.Arm64.DecodeCrypto`), then scalar
    -- floating point (`Janus.Arm64.DecodeFloat`); the two accept disjoint encodings
    match decodeCrypto w with
    | some c => some (.crypto c)
    | none => decodeFloat w

/-- Decode a 32-bit A64 instruction word. Words `≥ 2^32` are rejected. -/
def decode (w : Nat) : Option Instr :=
  if w ≥ 2 ^ 32 then none else
  let op0 := bits w 28 25
  if op0 / 2 = 0b100 then decodeDPImm w            -- 100x
  else if op0 / 2 = 0b101 then decodeBranchSys w   -- 101x
  else if op0 % 2 = 0 && op0 / 4 % 2 = 1 then decodeLdSt w   -- x1x0
  else if op0 % 8 = 0b101 then decodeDPReg w       -- x101
  else if op0 % 8 = 0b111 then decodeSimdDP w      -- x111
  else decodeReserved w  -- UDF #imm16 (`Janus.Arm64.DecodeSys`); SME, SVE, unallocated: none

/-- The decoder of the model (`step`): the classes of `decode`, and for the words it rejects, the
Advanced SIMD classes of `decodeNeon` (`Janus.Arm64.DecodeNeon`). `decode` keeps its own
definition so that proofs unfolding it class by class are unaffected. -/
def decodeAll (w : Nat) : Option Instr :=
  match decode w with
  | some i => some i
  | none => (decodeNeon w).map Instr.neon

theorem decodeAll_of_decode {w : Nat} {i : Instr} (h : decode w = some i) : decodeAll w = some i := by
  simp [decodeAll, h]

end Janus.Arm64
