import Janus.Arm64.NeonInstr
import Janus.Arm64.Bits

/-!
# A64 decoder: Advanced SIMD (NEON) classes

`decodeNeon w` maps a 32-bit word to a `NeonInstr`, or `none` when the word is outside the
supported subset **or** is a reserved / unallocated / UNDEFINED / CONSTRAINED UNPREDICTABLE
encoding within it. `Janus.Arm64.decode` consults it only for words its own classes reject, so
the original decoder's results never change.

Every check transcribes the `decode` pseudocode of the instruction (sail-arm `instrs64.sail`,
Armv9.4-A): the `size`/`Q`/`sz`/`immh` combinations that are `UNDEFINED`, the opcodes that are
unallocated, and the forms of optional features that the model does not implement, which are
rejected (`none`) rather than guessed:

* half precision (FEAT_FP16: the FP16 three-same/two-misc/by-element classes, `size = 00` FP
  by element, `immh = 001x` fixed-point conversions, `FCVTL`/`FCVTN` to and from half);
* BFloat16, dot products (FEAT_DotProd, FEAT_I8MM), `SQRDMLAH`/`SQRDMLSH` (FEAT_RDM),
  `FMLAL`/`FMLSL` (FEAT_FHM), `FCMLA`/`FCADD` (FEAT_FCMA), `FRINT32*/64*` (FEAT_FRINTTS);
* `PMULL`/`PMULL2` and the cryptographic extensions (another package);
* `LDNP`/`STNP` loading the same register twice (`Rt == Rt2`, CONSTRAINED UNPREDICTABLE).

The structure is the ARM ARM class table of the "Data Processing -- Scalar Floating-Point and
Advanced SIMD" group and the SIMD&FP part of "Loads and Stores"; only `Nat` arithmetic and `if`
are used, so `decide`/`rfl` evaluate it on literal words.
-/

namespace Janus.Arm64

/-- `HighestSetBit` of a non-zero 4-bit `immh`. -/
def neonHsb4 (v : Nat) : Nat := if v ≥ 8 then 3 else if v ≥ 4 then 2 else if v ≥ 2 then 1 else 0

/-- Integer opcodes of the (vector) three-same class and whether `size`/`Q` allow them
(`reservedQ` = `size:Q == 110`). -/
def neonThreeSameIntOK (U Q : Bool) (size opcode : Nat) : Bool :=
  let notQ := !(size = 3 && !Q)
  if opcode = 0b00000 || opcode = 0b00010 || opcode = 0b00100 then size ≠ 3    -- (U)(R)HADD, HSUB
  else if opcode = 0b00001 || opcode = 0b00101 then notQ                         -- SQADD, SQSUB
  else if opcode = 0b00011 then true                                             -- logical
  else if opcode = 0b00110 || opcode = 0b00111 then notQ                         -- CMGT/CMHI/CMGE/CMHS
  else if opcode / 4 = 0b010 then notQ                                           -- SSHL .. UQRSHL
  else if opcode = 0b01100 || opcode = 0b01101 then size ≠ 3                     -- MAX/MIN
  else if opcode = 0b01110 || opcode = 0b01111 then size ≠ 3                     -- ABD/ABA
  else if opcode = 0b10000 || opcode = 0b10001 then notQ                         -- ADD/SUB, CMTST/CMEQ
  else if opcode = 0b10010 then size ≠ 3                                         -- MLA/MLS
  else if opcode = 0b10011 then (if U then size = 0 else size ≠ 3)               -- PMUL / MUL
  else if opcode = 0b10100 || opcode = 0b10101 then size ≠ 3                     -- MAXP/MINP
  else if opcode = 0b10110 then size = 1 || size = 2                             -- SQ(R)DMULH
  else if opcode = 0b10111 then !U && notQ                                       -- ADDP
  else false

/-- Floating-point opcodes (`11xxx`) of the three-same class by `U` and `a = size<1>` (vector);
`scalar` selects the scalar three-same table. -/
def neonThreeSameFPOK (scalar U a : Bool) (opcode : Nat) : Bool :=
  if scalar then
    if opcode = 0b11011 then !U && !a                       -- FMULX
    else if opcode = 0b11100 then !(!U && a)                -- FCMEQ, FCMGE, FCMGT
    else if opcode = 0b11101 then U                         -- FACGE, FACGT
    else if opcode = 0b11111 then !U                        -- FRECPS, FRSQRTS
    else if opcode = 0b11010 then U && a                    -- FABD
    else false
  else
    if opcode = 0b11000 || opcode = 0b11010 || opcode = 0b11110 then true
    else if opcode = 0b11001 then !U                        -- FMLA, FMLS (U = 1: FEAT_FHM)
    else if opcode = 0b11011 then !a                        -- FMULX, FMUL
    else if opcode = 0b11100 then !(!U && a)                -- FCMEQ, FCMGE, FCMGT
    else if opcode = 0b11101 then U                         -- FACGE, FACGT (U = 0: FEAT_FHM)
    else if opcode = 0b11111 then !(U && a)                 -- FRECPS, FRSQRTS, FDIV
    else false

/-- Scalar three same, integer opcodes. -/
def neonSThreeSameIntOK (size opcode : Nat) : Bool :=
  if opcode = 0b00001 || opcode = 0b00101 || opcode = 0b01001 || opcode = 0b01011 then true
  else if opcode = 0b01000 || opcode = 0b01010 || opcode = 0b00110 || opcode = 0b00111 ||
      opcode = 0b10000 || opcode = 0b10001 then size = 3
  else if opcode = 0b10110 then size = 1 || size = 2
  else false

/-- Vector two-register miscellaneous: integer opcodes. -/
def neonTwoMiscIntOK (U Q : Bool) (size opcode : Nat) : Bool :=
  let notQ := !(size = 3 && !Q)
  if opcode = 0b00000 then (if U then size ≤ 1 else size ≤ 2)                 -- REV64 / REV32
  else if opcode = 0b00001 then !U && size = 0                                 -- REV16
  else if opcode = 0b00010 || opcode = 0b00110 then size ≠ 3                   -- (U/S)ADDLP, ADALP
  else if opcode = 0b00011 then notQ                                           -- SUQADD, USQADD
  else if opcode = 0b00100 then size ≠ 3                                       -- CLS, CLZ
  else if opcode = 0b00101 then (if U then size ≤ 1 else size = 0)             -- NOT, RBIT / CNT
  else if opcode = 0b00111 then notQ                                           -- SQABS, SQNEG
  else if opcode = 0b01000 || opcode = 0b01001 || opcode = 0b01011 then notQ   -- CM.. #0, ABS/NEG
  else if opcode = 0b01010 then !U && notQ                                     -- CMLT #0
  else if opcode = 0b10010 || opcode = 0b10100 then size ≠ 3                   -- XTN, SQXTUN, (U/S)QXTN
  else if opcode = 0b10011 then U && size ≠ 3                                  -- SHLL
  else false

/-- Vector two-register miscellaneous: floating-point opcodes (`a = size<1>`, `sz = size<0>`). -/
def neonTwoMiscFPOK (U Q a : Bool) (sz opcode : Nat) : Bool :=
  let bulk := !(sz = 1 && !Q)
  if opcode = 0b10110 then !a && sz = 1                        -- FCVTN, FCVTXN (from double)
  else if opcode = 0b10111 then !U && !a && sz = 1             -- FCVTL (to double)
  else if opcode = 0b11000 then bulk && !(U && a)              -- FRINTN/P/A (U=1, a=1: UNDEF)
  else if opcode = 0b11001 || opcode = 0b11010 || opcode = 0b11011 then bulk
  else if opcode = 0b11100 then (if a then sz = 0 else bulk)   -- URECPE/URSQRTE, FCVTAS/AU
  else if opcode = 0b11101 then bulk                           -- SCVTF/UCVTF, FRECPE/FRSQRTE
  else if opcode = 0b01100 || opcode = 0b01101 then a && bulk  -- FCMGT/GE/EQ/LE #0
  else if opcode = 0b01110 then a && !U && bulk                -- FCMLT #0
  else if opcode = 0b01111 then a && bulk                      -- FABS, FNEG
  else if opcode = 0b11111 then a && U && bulk                 -- FSQRT
  else false

/-- Scalar two-register miscellaneous (integer and floating point). -/
def neonSTwoMiscOK (U : Bool) (size opcode : Nat) : Bool :=
  let a := size / 2 = 1
  let sz := size % 2
  if opcode = 0b00011 || opcode = 0b00111 then true                            -- SUQADD.., SQABS..
  else if opcode = 0b01000 || opcode = 0b01001 || opcode = 0b01011 then size = 3
  else if opcode = 0b01010 then !U && size = 3                                 -- CMLT #0
  else if opcode = 0b10010 then U && size ≠ 3                                  -- SQXTUN
  else if opcode = 0b10100 then size ≠ 3                                       -- SQXTN, UQXTN
  else if opcode = 0b10110 then U && !a && sz = 1                              -- FCVTXN
  else if opcode = 0b11010 || opcode = 0b11011 then true                       -- FCVT{N,P,M,Z}{S,U}
  else if opcode = 0b11100 then !a                                             -- FCVTAS, FCVTAU
  else if opcode = 0b11101 then true                                           -- SCVTF/UCVTF, FRECPE/FRSQRTE
  else if opcode = 0b01100 || opcode = 0b01101 then a                          -- FCMGT/GE/EQ/LE #0
  else if opcode = 0b01110 then a && !U                                        -- FCMLT #0
  else if opcode = 0b11111 then a && !U                                        -- FRECPX
  else false

/-- Vector shift by immediate (`immh ≠ 0`). -/
def neonShiftImmOK (U Q : Bool) (immh opcode : Nat) : Bool :=
  let wide := immh ≥ 8
  let notWideD := !(wide && !Q)
  if opcode = 0b00000 || opcode = 0b00010 || opcode = 0b00100 || opcode = 0b00110 then notWideD
  else if opcode = 0b01000 then U && notWideD                                   -- SRI
  else if opcode = 0b01010 then notWideD                                        -- SHL / SLI
  else if opcode = 0b01100 then U && notWideD                                   -- SQSHLU
  else if opcode = 0b01110 then notWideD                                        -- SQSHL/UQSHL #imm
  else if opcode / 4 = 0b100 then !wide                                         -- (SQ/UQ)(R)SHR(U)N
  else if opcode = 0b10100 then !wide                                           -- SSHLL/USHLL
  else if opcode = 0b11100 || opcode = 0b11111 then immh ≥ 4 && notWideD        -- (S/U)CVTF, FCVTZ #fbits
  else false

/-- Scalar shift by immediate. -/
def neonSShiftImmOK (U : Bool) (immh opcode : Nat) : Bool :=
  let wide := immh ≥ 8
  if immh = 0 then false
  else if opcode = 0b00000 || opcode = 0b00010 || opcode = 0b00100 || opcode = 0b00110 ||
      opcode = 0b01010 then wide
  else if opcode = 0b01000 then U && wide                                        -- SRI
  else if opcode = 0b01100 then U                                                -- SQSHLU
  else if opcode = 0b01110 then true                                             -- SQSHL/UQSHL #imm
  else if opcode = 0b10000 || opcode = 0b10001 then U && !wide                   -- SQ(R)SHRUN
  else if opcode = 0b10010 || opcode = 0b10011 then !wide                        -- (SQ/UQ)(R)SHRN
  else if opcode = 0b11100 || opcode = 0b11111 then immh ≥ 4                     -- fixed point
  else false

/-- Vector x indexed element: the opcode/size combinations. -/
def neonByElemOK (U Q L : Bool) (size opcode : Nat) : Bool :=
  let int := size = 1 || size = 2
  let fp := size / 2 = 1 && !(size % 2 = 1 && L) && !(size % 2 = 1 && !Q)
  if !U then
    if opcode = 0b1000 || opcode = 0b0010 || opcode = 0b0110 || opcode = 0b1010 ||
        opcode = 0b0011 || opcode = 0b0111 || opcode = 0b1011 || opcode = 0b1100 ||
        opcode = 0b1101 then int
    else if opcode = 0b0001 || opcode = 0b0101 || opcode = 0b1001 then fp
    else false
  else
    if opcode = 0b0000 || opcode = 0b0100 || opcode = 0b0010 || opcode = 0b0110 ||
        opcode = 0b1010 then int
    else if opcode = 0b1001 then fp
    else false

/-- Scalar x indexed element. -/
def neonSByElemOK (U L : Bool) (size opcode : Nat) : Bool :=
  let int := size = 1 || size = 2
  let fp := size / 2 = 1 && !(size % 2 = 1 && L)
  if !U then
    if opcode = 0b0011 || opcode = 0b0111 || opcode = 0b1011 || opcode = 0b1100 ||
        opcode = 0b1101 then int
    else if opcode = 0b0001 || opcode = 0b0101 || opcode = 0b1001 then fp
    else false
  else opcode = 0b1001 && fp

/-- Advanced SIMD data processing (`op0 = x111`), the classes of `NeonInstr`. -/
def decodeNeonDP (w : Nat) : Option NeonInstr :=
  let rd := bits w 4 0
  let rn := bits w 9 5
  let rm := bits w 20 16
  let Q := bit w 30
  let U := bit w 29
  let size := bits w 23 22
  if w &&& 0x9F200400 = 0x0E200400 then
    -- Three same: 0 Q U 01110 size 1 Rm opcode 1 Rn Rd
    let opcode := bits w 15 11
    let ok := if opcode / 8 = 0b11 then neonThreeSameFPOK false U (size / 2 = 1) opcode &&
        !(size % 2 = 1 && !Q)
      else neonThreeSameIntOK U Q size opcode
    if ok then some (.threeSame Q U size rm opcode rn rd) else none
  else if w &&& 0xDF200400 = 0x5E200400 then
    -- Scalar three same: 01 U 11110 size 1 Rm opcode 1 Rn Rd
    let opcode := bits w 15 11
    let ok := if opcode / 8 = 0b11 then neonThreeSameFPOK true U (size / 2 = 1) opcode
      else neonSThreeSameIntOK size opcode
    if ok then some (.sThreeSame U size rm opcode rn rd) else none
  else if w &&& 0x9F200C00 = 0x0E200000 then
    -- Three different: 0 Q U 01110 size 1 Rm opcode 00 Rn Rd
    let opcode := bits w 15 12
    let ok := if opcode = 0b1001 || opcode = 0b1011 || opcode = 0b1101 then !U && (size = 1 || size = 2)
      else opcode < 0b1110 && size ≠ 3
    if ok then some (.threeDiff Q U size rm opcode rn rd) else none
  else if w &&& 0xDF200C00 = 0x5E200000 then
    -- Scalar three different: 01 U 11110 size 1 Rm opcode 00 Rn Rd
    let opcode := bits w 15 12
    if !U && (opcode = 0b1001 || opcode = 0b1011 || opcode = 0b1101) && (size = 1 || size = 2) then
      some (.sThreeDiff U size rm opcode rn rd)
    else none
  else if w &&& 0x9F3E0C00 = 0x0E200800 then
    -- Two-register miscellaneous: 0 Q U 01110 size 10000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    let ok := if opcode ≥ 0b01100 && opcode ≠ 0b10010 && opcode ≠ 0b10011 && opcode ≠ 0b10100 then
        neonTwoMiscFPOK U Q (size / 2 = 1) (size % 2) opcode
      else neonTwoMiscIntOK U Q size opcode
    if ok then some (.twoMisc Q U size opcode rn rd) else none
  else if w &&& 0xDF3E0C00 = 0x5E200800 then
    -- Scalar two-register miscellaneous: 01 U 11110 size 10000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    if neonSTwoMiscOK U size opcode then some (.sTwoMisc U size opcode rn rd) else none
  else if w &&& 0x9F3E0C00 = 0x0E300800 then
    -- Across lanes: 0 Q U 01110 size 11000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    let intOK := size ≠ 3 && !(size = 2 && !Q)
    let ok :=
      if opcode = 0b00011 || opcode = 0b01010 || opcode = 0b11010 then intOK
      else if opcode = 0b11011 then !U && intOK
      else if opcode = 0b01100 || opcode = 0b01111 then U && size % 2 = 0 && Q   -- F(MAX|MIN)(NM)V .4S
      else false
    if ok then some (.across Q U size opcode rn rd) else none
  else if w &&& 0xDF3E0C00 = 0x5E300800 then
    -- Scalar pairwise: 01 U 11110 size 11000 opcode 10 Rn Rd
    let opcode := bits w 16 12
    let ok := if opcode = 0b11011 then !U && size = 3                 -- ADDP (scalar)
      else if opcode = 0b01101 then U && size / 2 = 0                  -- FADDP (scalar)
      else if opcode = 0b01100 || opcode = 0b01111 then U              -- F(MAX|MIN)(NM)P (scalar)
      else false
    if ok then some (.sPairwise U size opcode rn rd) else none
  else if w &&& 0xBF208C00 = 0x0E000800 then
    -- Permute: 0 Q 001110 size 0 Rm 0 opcode 10 Rn Rd
    let opcode := bits w 14 12
    if opcode % 4 = 0 || (size = 3 && !Q) then none
    else some (.perm Q size rm opcode rn rd)
  else if w &&& 0x9F800400 = 0x0F000400 then
    -- Shift by immediate: 0 Q U 011110 immh immb opcode 1 Rn Rd (immh = 0: modified immediate)
    let immh := bits w 22 19
    let opcode := bits w 15 11
    if immh ≠ 0 && neonShiftImmOK U Q immh opcode then
      some (.shiftImm Q U immh (bits w 18 16) opcode rn rd)
    else none
  else if w &&& 0xDF800400 = 0x5F000400 then
    -- Scalar shift by immediate: 01 U 111110 immh immb opcode 1 Rn Rd
    let immh := bits w 22 19
    let opcode := bits w 15 11
    if neonSShiftImmOK U immh opcode then some (.sShiftImm U immh (bits w 18 16) opcode rn rd)
    else none
  else if w &&& 0x9F000400 = 0x0F000000 then
    -- Vector x indexed element: 0 Q U 01111 size L M Rm opcode H 0 Rn Rd
    let L := bit w 21
    let opcode := bits w 15 12
    if neonByElemOK U Q L size opcode then
      some (.byElem Q U size L (bit w 20) (bits w 19 16) opcode (bit w 11) rn rd)
    else none
  else if w &&& 0xDF000400 = 0x5F000000 then
    -- Scalar x indexed element: 01 U 11111 size L M Rm opcode H 0 Rn Rd
    let L := bit w 21
    let opcode := bits w 15 12
    if neonSByElemOK U L size opcode then
      some (.sByElem U size L (bit w 20) (bits w 19 16) opcode (bit w 11) rn rd)
    else none
  else if w &&& 0xFFE0FC00 = 0x5E000400 then
    -- Scalar copy, DUP (element): 01 0 11110000 imm5 0 0000 1 Rn Rd; `size = LowestSetBit(imm5)`
    let imm5 := bits w 20 16
    if imm5 % 16 = 0 then none else some (.sDup imm5 rn rd)
  else if w &&& 0x7F200000 = 0x1E000000 then
    -- Conversion between floating point and fixed point: sf 0 0 11110 ftype 0 rmode opcode
    -- scale Rn Rd. `if sf == '0' && scale<5> == '0' then UNDEFINED`; SCVTF/UCVTF are
    -- `rmode:opcode<2:1> = 00:01`, FCVTZS/FCVTZU `11:00`; half precision is rejected.
    let sf := bit w 31
    let ftype := bits w 23 22
    let rmode := bits w 20 19
    let opcode := bits w 18 16
    let scale := bits w 15 10
    if ftype ≥ 2 then none
    else if !sf && scale < 32 then none
    else if (rmode = 0 && opcode / 2 = 1) || (rmode = 3 && opcode / 2 = 0) then
      some (.fpCvtFixed sf ftype rmode opcode scale rn rd)
    else none
  else none

/-- SIMD&FP loads and stores of `NeonInstr`: LD2–LD4/ST2–ST4 (multiple structures) and
LDNP/STNP. -/
def decodeNeonLdSt (w : Nat) : Option NeonInstr :=
  let rt := bits w 4 0
  let rn := bits w 9 5
  if w &&& 0xBFBF0000 = 0x0C000000 || w &&& 0xBFA00000 = 0x0C800000 then
    -- Load/store multiple structures: 0 Q 0011000 L 000000 opcode size Rn Rt (no offset),
    -- 0 Q 0011001 L 0 Rm opcode size Rn Rt (post-index). LD4/ST4 opcode 0000, LD3/ST3 0100,
    -- LD2/ST2 1000; `if size:Q == '110' && selem != 1 then UNDEFINED`.
    let opcode := bits w 15 12
    let size := bits w 11 10
    let Q := bit w 30
    if (opcode = 0b0000 || opcode = 0b0100 || opcode = 0b1000) && !(size = 3 && !Q) then
      some (.ldstStruct Q (bit w 22) opcode size (bit w 23) (bits w 20 16) rn rt)
    else none
  else if w &&& 0x3F800000 = 0x2C000000 then
    -- LDNP/STNP (SIMD&FP): opc 101 1 000 L imm7 Rt2 Rn Rt; `opc == '11'` UNDEFINED; a load with
    -- `t == t2` is CONSTRAINED UNPREDICTABLE.
    let opc := bits w 31 30
    let L := bit w 22
    let rt2 := bits w 14 10
    if opc = 3 || (L && rt == rt2) then none
    else some (.ldstNP opc L (bits w 21 15) rt2 rn rt)
  else none

/-- The Advanced SIMD classes of `NeonInstr`, by the top-level `op0` field. -/
def decodeNeon (w : Nat) : Option NeonInstr :=
  if w ≥ 2 ^ 32 then none else
  let op0 := bits w 28 25
  if op0 % 2 = 0 && op0 / 4 % 2 = 1 then decodeNeonLdSt w   -- x1x0: loads and stores
  else if op0 % 8 = 0b111 then decodeNeonDP w                -- x111: SIMD&FP data processing
  else none

end Janus.Arm64
