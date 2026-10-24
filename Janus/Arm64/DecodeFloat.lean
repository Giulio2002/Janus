import Janus.Arm64.Instr
import Janus.Arm64.Bits

/-!
# A64 decoder: scalar floating point

The scalar floating-point data-processing classes of the A64 "Data Processing -- Scalar
Floating-Point and Advanced SIMD" group (`op0 = x111`), for single (`ftype = 00`) and double
(`ftype = 01`) precision. `decodeSimdDP` (`Janus.Arm64.Decode`) calls `decodeFloat` for the
words its other branches do not claim, and `decodeFpCvtInt` for the conversions between
floating point and integers that are not `FMOV`.

Rejected (`none`): half precision (`ftype = 11`, FEAT_FP16) and `ftype = 10`, `M = 1` or
`S = 1`, BFCVT, FCVT to or from half precision and FCVT to the same precision, FRINT32*/
FRINT64* (FEAT_FRINTTS), FJCVTZS, conversions to and from fixed point, every unallocated
`opcode`/`rmode` combination, and the CONSTRAINED UNPREDICTABLE forms (non-zero `Rm` in
`FCMP #0.0`, non-zero should-be-zero `opcode2<2:0>` and `imm5`). Encodings from the ARM ARM
tables (C4.1.96) and the decode pseudocode of each instruction.
-/

namespace Janus.Arm64

/-- Conversion between floating point and integer other than FMOV
(`sf 0 0 11110 ftype 1 rmode opcode 000000 Rn Rd`; the caller has matched the fixed bits). -/
def decodeFpCvtInt (w : Nat) : Option Instr :=
  let sf := bit w 31
  let ftype := bits w 23 22
  let rmode := bits w 20 19
  let opcode := bits w 18 16
  let rn := bits w 9 5
  let rd := bits w 4 0
  if ftype ≥ 2 then none
  else if opcode ≤ 1 then some (.fpCvtInt sf ftype rmode opcode rn rd)
  else if opcode ≤ 5 then (if rmode = 0 then some (.fpCvtInt sf ftype rmode opcode rn rd) else none)
  else none

/-- The other scalar floating-point classes (`M 0 S 1111x ftype ...` with `M = S = 0`). -/
def decodeFloat (w : Nat) : Option Instr :=
  let rd := bits w 4 0
  let rn := bits w 9 5
  let rm := bits w 20 16
  let ftype := bits w 23 22
  if ftype ≥ 2 then none
  else if w &&& 0xFF000000 = 0x1F000000 then
    -- Floating-point data-processing (3 source): 0 0 0 11111 ftype o1 Rm o0 Ra Rn Rd
    some (.fpDP3 ftype (bit w 21) rm (bit w 15) (bits w 14 10) rn rd)
  else if w &&& 0xFF200000 = 0x1E200000 then
    let low := bits w 11 10
    if low = 1 then
      -- Floating-point conditional compare: 0 0 0 11110 ftype 1 Rm cond 01 Rn op nzcv
      some (.fpCcmp ftype rm (bits w 15 12) (bit w 4) rn (bits w 3 0))
    else if low = 2 then
      -- Floating-point data-processing (2 source): 0 0 0 11110 ftype 1 Rm opcode 10 Rn Rd
      let opcode := bits w 15 12
      if opcode ≤ 8 then some (.fpDP2 ftype rm opcode rn rd) else none
    else if low = 3 then
      -- Floating-point conditional select: 0 0 0 11110 ftype 1 Rm cond 11 Rn Rd
      some (.fpCsel ftype rm (bits w 15 12) rn rd)
    else if bits w 14 10 = 0b10000 then
      -- Floating-point data-processing (1 source): 0 0 0 11110 ftype 1 opcode 10000 Rn Rd
      let opcode := bits w 20 15
      let ok := opcode ≤ 3 || ((opcode = 4 || opcode = 5) && opcode - 4 ≠ ftype) ||
        (8 ≤ opcode && opcode ≤ 15 && opcode ≠ 13)
      if ok then some (.fpDP1 ftype opcode rn rd) else none
    else if bits w 13 10 = 0b1000 then
      -- Floating-point compare: 0 0 0 11110 ftype 1 Rm op 1000 Rn opcode2, op = 00,
      -- opcode2 = opc:000; FCMP #0.0 has Rm = (0)(0)(0)(0)(0)
      if bits w 15 14 ≠ 0 || bits w 2 0 ≠ 0 then none else
      let opc := bits w 4 3
      if opc % 2 = 1 && rm ≠ 0 then none else some (.fpCmp ftype rm opc rn)
    else if bits w 12 10 = 0b100 then
      -- Floating-point immediate: 0 0 0 11110 ftype 1 imm8 100 imm5 Rd, imm5 = 00000
      if bits w 9 5 ≠ 0 then none else some (.fpImm ftype (bits w 20 13) rd)
    else none
  else none

end Janus.Arm64
