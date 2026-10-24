import Janus.Arm64.Float
import Janus.Arm64.Vector

/-!
# Scalar floating-point instructions (trusted)

The `Operation` pseudocode of the scalar floating-point data-processing classes, on top of the
ASL library in `Janus.Arm64.Float`; `Janus.Arm64.exec` dispatches the floating-point
constructors of `Instr` here.

* Operands are `V[n, esize]` (the low 32 or 64 bits of the register).
* A scalar result is written as `V[d, 128] = result` where `result` starts as `V[src, 128]` when
  `IsMerging(FPCR)` (`FPCR.NEP = 1`, FEAT_AFP) and as zero otherwise, with element 0 replaced:
  the merge source is `V[n]` for `FADD FSUB FMUL FNMUL FDIV FMAX FMIN FMAXNM FMINNM`, `V[a]`
  for `FMADD FMSUB FNMADD FNMSUB`, and `V[d]` for `FABS FNEG FSQRT FCVT FRINT*` and
  `SCVTF`/`UCVTF`. `FMOV` (register and immediate) and `FCSEL` never merge
  (`V[d, esize] = ...` zero-extends).
* Exceptions (`FP.Exc`): if one raised through `FPProcessException` has its trap enabled in
  `FPCR`, the instruction faults with `Fault.fpTrapped`; otherwise every raised bit is ORed
  into `FPSR` (`fpCommit`).
* `FCMP`/`FCMPE`/`FCCMP`/`FCCMPE` write `PSTATE.NZCV`; the conversions to integers write
  `X[d, intsize]` (zero-extended, `XZR` discards).

`ftype` is `00` (single) or `01` (double); the decoder rejects the other values.
-/

namespace Janus.Arm64

open Janus.Float Janus.Arm64.FP

/-- The format of `ftype`. -/
def ftypeFmt (ftype : Nat) : Fmt := if ftype = 0 then binary32 else binary64

/-- The element size of `ftype`. -/
def ftypeSize (ftype : Nat) : Nat := if ftype = 0 then 32 else 64

/-- `NZCV` as `Flags` from the 4-bit value `N:Z:C:V`. -/
def flagsOfNzcv (nzcv : Nat) : Flags :=
  { n := nzcv / 8 % 2 = 1, z := nzcv / 4 % 2 = 1, c := nzcv / 2 % 2 = 1, v := nzcv % 2 = 1 }

/-- Commit the exceptions `exc` of a floating-point instruction executed in `s` whose
architectural result is `t`: fault if a raised exception is trap-enabled, otherwise `t` with
the raised bits ORed into `FPSR`. -/
def fpCommit (s : State) (exc : Exc) (t : State) : Except Fault State :=
  if exc.proc &&& trapEnables s.fpcr.toNat ≠ 0 then .error (.fpTrapped s.pc.toNat)
  else .ok { t with fpsr := t.fpsr ||| BitVec.ofNat 32 (exc.proc ||| exc.direct) }

/-- `V[d, 128] = result` where `result` is `base` (`V[src, 128]` when merging, else zero) with
element 0 of `esize` bits set to `r`. -/
def State.setScalar (s : State) (d esize base r : Nat) : State :=
  s.setV d 128 (base / 2 ^ esize * 2 ^ esize + r % 2 ^ esize)

/-- The upper-part source of a scalar result: `V[src, 128]` when `FPCR.NEP = 1`, else zero. -/
def State.mergeBase (s : State) (src : Nat) : Nat :=
  if isMerging s.fpcr.toNat then s.getV src 128 else 0

/-- Floating-point data-processing (1 source): `FMOV` (`opcode = 0`), `FABS` (1), `FNEG` (2),
`FSQRT` (3), `FCVT` to single (4) / double (5), `FRINTN` (8), `FRINTP` (9), `FRINTM` (10),
`FRINTZ` (11), `FRINTA` (12), `FRINTX` (14), `FRINTI` (15). -/
def execFpDP1 (s : State) (ftype opcode rn rd : Nat) : Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let fpcr := s.fpcr.toNat
  let op := s.getV rn N
  if opcode = 0 then .ok (s.setV rd N op)
  else if opcode = 1 then .ok (s.setScalar rd N (s.mergeBase rd) (fpAbs f fpcr op))
  else if opcode = 2 then .ok (s.setScalar rd N (s.mergeBase rd) (fpNeg f fpcr op))
  else if opcode = 3 then
    let o := fpSqrt f fpcr op
    fpCommit s o.2 (s.setScalar rd N (s.mergeBase rd) o.1)
  else if opcode = 4 || opcode = 5 then
    let g := if opcode = 4 then binary32 else binary64
    let o := fpConvert f g fpcr (roundingMode fpcr) op
    fpCommit s o.2 (s.setScalar rd (if opcode = 4 then 32 else 64) (s.mergeBase rd) o.1)
  else
    -- FRINT<r>: rmode = opcode<2:0>; 0xx FPDecodeRounding, 100 TIEAWAY, 110 FRINTX (exact),
    -- 111 FRINTI
    let rmode := opcode % 8
    let rounding :=
      if rmode < 4 then decodeRounding rmode else if rmode = 4 then RM.rna else roundingMode fpcr
    let o := fpRoundInt f fpcr rounding (rmode = 6) op
    fpCommit s o.2 (s.setScalar rd N (s.mergeBase rd) o.1)

/-- Floating-point data-processing (2 source): `FMUL` (`opcode = 0`), `FDIV` (1), `FADD` (2),
`FSUB` (3), `FMAX` (4), `FMIN` (5), `FMAXNM` (6), `FMINNM` (7), `FNMUL` (8). -/
def execFpDP2 (s : State) (ftype rm opcode rn rd : Nat) : Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let fpcr := s.fpcr.toNat
  let op1 := s.getV rn N
  let op2 := s.getV rm N
  let o :=
    if opcode = 0 then fpMul f fpcr op1 op2
    else if opcode = 1 then fpDiv f fpcr op1 op2
    else if opcode = 2 then fpAdd f fpcr op1 op2
    else if opcode = 3 then fpSub f fpcr op1 op2
    else if opcode = 4 then fpMaxMin true f fpcr (ah fpcr) op1 op2
    else if opcode = 5 then fpMaxMin false f fpcr (ah fpcr) op1 op2
    else if opcode = 6 then fpMaxMinNum true f fpcr op1 op2
    else if opcode = 7 then fpMaxMinNum false f fpcr op1 op2
    else (fpNeg f fpcr (fpMul f fpcr op1 op2).1, (fpMul f fpcr op1 op2).2)
  fpCommit s o.2 (s.setScalar rd N (s.mergeBase rn) o.1)

/-- Floating-point data-processing (3 source): `FMADD` (`o1 o0 = 00`), `FMSUB` (01),
`FNMADD` (10), `FNMSUB` (11): `opa_neg = o1`, `op1_neg = o0 != o1`, then
`FPMulAdd(operanda, operand1, operand2)`. -/
def execFpDP3 (s : State) (ftype : Nat) (o1 : Bool) (rm : Nat) (o0 : Bool) (ra rn rd : Nat) :
    Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let fpcr := s.fpcr.toNat
  let a := s.getV ra N
  let n := s.getV rn N
  let m := s.getV rm N
  let a := if o1 then fpNeg f fpcr a else a
  let n := if o0 != o1 then fpNeg f fpcr n else n
  let o := fpMulAdd f fpcr a n m
  fpCommit s o.2 (s.setScalar rd N (s.mergeBase ra) o.1)

/-- `FCMP` / `FCMPE` (`opc<1>`: signal on quiet NaNs), against `#0.0` when `opc<0> = 1`. -/
def execFpCmp (s : State) (ftype rm opc rn : Nat) : Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let op1 := s.getV rn N
  let op2 := if opc % 2 = 1 then zero f false else s.getV rm N
  let o := fpCompare f s.fpcr.toNat (opc / 2 % 2 = 1) op1 op2
  fpCommit s o.2 { s with flags := flagsOfNzcv o.1 }

/-- `FCCMP` / `FCCMPE` (`signal`): the comparison's `NZCV` if the condition holds, else
`nzcv`. -/
def execFpCcmp (s : State) (ftype rm : Nat) (holds signal : Bool) (rn nzcv : Nat) :
    Except Fault State :=
  if holds then
    let f := ftypeFmt ftype
    let N := ftypeSize ftype
    let o := fpCompare f s.fpcr.toNat signal (s.getV rn N) (s.getV rm N)
    fpCommit s o.2 { s with flags := flagsOfNzcv o.1 }
  else .ok { s with flags := flagsOfNzcv nzcv }

/-- `FCSEL`: `V[d, esize] = if ConditionHolds(cond) then V[n] else V[m]`. -/
def execFpCsel (s : State) (ftype rm : Nat) (holds : Bool) (rn rd : Nat) : State :=
  let N := ftypeSize ftype
  s.setV rd N (if holds then s.getV rn N else s.getV rm N)

/-- `FMOV` (scalar, immediate): `V[d, esize] = VFPExpandImm(imm8)`. -/
def execFpImm (s : State) (ftype imm8 rd : Nat) : State :=
  s.setV rd (ftypeSize ftype) (vfpExpandImm (ftypeFmt ftype) imm8)

/-- Conversions between floating point and integers (not the `FMOV` forms):
`FCVT{N,P,M,Z}{S,U}` (`opcode = 00u`, `rmode` selects the rounding), `SCVTF`/`UCVTF`
(`opcode = 01u`, `rmode = 00`, rounding from `FPCR`), `FCVTA{S,U}` (`opcode = 10u`,
`rmode = 00`, ties away). `sf`: 64-bit general register. -/
def execFpCvtInt (s : State) (sf : Bool) (ftype rmode opcode rn rd : Nat) : Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let fpcr := s.fpcr.toNat
  let intsize := if sf then 64 else 32
  let unsigned := opcode % 2 = 1
  if opcode / 2 = 1 then
    let x := (s.readZR rn).toNat % 2 ^ intsize
    let o := fixedToFP f fpcr unsigned (roundingMode fpcr) intsize x
    fpCommit s o.2 (s.setScalar rd N (s.mergeBase rd) o.1)
  else
    let rounding := if opcode / 2 = 2 then RM.rna else decodeRounding rmode
    let o := fpToFixed f fpcr unsigned rounding intsize (s.getV rn N)
    fpCommit s o.2 (s.writeZR rd (BitVec.ofNat 64 o.1))

end Janus.Arm64
