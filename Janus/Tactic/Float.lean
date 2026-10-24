import Janus.Tactic.Vector
import Janus.Arm64.ExecFloat

/-!
# Symbolic execution of the scalar floating-point instructions (arm64)

`exec` equations (by `rfl`) for the floating-point constructors of `Instr` and the unfoldings
of the executor plumbing (`execFpDP2`, `fpCommit`, `State.setScalar`, ...), in `janus_exec`.
The floating-point operations themselves (`FP.fpAdd`, `FP.fpMulAdd`, `FP.fpToFixed`, ...) are
**not** unfolded: a symbolic register holds a term like `(FP.fpAdd binary64 fpcr a b).1`.
The steps evaluate completely when the proof provides the value of `FPCR` (e.g. `s.fpcr = 0`
as a `janus_run` argument): then the trap check `exc &&& trapEnables fpcr ≠ 0` and the merge
selection `IsMerging(FPCR)` are closed literals. Nothing here is trusted.
-/

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.Arm64.FP

attribute [janus_exec] ftypeFmt ftypeSize execFpDP1 execFpDP2 execFpDP3 execFpCmp execFpCcmp
  execFpCsel execFpImm execFpCvtInt fpCommit State.setScalar State.mergeBase FP.decodeRounding

@[janus_exec] theorem trapEnables_zero : trapEnables 0 = 0 := by decide
@[janus_exec] theorem fp_and_zero (n : Nat) : n &&& 0 = 0 := Nat.and_zero n
@[janus_exec] theorem fp_mod_one (n : Nat) : n % 1 = 0 := Nat.mod_one n
@[janus_exec] theorem isMerging_zero : isMerging 0 = false := by decide
@[janus_exec] theorem fpcr_zero_toNat : (0 : BitVec 32).toNat = 0 := rfl

section ExecEqns

variable (s : State)

@[janus_exec] theorem exec_fpDP1 (ftype opcode rn rd : Nat) :
    exec (.fpDP1 ftype opcode rn rd) s =
      match execFpDP1 s ftype opcode rn rd with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_fpDP2 (ftype rm opcode rn rd : Nat) :
    exec (.fpDP2 ftype rm opcode rn rd) s =
      match execFpDP2 s ftype rm opcode rn rd with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_fpDP3 (ftype : Nat) (o1 : Bool) (rm : Nat) (o0 : Bool) (ra rn rd : Nat) :
    exec (.fpDP3 ftype o1 rm o0 ra rn rd) s =
      match execFpDP3 s ftype o1 rm o0 ra rn rd with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_fpCmp (ftype rm opc rn : Nat) :
    exec (.fpCmp ftype rm opc rn) s =
      match execFpCmp s ftype rm opc rn with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_fpCcmp (ftype rm cond : Nat) (signal : Bool) (rn nzcv : Nat) :
    exec (.fpCcmp ftype rm cond signal rn nzcv) s =
      match execFpCcmp s ftype rm (conditionHolds cond s.flags) signal rn nzcv with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_fpCsel (ftype rm cond rn rd : Nat) :
    exec (.fpCsel ftype rm cond rn rd) s =
      .ok (execFpCsel s ftype rm (conditionHolds cond s.flags) rn rd).next := rfl
@[janus_exec] theorem exec_fpImm (ftype imm8 rd : Nat) :
    exec (.fpImm ftype imm8 rd) s = .ok (execFpImm s ftype imm8 rd).next := rfl
@[janus_exec] theorem exec_fpCvtInt (sf : Bool) (ftype rmode opcode rn rd : Nat) :
    exec (.fpCvtInt sf ftype rmode opcode rn rd) s =
      match execFpCvtInt s sf ftype rmode opcode rn rd with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl

end ExecEqns

end Janus.Tactic
