import Janus.Tactic.Basic
import Janus.Tactic.Common

/-!
# Symbolic execution of the ordered, exclusive, atomic and DC ZVA instructions

`exec` equations (by `rfl`) and helper unfoldings for the instructions added with the
single-threaded atomics model (`Instr.ldstOrdered`, `ldExcl`, `atomic`, `cas`, `casp`, `clrex`,
`prefetch`, `mrsDczid`, `dcZva`), registered in the `janus_exec` simp set. Kept in a file of
its own so the core automation (`Janus.Tactic.Basic`, `Core`) is untouched. Nothing here is
trusted.
-/

namespace Janus.Tactic

open Janus Janus.Arm64

section ExecEqns

variable (s : State)

@[janus_exec] theorem exec_clrex (crm : Nat) : exec (.clrex crm) s = .ok s.next := rfl
@[janus_exec] theorem exec_prefetch (prfop : Nat) : exec (.prefetch prfop) s = .ok s.next := rfl
@[janus_exec] theorem exec_mrsDczid (rt : Nat) :
    exec (.mrsDczid rt) s = .ok (s.writeZR rt (s.dczid.setWidth 64)).next := rfl
@[janus_exec] theorem exec_dcZva (rt : Nat) : exec (.dcZva rt) s = execDcZva s rt := rfl
@[janus_exec] theorem exec_ldstOrdered (size : Nat) (L rcpc : Bool) (rn rt : Nat) :
    exec (.ldstOrdered size L rcpc rn rt) s = execOrdered s size L rn rt := rfl
@[janus_exec] theorem exec_ldExcl (size : Nat) (o0 : Bool) (rn rt : Nat) :
    exec (.ldExcl size o0 rn rt) s = execOrdered s size true rn rt := rfl
@[janus_exec] theorem exec_atomic (size : Nat) (A R : Bool) (rs : Nat) (op : AtomicOp) (rn rt : Nat) :
    exec (.atomic size A R rs op rn rt) s = execAtomic s size op rs rn rt := rfl
@[janus_exec] theorem exec_cas (size : Nat) (L o0 : Bool) (rs rn rt : Nat) :
    exec (.cas size L o0 rs rn rt) s = execCas s size rs rn rt := rfl
@[janus_exec] theorem exec_casp (sz L o0 : Bool) (rs rn rt : Nat) :
    exec (.casp sz L o0 rs rn rt) s = execCasp s (if sz then 8 else 4) rs rn rt := rfl

end ExecEqns

attribute [janus_exec] execOrdered execAtomic execCas execCasp execDcZva atomicOp

/-- The value of a byte flag read with `ldrb` and tested with `tbz/tbnz #0`. -/
@[janus_exec, janus_post] theorem getLsbD_zero_ofNat_readLE_1 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 1)).getLsbD 0 = decide (m.readLE a 1 % 2 = 1) := by
  rw [BitVec.getLsbD_ofNat]
  simp [Nat.testBit_zero]

/-- `tbz`/`tbnz` compare a bit with the branch sense: put the comparison in `decide` form. -/
@[janus_exec, janus_post] theorem decide_beq_false (p : Prop) [Decidable p] :
    (decide p == false) = decide ¬p := by by_cases h : p <;> simp [h]
@[janus_exec, janus_post] theorem decide_beq_true (p : Prop) [Decidable p] :
    (decide p == true) = decide p := by by_cases h : p <;> simp [h]

-- `tbz`/`tbnz` on a bit that execution already computed (e.g. after `cset`).
attribute [janus_exec, janus_post] Bool.true_beq Bool.false_beq Bool.not_true Bool.not_false

/-- `toNat` of a zero-extended 32-bit load. -/
@[janus_exec, janus_post] theorem toNat_ofNat_readLE_4 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 4)).toNat = m.readLE a 4 := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_trans (Memory.readLE_lt m a 4) (by decide))

end Janus.Tactic

/-! ## Addresses of writable globals named by the code

The extractor does not copy writable globals (their contents are not fixed by the binary), so a
proof that reads one, e.g. `runtime.arm64HasATOMICS`, states its precondition at the address the
code computes. `adrpLdTarget` recomputes that address from the extracted `ADRP`+`LDR` words, so a
statement does not depend on a hand-copied literal, and `janus_eval_nat` turns it into a numeral
(checked by `decide`) for the executor. -/

namespace Janus.Spec

open Janus Janus.Arm64

/-- Word `i` of the extracted segment `name` (0 if absent). -/
def segWord (p : Program) (name : String) (i : Nat) : Nat :=
  match p.segments.find? (·.name == name) with
  | some seg => seg.words.getD i 0
  | none => 0

/-- The address read by the pair `ADRP Xd, page` (word `w1` at `pc`) and
`LDR{B,H,SW,W,X} Wt|Xt, [Xd, #imm12 << scale]` (word `w2`):
`(pc AND NOT 0xFFF) + SignExtend(immhi:immlo:Zeros(12), 64) + (imm12 << scale)`, modulo `2^64`. -/
def adrpLdTarget (pc w1 w2 scale : Nat) : Nat :=
  let imm := bits w1 23 5 * 4 + bits w1 30 29
  ((pc / 4096 * 4096 + imm * 4096 + (if imm ≥ 2 ^ 20 then 2 ^ 64 - 2 ^ 33 else 0)) % 2 ^ 64 +
    bits w2 21 10 * 2 ^ scale) % 2 ^ 64

end Janus.Spec

namespace Janus.Tactic

open Lean Elab Tactic Meta in
/-- `janus_eval_nat h : c` for a closed `Nat` constant `c`: evaluates it and adds
`h : c = <numeral>`, proved by `decide` (checked by the kernel; the evaluation only finds the
numeral). The constant is evaluated over imported constants when possible
(`Common.unfoldLocalDefs`), so that the evaluation does not wait for the compiled environment of
the rest of the file. -/
elab "janus_eval_nat " h:ident " : " c:ident : tactic => withMainContext do
  let e ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload c)
  let e' ← Common.unfoldLocalDefs e
  let v ← if e' == e then unsafe evalExpr Nat (mkConst ``Nat) e else
    try unsafe evalExpr Nat (mkConst ``Nat) e' catch _ => unsafe evalExpr Nat (mkConst ``Nat) e
  let eq ← mkEq e (mkNatLit v)
  let pf ← mkDecideProof eq
  let (_, g') ← (← (← getMainGoal).assert h.getId eq pf).intro1P
  replaceMainGoal [g']

end Janus.Tactic
