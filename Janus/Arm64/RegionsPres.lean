import Lean
import Janus.Arm64.Exec
import Janus.Arm64.MemoryLemmas

/-!
# The Arm64 executor keeps the memory regions

`exec_regions : exec i s = .ok s' → s'.mem.regions = s.mem.regions` (and `step_regions`): every
store goes through the checked `store`, which only rewrites bytes (`Memory.store_regions`), and no
other instruction touches `mem`. This is the base of `Program.Steps.regions` (`Janus.Run`).

The proof is a case analysis on the instruction, done by one tactic (`regok`) over the unfolded
executor, with a `RegOK s r` ("every successful result of `r` has the regions of `s`") goal.
-/

namespace Janus.Arm64

/-- Every successful result of `r` has the same regions as `s`. -/
def RegOK (s : State) (r : Except Fault State) : Prop :=
  ∀ t, r = .ok t → t.mem.regions = s.mem.regions

namespace RegOK

variable {s t : State}

theorem ok (h : t.mem.regions = s.mem.regions) : RegOK s (.ok t) :=
  fun _ e => by cases e; exact h

theorem error {e : Fault} : RegOK s (.error e) := fun _ e => by cases e

theorem ite {c : Prop} [Decidable c] {a b : Except Fault State} (h1 : c → RegOK s a)
    (h2 : ¬c → RegOK s b) : RegOK s (if c then a else b) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h1 hc
  · rw [ite_eq_right hc]; exact h2 hc

theorem of_eq {E : Except Fault State} (h : RegOK s E) (he : E = .ok t) :
    t.mem.regions = s.mem.regions := h t he

end RegOK

namespace State

@[simp] theorem mem_next (s : State) : s.next.mem = s.mem := rfl
@[simp] theorem mem_setX {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setX r v).mem = s.mem := by
  simp [setX]
@[simp] theorem mem_setXSP {N : Nat} (s : State) (r : Nat) (v : BitVec N) :
    (s.setXSP r v).mem = s.mem := by simp [setXSP]
@[simp] theorem mem_setV (s : State) (d w v : Nat) : (s.setV d w v).mem = s.mem := rfl
@[simp] theorem mem_setFlags (s : State) (f : Flags) : (s.setFlags f).mem = s.mem := rfl

end State

theorem mem_ldStructRegs (s : State) (rt esize ds blk : Nat) :
    ∀ k selem, (NeonExec.ldStructRegs s rt esize ds blk k selem).mem = s.mem := by
  intro k selem
  induction k with
  | zero => rfl
  | succ k ih => simp only [NeonExec.ldStructRegs, State.mem_setV, ih]

theorem mem_execCrypto (s : State) (c : CryptoInstr) : (execCrypto s c).mem = s.mem := by
  unfold execCrypto
  split <;> (repeat' split) <;> first | rfl | simp

theorem mem_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then a else b).mem = if c then a.mem else b.mem := apply_ite _ _ _ _

open Lean Elab Tactic in
/-- The closers of `regok` that need the hypotheses `E = .ok t`: `t`'s regions are those of `s`
because `RegOK s E`, which `regok` proves in turn. -/
syntax (name := regokEq) "regok_eq" : tactic

syntax (name := regokTac) "regok" : tactic

syntax (name := regokStore) "regok_store" : tactic

/-- Lemmas about helper functions proved after the closers (`regok`); extended by `macro_rules`. -/
syntax (name := regokLem) "regok_lem" : tactic

macro_rules
  | `(tactic| regok_lem) => `(tactic| fail "no lemma")

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| regok_eq) => withMainContext do
    let g ← getMainGoal
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, _, r) := ty.eq? | continue
      unless r.isAppOfArity ``Except.ok 3 do continue
      let e ← Term.exprToSyntax (mkFVar d.fvarId)
      try
        evalTactic (← `(tactic| (refine RegOK.of_eq ?_ $e; regok)))
        return
      catch _ => setGoals [g]
    throwError "regok_eq: no hypothesis applies"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| regok_store) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      unless r.isAppOfArity ``Except.ok 3 && l.isAppOfArity ``store 4 && r.appArg!.isFVar do continue
      let e ← Term.exprToSyntax (mkFVar d.fvarId)
      evalTactic (← `(tactic| (obtain ⟨-, hh⟩ := (store_ok_iff _ _).1 $e; subst hh)))
      replaceMainGoal [← (← getMainGoal).tryClear d.fvarId]
      return
    throwError "regok_store: no store hypothesis"

macro_rules
  | `(tactic| regok) => `(tactic| repeat' first
      | exact RegOK.error
      | assumption
      | regok_lem
      | regok_store
      | (apply RegOK.ok; simp only [mem_ite, State.mem_next, State.mem_writeZR, State.mem_writeSP,
          State.mem_setX, State.mem_setXSP, State.mem_setV, State.mem_setFlags, Memory.regions_writeLE,
          mem_ldStructRegs, mem_execCrypto, ite_self]; done)
      | (apply RegOK.ok; simp only [mem_ite, State.mem_next, State.mem_writeZR, State.mem_writeSP,
          State.mem_setX, State.mem_setXSP, State.mem_setV, State.mem_setFlags, Memory.regions_writeLE,
          mem_ldStructRegs, mem_execCrypto, ite_self]; regok_eq)
      | (apply RegOK.ite <;> intro _)
      | split
      | dsimp only)


/-! ## The recursive helpers -/

theorem ldMulti_regok (s : State) (rt rbytes : Nat) (addr : W64) :
    ∀ k, RegOK s (ldMulti s rt rbytes addr k) := by
  intro k
  induction k with
  | zero => simp only [ldMulti]; exact RegOK.ok rfl
  | succ k ih => simp only [ldMulti]; regok

theorem stMulti_regok (s : State) (rt rbytes : Nat) (addr : W64) :
    ∀ k, RegOK s (stMulti s rt rbytes addr k) := by
  intro k
  induction k with
  | zero => simp only [stMulti]; exact RegOK.ok rfl
  | succ k ih => simp only [stMulti]; regok

theorem ldSingle_regok (s : State) (rt eb idx : Nat) (rep : Bool) (ds : Nat) (addr : W64) :
    ∀ k, RegOK s (ldSingle s rt eb idx rep ds addr k) := by
  intro k
  induction k with
  | zero => simp only [ldSingle]; exact RegOK.ok rfl
  | succ k ih => simp only [ldSingle]; regok

theorem stSingle_regok (s : State) (rt eb idx : Nat) (addr : W64) :
    ∀ k, RegOK s (stSingle s rt eb idx addr k) := by
  intro k
  induction k with
  | zero => simp only [stSingle]; exact RegOK.ok rfl
  | succ k ih => simp only [stSingle]; regok

macro_rules
  | `(tactic| regok_lem) => `(tactic| first
      | exact ldMulti_regok _ _ _ _ _
      | exact stMulti_regok _ _ _ _ _
      | exact ldSingle_regok _ _ _ _ _ _ _ _
      | exact stSingle_regok _ _ _ _ _ _)

/-! ## The executor -/

set_option maxHeartbeats 4000000 in
/-- Every successful `exec` keeps the regions: every store goes through `store`. -/
theorem exec_regok (i : Instr) (s : State) : RegOK s (exec i s) := by
  cases i <;> simp only [exec, NeonExec.across, NeonExec.byElem, NeonExec.fpCvtFixed, NeonExec.intCommit, NeonExec.ldstNP, NeonExec.ldstStruct, NeonExec.memIndexed, NeonExec.memVPair, NeonExec.qcCommit, NeonExec.sByElem, NeonExec.sPairwise, NeonExec.sShiftImm, NeonExec.sThreeDiff, NeonExec.sThreeSame, NeonExec.sTwoMisc, NeonExec.setVpart, NeonExec.shiftImm, NeonExec.threeDiff, NeonExec.threeSame, NeonExec.twoMisc, NeonExec.baseAddr, State.setScalar, branchReg, baseAddr, execAddSubCarry, execAddSubExt, execAddSubImm, execAddSubShifted, execAtomic, execBitfield, execCas, execCasp, execCls, execClz, execCondCmp, execCondSel, execDcZva, execDiv, execExtr, execFmovGen, execFpCcmp, execFpCmp, execFpCsel, execFpCvtInt, execFpDP1, execFpDP2, execFpDP3, execFpImm, execLdExcl, execLdExclPair, execLogicalImm, execLogicalShifted, execMadd, execMaddl, execMoveWide, execMulh, execNeon, execOrdered, execRbit, execRev, execShiftV, execStExcl, execStExclData, execStExclPair, execVAcross, execVCopy, execVLdStMulti, execVLdStSingle, execVShiftImm, execVThreeSame, execVTwoMisc, fpCommit, memIndexed, memPair, memSingle, memV, memVPair, setVHigh]
  all_goals regok

theorem exec_regions {i : Instr} {s s' : State} (h : exec i s = .ok s') :
    s'.mem.regions = s.mem.regions := exec_regok i s s' h

/-- A successful `step` keeps the memory regions. -/
theorem step_regions {w : Nat} {s s' : State} (h : step w s = .ok s') :
    s'.mem.regions = s.mem.regions := by
  unfold step at h
  split at h
  · exact exec_regions h
  · cases h

end Janus.Arm64
