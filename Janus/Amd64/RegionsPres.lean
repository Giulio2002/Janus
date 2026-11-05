import Lean
import Janus.Amd64.Exec
import Janus.Arm64.MemoryLemmas

/-!
# The amd64 executor keeps the memory regions

`exec_regions : exec i len s = .ok s' → s'.mem.regions = s.mem.regions` (and `step_regions`): the
amd64 counterpart of `Janus.Arm64.exec_regions`. Every store goes through the checked `store` (or
`writeLE`, `ExecAVX.writeMasked`), which only rewrite bytes. Base of `Amd64.Program.Steps.regions`
(`Janus.Amd64.RunRegions`).
-/

namespace Janus.Amd64

open Janus.Arm64 (Memory)

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

/-- Regions are all that is compared, so `RegOK` transfers along a state with equal regions. -/
theorem trans {s₁ : State} {E : Except Fault State} (h : RegOK s₁ E)
    (e : s₁.mem.regions = s.mem.regions) : RegOK s E :=
  fun t ht => (h t ht).trans e

end RegOK

theorem store_ok_iff (m : Memory) (a n v : Nat) {m' : Memory} :
    store m a n v = .ok m' ↔ m.accessible a n true = true ∧ m' = m.writeLE a n v := by
  unfold store
  cases hw : m.accessible a n true
  · cases m.accessible a n false <;> exact ⟨(fun h' => nomatch h'), (fun ⟨h', _⟩ => nomatch h')⟩
  · rw [Memory.accessible_read_of_write m hw]
    exact ⟨(fun h' => ⟨rfl, (Except.ok.inj h').symm⟩), (fun ⟨_, hx⟩ => hx ▸ rfl)⟩

namespace State

@[simp] theorem mem_setReg (s : State) (r : Nat) (v : W64) : (s.setReg r v).mem = s.mem := rfl
@[simp] theorem mem_setXmm (s : State) (n : Nat) (v : W128) : (s.setXmm n v).mem = s.mem := rfl
@[simp] theorem mem_setYmmHi (s : State) (n : Nat) (v : W128) : (s.setYmmHi n v).mem = s.mem := rfl
@[simp] theorem mem_setZmmHi (s : State) (n : Nat) (v : BitVec 256) : (s.setZmmHi n v).mem = s.mem := rfl
@[simp] theorem mem_setV (s : State) (l n v : Nat) : (s.setV l n v).mem = s.mem := rfl
@[simp] theorem mem_putReg (s : State) (w r : Nat) (v : BitVec w) : (s.putReg w r v).mem = s.mem := by
  unfold putReg; split <;> rfl
@[simp] theorem mem_putHigh (s : State) (r : Nat) (v : BitVec 8) : (s.putHigh r v).mem = s.mem := rfl
@[simp] theorem mem_setFlags (s : State) (f : Flags) : (s.setFlags f).mem = s.mem := rfl
@[simp] theorem mem_setRip (s : State) (v : W64) : (s.setRip v).mem = s.mem := rfl
@[simp] theorem mem_raiseMx (s : State) (fl : Nat) : (s.raiseMx fl).mem = s.mem := rfl
@[simp] theorem mem_setXmmLow (s : State) (n w v : Nat) : (s.setXmmLow n w v).mem = s.mem := rfl
@[simp] theorem mem_advanceUndef (s : State) : s.advanceUndef.mem = s.mem := rfl

end State

@[simp] theorem mem_sse_setXmm (s : State) (n : Nat) (v : W128) : (ExecSSE.setXmm s n v).mem = s.mem := rfl
@[simp] theorem mem_sse_setReg (s : State) (r : Nat) (v : W64) : (ExecSSE.setReg s r v).mem = s.mem := rfl
@[simp] theorem mem_sse_raiseMx (s : State) (fl : Nat) : (ExecSSE.raiseMx s fl).mem = s.mem := rfl
@[simp] theorem mem_avx_setV (s : State) (l n v : Nat) : (ExecAVX.setV s l n v).mem = s.mem := rfl
@[simp] theorem mem_evex_setZ (s : State) (l n v : Nat) : (ExecEVEX.setZ s l n v).mem = s.mem := rfl
@[simp] theorem mem_evex_setK (s : State) (n v : Nat) : (ExecEVEX.setK s n v).mem = s.mem := rfl

theorem mem_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then a else b).mem = if c then a.mem else b.mem := apply_ite _ _ _ _

@[simp] theorem regions_writeMasked (m : Memory) (addr sz : Nat) (p : Nat → Bool) (v : Nat) :
    ∀ k, (ExecAVX.writeMasked m addr sz p v k).regions = m.regions := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ExecAVX.writeMasked]
    split
    · simp [ih]
    · exact ih

open Lean Elab Tactic in
syntax (name := regok64Eq) "regok64_eq" : tactic

syntax (name := regok64Tac) "regok64" : tactic

syntax (name := regok64Store) "regok64_store" : tactic

/-- Lemmas about helper functions proved after the closers; extended by `macro_rules`. -/
syntax (name := regok64Lem) "regok64_lem" : tactic

macro_rules
  | `(tactic| regok64_lem) => `(tactic| fail "no lemma")

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| regok64_eq) => withMainContext do
    let g ← getMainGoal
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, _, r) := ty.eq? | continue
      unless r.isAppOfArity ``Except.ok 3 do continue
      let e ← Term.exprToSyntax (mkFVar d.fvarId)
      try
        evalTactic (← `(tactic| (refine RegOK.of_eq ?_ $e; regok64)))
        return
      catch _ => setGoals [g]
    throwError "regok64_eq: no hypothesis applies"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| regok64_store) => withMainContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      unless r.isAppOfArity ``Except.ok 3 && l.isAppOfArity ``store 4 && r.appArg!.isFVar do continue
      let e ← Term.exprToSyntax (mkFVar d.fvarId)
      evalTactic (← `(tactic| (obtain ⟨-, hh⟩ := (store_ok_iff _ _ _ _).1 $e; subst hh)))
      replaceMainGoal [← (← getMainGoal).tryClear d.fvarId]
      return
    throwError "regok64_store: no store hypothesis"

macro_rules
  | `(tactic| regok64) => `(tactic| repeat' first
      | exact RegOK.error
      | assumption
      | regok64_lem
      | regok64_store
      | (apply RegOK.ok; simp only [mem_ite, State.mem_setReg, State.mem_setXmm, State.mem_setYmmHi,
          State.mem_setZmmHi, State.mem_setV, State.mem_putReg, State.mem_putHigh, State.mem_setFlags,
          State.mem_setRip, State.mem_advanceUndef, State.mem_raiseMx, State.mem_setXmmLow, mem_sse_setXmm, mem_sse_setReg, mem_sse_raiseMx,
          mem_avx_setV, mem_evex_setZ, mem_evex_setK, Memory.regions_writeLE, regions_writeMasked,
          ite_self]; done)
      | (apply RegOK.ok; simp only [mem_ite, State.mem_setReg, State.mem_setXmm, State.mem_setYmmHi,
          State.mem_setZmmHi, State.mem_setV, State.mem_putReg, State.mem_putHigh, State.mem_setFlags,
          State.mem_setRip, State.mem_advanceUndef, State.mem_raiseMx, State.mem_setXmmLow, mem_sse_setXmm, mem_sse_setReg, mem_sse_raiseMx,
          mem_avx_setV, mem_evex_setZ, mem_evex_setK, Memory.regions_writeLE, regions_writeMasked,
          ite_self]; first | regok64_lem | regok64_eq)
      | (apply RegOK.ite <;> intro _)
      | split
      | dsimp only)

/-! ## The recursive helpers -/

theorem movsIter_regok (sz : Nat) : ∀ k (s : State), RegOK s (movsIter sz k s) := by
  intro k
  induction k with
  | zero => intro s; simp only [movsIter]; exact RegOK.ok rfl
  | succ k ih =>
    intro s
    simp only [movsIter]
    regok64
    all_goals exact RegOK.trans (ih _) (by simp)

theorem movsIterB_regok (sz : Nat) : ∀ k (s : State), RegOK s (movsIterB sz k s) := by
  intro k
  induction k with
  | zero => intro s; simp only [movsIterB]; exact RegOK.ok rfl
  | succ k ih =>
    intro s
    simp only [movsIterB]
    regok64
    all_goals exact RegOK.trans (ih _) (by simp)

theorem stosIter_regok (sz v : Nat) : ∀ k (s : State), RegOK s (stosIter sz v k s) := by
  intro k
  induction k with
  | zero => intro s; simp only [stosIter]; exact RegOK.ok rfl
  | succ k ih =>
    intro s
    simp only [stosIter]
    regok64
    all_goals exact RegOK.trans (ih _) (by simp)

theorem stosIterB_regok (sz v : Nat) : ∀ k (s : State), RegOK s (stosIterB sz v k s) := by
  intro k
  induction k with
  | zero => intro s; simp only [stosIterB]; exact RegOK.ok rfl
  | succ k ih =>
    intro s
    simp only [stosIterB]
    regok64
    all_goals exact RegOK.trans (ih _) (by simp)

theorem stMasked_regions {s : State} {addr l e k v : Nat} {sup : Bool} {m : Memory}
    (h : ExecEVEX.stMasked s addr l e k v sup = .ok m) : m.regions = s.mem.regions := by
  unfold ExecEVEX.stMasked at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain ⟨-, rfl⟩ := (store_ok_iff _ _ _ _).1 h; simp)
    | (cases h; simp)

macro_rules
  | `(tactic| regok64_lem) => `(tactic| first
      | exact movsIter_regok _ _ _
      | exact movsIterB_regok _ _ _
      | exact stosIter_regok _ _ _ _
      | exact stosIterB_regok _ _ _ _
      | exact stMasked_regions (by assumption))

/-! ## The executor -/

set_option maxHeartbeats 4000000 in
/-- Every successful `exec` keeps the regions: every store goes through `store`. -/
theorem exec_regok : ∀ (i : Instr) (len : Nat) (s : State), RegOK s (exec i len s) := by
  intro i
  induction i <;> intro len s <;> simp only [exec, ExecAVX.doneFPV, ExecAVX.doneS, ExecAVX.doneV, ExecAVX.exec, ExecAVX.gatherExec, ExecAVX.maskmovExec, ExecCrypto.exec, ExecEVEX.done, ExecEVEX.doneFP, ExecEVEX.exec, ExecSSE.doneFP, ExecSSE.doneX, ExecSSE.exec, X87.exec, X87.execWaiting, X87.fin, branchTo, exec, execAlu, execAndn, execBextr, execBit, execBlsx, execBzhi, execCount, execDiv, execImul, execMul1, execRcx, execShd, execShift, execShiftx, execUnary, fpDone, push64, writeLoc, writeV, writeX]
  all_goals regok64
  all_goals first
    | exact (by assumption : ∀ (len : Nat) (s : State), RegOK s (exec _ len s)) _ _
    | skip

theorem exec_regions {i : Instr} {len : Nat} {s s' : State} (h : exec i len s = .ok s') :
    s'.mem.regions = s.mem.regions := exec_regok i len s s' h

/-- A successful `step` keeps the memory regions. -/
theorem step_regions {bytes : List Nat} {s s' : State} (h : step bytes s = .ok s') :
    s'.mem.regions = s.mem.regions := by
  unfold step at h
  split at h
  · exact exec_regions h
  · cases h

end Janus.Amd64
