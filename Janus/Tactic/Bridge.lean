import Janus.Tactic.Basic

/-!
# From `Reaches`/`Ensures` to callee summaries (arm64)

`janus_run … calls [S]` and `Summary.of_codeIn` consume `Summary p a pre post`, i.e.
`ReachesRet p (s.regs LR) s (post s)` (ordinary steps of `p` up to the return address). A
function theorem is usually stated as `Reaches (p.withExit ret) s (IsReturn Q)` or `Ensures`.
This file is the bridge:

* `Reaches.toReachesRet`: a run of `p.withExit ret` that returns is a `ReachesRet p ret`.
* `Ensures.toSummary`: an `Ensures` theorem is a `Summary` (precondition: the call state of some
  admissible `ret`; postcondition: `ABIReturn s s' ∧ post s s'`).

Both need `p.fetch p.exitAddr = none` (no code at the extracted placeholder exit address; true
of every extracted program, `by decide`), because `Program.Steps p` refuses to step from
`p.exitAddr` while `p.withExit ret` does not.
-/

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.GoABI

/-- A returning run is a sequence of ordinary steps ending at the exit address. -/
theorem steps_of_run_returned {p : Program} :
    ∀ {n : Nat} {s s' : State}, p.run n s = .ok (.returned s') →
      ∃ k, Program.Steps p s k s' ∧ s'.pc.toNat = p.exitAddr := by
  intro n
  induction n with
  | zero => intro s s' h; cases h
  | succ n ih =>
    intro s s' h
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [Program.run_succ_exit hx] at h
      cases h
      exact ⟨0, .refl _, hx⟩
    · cases hs : p.stubAt s.pc.toNat with
      | some st => rw [Program.run_succ_stub hx hs] at h; cases h
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => rw [Program.run_succ_noCode hx hs hf] at h; cases h
        | some w =>
          cases hst : Arm64.step w s with
          | error e => rw [Program.run_succ_fault hx hs hf hst] at h; cases h
          | ok s₁ =>
            rw [Program.run_succ_step hx hs hf hst] at h
            obtain ⟨k, hk, hq⟩ := ih h
            exact ⟨k + 1, .step hx hs hf hst hk, hq⟩

/-- Ordinary steps of `p.withExit ret` are ordinary steps of `p` when `p` has no code at its
own exit address. -/
theorem steps_unExit {p : Program} {ret : Nat} (hx : p.fetch p.exitAddr = none) :
    ∀ {s s' : State} {k : Nat}, Program.Steps (p.withExit ret) s k s' → Program.Steps p s k s' := by
  intro s s' k h
  induction h with
  | refl => exact .refl _
  | step _ hs hf hst _ ih =>
    refine .step ?_ hs hf hst ih
    intro heq
    have hf' : p.fetch _ = some _ := hf
    rw [heq, hx] at hf'
    cases hf'

/-- A returning `Reaches` of `p.withExit ret` is a `ReachesRet` of `p` at `ret`. -/
theorem Reaches.toReachesRet {p : Program} {ret : Nat} {s : State} {Q : State → Prop}
    (h : Reaches (p.withExit ret) s (IsReturn Q)) (hret : RetAddr p ret)
    (hx : p.fetch p.exitAddr = none) : ReachesRet p (BitVec.ofNat 64 ret) s Q := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | stub _ _ _ => exact hq.elim
  | returned s' =>
    obtain ⟨k, hk, hpc⟩ := steps_of_run_returned hr
    refine ⟨k, s', steps_unExit hx hk, ?_, hq⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
    exact hpc

/-- **An `Ensures` theorem is a callee summary.** The precondition carries the call-state facts
(`CallSetup` of `p.withExit ret` for an admissible `ret`, hence `X30 = ret`); the postcondition is
the ABI return rules and the `Ensures` post. -/
theorem Ensures.toSummary {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p entry args pre post)
    (hx : p.fetch p.exitAddr = none) :
    Summary p entry
      (fun s => ∃ ret, RetAddr p ret ∧ CallSetup (p.withExit ret) entry args s ∧ pre s)
      (fun s s' => ABIReturn s s' ∧ post s s') := by
  intro s _ ⟨ret, hret, hsu, hpre⟩
  have h2 := (reaches_of_returns (h ret hret s hsu hpre)).toReachesRet hret hx
  rw [hsu.lr]
  exact h2

end Janus.Tactic
