import Janus.Amd64.Tactic

/-!
# From `Reaches`/`Ensures` to callee summaries (amd64)

Twin of `Janus.Tactic.Bridge`: `Reaches.toReachesRet` and `Ensures.toSummary` for
`Janus.Amd64`. `Summary p a pre post` is `ReachesRet p (retAddrOf s) s (post s)`; the
`CallSetup` of `p.withExit ret` puts `ret` at `[RSP]`.
-/

namespace Janus.Amd64.Tactic

open Janus Janus.Amd64 Janus.Amd64.GoABI

theorem steps_of_run_returned {p : Program} :
    ∀ {n : Nat} {s s' : State}, p.run n s = .ok (.returned s') →
      ∃ k, Program.Steps p s k s' ∧ s'.rip.toNat = p.exitAddr := by
  intro n
  induction n with
  | zero => intro s s' h; cases h
  | succ n ih =>
    intro s s' h
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [Program.run_succ_exit hx] at h
      cases h
      exact ⟨0, .refl _, hx⟩
    · cases hs : p.stubAt s.rip.toNat with
      | some st => rw [Program.run_succ_stub hx hs] at h; cases h
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => rw [Program.run_succ_noCode hx hs hf] at h; cases h
        | some w =>
          cases hst : Amd64.step w s with
          | error e => rw [Program.run_succ_fault hx hs hf hst] at h; cases h
          | ok s₁ =>
            rw [Program.run_succ_step hx hs hf hst] at h
            obtain ⟨k, hk, hq⟩ := ih h
            exact ⟨k + 1, .step hx hs hf hst hk, hq⟩

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

theorem Ensures.toSummary {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p entry args pre post)
    (hx : p.fetch p.exitAddr = none) :
    Summary p entry
      (fun s => ∃ ret, RetAddr p ret ∧ CallSetup (p.withExit ret) entry args s ∧ pre s)
      (fun s s' => ABIReturn s s' ∧ post s s') := by
  intro s _ ⟨ret, hret, hsu, hpre⟩
  obtain ⟨n, s', hr, hp⟩ := h ret hret s hsu hpre
  have h2 := (show Reaches (p.withExit ret) s (IsReturn fun s' => ABIReturn s s' ∧ post s s') from ⟨n, _, hr, hp⟩).toReachesRet hret hx
  rw [retAddrOf_eq, hsu.ret]
  exact h2

end Janus.Amd64.Tactic
