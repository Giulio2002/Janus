import Janus.Amd64.Tactic

/-!
# Recursive functions on amd64: summaries by well-founded induction over calls

The amd64 counterparts of `Janus.Tactic.Summary.induction` and `Summary.returns`
(`Janus/Tactic/Recursion.lean`): a recursive function's `Summary` is proved by strong induction
on a measure of the entry state, the induction hypothesis serving as the callee summary at the
recursive `CALL`. The return address is the word at `[RSP]` (`retAddrOf`).

See `examples/proofs-amd64/Fact/Proof.lean`.
-/

namespace Janus.Amd64.Tactic

open Janus Janus.Amd64 Janus.Amd64.GoABI

/-- Strong induction on a measure `μ` of the entry state (see the arm64 `Summary.induction`). -/
theorem Summary.induction {p : Program} {entry : Nat} {pre : State → Prop}
    {post : State → State → Prop} (μ : State → Nat)
    (step : ∀ n, Summary p entry (fun s => pre s ∧ μ s < n) post →
      Summary p entry (fun s => pre s ∧ μ s = n) post) :
    Summary p entry pre post := by
  have h : ∀ n, Summary p entry (fun s => pre s ∧ μ s < n) post := by
    intro n
    induction n with
    | zero => intro s _ ⟨_, h⟩; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro s hpc ⟨hp, hlt⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
      · exact ih s hpc ⟨hp, hlt⟩
      · exact step n ih s hpc ⟨hp, heq⟩
  intro s hpc hp
  exact h (μ s + 1) s hpc ⟨hp, Nat.lt_succ_self _⟩

/-- A summary of the function at `entry`, applied to its own call state (whose `[RSP]` holds
`ret`): the call returns to `ret` in a state satisfying `post`. -/
theorem Summary.returns {p : Program} {entry ret : Nat} {pre : State → Prop}
    {post : State → State → Prop} {s : State} {Q : State → Prop}
    (hsum : Summary p entry pre post) (hret : RetAddr p ret)
    (hpc : s.rip = BitVec.ofNat 64 entry) (hra : retAddrOf s = BitVec.ofNat 64 ret) (hpre : pre s)
    (hq : ∀ s', post s s' → Q s') : Returns (p.withExit ret) s Q := by
  apply returns_of_reaches
  refine Reaches.call (hsum.withExit hret) hpc hpre fun s' hr hp => ?_
  exact Reaches.exit_withExit hret (by rw [hr]; exact hra) (hq s' hp)

end Janus.Amd64.Tactic
