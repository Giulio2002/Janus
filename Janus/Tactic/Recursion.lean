import Janus.Tactic.Basic

/-!
# Recursive functions: summaries by well-founded induction over calls

A recursive Go function calls its own entry. Its `Summary` is proved by induction on a measure
of the call state (for `Fact(n)`: `n`), and inside the proof the induction hypothesis is the
summary itself for every state of smaller measure, passed to `janus_run calls [ih]` like any
callee summary. At the recursive call the executor proves the induction hypothesis's
precondition, which includes `μ s < n`: that the argument decreased.

`Summary.induction` packages the strong induction. `Summary.returns` turns the finished summary
into the `Returns` goal of the function's `Ensures` contract (the call state is at the entry and
`X30` holds the return address of `p.withExit ret`).

See `examples/proofs/Fact.lean` and docs/PROOFS.md, "Recursion".
-/

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.GoABI

/-- Strong induction on a measure `μ` of the entry state: to prove a summary for the states of
measure `n`, the summary may be used (as a callee summary) for every state of smaller measure. -/
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

/-- A summary of the function at `entry`, applied to its own call state: the call returns to
`ret` in a state satisfying `post`. -/
theorem Summary.returns {p : Program} {entry ret : Nat} {pre : State → Prop}
    {post : State → State → Prop} {s : State} {Q : State → Prop}
    (hsum : Summary p entry pre post) (hret : RetAddr p ret)
    (hpc : s.pc = BitVec.ofNat 64 entry) (hlr : s.regs 30 = BitVec.ofNat 64 ret) (hpre : pre s)
    (hq : ∀ s', post s s' → Q s') : Returns (p.withExit ret) s Q := by
  apply returns_of_reaches
  refine Reaches.call (hsum.withExit hret) hpc hpre fun s' hr hp => ?_
  exact Reaches.exit_withExit hret (by rw [hr]; exact hlr) (hq s' hp)

end Janus.Tactic
