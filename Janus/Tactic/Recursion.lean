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

/-! ## Mutual recursion: a family of entries with a shared measure

A strongly connected component of the call graph (`isEven`/`isOdd`; math/big's {`nat.mul`,
`karatsuba`, `(*Int).mul`}) has several entries that call each other. `Summary.induction_mutual`
proves one summary per member, indexed by any type `ι` (an inductive with one constructor per
member, or `Fin k`), by strong induction on a shared measure: member `i` at entry state `s` has
measure `μ i s : Nat`, and in the case `μ i s = n` the induction hypothesis `ih j` is the summary
of **every** member `j` for the states with `μ j s < n`. So each call inside the component, to
itself or to another member, must strictly decrease the measure; a call to another member at the
"same" argument is handled by weighting the members (`3·n + 2`, `3·n + 1`, `3·n` for a 3-cycle that
decreases `n` once per round). `Summary.induction_mutual_wf` is the same over any well-founded
relation (a lexicographic measure, say). Both are theorems from the definition of `Summary`; no
axiom beyond the allow-list is used.

Inside the proof of member `i`, `janus_run calls [ih j₁, ih j₂, …]` uses the hypotheses at the
calls, exactly like `Summary.induction`'s `ih` (the executor proves each callee precondition,
including the decrease of the measure). See `examples/proofs/IsEven.lean`, `CycA.lean` and their
amd64 counterparts. -/

/-- Mutual strong induction over a well-founded relation `r` on the measure values. -/
theorem Summary.induction_mutual_wf {p : Program} {ι : Sort _} {α : Sort _} {r : α → α → Prop}
    (hwf : WellFounded r) {entry : ι → Nat} {pre : ι → State → Prop}
    {post : ι → State → State → Prop} (μ : ι → State → α)
    (step : ∀ a, (∀ j, Summary p (entry j) (fun s => pre j s ∧ r (μ j s) a) (post j)) →
      ∀ i, Summary p (entry i) (fun s => pre i s ∧ μ i s = a) (post i)) :
    ∀ i, Summary p (entry i) (pre i) (post i) := by
  have h : ∀ a, ∀ i, Summary p (entry i) (fun s => pre i s ∧ μ i s = a) (post i) := by
    intro a
    induction a using hwf.induction with
    | _ a ih =>
      exact step a fun j s hpc ⟨hp, hlt⟩ => ih (μ j s) hlt j s hpc ⟨hp, rfl⟩
  intro i s hpc hp
  exact h (μ i s) i s hpc ⟨hp, rfl⟩

/-- Mutual strong induction on a shared natural-number measure: to prove the summary of member
`i` for the states of measure `n`, the summaries of all members may be used for every state of
smaller measure. -/
theorem Summary.induction_mutual {p : Program} {ι : Sort _} {entry : ι → Nat}
    {pre : ι → State → Prop} {post : ι → State → State → Prop} (μ : ι → State → Nat)
    (step : ∀ n, (∀ j, Summary p (entry j) (fun s => pre j s ∧ μ j s < n) (post j)) →
      ∀ i, Summary p (entry i) (fun s => pre i s ∧ μ i s = n) (post i)) :
    ∀ i, Summary p (entry i) (pre i) (post i) :=
  Summary.induction_mutual_wf (r := (· < ·)) Nat.lt_wfRel.wf μ step

/-- The single-entry `Summary.induction` is the one-member case of `Summary.induction_mutual`. -/
example {p : Program} {entry : Nat} {pre : State → Prop} {post : State → State → Prop}
    (μ : State → Nat)
    (step : ∀ n, Summary p entry (fun s => pre s ∧ μ s < n) post →
      Summary p entry (fun s => pre s ∧ μ s = n) post) :
    Summary p entry pre post :=
  Summary.induction_mutual (ι := Unit) (entry := fun _ => entry) (pre := fun _ => pre)
    (post := fun _ => post) (fun _ => μ) (fun n ih _ => step n (ih ())) ()

end Janus.Tactic
