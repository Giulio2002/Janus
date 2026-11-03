import Janus

/-! # `omega` and many disjunctive facts in `janus_run` (regression for U18)

`omega` splits on every disjunction of the hypotheses it needs. The aliasing facts of a statement about
many pointers (`Disjoint p q`, `Outside`, `Apart`, unfolded to `a + n ≤ b ∨ b + k ≤ a`) are disjunctions
about the pointers, and a call that cannot close its goal (a branch that is not pruned, a side
condition that is not provable) explores the splits: with ~100 such facts `janus_run` ran for more than
20 minutes (IntoBig, arm64) and was killed for memory. Now

* `janus_omega_prune` (the branch pruner of `janus_run`) first tries the hypotheses about the atoms of the
  branch condition alone, then the sparse attempts, and the full context only if it has at most
  `janus.omega.cap` disjunctions;
* `janus_omega_cap` (the last resort of the dischargers) does the same for a side condition.

The context below is a pigeonhole: eight numbers below 7, pairwise distinct (28 disjunctions), which no
case analysis can refute quickly (plain `omega` needs minutes on 6 numbers). The branch condition
`a + 1 = b` has nothing to do with it. -/

namespace JanusTests.OmegaCap

open Janus Janus.Tactic

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-- A branch condition that is not contradictory is not pruned, and fast (it would be refuted by the
pigeonhole if the whole context were handed to `omega`: the branch would be "pruned" for the wrong reason
after minutes). -/
example (a b : Nat) (hbr : a + 1 = b) (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) : True := by
  fail_if_success (have _ : False := by janus_omega_prune)
  fail_if_success (have _ : False := by janus_omega_cap)
  trivial

/-- A branch whose condition contradicts the facts about its own atoms is pruned, fast. -/
example (a b : Nat) (hbr : a + 1 = b) (h : b ≤ a) (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) : False := by
  janus_omega_prune

/-- Under the cap, the full context is used: a contradiction that needs a disjunction is found. -/
example (a b : Nat) (hbr : a = b) (h : a < b ∨ b < a) : False := by
  janus_omega_prune

example (a b : Nat) (h : a < b ∨ b < a) (h2 : a = b) : False := by
  janus_omega_cap

end JanusTests.OmegaCap
