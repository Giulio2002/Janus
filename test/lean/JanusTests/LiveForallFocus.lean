import Janus

/-! # `∀ r ∈ L, Outside …` side conditions amid unrelated disjunctions (regression for CALLS-MEMMOVE)

The precondition of a live copy (`MemmoveLive64`: `LiveSep L win`) becomes `∀ r, r ∈ L → Outside r.1 (r.2 - r.1) win`
for the live set `L` of the caller. `Common.dischargeLiveForall` (the `janus64_disch` case for such a goal) instantiates the
hypotheses `∀ r ∈ L, …` of the context at `r` and closes the arithmetic by `omega`. After several calls the context
holds a dozen unrelated disjunctions (the `Apart`/`Disjoint` facts of other pointers) that a full-context `omega`
splits: each case costs ~0.3 s, so the memmove call of `strconv.toError` ran for more than 1000 s (CALLS-MEMMOVE).
Now `omega` first runs on the hypotheses about the goal's atoms; the full context (under `janus.omega.cap`) is the
fallback.

The context below carries a pigeonhole (eight numbers below 7, pairwise distinct: 28 disjunctions, which no case
analysis refutes quickly) next to the facts about the goal. -/

namespace JanusTests.LiveForallFocus

open Janus Janus.Tactic

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-- The live window of a call (two stack ranges and a slot), provable from the one fact about `L`. -/
example (L : List (Nat × Nat)) (rsp : Nat)
    (hLs : ∀ r : Nat × Nat, r ∈ L → Outside r.1 (r.2 - r.1) [(rsp - 4192, rsp + 72)])
    (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) :
    ∀ r : Nat × Nat, r ∈ L → Outside r.1 (r.2 - r.1)
      ([(rsp - 96 - 4096, rsp - 96), (rsp - 96 + 8, rsp - 96 + 8 + 24)] ++ [(rsp - 96, rsp - 96 + 8)]) := by
  janus64_disch

/-- A condition that does not follow from the facts about `L` is refused (bounded by `janus.omega.cap`, not an
unbounded search over the pigeonhole). -/
example (L : List (Nat × Nat)) (rsp : Nat)
    (hLs : ∀ r : Nat × Nat, r ∈ L → Outside r.1 (r.2 - r.1) [(rsp - 100, rsp + 72)])
    (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) : True := by
  fail_if_success
    (have _ : ∀ r : Nat × Nat, r ∈ L → Outside r.1 (r.2 - r.1)
      ([(rsp - 96 - 4096, rsp - 96), (rsp - 96 + 8, rsp - 96 + 8 + 24)] ++ [(rsp - 96, rsp - 96 + 8)]) := by
        janus64_disch)
  trivial

end JanusTests.LiveForallFocus
