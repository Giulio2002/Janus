import Janus

/-! # Side-condition dischargers: candidate screening, `Apart` first, memo (regression for EX-SPEED)

`Common.dischargeOutside` / `dischargeApart` look for a hypothesis of the context that the goal follows from. They now
(1) screen every candidate with the first stage of the staged `omega` (`janus_omega_cheap`) before the full staged
search, trying the candidates that share the most atoms with the goal first; (2) close a disjunctive part by an `Apart`
fact before the staged search; (3) remember the proved parts of an `Outside` condition (`outsideMemo`). All three only
reorder or skip searches: every case below must still be proved, in particular the ones that need the staged search
(a case split) and the ones where the first candidate is the wrong one. -/

namespace JanusTests.DischargeOrder

open Janus Janus.Contracts Janus.Tactic

set_option linter.unusedVariables false

/-- The right hypothesis is not the first candidate. -/
example (rt : List (Nat × Nat)) (a n b k c m : Nat)
    (h1 : Outside c m rt) (h2 : Outside b k rt) (hl : b ≤ a) (hr : a + n ≤ b + k) :
    Outside a n rt := by
  janus64_disch

/-- A candidate that needs a case split (the staged search, not the screening stage). -/
example (rt : List (Nat × Nat)) (a n b k x : Nat)
    (h2 : Outside b k rt) (hx : x ≤ a ∨ x + 1 ≤ a) (hl : b ≤ x) (hr : a + n ≤ b + k) :
    Outside a n rt := by
  janus64_disch

/-- A list of ranges, each part from a hypothesis; the same goal twice (the second is the memo). -/
example (rt : List (Nat × Nat)) (x y : Nat) (h1 : Outside x 8 rt) (hy : x ≤ y) (hy2 : y + 4 ≤ x + 8) :
    Outside y 4 rt ∧ Outside y 4 rt := by
  constructor <;> janus64_disch

/-- Nothing proves it: still refused. -/
example (rt : List (Nat × Nat)) (a n b k : Nat) (h2 : Outside b k rt) : True := by
  fail_if_success (have _ : Outside a n rt := by janus64_disch)
  trivial

set_option maxHeartbeats 20000 in
/-- The wrong candidate first, amid a pigeonhole of 28 disjunctions: the old search ran every stage of the staged `omega`
on the wrong candidate (the capped full context takes seconds); the screening stage refuses it at once. -/
example (rt : List (Nat × Nat)) (a n b k c m : Nat)
    (h1 : Outside c m rt) (h2 : Outside b k rt) (hl : b ≤ a) (hr : a + n ≤ b + k) (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) :
    Outside a n rt := by
  janus64_disch

end JanusTests.DischargeOrder
