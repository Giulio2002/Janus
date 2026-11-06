import Janus

/-! # The discharger memo (`janus.dischMemo`): a side condition proved once is reused (regression for EX-SPEED)

`janus_disch` / `janus64_disch` remember the conditions they proved (`Common.withDischMemo`). A run asks the same
address and bound conditions again and again; the memo reuses the first proof (the kernel checks the final term as
always) where every hypothesis the proof uses is still present with the same type. Failures are not remembered. -/

namespace JanusTests.DischargeMemo

open Janus Janus.Tactic

set_option linter.unusedVariables false

set_option maxHeartbeats 1000 in
/-- The same condition 30 times amid a pigeonhole of 28 disjunctions (the condition needs the link through `z` that
the pruned context drops, so each proof is a search): with the memo it is found once. Without it (`set_option
janus.dischMemo false`, or the engine before the memo) these 30 searches exceed the 1000-heartbeat bound. -/
example (x z w : Nat) (h1 : x < z) (h2 : z < w ∨ z + 1 < w) (v0 : Nat) (v1 : Nat) (v2 : Nat) (v3 : Nat) (v4 : Nat) (v5 : Nat) (v6 : Nat) (v7 : Nat) (b0 : v0 < 7) (b1 : v1 < 7) (b2 : v2 < 7) (b3 : v3 < 7) (b4 : v4 < 7) (b5 : v5 < 7) (b6 : v6 < 7) (b7 : v7 < 7) (d0_1 : v0 < v1 ∨ v1 < v0) (d0_2 : v0 < v2 ∨ v2 < v0) (d0_3 : v0 < v3 ∨ v3 < v0) (d0_4 : v0 < v4 ∨ v4 < v0) (d0_5 : v0 < v5 ∨ v5 < v0) (d0_6 : v0 < v6 ∨ v6 < v0) (d0_7 : v0 < v7 ∨ v7 < v0) (d1_2 : v1 < v2 ∨ v2 < v1) (d1_3 : v1 < v3 ∨ v3 < v1) (d1_4 : v1 < v4 ∨ v4 < v1) (d1_5 : v1 < v5 ∨ v5 < v1) (d1_6 : v1 < v6 ∨ v6 < v1) (d1_7 : v1 < v7 ∨ v7 < v1) (d2_3 : v2 < v3 ∨ v3 < v2) (d2_4 : v2 < v4 ∨ v4 < v2) (d2_5 : v2 < v5 ∨ v5 < v2) (d2_6 : v2 < v6 ∨ v6 < v2) (d2_7 : v2 < v7 ∨ v7 < v2) (d3_4 : v3 < v4 ∨ v4 < v3) (d3_5 : v3 < v5 ∨ v5 < v3) (d3_6 : v3 < v6 ∨ v6 < v3) (d3_7 : v3 < v7 ∨ v7 < v3) (d4_5 : v4 < v5 ∨ v5 < v4) (d4_6 : v4 < v6 ∨ v6 < v4) (d4_7 : v4 < v7 ∨ v7 < v4) (d5_6 : v5 < v6 ∨ v6 < v5) (d5_7 : v5 < v7 ∨ v7 < v5) (d6_7 : v6 < v7 ∨ v7 < v6) : True := by
  have _h0 : x < w := by janus64_disch
  have _h1 : x < w := by janus64_disch
  have _h2 : x < w := by janus64_disch
  have _h3 : x < w := by janus64_disch
  have _h4 : x < w := by janus64_disch
  have _h5 : x < w := by janus64_disch
  have _h6 : x < w := by janus64_disch
  have _h7 : x < w := by janus64_disch
  have _h8 : x < w := by janus64_disch
  have _h9 : x < w := by janus64_disch
  have _h10 : x < w := by janus64_disch
  have _h11 : x < w := by janus64_disch
  have _h12 : x < w := by janus64_disch
  have _h13 : x < w := by janus64_disch
  have _h14 : x < w := by janus64_disch
  have _h15 : x < w := by janus64_disch
  have _h16 : x < w := by janus64_disch
  have _h17 : x < w := by janus64_disch
  have _h18 : x < w := by janus64_disch
  have _h19 : x < w := by janus64_disch
  have _h20 : x < w := by janus64_disch
  have _h21 : x < w := by janus64_disch
  have _h22 : x < w := by janus64_disch
  have _h23 : x < w := by janus64_disch
  have _h24 : x < w := by janus64_disch
  have _h25 : x < w := by janus64_disch
  have _h26 : x < w := by janus64_disch
  have _h27 : x < w := by janus64_disch
  have _h28 : x < w := by janus64_disch
  have _h29 : x < w := by janus64_disch
  trivial

/-- A cached proof is not reused where a hypothesis it uses is gone. -/
example (x z w : Nat) (h1 : x < z) (h2 : z < w ∨ z + 1 < w) : True := by
  have _ : True := by
    have _ : x < w := by janus64_disch
    trivial
  clear h1
  fail_if_success (have _ : x < w := by janus64_disch)
  trivial

end JanusTests.DischargeMemo
