import Janus

/-! # `Janus.Tactic.add_sub_norm`: `K + ptr - 1` as `ptr + (K - 1)` -/

namespace JanusTests.NatNorm

open Janus Janus.Tactic Janus.Arm64

example (p : Nat) : 8 + p - 1 = p + 7 := by
  simp (disch := omega) only [add_sub_norm, Nat.reduceSub]

/-- The address of a read over a store: after the normalisation the memory rule applies. -/
example (m : Memory) (p v : Nat) :
    (m.writeLE (p + 100) 8 v).readLE (8 + p - 1) 1 = m.readLE (p + 7) 1 := by
  simp (disch := omega) only [add_sub_norm, Nat.reduceSub, Memory.readLE_writeLE_of_disjoint]

/-- The side condition `c ≤ a` is needed: `0 + p - 1` is not `p + (0 - 1)` (the truncated subtraction). -/
example (p : Nat) : True := by
  fail_if_success
    have : 0 + p - 1 = p + (0 - 1) := by simp (disch := omega) only [add_sub_norm]
  trivial

end JanusTests.NatNorm
