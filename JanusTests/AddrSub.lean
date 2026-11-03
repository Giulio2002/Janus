import Janus

/-! # `addrDisch` with truncated subtraction of literals (S3)

Stack addresses are `sp - 48`, `sp - 152 + 8`, `sp - 48 - 4096`: truncated Nat subtractions of literals.
With a literal lower bound `4248 ≤ sp` among the hypotheses they are all offsets of the one base `sp - 4248`
(`addr_sub_lb`, `addr_sub_off`), so the same-base comparison of literals decides them without `omega`
(FV-B DivModB: 810 `readLE_writeLE_disjoint` discharges of 0.5 s each). The proofs are checked by the kernel
as always; a goal that is not decided here still goes to `omega`. -/

namespace JanusTests.AddrSub

open Janus Janus.Tactic

example (sp : Nat) (hlow : 4248 ≤ sp) :
    sp - 48 + 8 ≤ sp - 152 ∨ sp - 152 + 8 ≤ sp - 48 := by
  janus_omega

example (sp : Nat) (hlow : 4248 ≤ sp) : sp - 48 - 4096 + 8 ≤ sp - 48 - 8 := by
  janus_omega

example (sp : Nat) (hlow : 4248 ≤ sp) : sp - 152 + 16 = sp - 136 := by
  janus_omega

/-- An address fact that is false for its own offsets is still refuted. -/
example (sp : Nat) (hlow : 4248 ≤ sp) : True := by
  fail_if_success
    have : sp - 48 ≤ sp - 152 := by janus_omega
  trivial

/-- Without the lower bound the truncation matters and nothing is proved. -/
example (sp : Nat) : True := by
  fail_if_success
    have : sp - 48 + 8 ≤ sp - 152 ∨ sp - 152 + 8 ≤ sp - 48 := by janus_omega
  trivial

/-- A bound too small for the subtracted literal is not used (`sp - 152` can truncate). -/
example (sp : Nat) (hlow : 100 ≤ sp) : True := by
  fail_if_success
    have : sp - 48 + 8 ≤ sp - 152 := by janus_omega
  trivial

end JanusTests.AddrSub
