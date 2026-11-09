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

/-- A frame against a pointer: the frame is `[sp - 4248, sp + 40)`, so a stack slot `sp - 8` is disjoint from
the 16 bytes at `m` (one case split on the aliasing fact; `sp` and `sp - 4248` are the same base). -/
example (sp m : Nat) (hlow : 4248 ≤ sp) (hdm : m + 32 ≤ sp - 4248 ∨ sp + 40 ≤ m) :
    sp - 8 + 8 ≤ m ∨ m + 16 ≤ sp - 8 := by
  janus_omega

example (sp z : Nat) (hlow : 4248 ≤ sp) (hdz : z + 32 ≤ sp - 4248 ∨ sp + 40 ≤ z) :
    sp - 8 + 8 ≤ z + 16 ∨ z + 24 ≤ sp - 8 := by
  janus_omega

/-- The aliasing fact is needed: without it nothing is decided. -/
example (sp m : Nat) (hlow : 4248 ≤ sp) : True := by
  fail_if_success
    have : sp - 8 + 8 ≤ m ∨ m + 16 ≤ sp - 8 := by janus_omega
  trivial

end JanusTests.AddrSub
