import Janus

/-! # `janus_assumption_reducible` (S11)

`assumption` / `‹T›` unifies the goal with each hypothesis at default transparency, and a hypothesis about `readLE` of a long
chain of stores can cost 60-120 s per failed attempt (FV-A amd64 `Bytes`: 16 calls, 1316 s). `janus_assumption` tries the
hypotheses of the goal's head constant at reducible transparency first; `janus_assumption_reducible` is its reducible passes
alone, with no ordinary-`assumption` fallback, so a lookup with no match fails at once (amd64 `Bytes`: 24m06 with `‹…›`,
13m18 with `janus_assumption`, 2m13 with `janus_assumption_reducible` for the `first | … | …` alternatives). -/

namespace JanusTests.AssumptionReducible

open Janus Janus.Tactic

/-- It finds a hypothesis that matches up to reducible unfolding, also with a metavariable in the goal. -/
example (a b : Nat) (h : a % 16 = 0) (h2 : b = 3) : a % 16 = 0 := by janus_assumption_reducible

example (a b : Nat) (h : a % 16 = 0) (h2 : b = 3) : True := by
  have : ∃ x, x % 16 = 0 := ⟨_, (show _ % 16 = 0 by janus_assumption_reducible)⟩
  trivial

/-- A hypothesis that matches only after unfolding a definition is NOT found (that is the price of failing fast):
`janus_assumption` (with the ordinary `assumption` fallback) finds it. -/
def Two : Nat := 2
example (a : Nat) (h : a = Two) : a = 2 := by janus_assumption
example (a : Nat) (h : a = Two) : True := by
  fail_if_success
    have : a = 2 := by janus_assumption_reducible
  trivial

/-- As an alternative in `first`: no match falls through to the next alternative. -/
example (a b : Nat) (h : a = 1) : b = b := by
  first | (have _ : b = 0 := by janus_assumption_reducible) | rfl

end JanusTests.AssumptionReducible
