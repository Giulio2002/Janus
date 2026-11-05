import Janus

/-! # `janus_rfl` (S11)

`rfl` at default transparency on a goal that mentions a long chain of stores unfolds the chain before failing (35-95 s each in
FV-B's DivMod wrapper). `janus_rfl` = `with_reducible rfl`, then the full `rfl` only if the goal has no `writeLE`. -/

namespace JanusTests.JanusRfl

open Janus Janus.Arm64

def chain : Nat → Memory → Memory
  | 0, m => m
  | n+1, m => Memory.writeLE (chain n m) (1000 + 8 * n) 8 (n * 12345)

def Two : Nat := 2
def idN (x : Nat) : Nat := x

/-- A goal without stores that needs a delta step: the full `rfl` still runs. -/
example : Two = 2 := by janus_rfl
example (a : Nat) : a + 0 = a := by janus_rfl

/-- Reducible goals with stores are closed. -/
example (m : Memory) (v : Nat) : (m.writeLE 8 8 v).readLE 8 8 = (m.writeLE 8 8 v).readLE 8 8 := by janus_rfl

/- A goal with stores that only default-transparency `rfl` could close (a definition to unfold) is NOT closed: `janus_rfl` does
not run the full `rfl` when a `writeLE` occurs (the goals of `janus_run` hold literal `writeLE` chains, not `chain 400 m`). -/
example (m : Memory) (v : Nat) : True := by
  fail_if_success
    have : idN ((m.writeLE 8 8 v).readLE 5 8) = (m.writeLE 8 8 v).readLE 5 8 := by janus_rfl
  trivial

/-- ... while the same goal without a store is closed by the full `rfl`. -/
example (m : Memory) : idN (m.readLE 5 8) = m.readLE 5 8 := by janus_rfl

/-- As an alternative in `first`: the next one runs. -/
example (m : Memory) : (chain 400 m).readLE 5 8 = (chain 400 m).readLE 5 8 := by
  first | janus_rfl | simp

end JanusTests.JanusRfl
