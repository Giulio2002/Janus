import Janus

/-! # `janus_exact` (S3c)

`exact h` with an `h` that is not the goal elaborates it against the goal; with a long chain of stores in the goal
that costs minutes (FV-B DivMod `exact h_x15` on `readLE …` goals). `janus_exact h` compares the carriers of the
equations first and fails at once. -/

namespace JanusTests.JanusExact

open Janus Janus.Amd64

def chain : Nat → Janus.Arm64.Memory → Janus.Arm64.Memory
  | 0, m => m
  | n+1, m => Janus.Arm64.Memory.writeLE (chain n m) (1000 + 8 * n) 8 (n * 12345)

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

/-- The hypothesis is about another carrier (`W128` vs `Nat`): `janus_exact` fails quickly (plain `exact` takes
seconds to minutes here) and `first` continues. -/
example (s : Janus.Amd64.State) (m : Janus.Arm64.Memory) (ret : Nat) (h : s.xmm 15 = OfNat.ofNat 0)
    (h2 : Janus.Arm64.Memory.readLE (chain 400 m) 5 8 = ret) :
    Janus.Arm64.Memory.readLE (chain 400 m) 7 8 = ret ∨ True := by
  first | janus_exact h | exact Or.inr trivial

/-- It still closes goals whose literal is in another form, and goals through a structure update. -/
example (s : Janus.Amd64.State) (h : s.xmm 15 = OfNat.ofNat 0) : s.xmm 15 = 0#128 := by janus_exact h
example (s : Janus.Amd64.State) (h : s.xmm 15 = OfNat.ofNat 0) :
    ({ s with rip := 5 } : Janus.Amd64.State).xmm 15 = 0#128 := by janus_exact h

/-- A hypothesis of a different statement is rejected. -/
example (s : Janus.Amd64.State) (h : s.xmm 15 = 0#128) : True := by
  fail_if_success
    have : s.xmm 14 = 0#128 := by janus_exact h
  trivial

/-- Carriers equal only up to unfolding (an `abbrev`, a `def` alias) still close: the precheck unifies the carriers at
default transparency. -/
abbrev N' := Nat
def Word64 := BitVec 64

example (a b : Nat) (h : (a : N') = b) : a = b := by janus_exact h
example (a b : BitVec 64) (h : a = b) : (a : Word64) = b := by janus_exact h
/-- `janus_exact` skips a hypothesis of another shape quickly and still closes the right one. -/
example (s : Janus.Amd64.State) (m : Janus.Arm64.Memory) (ret : Nat) (h : s.xmm 15 = OfNat.ofNat 0)
    (h2 : Janus.Arm64.Memory.readLE (chain 400 m) 5 8 = ret) :
    Janus.Arm64.Memory.readLE (chain 400 m) 5 8 = ret := by
  first | janus_exact h | janus_exact h2

example (a b : Nat) (h : a = b) : a = b := by janus_close

end JanusTests.JanusExact
