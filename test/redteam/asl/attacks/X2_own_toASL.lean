import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X2: the proof defines its own `aslRun` and `Ensures.toASL` (in its namespace) and
proves an "ASL" statement with them, then asks for it as the theorem (`--theorem
Proof.correctness_asl`). The main verification accepts it as what it is, a theorem about
proof-local definitions (disclosed in the report); the ASL stage refuses it: the corollary is
derived only from an `Ensures` theorem, with JanusASL's own `Ensures.toASL`, never from a
proof-supplied one. -/

namespace Proof

/-- A fake "ASL run": always returns. -/
def aslRun (_p : Program) (_fuel : Nat) (_s : Nat) : Bool := true

theorem Ensures.toASL : ∀ (p : Program) (fuel s : Nat), aslRun p fuel s = true := fun _ _ _ => rfl

theorem correctness_asl : ∀ (fuel s : Nat), aslRun Extracted.program fuel s = true :=
  Ensures.toASL Extracted.program

end Proof
