import Extracted
/-! R1 (round 3): CRITICAL-1 moved into a proof-local definition. The statement mentions only
`Proof.mul x y` (a constant: it round-trips trivially and has no instance argument), while the
*disclosed body* of `Proof.mul` passes an inline `HMul` instance that adds. `checkInstArgs` and the
round trip only look at the theorem type, never at the bodies listed in `definitions`, so the
report discloses `Proof.mul := fun a b => a * b` for a function that adds. The target
example.com/basic.Add computes x + y. -/
open Janus Janus.GoABI Janus.Tactic
namespace Proof
def mul (a b : BitVec 64) : BitVec 64 :=
  @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ a b
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = mul x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
