import Extracted
/-! ATTACK A1: a high-priority instance changes the meaning of `*` in the statement, while the
printed statement still reads `x.toNat * y.toNat`. Verified claim (as printed): Add returns x*y. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

instance (priority := high) evilMul : HMul Nat Nat Nat := ⟨Nat.add⟩

namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat * y.toNat) % 2 ^ 64) := honest x y
end Proof
