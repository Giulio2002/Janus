import Extracted
/-! ATTACK A7: shadow `Extracted.program` with a private declaration of the same surface name
(a program whose code is `B .` at the entry... here: one that returns immediately). -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
private def Extracted.program : Program := { segments := [], stubs := [], exitAddr := Extracted.entry }
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = x.toNat * y.toNat) := by
  sorry
end Proof
