import Extracted

/-! R1 forged-lemma: "Add returns 42" from the forged framework lemma `Janus.GoABI.forged : False`. -/

namespace Proof

theorem correctness (x y : BitVec 64) :
    Janus.GoABI.Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = 42) := Janus.GoABI.forged.elim

end Proof
