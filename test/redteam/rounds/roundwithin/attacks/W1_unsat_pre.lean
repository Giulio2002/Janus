import Extracted

/-! Expected-reason: has no kernel-checked non-vacuity witness. A bound (0 instructions!) proved vacuously from a precondition no state meets. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.1.symm.trans hp.2) (by decide)

end Proof
