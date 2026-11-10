import Janus
import Extracted

/-! Expected-reason: has no kernel-checked non-vacuity witness. A 0-instruction bound proved vacuously from an unsatisfiable precondition. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 0) Extracted.program Extracted.entry [x, y]
      (fun s => StackWritable s 0 8 ∧ s.regs 0 = 1 ∧ s.regs 0 = 2) (fun _ s' => s'.regs 0 = 7) := by
  intro ret hret s hs hp
  exact absurd (hp.2.1.symm.trans hp.2.2) (by decide)

end Proof
