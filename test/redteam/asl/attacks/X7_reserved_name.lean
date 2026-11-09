import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X7: the proof adds a declaration under a reserved JanusASL root that does not clash
with any real one (`JanusASL.Proofs.LinuxEL0Config'`, a look-alike of the configuration predicate).
Nothing fails to import, so this exercises the trusted auditor's rule itself: no untrusted module
may declare a JanusASL, ArmASL, Sail, JanusASLWords or JanusASLCorollary name. -/

def JanusASL.Proofs.LinuxEL0Config' : Prop := True

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
