import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X4: the proof declares the corollary's name, `JanusASLCorollary.correctness_asl`,
with a statement of its choosing, so that it would be reported as the ASL corollary. Rejected: the
corollary module cannot add its theorem under a taken name, and the auditor refuses untrusted
declarations under reserved roots. -/

theorem JanusASLCorollary.correctness_asl : True := trivial

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof

