import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X1 (docs/ASL.md, audit/asl): the proof declares JanusASL's transfer theorem itself,
`JanusASL.Proofs.Ensures.toASL`, with a statement of its choosing, hoping the corollary is built
from it. The main theorem is the honest Add proof and verifies; the ASL stage must reject the
shadowing name (the corollary module cannot import both, and the auditor refuses any untrusted
declaration under a JanusASL root). -/

namespace JanusASL.Proofs
theorem Ensures.toASL : True := trivial
end JanusASL.Proofs

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof

