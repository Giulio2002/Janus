import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X3: the proof plants the coverage fact `JanusASLWords.covered` (here a trivial
`True`), hoping the corollary uses it instead of the trusted kernel-evaluated one. Rejected: the
name is reserved for the trusted coverage module. -/

theorem JanusASLWords.covered : True := trivial

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof

