import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X6: the theorem is about a program `p` that it only assumes equal to
`Extracted.program`; the ASL corollary must be about the identity-checked constant itself, so the
ASL stage refuses it (the main theorem, which mentions Extracted.program, verifies). -/

namespace Proof

theorem correctness (p : Program) (hp : p = Extracted.program) (x y : BitVec 64) :
    Ensures p Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  subst hp
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof
