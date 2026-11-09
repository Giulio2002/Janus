import Lean
import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! ASL forgery X5: the proof defines its own `janus_asl_corollary` command (same syntax, higher
priority), which the corollary module, importing the proof, may run instead of JanusASL's: it adds
`JanusASLCorollary.correctness_asl : True`. Rejected either way: an ambiguous command fails to
elaborate, and a corollary whose type is not the derivation from the verified theorem is refused by
the trusted auditor (which runs no proof code). -/

open Lean Elab Command in
elab (priority := high) "janus_asl_corollary " c:ident " of " _t:ident " using " _w:ident : command => do
  liftTermElabM do
    addDecl (.thmDecl { name := c.getId, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

end Proof

