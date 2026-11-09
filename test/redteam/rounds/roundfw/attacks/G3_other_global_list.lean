import Extracted

/-! Attack (G3): `GlobalIs` over a list other than `Extracted.program.globals`, a global that
holds whatever the proof chooses. janus-audit must require the extraction's own list. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

def fake : List GlobalSegment := [{ name := "example.com/basic.karatsubaCut", base := 0, size := 0 }]

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => GlobalIs fake s.mem "example.com/basic.karatsubaCut" 1 ∧ False)
      (fun _ _ => False) := by
  intro ret hret s hs h
  exact absurd h.2 id

end Proof
