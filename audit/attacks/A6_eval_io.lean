import Extracted
/-! ATTACK A6: `#eval` runs arbitrary IO while `janus verify` compiles the proof, with the
verifier's user privileges and no sandbox. Benign PoC: writes a marker file outside
`.janus-build` (next to the artifact directory). The same IO could rewrite the Janus library's
.olean files, `bin/janus`, or race-modify `.janus-build/Audit.lean` / `Extracted.olean` after the
integrity checks run. -/
#eval IO.FS.writeFile "/srv/janus/audit/work/A6-written-during-verify.txt" "proof code ran with write access\n"
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
