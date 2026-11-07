import Extracted
import Lean
open Lean Elab Command Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round n11 S1: the elaboration tries to read the janus cache dir (HMAC key), to write outside the sandbox, and to list
the framework build dir. Any success is turned into an elaboration error (so the verify must then be rejected).
Expected: Verified   (every probe fails inside the sandbox; a "SANDBOX ESCAPE" error means the verifier is attackable). -/

/-! UP4: a proof must behave identically whether or not a host file exists. It checks a host path chosen by the runner
(/srv/janus-up4/audit/up4/HOSTFILE-PRESENT, created or removed by run-hermetic.sh); inside the hermetic sandbox it is
never visible, so the elaboration is the same either way. Expected: Verified in BOTH states, identical output. -/
run_cmd do
  if (← System.FilePath.pathExists "/srv/janus-up4/audit/up4/HOSTFILE-PRESENT") then
    throwError "HERMETIC ESCAPE: host file visible"
  logInfo m!"host-file probe: absent"

namespace Proof
theorem correctness (impl : List Segment) (x y : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
