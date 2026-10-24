import Extracted
/-! U1b: the residual of U1. Under the `unshare` fallback only `/` used to be remounted
read-only, so a sandboxed proof could still write the host's `/tmp`, `/dev/shm` and every other
read-write mount (`/boot`, `/run/user/<uid>`, …). The proof tries each; the runner checks on
the host that no marker arrived. The theorem is honest; the side effect is the attack. Run with
`JANUS_SANDBOX=unshare`. -/
open Janus Janus.GoABI Janus.Tactic
run_cmd do
  for d in ["/tmp", "/dev/shm", "/boot", "/run/user/0", "/run"] do
    try IO.FS.writeFile (d ++ "/janus-u1b-marker") "planted by a sandboxed proof\n" catch _ => pure ()
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
