import Extracted
/-! U1: under the `unshare` fallback (no bwrap), only `/` is remounted read-only. If the janus
cache lives on another mount (here JANUS_CACHE_DIR under the host /tmp), the sandboxed proof can
write the trusted cache, e.g. plant a replay-cache marker. The theorem is honest; the side effect
is the attack. -/
open Janus Janus.GoABI Janus.Tactic
run_cmd do
  let some c ← IO.getEnv "JANUS_CACHE_DIR" | return
  IO.FS.createDirAll (c ++ "/v1/replay/00")
  IO.FS.writeFile (c ++ "/v1/replay/00/planted-by-sandboxed-proof") "x\n"
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
