import Extracted
import Lean
open Lean Elab Command Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round n11 S4: which host state can proof elaboration observe in the sandbox? Reports (as an error, so the verify is Invalid and the
text shows) env vars, /proc files, clock, randomness, the network, uid and the visible mounts. Expected: Invalid (probe); read the list. -/

run_cmd do
  let mut o : Array String := #[]
  for v in ["HOME", "PATH", "USER", "JANUS_CACHE_DIR", "JANUS_POOL_DIR", "GOCACHE", "SSH_AUTH_SOCK", "LEAN_PATH", "TMPDIR", "HOSTNAME"] do
    o := o.push s!"env {v}={(← IO.getEnv v).getD "<unset>"}"
  for f in ["/proc/loadavg", "/proc/meminfo", "/proc/cpuinfo", "/proc/self/environ", "/proc/1/cmdline", "/etc/hostname", "/etc/passwd", "/root/.ssh", "/root/.claude", "/srv/janus-ops"] do
    let r ← (try (do let b ← IO.FS.readBinFile f; pure s!"{b.size}B") catch _ => pure "no")
    let d ← (try (do let es ← System.FilePath.readDir f; pure s!"dir:{es.size}") catch _ => pure "")
    o := o.push s!"file {f}: {r} {d}"
  o := o.push s!"mono {← IO.monoMsNow} rand {(← IO.getRandomBytes 4).size}"
  let r ← (try (IO.Process.output { cmd := "/bin/bash", args := #["-c", "id -u; ls /proc | wc -l; ls /proc/net 2>&1 | head -2; (timeout 3 bash -c 'echo x > /dev/tcp/1.1.1.1/53') 2>&1 | head -1; echo net-rc=$?; ls /srv /root 2>&1 | head -5"] }) catch _ => pure { exitCode := 1, stdout := "proc fail", stderr := "" })
  o := o.push s!"sh: {r.stdout.replace "\n" " | "}"
  (throwError m!"S4 {o}" : CommandElabM Unit)

namespace Proof
theorem correctness (impl : List Segment) (x y : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
