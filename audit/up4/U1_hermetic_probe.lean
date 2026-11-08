import Extracted
import Lean
open Lean Elab Command Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round n11 S1: the elaboration tries to read the janus cache dir (HMAC key), to write outside the sandbox, and to list
the framework build dir. Any success is turned into an elaboration error (so the verify must then be rejected).
Expected: Verified   (every probe fails inside the sandbox; a "SANDBOX ESCAPE" error means the verifier is attackable). -/

/-! UP4 hermeticity probe: the elaboration tries to read the HMAC keys, ~/.cache, /srv, $HOME, /root, /etc/shadow and the
environment, and records whether a host file's presence is visible. Any success is an elaboration error ("HERMETIC ESCAPE"),
so the verify is then Invalid. Expected: Verified. -/
def entries (d : String) : IO (Array String) := do
  try return (← System.FilePath.readDir d).map (·.fileName) catch _ => return #[]

run_cmd do
  let mut hits : Array String := #[]
  let home := (← IO.getEnv "HOME").getD ""
  -- files that must not exist at all
  for p in ["/root/.cache/janus/v1/result/.key", "/root/.cache/janus/asl-cache-key", "/root/.cache/janus/asl-cache.key",
      "/etc/shadow", "/etc/hostname", "/etc/ssh", "/home", "/root/.bashrc", "/root/.ssh"] do
    if (← System.FilePath.pathExists p) then hits := hits.push p
  -- the key/ cache directories may exist only as ancestors of the exposed framework/workspace
  for e in ["asl-cache-key", "asl-cache.key", ".key"] do
    for d in ["/root/.cache/janus", "/root/.cache/janus/v1/result"] do
      if (← entries d).contains e then hits := hits.push s!"{d}/{e}"
  for e in ["result", "replay", "modstore", "oleans", "asl", "run", "tmp", "gc.lock"] do
    if (← entries "/root/.cache/janus/v1").contains e then hits := hits.push s!"v1/{e}"
  for e in (← entries "/root/.cache") do
    if e != "janus" then hits := hits.push s!"~/.cache/{e}"
  for e in (← entries "/root") do
    if e != ".cache" && e != ".elan" then hits := hits.push s!"/root/{e}"
  for e in (← entries "/srv") do
    if e != "janus-up4" && e != "janus-ops" then hits := hits.push s!"/srv/{e}"
  for e in (← entries "/srv/janus-ops") do
    if !e.startsWith "work.up4" then hits := hits.push s!"/srv/janus-ops/{e}"
  for e in (← entries "/root/.elan") do
    if e != "toolchains" then hits := hits.push s!"/root/.elan/{e}"
  if (← entries "/root/.elan/toolchains").size > 1 then hits := hits.push "more than one toolchain visible"
  for v in ["JANUS_CACHE_DIR", "JANUS_CACHE_KEY_DIR", "SSH_AUTH_SOCK", "GITHUB_TOKEN", "ANTHROPIC_API_KEY", "XDG_RUNTIME_DIR"] do
    if (← IO.getEnv v).isSome then hits := hits.push s!"env {v}"
  if home != "/tmp" then hits := hits.push s!"HOME={home}"
  if hits.size > 0 then throwError "HERMETIC ESCAPE {hits}"

namespace Proof
theorem correctness (impl : List Segment) (x y : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
