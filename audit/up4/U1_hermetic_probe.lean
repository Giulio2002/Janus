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
    if e != "__ROOT_NAME__" && e != "janus-ops" then hits := hits.push s!"/srv/{e}"
  for e in (← entries "/srv/janus-ops") do
    if !e.startsWith "work.up4" then hits := hits.push s!"/srv/janus-ops/{e}"
  for e in (← entries "/root/.elan") do
    if e != "toolchains" then hits := hits.push s!"/root/.elan/{e}"
  if (← entries "/root/.elan/toolchains").size > 1 then hits := hits.push "more than one toolchain visible"
  for v in ["JANUS_CACHE_DIR", "JANUS_CACHE_KEY_DIR", "SSH_AUTH_SOCK", "GITHUB_TOKEN", "ANTHROPIC_API_KEY", "XDG_RUNTIME_DIR"] do
    if (← IO.getEnv v).isSome then hits := hits.push s!"env {v}"
  if home != "/tmp" then hits := hits.push s!"HOME={home}"
  if hits.size > 0 then throwError "HERMETIC ESCAPE {hits}"

-- UP3 x UP4: the theorem is the plain Add one (no runtime link variable) with its tied Witness.nonvacuous, so the probe passes the
-- witness rule and reaches the sandbox stage it exercises; the runner passes both theorems.
namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000


def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def s0 : Janus.Arm64.State :=
  { regs := fun i => if i = 0 then (3) else if i = 1 then (4) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Arm64.State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64)) := by
  refine ⟨ret, s0, (3), (4), hret, setup, ?pre, correctness (3) (4) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
