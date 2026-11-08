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
