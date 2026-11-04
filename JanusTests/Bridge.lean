import Janus

/-! Tests for `Reaches.toReachesRet` / `Ensures.toSummary` (arm64 and amd64): a function theorem
stated as `Ensures` is usable as a callee summary (`janus_run … calls [S]`, `Reaches.call`). -/

namespace JanusTests.Bridge.Arm

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

def retProg : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

theorem ens (x : W64) : Ensures retProg 0x1000 [x] (fun _ => True) (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs _; janus_intro hs; janus_run

theorem noExitCode : retProg.fetch retProg.exitAddr = none := by decide

/-- The `Ensures` theorem as a summary. -/
theorem sum (x : W64) : Summary retProg 0x1000
    (fun s => ∃ ret, RetAddr retProg ret ∧ CallSetup (retProg.withExit ret) 0x1000 [x] s ∧ True)
    (fun s s' => ABIReturn s s' ∧ s'.regs 0 = x) :=
  Ensures.toSummary (ens x) noExitCode

/-- ... and a call through it reaches the continuation. -/
example (x : W64) (ret : Nat) (hret : RetAddr retProg ret) (s : State)
    (hs : CallSetup (retProg.withExit ret) 0x1000 [x] s) :
    Reaches (retProg.withExit ret) s (IsReturn fun s' => s'.regs 0 = x) :=
  Reaches.call ((sum x).withExit hret) hs.pc ⟨ret, hret, hs, trivial⟩ fun s' hpc ⟨_, h⟩ =>
    Reaches.exit_withExit hret (by rw [hpc, hs.lr]; rfl) h

/-- `Reaches` of `p.withExit ret` back to `ReachesRet p ret`. -/
example (x : W64) (ret : Nat) (hret : RetAddr retProg ret) (s : State)
    (hs : CallSetup (retProg.withExit ret) 0x1000 [x] s) :
    ReachesRet retProg (BitVec.ofNat 64 ret) s fun s' => s'.regs 0 = x := by
  refine Reaches.toReachesRet ?_ hret noExitCode
  janus_intro hs; janus_run

end JanusTests.Bridge.Arm

namespace JanusTests.Bridge.Amd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

def retProg : Janus.Amd64.Program := { segments := [⟨"f", 0x1000, [0xc3]⟩], stubs := [], exitAddr := 0 }

theorem ens (x : W64) : Ensures retProg 0x1000 [x] (fun s => StackWritable s 0 8)
    (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨hle, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run

theorem noExitCode : retProg.fetch retProg.exitAddr = none := by decide

theorem sum (x : W64) : Summary retProg 0x1000
    (fun s => ∃ ret, RetAddr retProg ret ∧ CallSetup (retProg.withExit ret) 0x1000 [x] s ∧
      StackWritable s 0 8)
    (fun s s' => ABIReturn s s' ∧ s'.regs 0 = x) :=
  Ensures.toSummary (ens x) noExitCode

example (x : W64) (ret : Nat) (hret : RetAddr retProg ret) (s : State)
    (hs : CallSetup (retProg.withExit ret) 0x1000 [x] s) (hw : StackWritable s 0 8) :
    Reaches (retProg.withExit ret) s (IsReturn fun s' => s'.regs 0 = x) :=
  Reaches.call ((sum x).withExit hret) hs.rip ⟨ret, hret, hs, hw⟩ fun s' hpc ⟨_, h⟩ =>
    Reaches.exit_withExit hret (by rw [hpc, retAddrOf_eq, hs.ret]; rfl) h

example (x : W64) (ret : Nat) (hret : RetAddr retProg ret) (s : State)
    (hs : CallSetup (retProg.withExit ret) 0x1000 [x] s) (hw : StackWritable s 0 8) :
    ReachesRet retProg (BitVec.ofNat 64 ret) s fun s' => s'.regs 0 = x := by
  refine Reaches.toReachesRet ?_ hret noExitCode
  obtain ⟨hle, hnw, hacc⟩ := hw
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  janus64_run

end JanusTests.Bridge.Amd
