import Janus

/-!
# Tests and witnesses for the kernel model (WP-C, `Janus.Kernel`, `Janus.Amd64.Kernel`)

* The runtime contracts around system calls are satisfiable: `Janus.Contracts.SyscallSat` and
  `SyscallSatAmd64` (`sched_satisfiable`, `convT64_satisfiable`); checked again here.
* A synthetic program `MOVZ X8, #172; SVC #0; RET` (getpid) is proved under `EnsuresK` with the
  `.syscall` stub at the `SVC`, and one ending in `BRK #0` under `Traps`.
-/

namespace KernelTests

section Arm64
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel

/-- `MOVZ X8, #172; SVC #0; RET` at `0x2000`, with the `.syscall` stub on the `SVC`. -/
def pidProg : Program :=
  { segments := [⟨"pid", 0x2000, [0xd2801588, 0xd4000001, 0xd65f03c0]⟩],
    stubs := [⟨"syscall", 0x2004, .syscall⟩], exitAddr := 0 }

theorem pid_spec (E : KEnv) :
    EnsuresK pidProg E 0x2000 [] (fun _ _ => True)
      (fun _ k s' k' => k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid) := by
  intro ret hret s k hs _
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run
  refine ⟨.svc, by kernel_site, Or.inl ⟨⟨.getpid, by simp [svcSys, Sys.ofArm64, setReg], by decide, trivial⟩, ?_⟩⟩
  rintro s' k' ⟨sc, m', r, hsc, heff, rfl⟩
  simp [svcSys, Sys.ofArm64, setReg] at hsc
  subst hsc
  obtain ⟨rfl, rfl, rfl⟩ := heff
  apply ReturnsK.of_reaches
  janus_run

/-- `MOVZ X0, #1; BRK #0` at `0x3000`, with the `.trap` stub on the `BRK`. -/
def brkProg : Program :=
  { segments := [⟨"brk", 0x3000, [0xd2800020, 0xd4200000]⟩],
    stubs := [⟨"trap:BRK", 0x3004, .trap⟩], exitAddr := 0 }

theorem brk_traps (s : State) (hpc : s.pc = 0x3000#64) : Traps brkProg s := by
  unfold Traps
  janus_run

/-- A `.trap` stub on a word that is no trap does not prove `Traps`. -/
example : trapAt { brkProg with stubs := [⟨"trap:BRK", 0x3000, .trap⟩] } 0x3000 = false := by decide

example := Janus.Kernel.Sat.sched_satisfiable
example := Janus.Kernel.Sat.convT64_satisfiable

end Arm64

section Amd64
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Amd64.Kernel

/-- `RET` at `0x1000` with a `.syscall` stub at `0x2000` that is `INT3`: not a kernel site. -/
example : Amd64.Kernel.siteOf { Janus.Amd64.Kernel.Sat.retProg64 with segments := [⟨"x", 0x2000, [0xcc]⟩] } "syscall" 0x2000 = none := by
  decide

/-- `SYSCALL` at `0x2000`. -/
example : Amd64.Kernel.siteOf { Janus.Amd64.Kernel.Sat.retProg64 with segments := [⟨"x", 0x2000, [0x0f, 0x05]⟩] } "syscall" 0x2000 =
    some .syscall := by decide

example := Janus.Amd64.Kernel.Sat.sched_satisfiable
example := Janus.Amd64.Kernel.Sat.convT64_satisfiable

end Amd64

end KernelTests
