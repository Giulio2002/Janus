import Janus

/-!
# Tests and witnesses for the kernel model (WP-C, `Janus.Kernel`, `Janus.Amd64.Kernel`)

* The runtime contracts around system calls are satisfiable by concrete code: `RET` meets
  `SchedContract` (entersyscall/exitsyscall), and a three-instruction function that stores its
  argument below `SP` and returns a pointer to it meets `ConvT64Contract`, on both ISAs.
* A synthetic program `MOVZ X8, #172; SVC #0; RET` (getpid) is proved under `EnsuresK` with the
  `.syscall` stub at the `SVC`, and one ending in `BRK #0` under `Traps`.
-/

namespace KernelTests

section Arm64
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel

/-- `RET` at `0x1000`. -/
def retProg : Program := { segments := [⟨"ret", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

theorem sched_witness (rt : List (Nat × Nat)) (stack : Nat) :
    SchedContract retProg 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
  janus_run
  refine ⟨0, s.regs, s.flags, s.vregs, s.mem, ?_, MemFrame.refl _ _, trivial⟩
  simp only [retState]
  congr 1
  funext i
  simp only [callRegs]
  split <;> simp

/-- `STUR X0, [SP, #-16]; SUB X0, SP, #16; RET` at `0x1000`. -/
def boxProg : Program :=
  { segments := [⟨"box", 0x1000, [0xf81f03e0, 0xd10043e0, 0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

theorem convT64_witness (rt : List (Nat × Nat)) (stack : Nat) (hs : 16 ≤ stack) :
    ConvT64Contract boxProg 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
  janus_run
  have hp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  refine ⟨s.sp - 16#64, s.regs, s.flags, s.vregs,
    s.mem.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat (s.regs 0)), ?_, ?_, ?_⟩
  · simp only [retState]
    congr 1
    funext i
    cases i with
    | zero => simp [callRegs, setReg]
    | succ n => simp only [callRegs, setReg, Nat.add_one_ne_zero, ite_false]; split <;> simp
  · exact MemFrame.of_writeLE _ _ (r := (s.sp.toNat - stack, s.sp.toNat - 8)) (by simp [calleeStack])
      (by simp only; omega) (by simp only; omega)
  · rw [hp]
    refine ⟨by omega, ?_, ?_⟩
    · rw [Memory.accessible_writeLE]
      exact Memory.accessible_sub _ h7 (Or.inl rfl) (by omega) (by omega)
    · rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 0).isLt

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

end Arm64

section Amd64
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Amd64.Kernel

/-- `RET` at `0x1000`. -/
def retProg64 : Amd64.Program := { segments := [⟨"ret", 0x1000, [0xc3]⟩], stubs := [], exitAddr := 0 }

theorem sched_witness64 (rt : List (Nat × Nat)) (stack : Nat) :
    Amd64.Kernel.SchedContract retProg64 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5⟩
  janus64_run
  refine ⟨0, s.regs, s.flags, s.xmm, s.ymmHi, s.mem, ?_, MemFrame.refl _ _, trivial⟩
  simp only [retState64, retAddrOf]
  congr 1
  · funext i
    simp only [callRegs64, setRegF]
    split
    · rfl
    · split
      · rfl
      · split <;> (try split) <;> (try split) <;> simp_all
  · funext i; split <;> simp_all

/-- `MOV [RSP-16], RAX; LEA RAX, [RSP-16]; RET` at `0x1000`. -/
def boxProg64 : Amd64.Program :=
  { segments := [⟨"box", 0x1000, [0x48, 0x89, 0x44, 0x24, 0xf0, 0x48, 0x8d, 0x44, 0x24, 0xf0, 0xc3]⟩],
    stubs := [], exitAddr := 0 }

theorem convT64_witness64 (rt : List (Nat × Nat)) (stack : Nat) (hs : 16 ≤ stack) :
    Amd64.Kernel.ConvT64Contract boxProg64 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5⟩
  janus64_run
  have hp : (s.regs 4 - 16#64).toNat = (s.regs 4).toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  refine ⟨s.regs 4 - 16#64, s.regs, s.flags, s.xmm, s.ymmHi,
    Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 16) 8 (s.regs 0).toNat, ?_, ?_, ?_⟩
  · simp only [retState64, retAddrOf]
    congr 1
    · funext i
      simp only [callRegs64, setRegF]
      by_cases a : i = 4 <;> by_cases b : i = 0 <;> simp_all <;> intros <;> split <;> (try split) <;> simp_all
    · funext i; split <;> simp_all
  · exact MemFrame.of_writeLE _ _ (r := ((s.regs 4).toNat - stack, (s.regs 4).toNat))
      (by simp [calleeStack64]) (by simp only; omega) (by simp only; omega)
  · rw [hp]
    refine ⟨by omega, ?_, ?_⟩
    · rw [Arm64.Memory.accessible_writeLE]
      exact Arm64.Memory.accessible_sub _ h5 (Or.inl rfl) (by omega) (by omega)
    · rw [Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 0).isLt

/-- `RET` at `0x1000` with a `.syscall` stub at `0x2000` that is `INT3`: not a kernel site. -/
example : Amd64.Kernel.siteOf { retProg64 with segments := [⟨"x", 0x2000, [0xcc]⟩] } "syscall" 0x2000 = none := by
  decide

/-- `SYSCALL` at `0x2000`. -/
example : Amd64.Kernel.siteOf { retProg64 with segments := [⟨"x", 0x2000, [0x0f, 0x05]⟩] } "syscall" 0x2000 =
    some .syscall := by decide

end Amd64

end KernelTests
