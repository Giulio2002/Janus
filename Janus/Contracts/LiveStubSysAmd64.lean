import Janus.Contracts.LiveStub
import Janus.Contracts.SyscallSatAmd64

/-!
# Scheduler hooks and `convT64` stubs at a program's own contract addresses (amd64)

As `LiveStubSys` (arm64): `RET` for `runtime.entersyscall`/`exitsyscall`, `MOV [RSP-16], RAX;
LEA RAX, [RSP-16]; RET` for `runtime.convT64`, the tactics proving `Amd64.Kernel.SchedContract` /
`ConvT64Contract` for them at the real address (the proofs of `SyscallSatAmd64.sched_witness64` /
`convT64_witness64`).
-/

namespace Janus.Contracts.LiveStubSysAmd64

/-- `runtime.entersyscall`, `runtime.exitsyscall`: `RET`. -/
def schedSeg (addr : Nat) : Janus.Amd64.Segment := ⟨"live-stub.sched", addr, [0xc3]⟩
/-- `runtime.convT64`: `MOV [RSP-16], RAX; LEA RAX, [RSP-16]; RET`. -/
def convT64Seg (addr : Nat) : Janus.Amd64.Segment :=
  ⟨"live-stub.convT64", addr, [0x48, 0x89, 0x44, 0x24, 0xf0, 0x48, 0x8d, 0x44, 0x24, 0xf0, 0xc3]⟩

end Janus.Contracts.LiveStubSysAmd64

/-- `Amd64.Kernel.SchedContract` against `LiveStubSysAmd64.schedSeg`. -/
syntax "janus64_sys_sched" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_sys_sched) => `(tactic| (
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Amd64.Kernel in
      (
      intro s hpc ⟨h1, h2, h3, h4, h5⟩
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine ⟨0, s.regs, s.flags, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _, trivial⟩
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
      )))

/-- `Amd64.Kernel.ConvT64Contract linked a rt stack` against `LiveStubSysAmd64.convT64Seg`, literal `stack ≥ 16`. -/
syntax "janus64_sys_convt64 " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_sys_convt64 $stack) => `(tactic| (
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Amd64.Kernel in
      (
      intro s hpc ⟨h1, h2, h3, h4, h5⟩
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      have hp : (s.regs 4 - 16#64).toNat = (s.regs 4).toNat - 16 := by
        rw [BitVec.toNat_sub]; simp; omega
      refine ⟨s.regs 4 - 16#64, s.regs, s.flags, s.xmm, s.ymmHi,
        Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 16) 8 (s.regs 0).toNat, s.zmmHi, s.kreg, ?_, ?_, ?_⟩
      · simp only [retState64, retAddrOf]
        congr 1
        · funext i
          simp only [callRegs64, setRegF]
          by_cases a : i = 4 <;> by_cases b : i = 0 <;> simp_all <;> intros <;> split <;> (try split) <;> simp_all
        · funext i; split <;> simp_all
      · exact MemFrame.of_writeLE _ _ (r := ((s.regs 4).toNat - $stack, (s.regs 4).toNat))
          (by simp [calleeStack64]) (by simp only; omega) (by simp only; omega)
      · rw [hp]
        refine ⟨by omega, ?_, ?_⟩
        · rw [Arm64.Memory.accessible_writeLE]
          exact Arm64.Memory.accessible_sub _ h5 (Or.inl rfl) (by omega) (by omega)
        · rw [Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 0).isLt
      )))
