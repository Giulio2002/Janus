import Janus.Contracts.LiveStub
import Janus.Contracts.SyscallSat

/-!
# Scheduler hooks and `convT64` stubs at a program's own contract addresses (arm64)

The stubs of `SyscallSat` (`RET` for `runtime.entersyscall`/`exitsyscall`; a store of the argument
below `SP` and a pointer to it for `runtime.convT64`), placed where an extracted program says the
runtime function is, and the tactics that prove `SchedContract` / `ConvT64Contract` for them: the
proofs of `SyscallSat.sched_witness` / `convT64_witness` with the program a closed constant
(`def linked := Extracted.program.link segs`) and the address a numeral (`janus_eval%`). Used for
the non-vacuity witnesses of theorems about code that makes system calls. Nothing is trusted: the
contracts are ordinary kernel-checked theorems.
-/

namespace Janus.Contracts.LiveStubSys

/-- `runtime.entersyscall`, `runtime.exitsyscall`: `RET`. -/
def schedSeg (addr : Nat) : Janus.Segment := ⟨"live-stub.sched", addr, [0xd65f03c0]⟩
/-- `runtime.convT64`: `STUR X0, [SP, #-16]; SUB X0, SP, #16; RET`. -/
def convT64Seg (addr : Nat) : Janus.Segment :=
  ⟨"live-stub.convT64", addr, [0xf81f03e0, 0xd10043e0, 0xd65f03c0]⟩

end Janus.Contracts.LiveStubSys

/-- `SchedContract` against `LiveStubSys.schedSeg`. -/
syntax "janus_sys_sched" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_sys_sched) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel in
      (
      intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine ⟨0, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, trivial⟩
      simp only [retStateX]
      congr 1
      funext i
      simp only [callRegs]
      split <;> simp
      )))

/-- `ConvT64Contract linked a rt stack` against `LiveStubSys.convT64Seg`, for a literal `stack ≥ 16`. -/
syntax "janus_sys_convt64 " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_sys_convt64 $stack) => `(tactic| (
      open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel in
      (
      intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      have hp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
        rw [BitVec.toNat_sub]; simp; omega
      refine ⟨s.sp - 16#64, s.regs, s.flags, s.vregs,
        s.mem.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat (s.regs 0)), s.excl, s.exclPass, ?_, ?_, ?_⟩
      · simp only [retStateX]
        congr 1
        funext i
        cases i with
        | zero => simp [callRegs, setReg]
        | succ n => simp only [callRegs, setReg, Nat.add_one_ne_zero, ite_false]; split <;> simp
      · exact MemFrame.of_writeLE _ _ (r := (s.sp.toNat - $stack, s.sp.toNat - 8)) (by simp [calleeStack])
          (by simp only; omega) (by simp only; omega)
      · rw [hp]
        refine ⟨by omega, ?_, ?_⟩
        · rw [Memory.accessible_writeLE]
          exact Memory.accessible_sub _ h7 (Or.inl rfl) (by omega) (by omega)
        · rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 0).isLt
      )))
