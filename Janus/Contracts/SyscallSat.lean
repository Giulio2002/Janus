import Janus.Contracts.Syscall

/-!
# The runtime contracts around system calls are satisfiable (arm64, round 9 SAT)

`SchedContract` (`runtime.entersyscall`/`exitsyscall`) and `ConvT64Contract` (`runtime.convT64`)
are `Summary` contracts. For each this file gives machine code that meets it (`RET`; a store of the
argument below `SP` and a pointer to it), proved by symbolic execution, and a call state that
satisfies its precondition: `<name>_satisfiable` (`audit/round9/run-round9.sh`, row SAT). The
kernel contracts are relations, satisfiable by `Kernel.Effect.total` and `Kernel.SiteNext.total`.
-/

namespace Janus.Kernel.Sat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Kernel

/-- `RET` at `0x1000`. -/
def retProg : Program := { segments := [⟨"ret", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

theorem sched_witness (rt : List (Nat × Nat)) (stack : Nat) :
    SchedContract retProg 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
  janus_run
  refine ⟨0, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, trivial⟩
  simp only [retStateX]
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
    s.mem.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat (s.regs 0)), s.excl, s.exclPass, ?_, ?_, ?_⟩
  · simp only [retStateX]
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

/-- A call state at `0x1000`: `SP = 0x200000` 16-aligned with 4 KiB of writable stack below it
and 64 bytes above, `X30 = 0x2000`. -/
def wstate : State :=
  { regs := fun i => if i = 30 then 0x2000#64 else 0, sp := 0x200000#64, pc := 0x1000#64,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨0x200000 - 4096, 4096 + 64, true⟩]⟩ }

theorem callOK_w (n : Nat) (hn : n ≤ 7) : CallOK wstate 4096 n := by
  have hw : wstate.mem.accessible (0x200000 - 4096) (4096 + 64) true = true := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by simp [wstate]; omega, ?_⟩
  exact Memory.accessible_mono _ hw (by simp [wstate]) (by simp [wstate]; omega)

theorem sched_satisfiable : ∃ (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    SchedContract p addr rt stack ∧ ∃ s : State, s.pc = BitVec.ofNat 64 addr ∧ CallOK s stack 0 :=
  ⟨retProg, 0x1000, [], 4096, sched_witness [] 4096, wstate, rfl, callOK_w 0 (by omega)⟩

theorem convT64_satisfiable : ∃ (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    ConvT64Contract p addr rt stack ∧ ∃ s : State, s.pc = BitVec.ofNat 64 addr ∧ CallOK s stack 1 :=
  ⟨boxProg, 0x1000, [], 4096, convT64_witness [] 4096 (by omega), wstate, rfl, callOK_w 1 (by omega)⟩

end Janus.Kernel.Sat
