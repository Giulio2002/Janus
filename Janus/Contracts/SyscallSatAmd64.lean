import Janus.Contracts.SyscallAmd64

/-!
# The runtime contracts around system calls are satisfiable (amd64, round 9 SAT)

As `Janus.Contracts.SyscallSat`: `RET` meets `Amd64.Kernel.SchedContract`, a store of `RAX`
below `RSP` and a pointer to it meets `Amd64.Kernel.ConvT64Contract`, and a call state satisfies
their precondition. The kernel relations are satisfiable by `Amd64.Kernel.SiteNext.total`.
-/

namespace Janus.Amd64.Kernel.Sat

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Amd64.Kernel

/-- `RET` at `0x1000`. -/
def retProg64 : Amd64.Program := { segments := [⟨"ret", 0x1000, [0xc3]⟩], stubs := [], exitAddr := 0 }

theorem sched_witness64 (rt : List (Nat × Nat)) (stack : Nat) :
    Amd64.Kernel.SchedContract retProg64 0x1000 rt stack := by
  intro s hpc ⟨h1, h2, h3, h4, h5⟩
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
    Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 16) 8 (s.regs 0).toNat, s.zmmHi, s.kreg, ?_, ?_, ?_⟩
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

/-- A call state at `0x1000`: `RSP = 0x200000` with the return address `0x2000` at `[RSP]`,
4 KiB of writable stack below and 64 bytes above. -/
def wstate : State :=
  { regs := fun i => if i = 4 then 0x200000#64 else 0, rip := 0x1000#64,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨fun a => if a = 0x200001 then 0x20 else 0, [⟨0x200000 - 4096, 4096 + 64, true⟩]⟩ }

theorem callOK_w (n : Nat) (hn : n ≤ 7) : CallOK64 wstate 4096 n := by
  have hw : wstate.mem.accessible (0x200000 - 4096) (4096 + 64) true = true := by decide
  refine ⟨by decide, by decide, by decide, by simp [wstate]; omega, ?_⟩
  exact Arm64.Memory.accessible_mono _ hw (by simp [wstate]) (by simp [wstate]; omega)

theorem sched_satisfiable : ∃ (p : Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Amd64.Kernel.SchedContract p addr rt stack ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 addr ∧ CallOK64 s stack 0 :=
  ⟨retProg64, 0x1000, [], 4096, sched_witness64 [] 4096, wstate, rfl, callOK_w 0 (by omega)⟩

theorem convT64_satisfiable : ∃ (p : Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat),
    Amd64.Kernel.ConvT64Contract p addr rt stack ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 addr ∧ CallOK64 s stack 1 :=
  ⟨boxProg64, 0x1000, [], 4096, convT64_witness64 [] 4096 (by omega), wstate, rfl, callOK_w 1 (by omega)⟩

end Janus.Amd64.Kernel.Sat
