import Extracted
/-! B1 after fix F3 (verify against audit/work/Add256): the claim of the attack is now
**refuted**. With `x = nil` and no memory, the first instruction `LDR X3, [X1]` faults
(`outsideAllocation 0 8`), which `NeverPanics` counts (a nil dereference is a Go panic on real
hardware). Stated for every admissible return address, as specifications now are. -/
open Janus Janus.Arm64 Janus.GoABI

namespace Proof
theorem correctness : ¬ ∀ (ret : Nat), RetAddr Extracted.program ret →
    ∀ (z y : BitVec 64) (s : State),
      CallSetup (Extracted.program.withExit ret) Extracted.entry [z, 0, y] s →
      s.mem.regions = [] → NeverPanics (Extracted.program.withExit ret) s := by
  intro h
  have hret : RetAddr Extracted.program 0x1000 := RetAddr.of_check (by decide)
  let s := setup (Extracted.program.withExit 0x1000) Extracted.entry [0, 0, 0] default
  have hs : CallSetup (Extracted.program.withExit 0x1000) Extracted.entry [0, 0, 0] s :=
    setup_callSetup _ (by decide)
  have hm : s.mem.regions = [] := rfl
  clear_value s
  have hn := h 0x1000 hret 0 0 s hs hm
  have hpc : s.pc.toNat = Extracted.entry := hs.pc_toNat (by decide)
  have hx1 : s.regs 1 = 0 := hs.reg (i := 1) (by simp)
  have hst : Arm64.step 0xf9400023 s = .error (.outsideAllocation 0 8) := by
    rw [Arm64.step_of_decode (i := .ldstUImm 3 1 0 1 3) (by decide)]
    simp [Arm64.exec, Arm64.memIndexed, Arm64.baseAddr, Arm64.memSingle, Arm64.load,
      Memory.accessible, hx1, hm]
  have hrun : (Extracted.program.withExit 0x1000).run 1 s = .error (.outsideAllocation 0 8) :=
    Program.run_succ_fault (by rw [hpc]; decide) (by rw [hpc]; decide) (by rw [hpc]; decide) hst
  exact nomatch (hn 1).2 _ hrun
end Proof
