import Extracted
/-! ATTACK B1 (blocked by fix F3: this proof must now FAIL; see B1_refuted.lean): `NeverPanics` was satisfied by a run that *faults*. For Add256 (artifact
audit/work/Add256) with `x = nil` the first instruction `LDR X3, [X1]` reads address 0. On real
hardware Go turns that SIGSEGV into `panic: runtime error: invalid memory address or nil pointer
dereference`; in the model it is the fault `outsideAllocation 0 8`, so `NeverPanics` is provable.
The printed claim "Add256(z, nil, y) never panics" is false of the Go program. -/
open Janus Janus.Arm64 Janus.GoABI

namespace Proof
theorem correctness (z y : BitVec 64) (s : State)
    (hs : CallSetup Extracted.program Extracted.entry [z, 0, y] s) (hm : s.mem.regions = []) :
    NeverPanics Extracted.program s := by
  intro fuel name s'
  have hpc : s.pc.toNat = 0x931a0 := hs.pc_toNat (by decide)
  have hx1 : s.regs 1 = 0 := hs.reg (i := 1) (by simp)
  cases fuel with
  | zero => simp
  | succ n =>
    have hst : Arm64.step 0xf9400023 s = .error (.outsideAllocation 0 8) := by
      rw [Arm64.step_of_decode (i := .ldstUImm 3 1 0 1 3) (by decide)]
      simp [Arm64.exec, Arm64.memIndexed, Arm64.baseAddr, Arm64.memSingle, Arm64.load,
        Memory.accessible, hm, hx1]
    rw [Program.run_succ_fault (by rw [hpc]; decide) (by rw [hpc]; decide)
      (by rw [hpc]; decide) hst]
    simp
end Proof
