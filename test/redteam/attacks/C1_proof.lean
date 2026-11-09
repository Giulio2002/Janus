import Extracted
/-! ATTACK C1 proof: with the poisoned search path, a "multiplication" spec of Add verifies and the
statement says exactly `Extracted.program`. -/
open Janus Janus.Arm64 Janus.GoABI
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun s => s.regs 0 = x * y)
      (fun _ s' => s'.regs 0 = x * y) := by
  intro s hs hpre
  refine ⟨1, s, ?_, ⟨rfl, rfl, rfl, rfl⟩, hpre⟩
  have hpc : s.pc.toNat = Extracted.entry := hs.pc_toNat (by decide)
  simp [Program.run, Extracted.program, Extracted.entry] at hpc ⊢
  simp [hpc]
end Proof
