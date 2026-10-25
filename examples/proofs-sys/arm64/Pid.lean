import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Kernel

namespace Proof

theorem correctness (E : KEnv) :
    EnsuresK Extracted.program E Extracted.entry []
      (fun s _ => GuardOK s 0 ∧ StackOK s 72 0)
      (fun _ k s' k' => k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run
  refine ⟨.svc, by rw [siteOf_withExit]; decide, Or.inl ⟨⟨.getpid, ?_, by decide, trivial⟩, ?_⟩⟩
  · simp [svcSys, Sys.ofArm64, setReg]
  rintro s' k' ⟨sc, m', r, hsc, heff, rfl⟩
  simp [svcSys, Sys.ofArm64, setReg] at hsc
  subst hsc
  obtain ⟨rfl, rfl, rfl⟩ := heff
  apply ReturnsK.of_reaches
  janus_run
  exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])

end Proof
