import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Kernel Janus.Amd64.Kernel

namespace Proof

theorem correctness (E : KEnv) :
    EnsuresK Extracted.program E Extracted.entry []
      (fun s _ => StackGuardOK s 0 ∧ StackWritable s 64 8 ∧ TlsG s ∧
        (s.fsBase.toNat ≤ (s.regs regSP).toNat - 64 ∨ (s.regs regSP).toNat + 16 ≤ s.fsBase.toNat))
      (fun _ k s' k' => k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩, ⟨htb, htr, htg⟩, htd⟩
  apply Janus.Amd64.Kernel.ReturnsK.of_reaches
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw htg htd
  janus64_run
  refine ⟨.syscall, by rw [Amd64.Kernel.siteOf_withExit]; decide,
    Or.inl ⟨⟨.getpid, ?_, by decide, trivial⟩, ?_⟩⟩
  · simp [sysOf, Sys.ofAmd64, setRegF]
  rintro s' k' ⟨sc, m', r, r11, hsc, heff, rfl⟩
  simp [sysOf, Sys.ofAmd64, setRegF] at hsc
  subst hsc
  obtain ⟨rfl, rfl, rfl⟩ := heff
  apply Janus.Amd64.Kernel.ReturnsK.of_reaches
  janus64_run
  exact ⟨rfl, BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])⟩

end Proof
