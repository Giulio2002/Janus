import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts.Misc

namespace Proof

/-- `runtime.complex128div`. -/
abbrev cdivAddr : Nat := segAddr Extracted.program "runtime.complex128div"

/-- `runtime.inf`: the word `ADRP`+`LDR` at `complex128div+0x90` read. -/
def infAddr : Nat :=
  adrpLdTarget (cdivAddr + 0x90) (segWord Extracted.program "runtime.complex128div" 36)
    (segWord Extracted.program "runtime.complex128div" 37) 3

set_option maxHeartbeats 0 in
theorem correctness (a b c d : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 56) 56 ∧
        s.fpcr = 0 ∧ s.getV 0 64 = a.toNat ∧ s.getV 1 64 = b.toNat ∧ s.getV 2 64 = c.toNat ∧
        s.getV 3 64 = d.toNat ∧ RuntimeInf s.mem infAddr ∧ Disjoint infAddr 8 (s.sp.toNat - 56) 56)
      (fun _ s' => ResultIs binary64 (cdiv true a.toNat b.toNat c.toNat d.toNat).1 (s'.getV 0 64) ∧
        ResultIs binary64 (cdiv true a.toNat b.toNat c.toNat d.toNat).2 (s'.getV 1 64)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd, hf, h0, h1, h2, h3, ⟨hi1, hi2, hi3⟩, hid⟩
  janus_intro hs
  simp only [Disjoint, State.getV] at hgd hid h0 h1 h2 h3
  janus_eval_nat hI : infAddr
  rw [hI] at hi1 hi2 hi3 hid
  janus_run (budget := 20000000) [h0, h1, h2, h3, hf]
  all_goals done

end Proof
