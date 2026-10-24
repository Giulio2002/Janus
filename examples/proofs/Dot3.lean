import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float
namespace Proof
theorem correctness (a0 a1 a2 b0 b1 b2 : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = a0.toNat ∧ s.getV 1 64 = a1.toNat ∧ s.getV 2 64 = a2.toNat ∧
        s.getV 3 64 = b0.toNat ∧ s.getV 4 64 = b1.toNat ∧ s.getV 5 64 = b2.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64
        ((mul binary64 .rne a0.toNat b0.toNat).bind fun t =>
          (fma binary64 .rne a1.toNat b1.toNat t).bind fun u => fma binary64 .rne a2.toNat b2.toNat u)
        (s'.getV 0 64)) := by
  intro ret hret s hs ⟨h0, h1, h2, h3, h4, h5, hf⟩
  janus_intro hs
  simp only [State.getV] at h0 h1 h2 h3 h4 h5
  janus_run [h0, h1, h2, h3, h4, h5, hf]
  trace_state
  sorry
end Proof
