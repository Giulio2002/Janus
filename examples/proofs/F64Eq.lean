import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts.Mem

namespace Proof

theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.getV 1 64 = y.toNat ∧ s.fpcr = 0)
      (fun _ s' => (s'.regs 0).toNat % 256 = (feq binary64 x.toNat y.toNat).toNat) := by
  intro ret hret s hs ⟨hx, hy, hf⟩
  janus_intro hs
  simp only [State.getV] at hx hy
  janus_run [hx, hy, hf]
  cases feq binary64 x.toNat y.toNat <;> rfl

end Proof
