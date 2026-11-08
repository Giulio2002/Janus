import Extracted
open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Contracts Janus.Contracts.Map
theorem t1 {K V : Type} {M : MapModel K V} {n : Nat} {s : State} (a : BitVec 64) (h : RTPre M n s) :
    RTPre M n { s with pc := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c, o⟩
