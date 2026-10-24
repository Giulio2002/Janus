import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/basic.ClearMap" 7)
    (segWord Extracted.program "example.com/basic.ClearMap" 8) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hclr : Contracts.Map.Clear (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapclear") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m]
      (fun s => CallerOK M s 32 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun s s' => IsMap M s'.mem m.toNat AMap.empty ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapclear"]
  refine Reaches.call (Summary.withExit (hclr f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 32))
      (hi := s.sp.toNat + 0) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hmap'⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hmap' henv'
    exact ⟨hmap', henv'⟩

end Proof
