import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Lookup" 8)
    (segWord Extracted.program "example.com/basic.Lookup" 9) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_fast64") M)
    (m k : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k]
      (fun s => CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => s'.regs 0 = (f k).getD 0 ∧ (s'.regs 1).toNat % 256 = (f k).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess2_fast64"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
     by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48)) (hi := s.sp.toNat + 0)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hs3 hok
    exact ⟨by rw [hs3]; simp, hok⟩

end Proof
