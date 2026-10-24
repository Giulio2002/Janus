import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.Insert" 9)
    (segWord Extracted.program "example.com/basic.Insert" 10) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 48 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set k v) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_fast64"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, by simpa [setReg] using hm0, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48))
      (hi := s.sp.toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 32) (by omega) (by omega))
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hset
    exact ⟨(hset v).1, (hset v).2.1⟩

end Proof
