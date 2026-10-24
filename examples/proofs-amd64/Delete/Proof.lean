import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x14)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (hdel : Contracts.MapAmd64.Delete (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapdelete_fast64") M)
    (m k : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k]
      (fun s => CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun s s' => IsMap M s'.mem m.toNat (f.erase k) ∧ M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapdelete_fast64"]
  refine Reaches.call (Summary.withExit (hdel f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by decide) (by decide),
     by simpa [setRegF] using hty, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap'⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    janus64_run
    simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hmap' henv'
    exact ⟨hmap', henv'⟩

end Proof
