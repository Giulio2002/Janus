import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x16)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 128) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2") M)
    (m kp : BitVec 64) (f : AMap (BitVec 128) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp]
      (fun s => CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        Buffer s kp 16 false ∧
        Janus.Spec.Disjoint kp.toNat 16 ((s.regs 4).toNat - (M.depth + 40)) (M.depth + 40 + 8))
      (fun s s' =>
        let key := BitVec.ofNat 128 (s.mem.readLE kp.toNat 16)
        s'.regs 0 = (f key).getD 0 ∧ (s'.regs 3).toNat % 256 = (f key).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, ⟨hk1, hk2⟩, hkd⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout hkd
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess2"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by decide) (by decide), by simpa [setRegF] using hty, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, Arm64.Memory.accessible_writeLE]; exact hk2
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus64_run
    all_goals simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hs3 hok
    all_goals (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at hs3)
    all_goals (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at hok)
    all_goals first | exact hok | exact ⟨by rw [hs3]; simp, hok⟩

end Proof
