import Janus
import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x23)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M)
    (hacc : Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 40 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f)
      (fun _ s' => s'.regs 0 = v ∧ M.Rep s'.mem m.toNat (f.set k v)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign_fast64"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by decide) (by decide),
     by simpa [setRegF] using hty, by simpa [setRegF] using hm0, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 40))
      (n := M.depth + 40 + 32) (by omega) (by omega))
    have hdg := Janus.InRanges.disjoint hin hgo
    janus64_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast64"]
    have ho40 : Outside ((s.regs 4).toNat - 40) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    refine Reaches.call (Summary.withExit (hacc (f.set k v)) hret) rfl
      ⟨RTPre.of_parts hc (by rw [hl.env_writeLE _ _ ho40]; simpa [setRegF, keepABI] using (hset v).2.1)
        (fun a n w => by simp only [Arm64.Memory.accessible_writeLE, hfr.accessible])
        (by rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
              Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hfr.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              exact ⟨hgo, by omega, by omega⟩)]
            repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
        (by simp [setRegF, keepABI, hsp40]) (by simp [setRegF, keepABI]) (by simp [keepX15, hs.zero])
        (by simpa using hs.df) (by decide) (by decide),
       by simpa [setRegF] using hty, ?_⟩ ?_
    · simp only [setRegF, keepABI_apply]; simp only [reduceIte, Nat.reduceEqDiff]
      exact (isMap_of_ne hm0).2 (by rw [hl.rep_writeLE _ _ _ ho40]; exact (hset v).1)
    · intro s'' hpc'' ⟨r2, x2, y2, fl2, m'', hs'', hfr2, henv2, hoth2, hmap2, ⟨hs1, hs2, hs3⟩⟩
      subst hs''
      simp only [rtWrites, calleeStack, List.append_nil, setRegF, keepABI_apply, reduceIte,
        Nat.reduceEqDiff, hsp40] at hfr2
      have hacc1 : s.mem.accessible (r2 0).toNat 8 false = true := by
        rw [hfr2.accessible] at hs1; simpa [hfr.accessible] using hs1
      janus64_run
      all_goals simp only [setRegF, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hs3 hmap2
      exact ⟨by simp, (isMap_of_ne hm0).1 hmap2⟩

end Proof
