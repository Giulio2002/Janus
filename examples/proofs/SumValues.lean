import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x3c) (segWord Extracted.program "example.com/basic.SumValues" 15)
    (segWord Extracted.program "example.com/basic.SumValues" 16) 0

/-- The caller's memory after the prologue: the saved `X30` and `X29`. -/
abbrev M0 (s : State) (ret : Nat) : Memory :=
  (s.mem.writeLE (s.sp.toNat - 160) 8 ret).writeLE (s.sp.toNat - 168) 8 (s.regs 29).toNat

/-- What may differ from `M0` during the loop: the private memory, the runtime's stack below
the frame, and the frame's spill slots and iterator struct. -/
abbrev rs (M : MapModel (BitVec 64) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  M.priv ++ [(s.sp.toNat - 160 - M.depth, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 8)]

set_option maxHeartbeats 0 in
theorem loop (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hnext : IterNext (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterNext") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State) (hc : CallerOK M s 160 0)
    (hret' : ret % 4 = 0 ∧ ret < 2 ^ 48) :
    ∀ (ks done : List (BitVec 64)) (S : State) (acc : BitVec 64) (Mi : Memory),
      Keys f (done ++ ks) →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x74) → S.sp = s.sp - BitVec.ofNat 64 160 → S.regs 0 = acc →
      acc.toNat = sumValues f done % 2 ^ 64 →
      S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = Mi →
      MemFrame ((s.mem.writeLE (s.sp.toNat - 160) 8 ret).writeLE (s.sp.toNat - 168) 8 (s.regs 29).toNat) Mi
        (M.priv ++ [(s.sp.toNat - 160 - M.depth, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 8)]) → M.Env Mi (s.regs 28) → IsMap M Mi m.toNat f →
      M.Iter Mi (s.sp.toNat - 104) m.toNat f ks → View64 M Mi (s.sp.toNat - 104) f ks →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ∀ ks, Keys f ks → (s'.regs 0).toNat = sumValues f ks % 2 ^ 64) := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd hgo
  have hal' : (s.sp.toNat - 160) % 16 = 0 := by omega
  have h160 : 168 ≤ s.sp.toNat := by omega
  intro ks
  induction ks with
  | nil =>
    intro done S acc Mi hk hpc hsp h0 hacc h28 h18 hm hfr henv' hmap' hit hv
    simp only [View64, IterView] at hv
    have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
    janus_run
    intro ks hks
    rw [hacc, sumValues_keys (by simpa using hk) hks]
  | cons k ks ih =>
    intro done S acc Mi hk hpc hsp h0 hacc h28 h18 hm hfr henv' hmap' hit hv
    have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
    obtain ⟨hkp, hka, hki, hkv, hea, hei, hev⟩ := hv
    rw [show s.sp.toNat - 104 + 8 = s.sp.toNat - 96 by omega] at hea hei hev
    -- the element pointer is in the private memory, so outside the stack window
    have hed := InRanges.disjoint hei hout
    have hea0 : s.mem.accessible (Mi.readLE (s.sp.toNat - 96) 8) 8 false = true := by
      rw [hfr.accessible] at hea; simpa using hea
    janus_run until [Extracted.program.contractAddr "runtime.mapIterNext"]
    have ho112 : Outside (s.sp.toNat - 112) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    have ho120 : Outside (s.sp.toNat - 120) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    have hsp160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hsp104 : (s.sp - 104#64).toNat = s.sp.toNat - 104 := by
      rw [BitVec.toNat_sub]; simp; omega
    refine Reaches.call (Summary.withExit (hnext m.toNat f k ks) hret) rfl
      ⟨RTPre.of_parts hc
        (by rw [hl.env_writeLE _ _ ho120, hl.env_writeLE _ _ ho112]; exact henv')
        (fun a n w => by simp only [Memory.accessible_writeLE, hfr.accessible])
        (by
          rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Memory.readLE_writeLE_of_disjoint _ _ (by omega), hfr.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              exact ⟨hgo, by omega, by omega⟩)]
          repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
        hsp160 (by simp [setReg, h28]) (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
       by rw [hl.isMap_writeLE _ _ _ ho120, hl.isMap_writeLE _ _ _ ho112]; exact hmap',
       by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104]
          rw [hl.iter_writeLE _ _ _ _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true, iterSize]; exact ⟨ho120, by omega⟩),
            hl.iter_writeLE _ _ _ _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true, iterSize]; exact ⟨ho112, by omega⟩)]
          exact hit,
       by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
          exact Outside.of_sub hout (by omega) (by omega)⟩ ?_
    intro s' hpc' ⟨r, vr, fl, m'', hs', hfr2, henv2, hoth, hmap2, hit2, hv2⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.cons_append, List.nil_append, hsp160, setReg_apply,
      reduceIte, Nat.reduceEqDiff, hsp104] at hfr2
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104] at hit2 hv2
    have hval : Mi.readLE (Mi.readLE (s.sp.toNat - 96) 8) 8 = ((f k).getD 0).toNat := by
      rw [← hev]
    have hr1 : m''.readLE (s.sp.toNat - 112) 8 = acc.toNat := by
      rw [hfr2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, and_assoc]
        refine ⟨ho112, ?_, ?_, ?_⟩ <;> omega)]
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt acc.isLt
    have hr2 : m''.readLE (s.sp.toNat - 120) 8 = ((f k).getD 0).toNat := by
      rw [hfr2.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true, and_assoc]
        refine ⟨ho120, ?_, ?_, ?_⟩ <;> omega)]
      rw [Memory.readLE_writeLE_self, hval]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    janus_run until [Extracted.entry + 0x74]
    simp only [setReg_apply, keepABI_apply, reduceIte, Nat.reduceEqDiff] at henv2
    refine ih (done ++ [k]) _ _ m''
      (by simp only [List.append_assoc, List.singleton_append]; exact hk) rfl rfl rfl ?_ (by simp [setReg, keepABI, h28])
      (by simp [setReg, keepABI, h18]) rfl ?_ (by simpa [h28] using henv2) hmap2 hit2 hv2
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hval, sumValues_append, hacc]
      simp only [sumValues_cons, sumValues_nil]
      have := ((f k).getD 0).isLt
      omega
    · have hmem : (s.sp.toNat - 152, s.sp.toNat - 8) ∈
          M.priv ++ [(s.sp.toNat - 160 - M.depth, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 8)] :=
        List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      refine MemFrame.trans (((hfr.writeLE _ hmem (by omega) (by omega)).writeLE _ hmem
        (by omega) (by omega))) hfr2 ?_
      intro a n h
      simp only [outside_append, outside_cons, outside_nil, and_true, iterSize] at h ⊢
      obtain ⟨hp, h1, h2⟩ := h
      exact ⟨⟨hp, h1, h2⟩, ⟨hp, by omega, by omega⟩, by omega⟩

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hstart : IterStart (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterStart") M)
    (hnext : IterNext (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterNext") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m]
      (fun s => CallerOK M s 160 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => ∀ ks, Keys f ks → (s'.regs 0).toNat = sumValues f ks % 2 ^ 64) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd hgo
  have hal' : (s.sp.toNat - 160) % 16 = 0 := by omega
  have hsp160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by rw [BitVec.toNat_sub]; simp; omega
  have hsp104 : (s.sp - 104#64).toNat = s.sp.toNat - 104 := by rw [BitVec.toNat_sub]; simp; omega
  janus_run until [Extracted.program.contractAddr "runtime.mapIterStart"]
  refine Reaches.call (Summary.withExit (hstart f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 160))
      (hi := s.sp.toNat + 0) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
    exact Outside.of_sub hout (by omega) (by omega)
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hmap', ks, hks, hit, hv⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.cons_append, List.nil_append, hsp160, setReg_apply,
      reduceIte, Nat.reduceEqDiff, hsp104] at hfr hit hv henv' hmap'
    janus_run until [Extracted.entry + 0x74]
    refine loop impl M hl hnext m f ret hret s hc ⟨hret.aligned, hret.user⟩ ks [] _ 0#64 m' (by simpa using hks)
      rfl rfl (by simp [setReg]) (by simp [sumValues_nil]) (by simp [setReg, keepABI])
      (by simp [setReg, keepABI]) rfl ?_ (by simpa using henv') hmap' hit hv
    have hmem : (s.sp.toNat - 152, s.sp.toNat - 8) ∈
        M.priv ++ [(s.sp.toNat - 160 - M.depth, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 8)] :=
      List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    refine MemFrame.trans (rs := M.priv ++ [(s.sp.toNat - 160 - M.depth, s.sp.toNat - 168),
      (s.sp.toNat - 152, s.sp.toNat - 8)]) (by janus_frame) hfr ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true, iterSize] at h ⊢
    obtain ⟨hp, h1, h2⟩ := h
    exact ⟨⟨hp, h1, h2⟩, ⟨hp, by omega, by omega⟩, by omega⟩

end Proof
