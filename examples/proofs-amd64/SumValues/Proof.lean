import Janus
import Extracted

/-!
# `SumValues(m)` returns the sum of the values, for every iteration order (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns, and for **every** listing `ks` of the keys of `f` (each key once, in any order) the result is the sum of the values over `ks` modulo `2^64`. The iterator contracts promise only that keys come in *some* order, so the proof covers every order Go's randomised iteration may pick; the loop is proved by induction on the keys still to come.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.MapAmd64` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted RIP-relative `LEA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x38)

set_option maxHeartbeats 0 in
theorem loop (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hnext : IterNext (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterNext") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State) (hc : CallerOK M s 144 8)
    (hrs : s.mem.readLE (s.regs 4).toNat 8 = ret) (hx : s.xmm 15 = 0) :
    ∀ (ks done : List (BitVec 64)) (S : State) (acc : BitVec 64) (Mi : Memory),
      Keys f (done ++ ks) →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x6a) → S.regs 4 = s.regs 4 - BitVec.ofNat 64 136 →
      S.regs 0 = acc → acc.toNat = sumValues f done % 2 ^ 64 →
      S.regs 14 = s.regs 14 → S.regs 5 = s.regs 4 - BitVec.ofNat 64 8 → S.mem = Mi →
      S.xmm 15 = 0 → S.df = false →
      MemFrame (s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) Mi
        (M.priv ++ [((s.regs 4).toNat - 144 - M.depth, (s.regs 4).toNat - 8)]) →
      M.Env Mi (s.regs 14) → IsMap M Mi m.toNat f →
      M.Iter Mi ((s.regs 4).toNat - 104) m.toNat f ks → View64 M Mi ((s.regs 4).toNat - 104) f ks →
      Reaches ((Extracted.program.link impl).withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        ∀ ks, Keys f ks → (s'.regs 0).toNat = sumValues f ks % 2 ^ 64) := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have h144 : 144 ≤ (s.regs 4).toNat := by omega
  have hsp136 : (s.regs 4 - BitVec.ofNat 64 136).toNat = (s.regs 4).toNat - 136 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hsp144 : (s.regs 4 - BitVec.ofNat 64 144).toNat = (s.regs 4).toNat - 144 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hsp104 : (s.regs 4 - BitVec.ofNat 64 104).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp; omega
  intro ks
  induction ks with
  | nil =>
    intro done S acc Mi hk hpc hsp h0 hacc h14 h5 hm hx' hdf hfr henv' hmap' hit hv
    simp only [View64, IterView] at hv
    janus64_run
    intro ks hks
    rw [hacc, sumValues_keys (by simpa using hk) hks]
  | cons k ks ih =>
    intro done S acc Mi hk hpc hsp h0 hacc h14 h5 hm hx' hdf hfr henv' hmap' hit hv
    obtain ⟨hkp, hka, hki, hkv, hea, hei, hev⟩ := hv
    rw [show (s.regs 4).toNat - 104 + 8 = (s.regs 4).toNat - 96 by omega] at hea hei hev
    have hed := Janus.InRanges.disjoint hei hout
    have hea0 : s.mem.accessible (Mi.readLE ((s.regs 4).toNat - 96) 8) 8 false = true := by
      rw [hfr.accessible] at hea; simpa using hea
    janus64_run until [Extracted.program.contractAddr "runtime.mapIterNext"]
    have ho112 : Outside ((s.regs 4).toNat - 112) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    have ho144 : Outside ((s.regs 4).toNat - 144) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    refine Reaches.call (Summary.withExit (hnext m.toNat f k ks) hret) rfl
      ⟨RTPre.of_parts hc
        (by rw [hl.env_writeLE _ _ ho144, hl.env_writeLE _ _ ho112]; exact henv')
        (fun a n w => by simp only [Arm64.Memory.accessible_writeLE, hfr.accessible])
        (by
          rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hfr.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              exact ⟨hgo, by omega⟩)]
          repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
        (by simp [setRegF, hsp144]) (by simp [setRegF, h14]) (by simpa using hx') (by simpa using hdf)
        (by simp [setRegF, keepABI, hsp104, hsp136, hsp144, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide),
       by rw [hl.isMap_writeLE _ _ _ ho144, hl.isMap_writeLE _ _ _ ho112]; exact hmap',
       by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104]
          rw [hl.iter_writeLE _ _ _ _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true, iterSize]; exact ⟨ho144, by omega⟩),
            hl.iter_writeLE _ _ _ _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true, iterSize]; exact ⟨ho112, by omega⟩)]
          exact hit,
       by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
          exact Outside.of_sub hout (by omega) (by omega)⟩ ?_
    intro s' hpc' ⟨r, x, y, fl, m'', _, _, hs', hfr2, henv2, hoth, hmap2, hit2, hv2⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.cons_append, List.nil_append, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp144, hsp104] at hfr2
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104] at hit2 hv2 henv2
    janus64_run until [Extracted.entry + 0x6a]
    have hmem : ((s.regs 4).toNat - 144 - M.depth, (s.regs 4).toNat - 8) ∈
        M.priv ++ [((s.regs 4).toNat - 144 - M.depth, (s.regs 4).toNat - 8)] :=
      List.mem_append.2 (Or.inr (List.mem_singleton_self _))
    refine ih (done ++ [k]) _ _ m''
      (by simp only [List.append_assoc, List.singleton_append]; exact hk) rfl
      (by simp only [setRegF, keepABI, reduceIte, Nat.reduceEqDiff, hsp]
          exact Janus.Tactic.bv_sub_add_le _ rfl) rfl ?_ (by simp [setRegF, keepABI, h14])
      (by simp [setRegF, keepABI, h5]) rfl (by simp [keepX15, hx']) (by simpa using hdf) ?_
      (by simpa [h14] using henv2) hmap2 hit2 hv2
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
      rw [BitVec.toNat_ofNat, Nat.mod_mod, sumValues_append, hacc]
      simp only [sumValues_cons, sumValues_nil]
      have h0' : (f k).getD 0#64 = (f k).getD 0 := rfl
      rw [h0']
      omega
    · refine MemFrame.trans (((hfr.writeLE _ hmem (by omega) (by omega)).writeLE _ hmem
        (by omega) (by omega))) hfr2 ?_
      intro a n h
      simp only [outside_append, outside_cons, outside_nil, and_true, iterSize] at h ⊢
      obtain ⟨hp, h1⟩ := h
      exact ⟨⟨hp, h1⟩, ⟨hp, by omega, by omega⟩, by omega⟩

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (hstart : IterStart (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterStart") M)
    (hnext : IterNext (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapIterNext") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m]
      (fun s => CallerOK M s 144 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => ∀ ks, Keys f ks → (s'.regs 0).toNat = sumValues f ks % 2 ^ 64) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp144 : (s.regs 4 - 144#64).toNat = (s.regs 4).toNat - 144 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hsp104 : (s.regs 4 - 104#64).toNat = (s.regs 4).toNat - 104 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapIterStart"]
  refine Reaches.call (Summary.withExit (hstart f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp144]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by simp [setRegF, keepABI, hsp104, hsp144, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide),
     by simpa [setRegF] using hty, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 144))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, Arm64.Memory.accessible_writeLE]
    exact Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
    exact Outside.of_sub hout (by omega) (by omega)
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hmap', ks, hks, hit, hv⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.cons_append, List.nil_append, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp144, hsp104] at hfr hit hv henv' hmap'
    janus64_run until [Extracted.entry + 0x6a]
    have hb144 : s.regs 4 - 144#64 + 8#64 = s.regs 4 - 136#64 := Janus.Tactic.bv_sub_add_le _ rfl
    refine loop impl M hl hnext m f ret hret s hc h_ret (by simpa using hs.zero) ks [] _ 0#64 m'
      (by simpa using hks) rfl (by simp [setRegF, keepABI, hb144]) (by simp [setRegF, keepABI])
      (by simp [sumValues_nil]) (by simp [setRegF, keepABI]) (by simp [setRegF, keepABI]) rfl
      (by simp [keepX15, hs.zero]) (by simpa using hs.df) ?_ (by simpa using henv') hmap' hit hv
    refine MemFrame.trans (rs := M.priv ++ [((s.regs 4).toNat - 144 - M.depth, (s.regs 4).toNat - 8)])
      (by janus_frame) hfr ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true, iterSize] at h ⊢
    obtain ⟨hp, h1⟩ := h
    exact ⟨⟨hp, h1⟩, ⟨hp, by omega, by omega⟩, by omega⟩

end Proof
