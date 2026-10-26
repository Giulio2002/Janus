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
          exact Outside.of_sub hout (by omega) (by omega),
       by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, calleeStack, hsp144,
            outside_cons, outside_nil, and_true]
          omega,
       by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, retSlot, hsp144,
            outside_cons, outside_nil, and_true]
          omega⟩ ?_
    intro s' hpc' ⟨r, x, y, fl, m'', hs', hfr2, henv2, hoth, hmap2, hit2, hv2⟩
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
     by simpa [setRegF] using hty, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 144))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, Arm64.Memory.accessible_writeLE]
    exact Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
    exact Outside.of_sub hout (by omega) (by omega)
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, calleeStack, hsp144,
      outside_cons, outside_nil, and_true]
    omega
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, retSlot, hsp144,
      outside_cons, outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ks, hks, hit, hv⟩
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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapSatAmd64.MEi`, code meeting `IterStart` (`MapSatAmd64.iterStartCode`
at `A0`) and `IterNext` (`MapSatAmd64.iterNextCode` at `A0 + 18`) for it, each behind a `JMP`
at its contract's address, and a call `SumValues(MP)`: the sum is `0`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64

/-- Both implementations: `IterStart` at `A0`, `IterNext` at `A0 + 18`. -/
def iterCode : List Nat := iterStartCode ++ iterNextCode

theorem start_impl : IterStart (toy.link (at0 iterCode)) A0 (MEi (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, hit, hpo, hco⟩ := hpre
  have hf := MEi_empty hmap
  subst hf
  have hit' := hit
  simp only [iterSize] at hit'
  have hp8 : Outside (s.regs 1).toNat 8 priv0 := Outside.of_sub hpo (by omega) (by simp [iterSize])
  have hag := Janus.Spec.Map.agrees_writeLE s.mem 0 hp8
  janus64_run
  have hfr : MemFrame s.mem (Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 1)) 8 0)
      (rtWrites (MEi (BitVec 64)) s 3 ++ [((s.regs 1).toNat, (s.regs 1).toNat + iterSize)]) := by
    simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, iterSize]
    simp only [MEi, ME_priv, ME_depth, priv0, List.cons_append, List.nil_append]
    janus_frame
  refine Janus.Contracts.MapStr.mapReturn64_of (MEi _) 3 _ _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((MEi_laws _).env_frame _ _ _ hze hag)
    (fun _ _ _ h => (MEi_laws _).rep_frame _ _ _ _ h hag)
    ⟨IsMap.frame (MEi_laws _) hmap hag, [], keys_empty,
      ⟨by decide, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  show Janus.Arm64.Memory.readLE _ _ 8 = 0
  rw [Janus.Arm64.Memory.readLE_writeLE_self]

theorem next_impl : IterNext (toy.link (at0 iterCode)) (A0 + 18) (MEi (BitVec 64)) := by
  rw [link_at0]
  intro mp f k ks s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hmap, ⟨hlen, hit⟩, hpo, hco⟩ := hpre
  have hks : ks = [] := by
    cases ks with
    | nil => rfl
    | cons _ _ => simp at hlen
  subst hks
  have hit' := hit
  simp only [iterSize] at hit'
  have hp8 : Outside (s.regs 0).toNat 8 priv0 := Outside.of_sub hpo (by omega) (by simp [iterSize])
  have hag := Janus.Spec.Map.agrees_writeLE s.mem 0 hp8
  janus64_run
  have hfr : MemFrame s.mem (Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 0)) 8 0)
      (rtWrites (MEi (BitVec 64)) s 1 ++ [((s.regs 0).toNat, (s.regs 0).toNat + iterSize)]) := by
    simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, iterSize]
    simp only [MEi, ME_priv, ME_depth, priv0, List.cons_append, List.nil_append]
    janus_frame
  refine Janus.Contracts.MapStr.mapReturn64_of (MEi _) 1 _ _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((MEi_laws _).env_frame _ _ _ hze hag)
    (fun _ _ _ h => (MEi_laws _).rep_frame _ _ _ _ h hag)
    ⟨IsMap.frame (MEi_laws _) hmap hag,
      ⟨by decide, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  show Janus.Arm64.Memory.readLE _ _ 8 = 0
  rw [Janus.Arm64.Memory.readLE_writeLE_self]

def sAddr : Nat := Extracted.program.contractAddr "runtime.mapIterStart"
def nAddr : Nat := Extracted.program.contractAddr "runtime.mapIterNext"

def trampS : Janus.Amd64.Segment := { name := "trampS", base := sAddr, bytes := jmpBytes sAddr A0 }
def trampN : Janus.Amd64.Segment := { name := "trampN", base := nAddr, bytes := jmpBytes nAddr (A0 + 18) }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := iterCode }
def implAt : List Janus.Amd64.Segment := [trampS, trampN, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [trampS, trampN]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem codeIn : CodeIn64 (segProg64 model0) (Extracted.program.link implAt) := by
  rw [link_eq]; exact codeIn_link64 _ model0 (by decide)

theorem modelS : IterStart (Extracted.program.link implAt) sAddr (MEi (BitVec 64)) := by
  have hA : IterStart (Extracted.program.link implAt) A0 (MEi (BitVec 64)) :=
    fun f => Summary.of_codeIn64 codeIn (start_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : sAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem modelN : IterNext (Extracted.program.link implAt) nAddr (MEi (BitVec 64)) := by
  have hA : IterNext (Extracted.program.link implAt) (A0 + 18) (MEi (BitVec 64)) :=
    fun mp f k ks => Summary.of_codeIn64 codeIn (next_impl mp f k ks)
  intro mp f k ks s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : nAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0 + 18]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA mp f k ks _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def mv : BitVec 64 := BitVec.ofNat 64 MP

/-- The witness call state: `SumValues(MP)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0) with rfl; rfl, rfl⟩

theorem pre0 : CallerOK (MEi (BitVec 64)) s0 144 8 ∧ (MEi (BitVec 64)).Typ mapType ∧
    IsMap (MEi (BitVec 64)) s0.mem mv.toNat AMap.empty := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩
  · simp only [MEi, ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MEi, ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (ret : Nat) (s : State) (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
    M.Laws ∧ IterStart (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mapIterStart") M ∧
    IterNext (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mapIterNext") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m] s ∧ m.toNat ≠ 0 ∧
    (CallerOK M s 144 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f) :=
  ⟨implAt, MEi _, ret, s0, mv, AMap.empty, MEi_laws _, modelS, modelN, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the sum over the empty map is `0`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 := by
  refine (correctness implAt (MEi _) (MEi_laws _) modelS modelN mv AMap.empty ret hret s0 setup
    pre0).mono ?_
  intro s' h
  refine ⟨h.1, BitVec.eq_of_toNat_eq ?_⟩
  rw [h.2 [] keys_empty]; rfl

end Witness

end Proof
