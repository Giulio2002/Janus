import Extracted

/-!
# `SumValues(m)` returns the sum of the values, for every iteration order (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns, and for **every** listing `ks` of the keys of `f` (each key once, in any order) the result is the sum of the values over `ks` modulo `2^64`. The iterator contracts promise only that keys come in *some* order, so the proof covers every order Go's randomised iteration may pick; the loop is proved by induction on the keys still to come.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.Map` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted `ADRP`+`ADD` words.
-/

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
          exact Outside.of_sub hout (by omega) (by omega),
       by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, calleeStack,
            hsp160, outside_cons, outside_nil, and_true]
          omega⟩ ?_
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
      (by decide) (by decide), by simpa [setReg] using hty, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 160))
      (hi := s.sp.toNat + 0) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, Memory.accessible_writeLE]
    exact Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize]
    exact Outside.of_sub hout (by omega) (by omega)
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hsp104, iterSize, calleeStack, hsp160,
      outside_cons, outside_nil, and_true]
    omega
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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `MapSat.MEI` (one empty, non-nil map at `MP`; iterators with at most one key left and
a writable iterator struct), code meeting `IterStart` (`str xzr, [x2]; ret` at `A0`) and
`IterNext` (`str xzr, [x0]; ret` at `A0 + 8`) for it, each reached from its contract's address
by a branch, and a call `SumValues(MP)`: `correctness` applies (`returns`: the sum is `0`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat

/-- Both implementations: `IterStart` at `A0`, `IterNext` at `A0 + 8`. -/
def iterCode : List Nat := [0xf900005f, 0xd65f03c0, 0xf900001f, 0xd65f03c0]

/-- `IterStart` for `MEI` (the iteration over the empty map ends at once). -/
theorem start_impl : IterStart (toy.link (at0 iterCode)) A0 (MEI (BitVec 64)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap, hit, hip, hic⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME_empty (K := BitVec 64) hmap
  subst hf
  have hip8 : Outside (s.regs 2).toNat 8 (MEI (BitVec 64)).priv :=
    Outside.of_sub hip (by omega) (by simp [iterSize])
  have hw : s.mem.accessible (s.regs 2).toNat 8 true = true :=
    Memory.accessible_mono _ hit (Nat.le_refl _) (by simp [iterSize])
  janus_run
  have ha := agrees_writeLE s.mem 0 hip8
  refine mapReturn_of (MEI _) 3 _ _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
    (ZEnv.frame hze ha) (fun _ _ _ h => (MEI_laws _).rep_frame _ _ _ _ h ha)
    ⟨IsMap.frame (MEI_laws _) hmap ha, [], keys_empty,
      ⟨Nat.zero_le _, by rw [Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  · simp only [rtWrites, List.append_assoc]
    exact (MemFrame.refl _ _).writeLE_inRanges _
      ⟨((s.regs 2).toNat, (s.regs 2).toNat + iterSize), by simp, Nat.le_refl _, by simp [iterSize]⟩
  · show (s.mem.writeLE (s.regs 2).toNat 8 _).readLE (s.regs 2).toNat 8 = 0
    rw [Memory.readLE_writeLE_self]

/-- `IterNext` for `MEI` (one key left: the iteration ends). -/
theorem next_impl : IterNext (toy.link (at0 iterCode)) (A0 + 8) (MEI (BitVec 64)) := by
  rw [link_at0]
  intro mp f k ks s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, hmap, ⟨hlen, hit⟩, hip, hic⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hks : ks = [] := by cases ks <;> simp_all
  subst hks
  have hip8 : Outside (s.regs 0).toNat 8 (MEI (BitVec 64)).priv :=
    Outside.of_sub hip (by omega) (by simp [iterSize])
  have hw : s.mem.accessible (s.regs 0).toNat 8 true = true :=
    Memory.accessible_mono _ hit (Nat.le_refl _) (by simp [iterSize])
  janus_run
  have ha := agrees_writeLE s.mem 0 hip8
  refine mapReturn_of (MEI _) 1 _ _ s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
    (ZEnv.frame hze ha) (fun _ _ _ h => (MEI_laws _).rep_frame _ _ _ _ h ha)
    ⟨IsMap.frame (MEI_laws _) hmap ha, ⟨Nat.zero_le _, by rw [Memory.accessible_writeLE]; exact hit⟩, ?_⟩
  · simp only [rtWrites, List.append_assoc]
    exact (MemFrame.refl _ _).writeLE_inRanges _
      ⟨((s.regs 0).toNat, (s.regs 0).toNat + iterSize), by simp, Nat.le_refl _, by simp [iterSize]⟩
  · show (s.mem.writeLE (s.regs 0).toNat 8 _).readLE (s.regs 0).toNat 8 = 0
    rw [Memory.readLE_writeLE_self]

def sAddr : Nat := Extracted.program.contractAddr "runtime.mapIterStart"
def nAddr : Nat := Extracted.program.contractAddr "runtime.mapIterNext"

def trampS : Segment := { name := "trampS", base := sAddr, words := [branchWord sAddr A0] }
def trampN : Segment := { name := "trampN", base := nAddr, words := [branchWord nAddr (A0 + 8)] }
def model0 : Segment := { name := "model", base := A0, words := iterCode }
def implAt : List Segment := [trampS, trampN, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [trampS, trampN]).link [model0] := by
  simp [Program.link, implAt]

theorem codeIn : CodeIn (segProg model0) (Extracted.program.link implAt) := by
  rw [link_eq]; exact codeIn_link _ model0 (by decide)

theorem modelS : IterStart (Extracted.program.link implAt) sAddr (MEI (BitVec 64)) := by
  have hA : IterStart (Extracted.program.link implAt) A0 (MEI (BitVec 64)) :=
    fun f => Summary.of_codeIn codeIn (start_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : sAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem modelN : IterNext (Extracted.program.link implAt) nAddr (MEI (BitVec 64)) := by
  have hA : IterNext (Extracted.program.link implAt) (A0 + 8) (MEI (BitVec 64)) :=
    fun mp f k ks => Summary.of_codeIn codeIn (next_impl mp f k ks)
  intro mp f k ks s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : nAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0 + 8]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA mp f k ks _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def mv : BitVec 64 := BitVec.ofNat 64 MP

/-- The witness call state: `SumValues(MP)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0) with rfl; rfl⟩

theorem pre0 : CallerOK (MEI (BitVec 64)) s0 160 0 ∧ (MEI (BitVec 64)).Typ mapType ∧
    IsMap (MEI (BitVec 64)) s0.mem mv.toNat AMap.empty := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 (mmem_rep _)⟩
  · simp only [MEI_priv, MEI_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MEI_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (ret : Nat)
    (s : State) (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
    M.Laws ∧ IterStart (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mapIterStart") M ∧
    IterNext (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mapIterNext") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m] s ∧ m.toNat ≠ 0 ∧
    (CallerOK M s 160 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f) :=
  ⟨implAt, MEI _, ret, s0, mv, AMap.empty, MEI_laws _, modelS, modelN, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the sum over the empty map is `0`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 := by
  refine (correctness implAt (MEI _) (MEI_laws _) modelS modelN mv AMap.empty ret hret s0 setup
    pre0).mono ?_
  intro s' h
  refine ⟨h.1, BitVec.eq_of_toNat_eq ?_⟩
  rw [h.2 [] keys_empty]; rfl

end Witness

end Proof
