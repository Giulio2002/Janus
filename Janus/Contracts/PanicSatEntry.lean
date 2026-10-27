import Janus.Contracts.PanicSatEngine

/-!
# The entry of the model engine: `gopanic`, `Goexit`, `deferreturn`

The entry code of the model engine writes the loop's frame and brings the machine to the loop
head `LH` in a state meeting the invariant `Inv0` of `PanicSatEngine`; with `engine_loop` this gives
the three contracts.
-/

set_option linter.constructorNameAsVariable false

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel Janus.Spec.Map

/-- The invariant at the first loop head, from what the entry code did. -/
theorem Inv0.init {T : List FuncInfo} {s c : State} {F : Frame} {mode : DeferMode} {x28 x18 : W64}
    {lr x29 : Nat} {ph : Nat} {ch : List PanicRec} {rm : Nat}
    (hfo : FrameOK (P0 T RPa) s.mem F (frameItems s.mem F (defers0 s.mem)))
    (hF1 : F.sp % 16 = 0) (hF2 : F.sp + 8 ≤ 2 ^ 48) (hF3 : 96 ≤ F.sp)
    (hspB : F.sp ≤ B ∨ B + 0x1000 + 96 ≤ F.sp)
    (hbd : F.bound < 2 ^ 64) (hres : F.resume % 4 = 0 ∧ F.resume < 2 ^ 48)
    (hlr : mode = .ret → lr % 4 = 0 ∧ lr < 2 ^ 48)
    (hcsp : c.sp.toNat + 96 = F.sp) (hc28 : c.regs 28 = x28)
    (hacc : s.mem.accessible (F.sp - 96) 96 true = true)
    (hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F))
    (hfm : FrameMem c.mem F mode ph x18.toNat lr x29)
    (henv : Env0 T c.mem) (hpan : panics0 c.mem = ch) (hroom : rm ≤ room0 c.mem)
    (hsv : mode = .ret → rd c.mem (B + 0x10) = 0) (hdef : defers0 c.mem = defers0 s.mem)
    (hba : ∀ ba sa, F.openAt = some (ba, sa) → c.mem.readLE ba 1 = s.mem.readLE ba 1)
    (hcur : curItems c.mem F ph = frameItems s.mem F (defers0 s.mem)) :
    Inv0 T s.mem F (frameItems s.mem F (defers0 s.mem)) (defers0 s.mem) mode x28 x18 lr x29 c ch rm ph := by
  have hcs : c.sp.toNat = F.sp - 96 := by omega
  have hac : c.mem.accessible c.sp.toNat 96 true = true := by rw [hmf.accessible, hcs]; exact hacc
  refine ⟨hcsp, hF1, hF2, hac, hc28, hspB, hfm, hlr, hbd, hres, henv, hpan, hroom, hsv,
    by rw [hdef], ?_, hfo, ?_, ?_⟩
  · exact (Agrees.of_memFrame hmf fun a ha => by
      obtain ⟨r, hr, h1, h2⟩ := ha
      obtain ⟨hr8, hro⟩ := keep_apart_fo hfo r hr
      exact Outside.of_sub hro h1 (by omega))
  · intro ba sa hF i hi
    rw [hba ba sa hF] at hi; exact hi
  · intro it hit; rw [hcur] at hit; exact hit

/-- A memory that agrees with `m` on the words other than `npan` and the saved state, and has
the same `npan`, has the same bookkeeping. -/
theorem bundle2 {T : List FuncInfo} {m m' : Memory} (henv : Env0 T m) (ha : Agrees m m' R2)
    (hnp : npan m' = npan m) :
    Env0 T m' ∧ defers0 m' = defers0 m ∧ panics0 m' = panics0 m ∧ room0 m' = room0 m := by
  have hnd := ndef_agree2 ha
  have hnp8 := henv.npan_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Env0.mk (by rw [ha.1]; exact henv.acc) (by omega) (by rw [hnd]; exact henv.ndef_le) (fun i hi => ?_)
      (tableOK_agree2 ha henv.table)
    rw [hnd] at hi
    obtain ⟨-, h2, h3, h4⟩ := recFields_agree2 ha (by have := henv.ndef_le; omega : i < 8)
    rw [h2, h3, h4]; exact henv.rec i hi
  · rw [defers0_eq, defers0_eq, hnd]; exact recList_agree2 ha _ (Nat.min_le_right _ _)
  · rw [panics0_eq, panics0_eq, hnp]; exact panList_agree2 ha _ (Nat.min_le_right _ _)
  · rw [room0_eq, room0_eq, hnd, hnp, capMin_agree2 ha _ (Nat.min_le_right _ _)]

theorem curItems_entry (m : Memory) (F : Frame) (ph : Nat) (h : ph = 0 → F.openAt = none) :
    curItems m F ph = frameItems m F (defers0 m) := by
  by_cases hph : ph = 0
  · subst hph
    rw [curItems_zero]
    simp [frameItems, h rfl]
  · exact curItems_ne hph

set_option maxHeartbeats 0 in
/-- The entry of `deferreturn`: the saved state is read and cleared, the loop's frame is written. -/
theorem seg_dr_entry (s : State) (hpc : s.pc = BitVec.ofNat 64 eDeferreturn)
    (hal : s.sp.toNat % 16 = 0) (hsp : s.sp.toNat + 8 ≤ 2 ^ 48) (h96 : 96 ≤ s.sp.toNat)
    (hacc : s.mem.accessible (s.sp.toNat - 96) 96 true = true) (hB : s.mem.accessible B 0x1000 true = true)
    (hspB : s.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s.sp.toNat) :
    ReachesRet qE (BitVec.ofNat 64 eLH) s (fun c => c.pc = BitVec.ofNat 64 eLH ∧ c.sp = BitVec.ofNat 64 (s.sp.toNat - 96) ∧
      c.regs 28 = s.regs 28 ∧ c.regs 18 = s.regs 18 ∧
      MemFrame s.mem c.mem [(B + 0x10, B + 0x18), (s.sp.toNat - 96, s.sp.toNat - 16)] ∧
      rd c.mem (B + 0x10) = 0 ∧
      c.mem.readLE (s.sp.toNat - 96) 8 = s.sp.toNat ∧ c.mem.readLE (s.sp.toNat - 96 + 8) 8 = s.sp.toNat ∧
      c.mem.readLE (s.sp.toNat - 96 + 16) 8 = 0 ∧ c.mem.readLE (s.sp.toNat - 96 + 24) 8 = 2 ∧
      c.mem.readLE (s.sp.toNat - 96 + 32) 8 = s.mem.readLE (B + 0x10) 8 ∧
      c.mem.readLE (s.sp.toNat - 96 + 40) 8 = s.mem.readLE (B + 0x18) 8 ∧
      c.mem.readLE (s.sp.toNat - 96 + 48) 8 = s.mem.readLE (B + 0x20) 8 ∧
      c.mem.readLE (s.sp.toNat - 96 + 56) 8 = (s.regs 18).toNat ∧
      c.mem.readLE (s.sp.toNat - 96 + 64) 8 = (s.regs 30).toNat ∧
      c.mem.readLE (s.sp.toNat - 96 + 72) 8 = (s.regs 29).toNat) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hacc' : s.mem.accessible (s.sp.toNat - 96) 96 true = true := hacc
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := s
  dsimp only at *
  simp only [eDeferreturn, eLH, E, B, Nat.reduceAdd] at hpc ⊢ hspB
  subst hpc
  janus_run
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · janus_frame


set_option maxHeartbeats 0 in
/-- The entry of `gopanic`: the `_panic` for `v` is pushed. -/
theorem seg_gp_push (s : State) (k : Nat) (hpc : s.pc = BitVec.ofNat 64 eGopanic)
    (hB : s.mem.accessible B 0x1000 true = true) (hk : npan s.mem = k) (hk8 : k < 8) :
    ReachesRet qE (BitVec.ofNat 64 eLookup) s (fun d => d.sp = s.sp ∧ d.regs 28 = s.regs 28 ∧ d.regs 18 = s.regs 18 ∧
      d.regs 30 = s.regs 30 ∧ d.regs 10 = 0 ∧ MemFrame s.mem d.mem [(B, B + 8), (panAt k, panAt k + 32)] ∧
      npan d.mem = k + 1 ∧ rd d.mem (panAt k) = (s.regs 0).toNat ∧ rd d.mem (panAt k + 8) = (s.regs 1).toNat ∧
      rd d.mem (panAt k + 16) = s.sp.toNat ∧ rd d.mem (panAt k + 24) = 0) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hk' : s.mem.readLE 65536 8 = k := hk
  have hmul : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq]; omega
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := s
  dsimp only at *
  simp only [eGopanic, eLookup, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [(show cm.readLE 65536 8 = k from hk'), hmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [panAt, B]; janus_frame
  all_goals
    simp only [rd, panAt, B]
    model_simp
    try (apply Nat.mod_eq_of_lt; have := BitVec.isLt (cr 0); have := BitVec.isLt (cr 1); have := BitVec.isLt csp; omega)


set_option maxHeartbeats 0 in
/-- The entry of `Goexit`: the `_panic` with `goexit` set is pushed. -/
theorem seg_ge_push (s : State) (k : Nat) (hpc : s.pc = BitVec.ofNat 64 eGoexit)
    (hB : s.mem.accessible B 0x1000 true = true) (hk : npan s.mem = k) (hk8 : k < 8) :
    ReachesRet qE (BitVec.ofNat 64 eLookup) s (fun d => d.sp = s.sp ∧ d.regs 28 = s.regs 28 ∧ d.regs 18 = s.regs 18 ∧
      d.regs 30 = s.regs 30 ∧ d.regs 10 = 1 ∧ MemFrame s.mem d.mem [(B, B + 8), (panAt k, panAt k + 32)] ∧
      npan d.mem = k + 1 ∧ rd d.mem (panAt k) = 0 ∧ rd d.mem (panAt k + 8) = 0 ∧
      rd d.mem (panAt k + 16) = s.sp.toNat ∧ rd d.mem (panAt k + 24) = 1) := by
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hk' : s.mem.readLE 65536 8 = k := hk
  have hmul : (BitVec.ofNat 64 k <<< 5).toNat = 32 * k := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    rw [Nat.shiftLeft_eq]; omega
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := s
  dsimp only at *
  simp only [eGoexit, eLookup, E, B, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [(show cm.readLE 65536 8 = k from hk'), hmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [panAt, B]; janus_frame
  all_goals
    simp only [rd, panAt, B]
    model_simp
    try (apply Nat.mod_eq_of_lt; have := BitVec.isLt csp; omega)


set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
/-- The test of the table search's loop head: a non-zero count goes on. -/
theorem seg_lk_cbz (c : State) (r : Nat) (hpc : c.pc = BitVec.ofNat 64 (E + 0x210))
    (h7 : c.regs 7 = BitVec.ofNat 64 (r + 1)) (hr : r + 1 < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x214)) c (fun d => d.mem = c.mem ∧ d.sp = c.sp ∧ d.regs = c.regs) := by
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  have hnz : (BitVec.ofNat 64 (r + 1) = 0) = False := by
    apply eq_false; intro h; have := congrArg BitVec.toNat h; simp [BitVec.toNat_ofNat] at this; omega
  janus_run [h7, hnz]

/-- One step of the model's table search, entry found. -/
theorem seg_lk_found (c : State) (ptr e sz ra : Nat) (hpc : c.pc = BitVec.ofNat 64 (E + 0x214))
    (h8 : c.regs 8 = BitVec.ofNat 64 ptr) (h30 : c.regs 30 = BitVec.ofNat 64 ra)
    (hp1 : ptr + 16 ≤ 2 ^ 48) (hacc : c.mem.accessible ptr 16 false = true)
    (he : c.mem.readLE ptr 8 = e) (hs : c.mem.readLE (ptr + 8) 8 = sz) (hovf : e + sz < 2 ^ 64)
    (hra : ra < 2 ^ 64) (h1 : e ≤ ra) (h2 : ra < e + sz) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x240)) c (fun d => d.mem = c.mem ∧ d.sp = c.sp ∧
      d.regs 8 = BitVec.ofNat 64 ptr ∧ d.regs 0 = BitVec.ofNat 64 e ∧ d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧
      d.regs 30 = c.regs 30 ∧ d.regs 10 = c.regs 10) := by
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run [he, hs, h8, h30, Nat.not_lt.2 h1, h2]

set_option maxHeartbeats 0 in
/-- One step of the model's table search, entry not matching: on to the next. -/
theorem seg_lk_next (c : State) (ptr e sz ra : Nat) (hpc : c.pc = BitVec.ofNat 64 (E + 0x214))
    (h8 : c.regs 8 = BitVec.ofNat 64 ptr) (h30 : c.regs 30 = BitVec.ofNat 64 ra)
    (hp1 : ptr + 16 ≤ 2 ^ 48) (hacc : c.mem.accessible ptr 16 false = true)
    (he : c.mem.readLE ptr 8 = e) (hs : c.mem.readLE (ptr + 8) 8 = sz) (hovf : e + sz < 2 ^ 64)
    (hra : ra < 2 ^ 64) (hn : ra < e ∨ e + sz ≤ ra) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x210)) c (fun d => d.mem = c.mem ∧ d.sp = c.sp ∧
      d.regs 7 = c.regs 7 - 1 ∧ d.regs 8 = c.regs 8 + 56 ∧ d.regs 28 = c.regs 28 ∧
      d.regs 18 = c.regs 18 ∧ d.regs 30 = c.regs 30 ∧ d.regs 10 = c.regs 10) := by
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  rcases hn with hn | hn
  · janus_run [he, hs, h8, h30, hn]
  · janus_run [he, hs, h8, h30, (show ¬ ra < e by omega), (show ¬ ra < e + sz by omega)]

theorem rr_bind {p : Program} {t1 t2 : W64} {s : State} {Q1 Q2 : State → Prop}
    (h : ReachesRet p t1 s Q1) (hk : ∀ s', s'.pc = t1 → Q1 s' → ReachesRet p t2 s' Q2) : ReachesRet p t2 s Q2 := by
  obtain ⟨k, s', hk1, hpc, hq⟩ := h
  obtain ⟨k', s'', hk2, hpc2, hq2⟩ := hk s' hpc hq
  exact ⟨k + k', s'', hk1.trans hk2, hpc2, hq2⟩

/-- The model's search of the function table for the function containing `ra`. -/
theorem seg_lookup (T : List FuncInfo) (ra : Nat) (hra : ra < 2 ^ 64) (hT : ∀ f ∈ T, f.entry + f.size < 2 ^ 64)
    (fi : FuncInfo) :
    ∀ (r i : Nat) (c : State), i + r = T.length → c.pc = BitVec.ofNat 64 (E + 0x210) →
      c.regs 7 = BitVec.ofNat 64 r → c.regs 8 = BitVec.ofNat 64 (tabAt i) → c.regs 30 = BitVec.ofNat 64 ra →
      TableOK c.mem T → c.mem.accessible B 0x1000 true = true →
      (T.drop i).find? (fun f => decide (f.entry ≤ ra ∧ ra < f.entry + f.size)) = some fi →
      ReachesRet qE (BitVec.ofNat 64 (E + 0x240)) c (fun d => d.mem = c.mem ∧ d.sp = c.sp ∧
        d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧ d.regs 30 = c.regs 30 ∧ d.regs 10 = c.regs 10 ∧
        ∃ j, j < T.length ∧ T[j]? = some fi ∧ d.regs 8 = BitVec.ofNat 64 (tabAt j) ∧ d.regs 0 = BitVec.ofNat 64 fi.entry)
  | 0, i, c, hlen, hpc, h7, h8, h30, htab, hB, hf => by
    have : T.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this] at hf; simp at hf
  | r + 1, i, c, hlen, hpc, h7, h8, h30, htab, hB, hf => by
    have hi : i < T.length := by omega
    obtain ⟨hl16, hnt, htE⟩ := htab
    have hb1 : (1 : BitVec 64).toNat = 1 := rfl
    have hb56 : (56 : BitVec 64).toNat = 56 := rfl
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := htE i hi
    have hdrop : T.drop i = T[i] :: T.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hTi := hT T[i] (List.getElem_mem hi)
    have hr64 : r + 1 < 2 ^ 64 := by omega
    have hptr : tabAt i + 16 ≤ 2 ^ 48 := by simp only [tabAt, B]; omega
    have hacc : c.mem.accessible (tabAt i) 16 false = true :=
      Memory.accessible_sub _ hB (Or.inl rfl) (by simp only [tabAt, B]; omega) (by simp only [tabAt, B]; omega)
    refine rr_bind (seg_lk_cbz c r hpc h7 hr64) fun c1 hpc1 hq1 => ?_
    obtain ⟨hm1, hsp1, hrg1⟩ := hq1
    have he' : c1.mem.readLE (tabAt i) 8 = T[i].entry := by rw [hm1]; exact e1
    have hs' : c1.mem.readLE (tabAt i + 8) 8 = T[i].size := by rw [hm1]; exact e2
    have h8' : c1.regs 8 = BitVec.ofNat 64 (tabAt i) := by rw [hrg1]; exact h8
    have h30' : c1.regs 30 = BitVec.ofNat 64 ra := by rw [hrg1]; exact h30
    have hacc' : c1.mem.accessible (tabAt i) 16 false = true := by rw [hm1]; exact hacc
    by_cases hpred : T[i].entry ≤ ra ∧ ra < T[i].entry + T[i].size
    · refine rr_bind (seg_lk_found c1 (tabAt i) T[i].entry T[i].size ra hpc1 h8' h30' hptr hacc' he' hs' hTi hra
        hpred.1 hpred.2) fun d hpcd hqd => ?_
      obtain ⟨hmd, hspd, h8d, h0d, h28d, h18d, h30d, h10d⟩ := hqd
      have hfi : T[i] = fi := by
        rw [hdrop] at hf
        simp only [List.find?_cons, decide_eq_true hpred, Option.some.injEq] at hf
        exact hf
      refine ReachesRet.done hpcd ⟨by rw [hmd, hm1], by rw [hspd, hsp1], ?_, ?_, ?_, ?_, i, hi, ?_, h8d, ?_⟩
      · rw [h28d, hrg1]
      · rw [h18d, hrg1]
      · rw [h30d, hrg1]
      · rw [h10d, hrg1]
      · rw [List.getElem?_eq_getElem hi, hfi]
      · rw [h0d, hfi]
    · have hpredf : decide (T[i].entry ≤ ra ∧ ra < T[i].entry + T[i].size) = false := decide_eq_false hpred
      refine rr_bind (seg_lk_next c1 (tabAt i) T[i].entry T[i].size ra hpc1 h8' h30' hptr hacc' he' hs' hTi hra
        (by omega)) fun c2 hpc2 hq2 => ?_
      obtain ⟨hm2, hsp2, h72, h82, h282, h182, h302, h102⟩ := hq2
      have hf' : (T.drop (i + 1)).find? (fun f => decide (f.entry ≤ ra ∧ ra < f.entry + f.size)) = some fi := by
        rw [hdrop] at hf
        simp only [List.find?_cons, hpredf] at hf
        exact hf
      have h7' : c2.regs 7 = BitVec.ofNat 64 r := by
        rw [h72, hrg1, h7]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have h8'' : c2.regs 8 = BitVec.ofNat 64 (tabAt (i + 1)) := by
        rw [h82, hrg1, h8]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, tabAt, B]; omega
      have ih := seg_lookup T ra hra hT fi r (i + 1) c2 (by omega) hpc2 h7' h8'' (by rw [h302, hrg1]; exact h30)
        (by rw [hm2, hm1]; exact ⟨hl16, hnt, htE⟩) (by rw [hm2, hm1]; exact hB) hf'
      refine reachesRet_mono ih fun d hd => ?_
      obtain ⟨hmd, hspd, h28d, h18d, h30d, h10d, j, hj, hTj, h8d, h0d⟩ := hd
      refine ⟨by rw [hmd, hm2, hm1], by rw [hspd, hsp2, hsp1], ?_, ?_, ?_, ?_, j, hj, hTj, h8d, h0d⟩
      · rw [h28d, h282, hrg1]
      · rw [h18d, h182, hrg1]
      · rw [h30d, h302, hrg1]
      · rw [h10d, h102, hrg1]


set_option maxHeartbeats 0 in
/-- `FOUND`/`SETUP` for a function without open-coded defers. -/
theorem seg_found_noopen (c : State) (j fr dr entry : Nat) (hpc : c.pc = BitVec.ofNat 64 (E + 0x240))
    (h8 : c.regs 8 = BitVec.ofNat 64 (tabAt j)) (h0 : c.regs 0 = BitVec.ofNat 64 entry)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 8 ≤ 2 ^ 48) (h96 : 96 ≤ c.sp.toNat)
    (hacc : c.mem.accessible (c.sp.toNat - 96) 96 true = true)
    (hB : c.mem.accessible B 0x1000 true = true) (hj : j < 16)
    (hspB : c.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ c.sp.toNat)
    (hfr : c.mem.readLE (tabAt j + 16) 8 = fr) (hdr : c.mem.readLE (tabAt j + 24) 8 = dr)
    (hop : c.mem.readLE (tabAt j + 32) 8 = 0) (hf64 : c.sp.toNat + fr < 2 ^ 64) (hd64 : entry + dr < 2 ^ 64)
    (hent : entry < 2 ^ 64) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun d => d.pc = BitVec.ofNat 64 eLH ∧
      d.sp = BitVec.ofNat 64 (c.sp.toNat - 96) ∧ d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧
      MemFrame c.mem d.mem [(c.sp.toNat - 96, c.sp.toNat - 16)] ∧
      d.mem.readLE (c.sp.toNat - 96) 8 = c.sp.toNat ∧ d.mem.readLE (c.sp.toNat - 96 + 8) 8 = c.sp.toNat + fr ∧
      d.mem.readLE (c.sp.toNat - 96 + 16) 8 = entry + dr ∧
      d.mem.readLE (c.sp.toNat - 96 + 24) 8 = (c.regs 10).toNat ∧
      d.mem.readLE (c.sp.toNat - 96 + 32) 8 = 0 ∧
      d.mem.readLE (c.sp.toNat - 96 + 56) 8 = (c.regs 18).toNat) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hacc' : c.mem.accessible (c.sp.toNat - 96) 96 true = true := hacc
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, B, Nat.reduceAdd] at hpc ⊢ hspB
  subst hpc
  simp only [tabAt, B] at hfr hdr hop h8
  janus_run [hfr, hdr, hop, h8, h0]
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · janus_frame

set_option maxHeartbeats 0 in
/-- `FOUND`/`SETUP` for a function with open-coded defers (offsets `o1` of the `deferBits` byte and
`o2` of the first slot below `varp`). -/
theorem seg_found_open (c : State) (j fr dr entry o1 o2 b ph : Nat) (hpc : c.pc = BitVec.ofNat 64 (E + 0x240))
    (h8 : c.regs 8 = BitVec.ofNat 64 (tabAt j)) (h0 : c.regs 0 = BitVec.ofNat 64 entry)
    (hal : c.sp.toNat % 16 = 0) (hsp : c.sp.toNat + 8 ≤ 2 ^ 48) (h96 : 96 ≤ c.sp.toNat)
    (hacc : c.mem.accessible (c.sp.toNat - 96) 96 true = true)
    (hB : c.mem.accessible B 0x1000 true = true) (hj : j < 16)
    (hspB : c.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ c.sp.toNat)
    (hfr : c.mem.readLE (tabAt j + 16) 8 = fr) (hdr : c.mem.readLE (tabAt j + 24) 8 = dr)
    (hop : c.mem.readLE (tabAt j + 32) 8 = 1) (ho1 : c.mem.readLE (tabAt j + 40) 8 = o1)
    (ho2 : c.mem.readLE (tabAt j + 48) 8 = o2) (hf64 : c.sp.toNat + fr < 2 ^ 64) (hd64 : entry + dr < 2 ^ 64)
    (hent : entry < 2 ^ 64) (hfr8 : 8 ≤ fr) (ho1' : o1 ≤ fr - 8) (ho2' : o2 ≤ fr - 8)
    (hba : c.mem.accessible (c.sp.toNat + fr - 8 - o1) 1 false = true)
    (hb : c.mem.readLE (c.sp.toNat + fr - 8 - o1) 1 = b) (hphd : (b = 0 ∧ ph = 0) ∨ (b ≠ 0 ∧ ph = 1)) :
    ReachesRet qE (BitVec.ofNat 64 eLH) c (fun d => d.pc = BitVec.ofNat 64 eLH ∧
      d.sp = BitVec.ofNat 64 (c.sp.toNat - 96) ∧ d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧
      MemFrame c.mem d.mem [(c.sp.toNat - 96, c.sp.toNat - 16)] ∧
      d.mem.readLE (c.sp.toNat - 96) 8 = c.sp.toNat ∧ d.mem.readLE (c.sp.toNat - 96 + 8) 8 = c.sp.toNat + fr ∧
      d.mem.readLE (c.sp.toNat - 96 + 16) 8 = entry + dr ∧
      d.mem.readLE (c.sp.toNat - 96 + 24) 8 = (c.regs 10).toNat ∧
      d.mem.readLE (c.sp.toNat - 96 + 32) 8 = ph ∧
      d.mem.readLE (c.sp.toNat - 96 + 40) 8 = c.sp.toNat + fr - 8 - o1 ∧
      d.mem.readLE (c.sp.toNat - 96 + 48) 8 = c.sp.toNat + fr - 8 - o2 ∧
      d.mem.readLE (c.sp.toNat - 96 + 56) 8 = (c.regs 18).toNat) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  have hacc' : c.mem.accessible (c.sp.toNat - 96) 96 true = true := hacc
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLH, E, B, Nat.reduceAdd] at hpc ⊢ hspB
  subst hpc
  simp only [tabAt, B] at hfr hdr hop ho1 ho2 h8
  have hadr : (18446744073709551616 - (8 + o1) + (BitVec.toNat csp + fr)) % 18446744073709551616 =
      BitVec.toNat csp + fr - 8 - o1 := by omega
  have hb' : cm.readLE ((18446744073709551616 - (8 + o1) + (BitVec.toNat csp + fr)) % 18446744073709551616) 1 = b := by
    rw [hadr]; exact hb
  have hba' : cm.accessible ((18446744073709551616 - (8 + o1) + (BitVec.toNat csp + fr)) % 18446744073709551616) 1 false = true := by
    rw [hadr]; exact hba
  have hb256 : b < 256 := by rw [← hb]; simpa using Memory.readLE_lt cm (BitVec.toNat csp + fr - 8 - o1) 1
  have hbm : b % 4294967296 = b := Nat.mod_eq_of_lt (by omega)
  rcases hphd with ⟨hb0, rfl⟩ | ⟨hb0, rfl⟩
  · subst hb0
    janus_run [hfr, hdr, hop, ho1, ho2, h8, h0, hb, hb']
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_frame
    · omega
    · omega
  · janus_run [hfr, hdr, hop, ho1, ho2, h8, h0, hb, hb', hb0, hbm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · janus_frame
    · omega
    · omega



set_option maxHeartbeats 0 in
/-- The start of the function-table search. -/
theorem seg_lk_entry (c : State) (hpc : c.pc = BitVec.ofNat 64 eLookup)
    (hB : c.mem.accessible B 0x1000 true = true) :
    ReachesRet qE (BitVec.ofNat 64 (E + 0x210)) c (fun d => d.mem = c.mem ∧ d.sp = c.sp ∧
      d.regs 7 = BitVec.ofNat 64 (c.mem.readLE (B + 0x28) 8) ∧ d.regs 8 = BitVec.ofNat 64 (tabAt 0) ∧
      d.regs 28 = c.regs 28 ∧ d.regs 18 = c.regs 18 ∧ d.regs 30 = c.regs 30 ∧ d.regs 10 = c.regs 10) := by
  have hB' : c.mem.accessible 65536 4096 true = true := hB
  obtain ⟨cr, csp, cpc, cfl, cm, cdz, cv, ctp, cfc, cfs⟩ := c
  dsimp only at *
  simp only [eLookup, E, Nat.reduceAdd] at hpc ⊢
  subst hpc
  janus_run

/-- What the model's table search needs of the function table. -/
def TOK (T : List FuncInfo) : Prop :=
  ∀ f ∈ T, f.entry + f.size < 2 ^ 64 ∧ f.entry + f.deferreturn < 2 ^ 48 ∧ (f.entry + f.deferreturn) % 4 = 0 ∧
    f.frame < 2 ^ 48 ∧ ∀ o ∈ f.openDefer, 8 ≤ f.frame ∧ o.1 ≤ f.frame - 8 ∧ o.2 ≤ f.frame - 8

theorem find_eq (T : List FuncInfo) (pc : Nat) :
    FuncInfo.find T pc = T.find? (fun f => decide (f.entry ≤ pc ∧ pc < f.entry + f.size)) := rfl

section lf
variable {p : Program}

set_option maxHeartbeats 0 in
/-- From the start of the table search to the loop head: the function containing the return
address is found and the loop's frame is written. -/
theorem lookup_found (hp : EngineAt p) (T : List FuncInfo) (hT : TOK T) {mode : DeferMode} (hm : mode ≠ .ret)
    (s1 : State) (fi : FuncInfo) (hpc : s1.pc = BitVec.ofNat 64 eLookup) (henv : Env0 T s1.mem)
    (hal : s1.sp.toNat % 16 = 0) (hsp : s1.sp.toNat + 8 ≤ 2 ^ 48) (h96 : 96 ≤ s1.sp.toNat)
    (hacc : s1.mem.accessible (s1.sp.toNat - 96) 96 true = true)
    (hspB : s1.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s1.sp.toNat)
    (hfind : FuncInfo.find T (s1.regs 30).toNat = some fi)
    (hmode : s1.regs 10 = BitVec.ofNat 64 (modeCode mode))
    (hba : fi.openDefer.isSome → s1.mem.accessible (fi.bitsAt s1.sp.toNat) 1 false = true) :
    ∃ k c, Program.Steps p s1 k c ∧ c.pc = BitVec.ofNat 64 eLH ∧ c.sp = BitVec.ofNat 64 (s1.sp.toNat - 96) ∧
      c.regs 28 = s1.regs 28 ∧ c.regs 18 = s1.regs 18 ∧
      MemFrame s1.mem c.mem [(s1.sp.toNat - 96, s1.sp.toNat - 16)] ∧
      FrameMem c.mem (frameOf fi s1.sp.toNat s1.mem) mode
        (if (frameOf fi s1.sp.toNat s1.mem).openAt.isSome then 1 else 0) (s1.regs 18).toNat 0 0 := by
  have htab := henv.table
  have hB := henv.acc
  obtain ⟨hl16, hnt, htE⟩ := htab
  have hra : (s1.regs 30).toNat < 2 ^ 64 := (s1.regs 30).isLt
  obtain ⟨k1, s2, hk1, hpc2, hq1⟩ := reachesRet_transfer hp (seg_lk_entry s1 hpc hB)
  obtain ⟨hm2, hsp2, h72, h82, h282, h182, h302, h102⟩ := hq1
  have hlk := seg_lookup T (s1.regs 30).toNat hra (fun f hf => (hT f hf).1) fi T.length 0 s2 (by omega)
    hpc2 (by rw [h72]; exact congrArg _ hnt) h82 (by rw [h302]; simp) (by rw [hm2]; exact ⟨hl16, hnt, htE⟩) (by rw [hm2]; exact hB)
    (by rw [find_eq] at hfind; exact hfind)
  obtain ⟨k2, s3, hk2, hpc3, hq3⟩ := reachesRet_transfer hp hlk
  obtain ⟨hm3, hsp3, h283, h183, h303, h103, j, hj, hTj, h83, h03⟩ := hq3
  have hTjfi : T[j] = fi := by
    rw [List.getElem?_eq_getElem hj] at hTj; exact Option.some.inj hTj
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := htE j hj
  rw [hTjfi] at e1 e2 e3 e4 e5 e6 e7
  have hfiT : fi ∈ T := by rw [← hTjfi]; exact List.getElem_mem hj
  obtain ⟨t1, t2, t3, t4, t5⟩ := hT fi hfiT
  have hsm : s3.mem = s1.mem := by rw [hm3, hm2]
  have hssp : s3.sp = s1.sp := by rw [hsp3, hsp2]
  have hspn : s3.sp.toNat = s1.sp.toNat := by rw [hssp]
  have h10 : (s3.regs 10) = BitVec.ofNat 64 (modeCode mode) := by rw [h103, h102, hmode]
  have h10n : (s3.regs 10).toNat = modeCode mode := by
    rw [h10, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; cases mode <;> simp [modeCode]
  have hfr : s3.mem.readLE (tabAt j + 16) 8 = fi.frame := by rw [hsm]; exact e3
  have hdr : s3.mem.readLE (tabAt j + 24) 8 = fi.deferreturn := by rw [hsm]; exact e4
  have hj16 : j < 16 := by omega
  have hacc3 : s3.mem.accessible (s3.sp.toNat - 96) 96 true = true := by rw [hsm, hspn]; exact hacc
  have hB3 : s3.mem.accessible B 0x1000 true = true := by rw [hsm]; exact hB
  have hspB3 : s3.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s3.sp.toNat := by rw [hspn]; exact hspB
  have hf64 : s3.sp.toNat + fi.frame < 2 ^ 64 := by rw [hspn]; omega
  have hd64 : fi.entry + fi.deferreturn < 2 ^ 64 := by omega
  have hent : fi.entry < 2 ^ 64 := by omega
  have hsteps : ∀ c, (∃ k, Program.Steps p s3 k c) → ∃ k, Program.Steps p s1 k c := fun c ⟨k, hk⟩ =>
    ⟨k1 + k2 + k, (hk1.trans hk2).trans hk⟩
  cases hod : fi.openDefer with
  | none =>
    have hop : s3.mem.readLE (tabAt j + 32) 8 = 0 := by rw [hsm]; have := e5; rw [hod] at this; simpa using this
    obtain ⟨k3, c, hk3, -, hq⟩ := reachesRet_transfer hp (seg_found_noopen s3 j fi.frame fi.deferreturn fi.entry hpc3 h83 h03
      (by rw [hspn]; exact hal) (by rw [hspn]; exact hsp) (by rw [hspn]; exact h96) hacc3 hB3 hj16 hspB3 hfr hdr hop hf64 hd64 hent)
    obtain ⟨hcpc, hcsp, hc28, hc18, hmf, w0, w8, w16, w24, w32, w56⟩ := hq
    rw [hspn] at hcsp hmf w0 w8 w16 w24 w32 w56
    refine ⟨k1 + k2 + k3, c, (hk1.trans hk2).trans hk3, hcpc, hcsp, by rw [hc28, h283, h282], by rw [hc18, h183, h182],
      by rw [← hsm]; exact hmf, ?_⟩
    have hF : (frameOf fi s1.sp.toNat s1.mem).openAt = none := by simp [frameOf, hod]
    have hph : (if (frameOf fi s1.sp.toNat s1.mem).openAt.isSome then 1 else 0) = 0 := by rw [hF]; rfl
    rw [hph]
    refine ⟨w0, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hm, fun h => absurd rfl h⟩
    · show c.mem.readLE (s1.sp.toNat - 96 + 8) 8 = s1.sp.toNat + fi.frame
      exact w8
    · show c.mem.readLE (s1.sp.toNat - 96 + 16) 8 = fi.entry + fi.deferreturn
      exact w16
    · show c.mem.readLE (s1.sp.toNat - 96 + 24) 8 = modeCode mode
      rw [← h10n]; exact w24
    · exact w32
    · intro ba sa h; rw [hF] at h; cases h
    · show c.mem.readLE (s1.sp.toNat - 96 + 56) 8 = (s1.regs 18).toNat
      rw [w56, h183, h182]
  | some o =>
    obtain ⟨o1, o2⟩ := o
    have hop : s3.mem.readLE (tabAt j + 32) 8 = 1 := by rw [hsm]; have := e5; rw [hod] at this; simpa using this
    have ho1 : s3.mem.readLE (tabAt j + 40) 8 = o1 := by rw [hsm]; have := e6; rw [hod] at this; simpa using this
    have ho2 : s3.mem.readLE (tabAt j + 48) 8 = o2 := by rw [hsm]; have := e7; rw [hod] at this; simpa using this
    obtain ⟨hf8, hf1, hf2⟩ := t5 (o1, o2) (by rw [hod]; rfl)
    have hbaa := hba (by rw [hod]; rfl)
    have hbitsAt : fi.bitsAt s1.sp.toNat = s1.sp.toNat + fi.frame - 8 - o1 := by
      simp [FuncInfo.bitsAt, FuncInfo.varp, hod]
    have hslotsAt : fi.slotsAt s1.sp.toNat = s1.sp.toNat + fi.frame - 8 - o2 := by
      simp [FuncInfo.slotsAt, FuncInfo.varp, hod]
    rw [hbitsAt] at hbaa
    have hbaa3 : s3.mem.accessible (s3.sp.toNat + fi.frame - 8 - o1) 1 false = true := by rw [hsm, hspn]; exact hbaa
    obtain ⟨b, hb⟩ : ∃ b, s1.mem.readLE (s1.sp.toNat + fi.frame - 8 - o1) 1 = b := ⟨_, rfl⟩
    have hb3 : s3.mem.readLE (s3.sp.toNat + fi.frame - 8 - o1) 1 = b := by rw [hsm, hspn]; exact hb
    have hphd : (b = 0 ∧ (if b = 0 then 0 else 1) = 0) ∨ (b ≠ 0 ∧ (if b = 0 then 0 else 1) = 1) := by
      by_cases hb0 : b = 0 <;> simp [hb0]
    obtain ⟨k3, c, hk3, -, hq⟩ := reachesRet_transfer hp (seg_found_open s3 j fi.frame fi.deferreturn fi.entry o1 o2 b
      (if b = 0 then 0 else 1) hpc3 h83 h03 (by rw [hspn]; exact hal) (by rw [hspn]; exact hsp) (by rw [hspn]; exact h96)
      hacc3 hB3 hj16 hspB3 hfr hdr hop ho1 ho2 hf64 hd64 hent hf8 hf1 hf2 hbaa3 hb3 hphd)
    obtain ⟨hcpc, hcsp, hc28, hc18, hmf, w0, w8, w16, w24, w32, w40, w48, w56⟩ := hq
    rw [hspn] at hcsp hmf w0 w8 w16 w24 w32 w40 w48 w56
    refine ⟨k1 + k2 + k3, c, (hk1.trans hk2).trans hk3, hcpc, hcsp, by rw [hc28, h283, h282], by rw [hc18, h183, h182],
      by rw [← hsm]; exact hmf, ?_⟩
    have hF : (frameOf fi s1.sp.toNat s1.mem).openAt =
        (if b = 0 then none else some (s1.sp.toNat + fi.frame - 8 - o1, s1.sp.toNat + fi.frame - 8 - o2)) := by
      simp only [frameOf, hod, hbitsAt, hslotsAt, hb]
    by_cases hb0 : b = 0
    · have hF0 : (frameOf fi s1.sp.toNat s1.mem).openAt = none := by rw [hF, if_pos hb0]
      have hph : (if (frameOf fi s1.sp.toNat s1.mem).openAt.isSome then 1 else 0) = 0 := by rw [hF0]; rfl
      rw [hph]
      have w32' : c.mem.readLE (s1.sp.toNat - 96 + 32) 8 = 0 := by rw [w32, if_pos hb0]
      refine ⟨w0, ?_, ?_, ?_, w32', ?_, ?_, fun h => absurd h hm, fun h => absurd rfl h⟩
      · show c.mem.readLE (s1.sp.toNat - 96 + 8) 8 = s1.sp.toNat + fi.frame
        exact w8
      · show c.mem.readLE (s1.sp.toNat - 96 + 16) 8 = fi.entry + fi.deferreturn
        exact w16
      · show c.mem.readLE (s1.sp.toNat - 96 + 24) 8 = modeCode mode
        rw [← h10n]; exact w24
      · intro ba sa h; rw [hF0] at h; cases h
      · show c.mem.readLE (s1.sp.toNat - 96 + 56) 8 = (s1.regs 18).toNat
        rw [w56, h183, h182]
    · have hF1 : (frameOf fi s1.sp.toNat s1.mem).openAt =
          some (s1.sp.toNat + fi.frame - 8 - o1, s1.sp.toNat + fi.frame - 8 - o2) := by rw [hF, if_neg hb0]
      have hph : (if (frameOf fi s1.sp.toNat s1.mem).openAt.isSome then 1 else 0) = 1 := by rw [hF1]; rfl
      rw [hph]
      have w32' : c.mem.readLE (s1.sp.toNat - 96 + 32) 8 = 1 := by rw [w32, if_neg hb0]
      refine ⟨w0, ?_, ?_, ?_, w32', ?_, ?_, fun h => absurd h hm, fun _ => by rw [hF1]; rfl⟩
      · show c.mem.readLE (s1.sp.toNat - 96 + 8) 8 = s1.sp.toNat + fi.frame
        exact w8
      · show c.mem.readLE (s1.sp.toNat - 96 + 16) 8 = fi.entry + fi.deferreturn
        exact w16
      · show c.mem.readLE (s1.sp.toNat - 96 + 24) 8 = modeCode mode
        rw [← h10n]; exact w24
      · intro ba sa h
        rw [hF1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨w40, w48⟩
      · show c.mem.readLE (s1.sp.toNat - 96 + 56) 8 = (s1.regs 18).toNat
        rw [w56, h183, h182]

end lf

section gp
variable {p : Program}

theorem rdsame_of_frame {m m' : Memory} {ws : List (Nat × Nat)} (hf : MemFrame m m' ws)
    (ho : ∀ a, (a = B + 8 ∨ (B + 0x28 ≤ a ∧ a + 8 ≤ B + 0x100) ∨ (B + 0x200 ≤ a ∧ a + 8 ≤ B + 0x1000)) →
      Outside a 8 ws) : RdSame m m' := fun a ha => hf.readLE a 8 (ho a ha)

/-- The end of the loop of `gopanic` or `Goexit`: the runtime unwinds past the frame. -/
theorem left_fin (hp : EngineAt p) {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
    {ds0 : List DeferRec} {mode : DeferMode} (hm : mode ≠ .ret) {x28 x18 : W64} {lr x29 : Nat} {c : State}
    {ch : List PanicRec} {rm : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode x28 x18 lr x29 c ch rm 0)
    (hpc : c.pc = BitVec.ofNat 64 eLH) (h18 : c.regs 18 = x18)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) :
    ∃ k d, Program.Steps p c k d ∧ LeftFrame (P0 T RPa) U0 x28 F ds0 ch rm c d := by
  obtain ⟨k, d, hk, hmem, h28, h18d, -, hret⟩ := step_fin hp hI h18 hpc rfl hend
  obtain ⟨hpcd, hspd⟩ := hret hm
  have hfi := fin_items hI.env hend
  refine ⟨k, d, hk, ⟨hpcd, hspd, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h28]; simp
  · show panics0 d.mem = ch; rw [hmem]; exact hI.pan
  · show defers0 d.mem = frameRest F.sp ds0
    rw [hmem, ← hfi.2]; exact hI.chn
  · rw [hmem]; exact MemFrame.refl _ _
  · show Env0 T d.mem; rw [hmem]; exact hI.env
  · show rm ≤ room0 d.mem; rw [hmem]; exact hI.room
  · show saved0 d.mem = saved0 c.mem; rw [hmem]

end gp

section dr
variable {p : Program} {T : List FuncInfo}

/-- The end of `deferreturn`'s loop. -/
theorem dr_fin (hp : EngineAt p) (s : State) {c : State} {ch : List PanicRec} {rm : Nat}
    (hI : Inv0 T s.mem (retFrame (P0 T RPa) s) (frameItems s.mem (retFrame (P0 T RPa) s) ((P0 T RPa).defers s.mem (gOf s)))
      ((P0 T RPa).defers s.mem (gOf s)) .ret (s.regs 28) (s.regs 18) (s.regs 30).toNat (s.regs 29).toNat c ch rm 0)
    (hpc : c.pc = BitVec.ofNat 64 eLH) (h18 : c.regs 18 = s.regs 18)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ (retFrame (P0 T RPa) s).sp) :
    ∃ k d, Program.Steps p c k d ∧ RetFin (P0 T RPa) s ((P0 T RPa).defers s.mem (gOf s)) ch rm c d := by
  obtain ⟨k, d, hk, hmem, h28, h18d, hret, -⟩ := step_fin hp hI h18 hpc rfl hend
  obtain ⟨hpcd, hspd, h29d⟩ := hret rfl
  have hfi := fin_items hI.env hend
  refine ⟨k, d, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcd]; simp
  · rw [hspd]; simp [retFrame]
  · exact h28
  · exact h18d
  · rw [h29d]; simp
  · rw [hmem]; exact MemFrame.refl _ _
  · show Env0 T d.mem; rw [hmem]; exact hI.env
  · show panics0 d.mem = ch; rw [hmem]; exact hI.pan
  · show defers0 d.mem = frameRest (retFrame (P0 T RPa) s).sp ((P0 T RPa).defers s.mem (gOf s))
    rw [hmem, ← hfi.2]; exact hI.chn
  · show saved0 d.mem = none; rw [hmem]; exact (saved0_none_iff _).2 (hI.sv rfl)
  · rfl
  · show rm ≤ room0 d.mem; rw [hmem]; exact hI.room

set_option maxHeartbeats 0 in
theorem deferreturn_run (hp : EngineAt p) :
    DeferreturnContract p eDeferreturn (P0 T RPa) U0 := by
  intro s hpc ⟨hpre, hfo⟩
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, ⟨h30a, h30b, hal, hst, h8, hs48, hacc⟩, hout⟩ := hpre
  have henv0 : Env0 T s.mem := henv
  simp only [P0_depth, P0_priv, Nat.mul_zero, Nat.add_zero] at hst hacc hout hs48 hacc
  have hB := henv0.acc
  have hspB : s.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s.sp.toNat := by
    simp only [outside_cons, outside_nil, and_true] at hout; simp only [B] at *; omega
  have hacc96 : s.mem.accessible (s.sp.toNat - 96) 96 true = true :=
    Memory.accessible_mono _ hacc (by omega) (by omega)
  have hseg := seg_dr_entry s hpc hal (by omega) (by omega) hacc96 hB hspB
  obtain ⟨k0, c, hk0, -, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hcpc, hcsp, hc28, hc18, hmf0, hsv0, w0, w8, w16, w24, w32, w40, w48, w56, w64, w72⟩ := hq
  have hsp64 : s.sp.toNat < 2 ^ 64 := s.sp.isLt
  have hcs : c.sp.toNat = s.sp.toNat - 96 := by
    rw [hcsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  -- the frame
  have hsaved : saved0 s.mem = if rd s.mem (B + 0x10) = 0 then none else
      some (rd s.mem (B + 0x18), rd s.mem (B + 0x20)) := saved0_eq s.mem
  have hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) (retFrame (P0 T RPa) s) ++
      bitsWin (retFrame (P0 T RPa) s)) := hmf0.mono fun a n h => by
    simp only [outside_append, P0_priv, outside_cons, outside_nil, and_true, rtWin, retFrame, P0_depth] at h ⊢
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    simp only [B] at *; omega
  have hfm : FrameMem c.mem (retFrame (P0 T RPa) s) .ret (rd s.mem (B + 0x10)) (s.regs 18).toNat
      (s.regs 30).toNat (s.regs 29).toNat := by
    refine ⟨w0, w8, w16, w24, w32, ?_, w56, fun _ => ⟨w64, w72⟩, ?_⟩
    · intro ba sa hF
      have hF' : saved0 s.mem = some (ba, sa) := hF
      rw [hsaved] at hF'
      split at hF'
      · cases hF'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hF'
        obtain ⟨rfl, rfl⟩ := hF'
        exact ⟨w40, w48⟩
    · intro hne
      show (saved0 s.mem).isSome = true
      rw [hsaved, if_neg hne]; rfl
  have ha2 : Agrees s.mem c.mem R2 := Agrees.of_memFrame hmf0 fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    simp only [R2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    simp only [outside_cons, outside_nil, and_true]
    rcases hr with rfl | rfl <;> simp only [B] at * <;> omega
  have hnp : npan c.mem = npan s.mem := hmf0.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]; simp only [B] at *; omega)
  obtain ⟨henvc, hdefc, hpanc, hroomc⟩ := bundle2 henv0 ha2 hnp
  have hba : ∀ ba sa, (retFrame (P0 T RPa) s).openAt = some (ba, sa) → c.mem.readLE ba 1 = s.mem.readLE ba 1 := by
    intro ba sa hF
    have h := hfo.1
    rw [hF] at h
    obtain ⟨-, -, hb3, hb4, -⟩ := h
    refine hmf0.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    simp only [P0_priv, outside_cons, outside_nil, and_true] at hb3
    simp only [retFrame] at hb4
    simp only [B] at *; omega
  have hcur : curItems c.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) =
      frameItems s.mem (retFrame (P0 T RPa) s) (defers0 s.mem) := by
    have hc1 : curItems c.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) =
        curItems s.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) := by
      refine curItems_congr (m := s.mem) (m' := c.mem) hdefc fun ba sa hF _ => ⟨hba ba sa hF, fun i hi => ?_⟩
      have h := hfo.1
      rw [hF] at h
      obtain ⟨-, -, -, -, h5, -⟩ := h
      obtain ⟨-, -, -, a4, a5⟩ := h5 i hi
      refine hmf0.readLE _ _ ?_
      simp only [P0_priv, outside_cons, outside_nil, and_true] at a5
      simp only [outside_cons, outside_nil, and_true]
      simp only [retFrame] at a4
      simp only [B] at *; omega
    rw [hc1]
    refine curItems_entry _ _ _ fun h0 => ?_
    show saved0 s.mem = none
    rw [hsaved, if_pos h0]
  have hI := Inv0.init (T := T) (s := s) (c := c) (F := retFrame (P0 T RPa) s) (mode := .ret) (x28 := s.regs 28)
    (x18 := s.regs 18) (lr := (s.regs 30).toNat) (x29 := (s.regs 29).toNat) (ph := rd s.mem (B + 0x10))
    (ch := panics0 s.mem) (rm := room0 s.mem) hfo hal (by simp only [retFrame]; omega) (by simp only [retFrame]; omega)
    (by simp only [retFrame]; exact hspB) (by simp only [retFrame]; exact hsp64) ⟨rfl, by simp only [retFrame]; omega⟩
    (fun _ => ⟨h30a, h30b⟩) (by simp only [retFrame]; omega) hc28 (by simp only [retFrame]; exact hacc96) hmf hfm
    henvc hpanc (by rw [hroomc]; exact Nat.le_refl _) (fun _ => hsv0) hdefc hba hcur
  have hloop := engine_loop (p := p) (T := T) (m0 := s.mem) (F := retFrame (P0 T RPa) s)
    (items0 := frameItems s.mem (retFrame (P0 T RPa) s) (defers0 s.mem)) (ds0 := defers0 s.mem) (mode := .ret)
    (x28 := s.regs 28) (x18 := s.regs 18) (lr := (s.regs 30).toNat) (x29 := (s.regs 29).toNat) hp
    (Fin := RetFin (P0 T RPa) s ((P0 T RPa).defers s.mem (gOf s)))
    (fun ch rm c c' d hm _ hf => RetFin.prefix hm hf)
    (fun c ch rm hpc h18 hI _ hend => dr_fin hp s hI hpc h18 hend) _ c (panics0 s.mem) (room0 s.mem)
    (rd s.mem (B + 0x10)) rfl hcpc hc18 hI (fun h => absurd h (by decide))
  rw [hcur] at hloop
  exact Engine.of_prefix_ret (fun ch rm d hf => RetFin.prefix (hmf) hf) hk0 hmf rfl hloop

end dr

end Janus.Contracts.PanicSat
