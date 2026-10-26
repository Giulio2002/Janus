import Janus.Contracts.PanicSatEngine

/-!
# The entry of the model engine: `gopanic`, `Goexit`, `deferreturn`

The entry code of the model engine writes the loop's frame and brings the machine to the loop
head `LH` in a state meeting the invariant `Inv0` of `PanicSatEngine`; with `engine_loop` this gives
the three contracts.
-/

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
    (fun ch rm c c' d hm hf => RetFin.prefix hm hf)
    (fun c ch rm hpc h18 hI _ hend => dr_fin hp s hI hpc h18 hend) _ c (panics0 s.mem) (room0 s.mem)
    (rd s.mem (B + 0x10)) rfl hcpc hc18 hI (fun h => absurd h (by decide))
  rw [hcur] at hloop
  exact Engine.of_prefix_ret (fun ch rm d hf => RetFin.prefix (hmf) hf) hk0 hmf rfl hloop

end dr

end Janus.Contracts.PanicSat
