import PrintProofs.Arm64.FnHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print

namespace PrintFn

/-! ## `printlock` with the print count 0 (takes `debuglock` through `lock2`) and `printunlock`
with the count 1 (releases it through `unlock2`) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
/-- `runtime.printlock` with the M's print count 0: `lock2(&debuglock)`; afterwards the count is 1, the
lock is held and `m.locks` is one higher (`lock2`'s increment; `printlock`'s own `locks++`/`locks--`
cancel). -/
theorem printlock_free (impl : List Segment) (rt : List (Nat × Nat)) (LS : Nat)
    (hl : Lock2Contract (P.link impl) (P.contractAddr "runtime.lock2") rt LS) :
    Summary (P.link impl) (segAddr P "runtime.printlock")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s (LS + 32) 0 ∧
        8 ≤ LS ∧ GuardOK s 0 ∧
        (s.regs 28).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 48) 8 false = true ∧
        s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 true = true ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 = 0 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 + 3 < 2 ^ 31 ∧
        DL + 8 ≤ 2 ^ 48 ∧ s.mem.accessible DL 8 true = true ∧ ¬ lockHeld s.mem DL ∧
        InRanges DL 8 rt ∧ InRanges (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 rt ∧
        Outside (s.sp.toNat - (LS + 32)) (LS + 32) rt ∧ Outside ((s.regs 28).toNat + 16) 8 rt ∧
        Outside ((s.regs 28).toNat + 48) 8 rt ∧
        Outside (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 rt ∧
        Apart DL 8 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 ∧
        Apart ((s.regs 28).toNat + 48) 8 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 ∧
        Sep (s.sp.toNat - (LS + 32)) (LS + 32) [((s.regs 28).toNat + 16, 8), ((s.regs 28).toNat + 48, 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), (DL, 8)])
      (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
        s' = retState s junk [] f v m ∧
        MemFrame s.mem m (rt ++ [(s.sp.toNat - (LS + 32), s.sp.toNat - 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 268),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280)]) ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 = 1 ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 + 1 ∧
        lockHeld m DL) := by
  -- PROOF printlock_free
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, hLS, ⟨hg1, hg2, hg3⟩, hgm1, hgm2, hm1, hm2, hc0, hl31,
    hdl1, hdl2, hfree, hin1, hin2, ho1, ho2, ho3, ho4, hapd, hapg, hout⟩
  simp only [lockHeld] at hfree
  simp only [sep_cons, sep_nil, and_true] at hout
  obtain ⟨hout_1, hout_2, hout_3, hout_4⟩ := hout
  -- the fixed-size frame of `printlock` inside the window (for `omega` without `LS`)
  have f1 : Apart (s.sp.toNat - 40) 32 ((s.regs 28).toNat + 16) 8 := Apart.sub hout_1 (by omega) (by omega) (by omega) (by omega)
  have f2 : Apart (s.sp.toNat - 40) 32 ((s.regs 28).toNat + 48) 8 := Apart.sub hout_2 (by omega) (by omega) (by omega) (by omega)
  have f3 : Apart (s.sp.toNat - 40) 32 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 := Apart.sub hout_3 (by omega) (by omega) (by omega) (by omega)
  have f4 : Apart (s.sp.toNat - 40) 32 DL 8 := Apart.sub hout_4 (by omega) (by omega) (by omega) (by omega)
  janus_eval_nat h_dl : DL
  simp only [h_dl] at *
  have hlt : s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 < 128 := by omega
  have hlt2 : s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 < 2147483648 := by omega
  janus_run [rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero,
    sext32_add_mod, sext8_add_mod, sext8_add_mod', hlt, hlt2, hc0] calls [hl]
  rename_i _ _ _ _ m hfr hheld hlk _
  have e1 : m.readLE ((s.regs 28).toNat + 48) 8 = s.mem.readLE ((s.regs 28).toNat + 48) 8 := by
    janus_simp
  rw [e1] at hlk
  refine ⟨_, _, _, _, by ret_state, by janus_frame, ?_, ?_, ?_⟩
  all_goals janus_simp
  · rw [hlk]; split <;> omega
  · exact hheld

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
/-- `runtime.printunlock` with the M's print count 1: `unlock2(&debuglock)`; afterwards the count is
0, the lock's key byte is cleared and `m.locks` is one lower (`unlock2`'s decrement). -/
theorem printunlock_last (impl : List Segment) (rt : List (Nat × Nat)) (LS : Nat)
    (hu : Unlock2Contract (P.link impl) (P.contractAddr "runtime.unlock2") rt LS) :
    Summary (P.link impl) (segAddr P "runtime.printunlock")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ StackOK s (LS + 32) 0 ∧
        8 ≤ LS ∧ GuardOK s 0 ∧
        (s.regs 28).toNat + 56 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 48) 8 false = true ∧
        s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 true = true ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 = 1 ∧
        1 ≤ s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 ∧
        s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 + 3 < 2 ^ 31 ∧
        DL + 8 ≤ 2 ^ 48 ∧ s.mem.accessible DL 8 true = true ∧ lockHeld s.mem DL ∧
        InRanges DL 8 rt ∧ InRanges (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 rt ∧
        Outside (s.sp.toNat - (LS + 32)) (LS + 32) rt ∧ Outside ((s.regs 28).toNat + 16) 8 rt ∧
        Outside ((s.regs 28).toNat + 48) 8 rt ∧
        Outside (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 rt ∧
        Apart DL 8 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 ∧
        Apart ((s.regs 28).toNat + 48) 8 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 ∧
        Sep (s.sp.toNat - (LS + 32)) (LS + 32) [((s.regs 28).toNat + 16, 8), ((s.regs 28).toNat + 48, 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264, 16), (DL, 8)])
      (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
        s' = retState s junk [] f v m ∧
        MemFrame s.mem m (rt ++ [(s.sp.toNat - (LS + 32), s.sp.toNat - 8),
          (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279, s.mem.readLE ((s.regs 28).toNat + 48) 8 + 280)]) ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 = 0 ∧
        m.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 + 1 =
          s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 4 ∧
        m.readLE DL 1 = 0) := by
  -- PROOF printunlock_last
  intro s hpc ⟨h30a, h30b, ⟨hal, hb, ha, hw⟩, hLS, ⟨hg1, hg2, hg3⟩, hgm1, hgm2, hm1, hm2, hc0, hl0, hl31,
    hdl1, hdl2, hheld0, hin1, hin2, ho1, ho2, ho3, ho4, hapd, hapg, hout⟩
  simp only [lockHeld] at hheld0
  simp only [sep_cons, sep_nil, and_true] at hout
  obtain ⟨hout_1, hout_2, hout_3, hout_4⟩ := hout
  have f1 : Apart (s.sp.toNat - 40) 32 ((s.regs 28).toNat + 16) 8 := Apart.sub hout_1 (by omega) (by omega) (by omega) (by omega)
  have f2 : Apart (s.sp.toNat - 40) 32 ((s.regs 28).toNat + 48) 8 := Apart.sub hout_2 (by omega) (by omega) (by omega) (by omega)
  have f3 : Apart (s.sp.toNat - 40) 32 (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 264) 16 := Apart.sub hout_3 (by omega) (by omega) (by omega) (by omega)
  have f4 : Apart (s.sp.toNat - 40) 32 DL 8 := Apart.sub hout_4 (by omega) (by omega) (by omega) (by omega)
  janus_eval_nat h_dl : DL
  simp only [h_dl] at *
  have hlt : s.mem.readLE (s.mem.readLE ((s.regs 28).toNat + 48) 8 + 279) 1 < 128 := by omega
  janus_run [rotateRight_zero64, sext8_and255, ofNat_and255, setWidth32_ofNat, ofNat32_eq_zero,
    sext32_add_mod, sext8_add_mod, sext8_add_mod', hlt, hc0] calls [hu]
  rename_i _ _ _ _ m hfr hkey hlk _
  have e1 : m.readLE ((s.regs 28).toNat + 48) 8 = s.mem.readLE ((s.regs 28).toNat + 48) 8 := by
    janus_simp
  rw [e1] at hlk
  refine ⟨_, _, _, _, by ret_state, by janus_frame, ?_, ?_, ?_⟩
  all_goals janus_simp
  · exact hlk
  · exact hkey

end PrintFn
