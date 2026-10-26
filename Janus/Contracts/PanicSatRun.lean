import Janus.Contracts.PanicSatEntry

/-!
# `gopanic` and `Goexit`: the model engine meets the contracts (arm64)
-/

set_option linter.constructorNameAsVariable false

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel Janus.Spec.Map

section gp
variable {p : Program}

set_option maxHeartbeats 0 in
theorem gopanic_run (hp : EngineAt p) (T : List FuncInfo) (hT : TOK T) :
    GopanicContract p eGopanic (P0 T RPa) U0 T := by
  intro s fi hpc hfind ⟨hpre, hx0, hroom, hbaq, hfo⟩
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, ⟨h30a, h30b, hal, hst, h8, hs48, hacc⟩, hout⟩ := hpre
  have henv0 : Env0 T s.mem := henv
  simp only [P0_depth, P0_priv] at hst hacc hout hs48
  have hB := henv0.acc
  have hroom0 : 0 < room0 s.mem := hroom
  obtain ⟨hnp8, hnd8, hcap⟩ := room0_pos hroom0
  have hsp64 : s.sp.toNat < 2 ^ 64 := s.sp.isLt
  have hspB : s.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s.sp.toNat := by
    simp only [outside_cons, outside_nil, and_true] at hout; simp only [B] at *; omega
  have hacc96 : s.mem.accessible (s.sp.toNat - 96) 96 true = true :=
    Memory.accessible_mono _ hacc (by omega) (by omega)
  -- push the `_panic`
  obtain ⟨k, hk⟩ : ∃ k, npan s.mem = k := ⟨_, rfl⟩
  obtain ⟨kp, s1, hkp, hpc1, hq1⟩ := reachesRet_transfer hp (seg_gp_push s k hpc hB hk (by omega))
  obtain ⟨hsp1, h281, h181, h301, h101, hmf1, hnp1, e0, e8, e16, e24⟩ := hq1
  have hk8 : k < 8 := by rw [hk] at hnp8; exact hnp8
  have hws1 : ∀ a, (a = B + 8 ∨ (B + 0x28 ≤ a ∧ a + 8 ≤ B + 0x100) ∨ (B + 0x200 ≤ a ∧ a + 8 ≤ B + 0x1000)) →
      Outside a 8 [(B, B + 8), (panAt k, panAt k + 32)] := by
    intro a ha; simp only [outside_cons, outside_nil, and_true, panAt, B] at ha ⊢; omega
  have hrd1 : RdSame s.mem s1.mem := rdsame_of_frame hmf1 hws1
  have hnp1' : npan s1.mem ≤ 8 := by rw [hnp1]; omega
  obtain ⟨henv1, hdef1, hroom1⟩ := bundle3 henv0 hrd1 (by rw [hmf1.accessible]; exact hB) hnp1'
  have hpan1 : panics0 s1.mem =
      { arg := ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩, start := s.sp.toNat } :: panics0 s.mem := by
    rw [panics0_top (k := k) hnp1 hk8]
    have hl : panList s1.mem k = panList s.mem k := panList_frame hmf1 k (fun i hi => by
      simp only [outside_cons, outside_nil, and_true, panAt, B]; omega)
    rw [hl, panics0_eq, hk, Nat.min_eq_left (by omega)]
    simp only [decPan, e0, e8, e16, e24]
    simp
  have hsv1 : saved0 s1.mem = saved0 s.mem := by
    rw [saved0_eq, saved0_eq]
    have hr : ∀ a, (a = B + 0x10 ∨ a = B + 0x18 ∨ a = B + 0x20) → rd s1.mem a = rd s.mem a := fun a ha =>
      hmf1.readLE a 8 (by simp only [outside_cons, outside_nil, and_true, panAt, B] at ha ⊢; omega)
    rw [hr _ (Or.inl rfl), hr _ (Or.inr (Or.inl rfl)), hr _ (Or.inr (Or.inr rfl))]
  have hba1 : fi.openDefer.isSome → s1.mem.accessible (fi.bitsAt s1.sp.toNat) 1 false = true := fun h => by
    rw [hmf1.accessible, hsp1]; exact (hbaq h).1
  obtain ⟨kl, c, hkl, hcpc, hcsp, hc28, hc18, hmfl, hfmc⟩ := lookup_found hp T hT (mode := .panic) (by decide) s1 fi
    hpc1 henv1 (by rw [hsp1]; exact hal) (by rw [hsp1]; omega) (by rw [hsp1]; omega)
    (by rw [hmf1.accessible, hsp1]; exact hacc96) (by rw [hsp1]; exact hspB) (by rw [h301]; exact hfind)
    (by rw [h101]; rfl) hba1
  have hbyte : fi.openDefer.isSome → s1.mem.readLE (fi.bitsAt s.sp.toNat) 1 = s.mem.readLE (fi.bitsAt s.sp.toNat) 1 :=
    fun h => hmf1.readLE _ _ (by
      have := (hbaq h).2
      simp only [P0_priv, outside_cons, outside_nil, and_true] at this
      simp only [outside_cons, outside_nil, and_true, panAt, B] at this ⊢; omega)
  have hFF : frameOf fi s1.sp.toNat s1.mem = frameOf fi s.sp.toNat s.mem := by
    rw [hsp1]; unfold frameOf
    cases hod : fi.openDefer with
    | none => rfl
    | some _ => simp only [hbyte (by rw [hod]; rfl)]
  rw [hFF, h181] at hfmc
  have hl := P0_laws T RPa
  have hfiT : fi ∈ T := by
    rw [find_eq] at hfind; exact List.mem_of_find?_eq_some hfind
  obtain ⟨t1, t2, t3, t4, t5⟩ := hT fi hfiT
  have hcs : c.sp.toNat = s.sp.toNat - 96 := by
    rw [hcsp, hsp1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmfl' : MemFrame s1.mem c.mem [(s.sp.toNat - 96, s.sp.toNat - 16)] := by rw [← hsp1]; exact hmfl
  have hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) (frameOf fi s.sp.toNat s.mem) ++
      bitsWin (frameOf fi s.sp.toNat s.mem)) :=
    hmf1.trans hmfl' fun a n h => by
      simp only [outside_append, P0_priv, outside_cons, outside_nil, and_true, rtWin, frameOf, P0_depth, panAt, B] at h ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h
      omega
  have hagc : Agrees s1.mem c.mem [(B, B + 0x1000)] := Agrees.of_memFrame hmfl' fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [outside_cons, outside_nil, and_true]
    simp only [B] at *; omega
  have henvc : Env0 T c.mem := hl.env_frame _ _ henv1 hagc
  have hdefc : defers0 c.mem = defers0 s.mem := (hl.defers_frame s1.mem c.mem 0 hagc).trans hdef1
  have hpanc : panics0 c.mem = { arg := ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩, start := s.sp.toNat } :: panics0 s.mem :=
    (hl.panics_frame s1.mem c.mem 0 hagc).trans hpan1
  have hsvc : saved0 c.mem = saved0 s.mem := (hl.saved_frame s1.mem c.mem 0 hagc).trans hsv1
  have hroomc : room0 c.mem = room0 s1.mem := hl.room_frame s1.mem c.mem 0 hagc
  have hroomc' : room0 s.mem - 1 ≤ room0 c.mem := by
    rw [hroomc, hroom1, room0_eq s.mem, hnp1, hk]
    omega
  have hrdboth : ∀ a n, Outside a n [(B, B + 0x1000)] → s.sp.toNat ≤ a → c.mem.readLE a n = s.mem.readLE a n := by
    intro a n ho hsa
    have e1 : s1.mem.readLE a n = s.mem.readLE a n := hmf1.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true, panAt, B] at ho ⊢; omega)
    have e2 : c.mem.readLE a n = s1.mem.readLE a n := hmfl'.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)
    rw [e2, e1]
  have hba : ∀ ba sa, (frameOf fi s.sp.toNat s.mem).openAt = some (ba, sa) → c.mem.readLE ba 1 = s.mem.readLE ba 1 := by
    intro ba sa hF
    have h := hfo.1
    rw [hF] at h
    obtain ⟨-, -, hb3, hb4, -⟩ := h
    simp only [P0_priv] at hb3
    exact hrdboth ba 1 hb3 hb4
  have hcur : curItems c.mem (frameOf fi s.sp.toNat s.mem)
      (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) = frameItems s.mem (frameOf fi s.sp.toNat s.mem) (defers0 s.mem) := by
    have hc1 : curItems c.mem (frameOf fi s.sp.toNat s.mem) (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) =
        curItems s.mem (frameOf fi s.sp.toNat s.mem) (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) := by
      refine curItems_congr (m := s.mem) (m' := c.mem) hdefc fun ba sa hF _ => ⟨hba ba sa hF, fun i hi => ?_⟩
      have h := hfo.1
      rw [hF] at h
      obtain ⟨-, -, -, -, h5, -⟩ := h
      obtain ⟨-, -, -, a4, a5⟩ := h5 i hi
      simp only [P0_priv] at a5
      exact hrdboth _ 8 a5 a4
    rw [hc1]
    refine curItems_entry _ _ _ fun h0 => ?_
    cases hF : (frameOf fi s.sp.toNat s.mem).openAt with
    | none => rfl
    | some _ => rw [hF] at h0; simp at h0
  have hI := Inv0.init (T := T) (s := s) (c := c) (F := frameOf fi s.sp.toNat s.mem) (mode := .panic)
    (x28 := s.regs 28) (x18 := s.regs 18) (lr := 0) (x29 := 0)
    (ph := if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0)
    (ch := { arg := ⟨(s.regs 0).toNat, (s.regs 1).toNat⟩, start := s.sp.toNat } :: panics0 s.mem)
    (rm := room0 s.mem - 1) hfo hal (by show s.sp.toNat + 8 ≤ 2 ^ 48; omega) (by show 96 ≤ s.sp.toNat; omega) hspB
    (by show s.sp.toNat + fi.frame < 2 ^ 64; omega) ⟨by show (fi.entry + fi.deferreturn) % 4 = 0; exact t3,
      by show fi.entry + fi.deferreturn < 2 ^ 48; exact t2⟩
    (fun h => absurd h (by decide)) (by show c.sp.toNat + 96 = s.sp.toNat; omega) (by rw [hc28, h281])
    (by show s.mem.accessible (s.sp.toNat - 96) 96 true = true; exact hacc96) hmf hfmc henvc hpanc hroomc'
    (fun h => absurd h (by decide)) hdefc hba hcur
  have hloop := engine_loop (p := p) (T := T) (m0 := s.mem) (F := frameOf fi s.sp.toNat s.mem)
    (items0 := frameItems s.mem (frameOf fi s.sp.toNat s.mem) (defers0 s.mem)) (ds0 := defers0 s.mem) (mode := .panic)
    (x28 := s.regs 28) (x18 := s.regs 18) (lr := 0) (x29 := 0) hp
    (Fin := LeftFrame (P0 T RPa) U0 (s.regs 28) (frameOf fi s.sp.toNat s.mem) ((P0 T RPa).defers s.mem (gOf s)))
    (fun ch rm c c' d hm hf => LeftFrame.prefix hm hf)
    (fun c ch rm hpc h18 hI _ hend => left_fin hp (by decide) hI hpc h18 hend) _ c _ _ _ rfl hcpc
    (by rw [hc18, h181]) hI (fun _ => ⟨_, _, rfl, rfl, rfl⟩)
  rw [hcur] at hloop
  exact Engine.of_prefix (fun ch rm d hf => LeftFrame.prefix hmf hf) (hkp.trans hkl) hmf hsvc rfl hloop


set_option maxHeartbeats 0 in
theorem goexit_run (hp : EngineAt p) (T : List FuncInfo) (hT : TOK T) :
    GoexitContract p eGoexit (P0 T RPa) U0 T := by
  intro s fi hpc hfind ⟨hpre, hroom, hbaq, hfo⟩
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, ⟨h30a, h30b, hal, hst, h8, hs48, hacc⟩, hout⟩ := hpre
  have henv0 : Env0 T s.mem := henv
  simp only [P0_depth, P0_priv] at hst hacc hout hs48
  have hB := henv0.acc
  have hroom0 : 0 < room0 s.mem := hroom
  obtain ⟨hnp8, hnd8, hcap⟩ := room0_pos hroom0
  have hsp64 : s.sp.toNat < 2 ^ 64 := s.sp.isLt
  have hspB : s.sp.toNat ≤ B ∨ B + 0x1000 + 96 ≤ s.sp.toNat := by
    simp only [outside_cons, outside_nil, and_true] at hout; simp only [B] at *; omega
  have hacc96 : s.mem.accessible (s.sp.toNat - 96) 96 true = true :=
    Memory.accessible_mono _ hacc (by omega) (by omega)
  -- push the `_panic`
  obtain ⟨k, hk⟩ : ∃ k, npan s.mem = k := ⟨_, rfl⟩
  obtain ⟨kp, s1, hkp, hpc1, hq1⟩ := reachesRet_transfer hp (seg_ge_push s k hpc hB hk (by omega))
  obtain ⟨hsp1, h281, h181, h301, h101, hmf1, hnp1, e0, e8, e16, e24⟩ := hq1
  have hk8 : k < 8 := by rw [hk] at hnp8; exact hnp8
  have hws1 : ∀ a, (a = B + 8 ∨ (B + 0x28 ≤ a ∧ a + 8 ≤ B + 0x100) ∨ (B + 0x200 ≤ a ∧ a + 8 ≤ B + 0x1000)) →
      Outside a 8 [(B, B + 8), (panAt k, panAt k + 32)] := by
    intro a ha; simp only [outside_cons, outside_nil, and_true, panAt, B] at ha ⊢; omega
  have hrd1 : RdSame s.mem s1.mem := rdsame_of_frame hmf1 hws1
  have hnp1' : npan s1.mem ≤ 8 := by rw [hnp1]; omega
  obtain ⟨henv1, hdef1, hroom1⟩ := bundle3 henv0 hrd1 (by rw [hmf1.accessible]; exact hB) hnp1'
  have hpan1 : panics0 s1.mem =
      { arg := ⟨0, 0⟩, goexit := true, start := s.sp.toNat } :: panics0 s.mem := by
    rw [panics0_top (k := k) hnp1 hk8]
    have hl : panList s1.mem k = panList s.mem k := panList_frame hmf1 k (fun i hi => by
      simp only [outside_cons, outside_nil, and_true, panAt, B]; omega)
    rw [hl, panics0_eq, hk, Nat.min_eq_left (by omega)]
    simp only [decPan, e0, e8, e16, e24]
    simp
  have hsv1 : saved0 s1.mem = saved0 s.mem := by
    rw [saved0_eq, saved0_eq]
    have hr : ∀ a, (a = B + 0x10 ∨ a = B + 0x18 ∨ a = B + 0x20) → rd s1.mem a = rd s.mem a := fun a ha =>
      hmf1.readLE a 8 (by simp only [outside_cons, outside_nil, and_true, panAt, B] at ha ⊢; omega)
    rw [hr _ (Or.inl rfl), hr _ (Or.inr (Or.inl rfl)), hr _ (Or.inr (Or.inr rfl))]
  have hba1 : fi.openDefer.isSome → s1.mem.accessible (fi.bitsAt s1.sp.toNat) 1 false = true := fun h => by
    rw [hmf1.accessible, hsp1]; exact (hbaq h).1
  obtain ⟨kl, c, hkl, hcpc, hcsp, hc28, hc18, hmfl, hfmc⟩ := lookup_found hp T hT (mode := .goexit) (by decide) s1 fi
    hpc1 henv1 (by rw [hsp1]; exact hal) (by rw [hsp1]; omega) (by rw [hsp1]; omega)
    (by rw [hmf1.accessible, hsp1]; exact hacc96) (by rw [hsp1]; exact hspB) (by rw [h301]; exact hfind)
    (by rw [h101]; rfl) hba1
  have hbyte : fi.openDefer.isSome → s1.mem.readLE (fi.bitsAt s.sp.toNat) 1 = s.mem.readLE (fi.bitsAt s.sp.toNat) 1 :=
    fun h => hmf1.readLE _ _ (by
      have := (hbaq h).2
      simp only [P0_priv, outside_cons, outside_nil, and_true] at this
      simp only [outside_cons, outside_nil, and_true, panAt, B] at this ⊢; omega)
  have hFF : frameOf fi s1.sp.toNat s1.mem = frameOf fi s.sp.toNat s.mem := by
    rw [hsp1]; unfold frameOf
    cases hod : fi.openDefer with
    | none => rfl
    | some _ => simp only [hbyte (by rw [hod]; rfl)]
  rw [hFF, h181] at hfmc
  have hl := P0_laws T RPa
  have hfiT : fi ∈ T := by
    rw [find_eq] at hfind; exact List.mem_of_find?_eq_some hfind
  obtain ⟨t1, t2, t3, t4, t5⟩ := hT fi hfiT
  have hcs : c.sp.toNat = s.sp.toNat - 96 := by
    rw [hcsp, hsp1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmfl' : MemFrame s1.mem c.mem [(s.sp.toNat - 96, s.sp.toNat - 16)] := by rw [← hsp1]; exact hmfl
  have hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) (frameOf fi s.sp.toNat s.mem) ++
      bitsWin (frameOf fi s.sp.toNat s.mem)) :=
    hmf1.trans hmfl' fun a n h => by
      simp only [outside_append, P0_priv, outside_cons, outside_nil, and_true, rtWin, frameOf, P0_depth, panAt, B] at h ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := h
      omega
  have hagc : Agrees s1.mem c.mem [(B, B + 0x1000)] := Agrees.of_memFrame hmfl' fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [outside_cons, outside_nil, and_true]
    simp only [B] at *; omega
  have henvc : Env0 T c.mem := hl.env_frame _ _ henv1 hagc
  have hdefc : defers0 c.mem = defers0 s.mem := (hl.defers_frame s1.mem c.mem 0 hagc).trans hdef1
  have hpanc : panics0 c.mem = { arg := ⟨0, 0⟩, goexit := true, start := s.sp.toNat } :: panics0 s.mem :=
    (hl.panics_frame s1.mem c.mem 0 hagc).trans hpan1
  have hsvc : saved0 c.mem = saved0 s.mem := (hl.saved_frame s1.mem c.mem 0 hagc).trans hsv1
  have hroomc : room0 c.mem = room0 s1.mem := hl.room_frame s1.mem c.mem 0 hagc
  have hroomc' : room0 s.mem - 1 ≤ room0 c.mem := by
    rw [hroomc, hroom1, room0_eq s.mem, hnp1, hk]
    omega
  have hrdboth : ∀ a n, Outside a n [(B, B + 0x1000)] → s.sp.toNat ≤ a → c.mem.readLE a n = s.mem.readLE a n := by
    intro a n ho hsa
    have e1 : s1.mem.readLE a n = s.mem.readLE a n := hmf1.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true, panAt, B] at ho ⊢; omega)
    have e2 : c.mem.readLE a n = s1.mem.readLE a n := hmfl'.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)
    rw [e2, e1]
  have hba : ∀ ba sa, (frameOf fi s.sp.toNat s.mem).openAt = some (ba, sa) → c.mem.readLE ba 1 = s.mem.readLE ba 1 := by
    intro ba sa hF
    have h := hfo.1
    rw [hF] at h
    obtain ⟨-, -, hb3, hb4, -⟩ := h
    simp only [P0_priv] at hb3
    exact hrdboth ba 1 hb3 hb4
  have hcur : curItems c.mem (frameOf fi s.sp.toNat s.mem)
      (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) = frameItems s.mem (frameOf fi s.sp.toNat s.mem) (defers0 s.mem) := by
    have hc1 : curItems c.mem (frameOf fi s.sp.toNat s.mem) (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) =
        curItems s.mem (frameOf fi s.sp.toNat s.mem) (if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0) := by
      refine curItems_congr (m := s.mem) (m' := c.mem) hdefc fun ba sa hF _ => ⟨hba ba sa hF, fun i hi => ?_⟩
      have h := hfo.1
      rw [hF] at h
      obtain ⟨-, -, -, -, h5, -⟩ := h
      obtain ⟨-, -, -, a4, a5⟩ := h5 i hi
      simp only [P0_priv] at a5
      exact hrdboth _ 8 a5 a4
    rw [hc1]
    refine curItems_entry _ _ _ fun h0 => ?_
    cases hF : (frameOf fi s.sp.toNat s.mem).openAt with
    | none => rfl
    | some _ => rw [hF] at h0; simp at h0
  have hI := Inv0.init (T := T) (s := s) (c := c) (F := frameOf fi s.sp.toNat s.mem) (mode := .goexit)
    (x28 := s.regs 28) (x18 := s.regs 18) (lr := 0) (x29 := 0)
    (ph := if (frameOf fi s.sp.toNat s.mem).openAt.isSome then 1 else 0)
    (ch := { arg := ⟨0, 0⟩, goexit := true, start := s.sp.toNat } :: panics0 s.mem)
    (rm := room0 s.mem - 1) hfo hal (by show s.sp.toNat + 8 ≤ 2 ^ 48; omega) (by show 96 ≤ s.sp.toNat; omega) hspB
    (by show s.sp.toNat + fi.frame < 2 ^ 64; omega) ⟨by show (fi.entry + fi.deferreturn) % 4 = 0; exact t3,
      by show fi.entry + fi.deferreturn < 2 ^ 48; exact t2⟩
    (fun h => absurd h (by decide)) (by show c.sp.toNat + 96 = s.sp.toNat; omega) (by rw [hc28, h281])
    (by show s.mem.accessible (s.sp.toNat - 96) 96 true = true; exact hacc96) hmf hfmc henvc hpanc hroomc'
    (fun h => absurd h (by decide)) hdefc hba hcur
  have hloop := engine_loop (p := p) (T := T) (m0 := s.mem) (F := frameOf fi s.sp.toNat s.mem)
    (items0 := frameItems s.mem (frameOf fi s.sp.toNat s.mem) (defers0 s.mem)) (ds0 := defers0 s.mem) (mode := .goexit)
    (x28 := s.regs 28) (x18 := s.regs 18) (lr := 0) (x29 := 0) hp
    (Fin := LeftFrame (P0 T RPa) U0 (s.regs 28) (frameOf fi s.sp.toNat s.mem) ((P0 T RPa).defers s.mem (gOf s)))
    (fun ch rm c c' d hm hf => LeftFrame.prefix hm hf)
    (fun c ch rm hpc h18 hI _ hend => left_fin hp (by decide) hI hpc h18 hend) _ c _ _ _ rfl hcpc
    (by rw [hc18, h181]) hI (fun h => absurd h (by decide))
  rw [hcur] at hloop
  exact Engine.of_prefix (fun ch rm d hf => LeftFrame.prefix hmf hf) (hkp.trans hkl) hmf hsvc rfl hloop

end gp

end Janus.Contracts.PanicSat
