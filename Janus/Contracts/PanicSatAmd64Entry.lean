import Janus.Contracts.PanicSatAmd64Lookup
import Janus.Contracts.PanicSatEntry


/-!
# `deferreturn`: the amd64 model engine meets the contract

The invariant at the first loop head (`Inv0.init`), the ends of the loops of `gopanic`/`Goexit`
(`left_fin`) and of `deferreturn` (`dr_fin`), and `deferreturn_run`. The x86-64 twin of
`Janus.Contracts.PanicSatEntry`.
-/

set_option linter.constructorNameAsVariable false

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Contracts.Panic (DeferMode Frame Item fnItems recItems openItems frameItems frameKeep bitsWin)
open Janus.Contracts.PanicSat (modeCode curItems topBit curItems_zero curItems_ne curItems_congr keep_apart_fo
  saved0_none_iff bundle2 bundle3 curItems_entry rdsame_of_frame fin_items R2)
open Janus.Spec.Map

/-- The invariant at the first loop head, from what the entry code did. -/
theorem Inv0.init {T : List FuncInfo} {s c : State} {F : Frame} {mode : DeferMode} {g bp : W64}
    {lr : Nat} {ph : Nat} {ch : List PanicRec} {rm : Nat}
    (hfo : FrameOK (P0 T RPa) s.mem F (frameItems s.mem F (defers0 s.mem)))
    (hF1 : F.sp % 8 = 0) (hF2 : F.sp ≤ 2 ^ 48) (hF3 : 112 ≤ F.sp)
    (hspB : F.sp ≤ B ∨ B + 0x1000 + 112 ≤ F.sp)
    (hbd : F.bound + 8 < 2 ^ 64) (hbl : F.sp ≤ F.bound) (hres : F.resume < 2 ^ 47)
    (hlr : mode = .ret → lr < 2 ^ 47 ∧ s.mem.accessible (F.sp - 8) 8 false = true)
    (hc14 : c.regs 14 = g) (hc5 : mode = .ret → c.regs 5 = bp) (hcx : c.xmm 15 = 0) (hcdf : c.df = false)
    (hacc : s.mem.accessible (F.sp - 112) 104 true = true)
    (hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) F ++ bitsWin F))
    (hfm : FrameMem c.mem F mode ph lr)
    (henv : Env0 T c.mem) (hpan : panics0 c.mem = ch) (hroom : rm ≤ room0 c.mem)
    (hsv : mode = .ret → rd c.mem (B + 0x10) = 0) (hdef : defers0 c.mem = defers0 s.mem)
    (hba : ∀ ba sa, F.openAt = some (ba, sa) → c.mem.readLE ba 1 = s.mem.readLE ba 1)
    (hcur : curItems c.mem F ph = frameItems s.mem F (defers0 s.mem)) :
    Inv0 T s.mem F (frameItems s.mem F (defers0 s.mem)) (defers0 s.mem) mode g bp lr c ch rm ph := by
  refine ⟨hF1, hF2, hF3, by rw [hmf.accessible]; exact hacc, hc14, hc5, hcx, hcdf, hspB, hfm,
    fun hm => ⟨(hlr hm).1, by rw [hmf.accessible]; exact (hlr hm).2⟩, hbd, hbl, hres, henv, hpan, hroom, hsv,
    by rw [hdef], ?_, hfo, ?_, ?_⟩
  · exact (Agrees.of_memFrame hmf fun a ha => by
      obtain ⟨r, hr, h1, h2⟩ := ha
      obtain ⟨hr8, hro⟩ := keep_apart_fo hfo.1 r hr
      exact Outside.of_sub hro h1 (by omega))
  · intro ba sa hF i hi
    rw [hba ba sa hF] at hi; exact hi
  · intro it hit; rw [hcur] at hit; exact hit

section gp
variable {p : Program}

/-- The end of the loop of `gopanic` or `Goexit`: the runtime unwinds past the frame. -/
theorem left_fin (hp : EngineAt p) {T : List FuncInfo} {m0 : Memory} {F : Frame} {items0 : List Item}
    {ds0 : List DeferRec} {mode : DeferMode} (hm : mode ≠ .ret) {g bp : W64} {lr : Nat} {c : State}
    {ch : List PanicRec} {rm : Nat}
    (hI : Inv0 T m0 F items0 ds0 mode g bp lr c ch rm 0)
    (hL : (c.regs 4).toNat + 104 = F.sp)
    (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ F.sp) :
    ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ LeftFrame (P0 T RPa) U1 g F ds0 ch rm c d := by
  obtain ⟨k, d, hk, hmem, -, h14, hx, hdf, -, hret⟩ := step_fin hp hI hL hpc rfl hend
  obtain ⟨hpcd, hspd⟩ := hret hm
  have hfi := fin_items hI.env hend
  refine ⟨k, d, hk, ⟨⟨hpcd, hspd, ?_⟩, hx, hdf⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h14]; exact (ofNat_toNat_self g).symm
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

theorem add8_ofNat (x : W64) (h : x.toNat + 8 < 2 ^ 64) : x + 8 = BitVec.ofNat 64 (x.toNat + 8) := by
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [BitVec.toNat_add, h8, BitVec.toNat_ofNat]

/-- The end of `deferreturn`'s loop. -/
theorem dr_fin (hp : EngineAt p) (s : State) {c : State} {ch : List PanicRec} {rm : Nat}
    (hI : Inv0 T s.mem (retFrame (P0 T RPa) s) (frameItems s.mem (retFrame (P0 T RPa) s) ((P0 T RPa).defers s.mem (gOf s)))
      ((P0 T RPa).defers s.mem (gOf s)) .ret (s.regs 14) (s.regs 5) (s.mem.readLE (s.regs 4).toNat 8) c ch rm 0)
    (hL : (c.regs 4).toNat + 104 = (retFrame (P0 T RPa) s).sp)
    (hpc : c.rip = BitVec.ofNat 64 eLH)
    (hend : ndef c.mem = 0 ∨ ∃ j, ndef c.mem = j + 1 ∧ recSp c.mem j ≠ (retFrame (P0 T RPa) s).sp) :
    ∃ k d, Janus.Amd64.Program.Steps p c k d ∧ RetFin (P0 T RPa) s ((P0 T RPa).defers s.mem (gOf s)) ch rm c d := by
  obtain ⟨k, d, hk, hmem, h5, h14, hx, hdf, hret, -⟩ := step_fin hp hI hL hpc rfl hend
  obtain ⟨hpcd, hspd⟩ := hret rfl
  have hfi := fin_items hI.env hend
  obtain ⟨hlr1, -⟩ := hI.hlr rfl
  have hsp8 : (s.regs 4).toNat + 8 < 2 ^ 64 := by
    have : (s.regs 4).toNat + 8 ≤ 2 ^ 48 := hI.hi
    omega
  refine ⟨k, d, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcd, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  · rw [hspd]; exact (add8_ofNat _ hsp8).symm
  · exact h14
  · exact h5 rfl
  · exact hx
  · exact hdf
  · rw [hmem]; exact MemFrame.refl _ _
  · show Env0 T d.mem; rw [hmem]; exact hI.env
  · show panics0 d.mem = ch; rw [hmem]; exact hI.pan
  · show defers0 d.mem = frameRest (retFrame (P0 T RPa) s).sp ((P0 T RPa).defers s.mem (gOf s))
    rw [hmem, ← hfi.2]; exact hI.chn
  · show saved0 d.mem = none; rw [hmem]; exact (saved0_none_iff _).2 (hI.sv rfl)
  · rfl
  · show rm ≤ room0 d.mem; rw [hmem]; exact hI.room

-- `Engine` is a `match` over the whole state: elaborating `engine_loop` against it would `whnf` it
-- (30-60 s) for the expected type's sake
attribute [local irreducible] Janus.Contracts.PanicAmd64.Engine in
set_option maxHeartbeats 0 in
theorem deferreturn_run (hp : EngineAt p) :
    DeferreturnContract p eDeferreturn (P0 T RPa) U1 := by
  intro s hpc ⟨hpre, hfo⟩
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hdep, hs48, hacc, hx0, hdf0, hra, hout⟩ := hpre
  have henv0 : Env0 T s.mem := henv
  simp only [P0_depth, P0_priv, Nat.mul_zero, Nat.add_zero] at hdep hacc hout hs48
  have hB := henv0.acc
  have hsp64 : (s.regs 4).toNat < 2 ^ 64 := (s.regs 4).isLt
  have hspB : (s.regs 4).toNat + 8 ≤ B ∨ B + 0x1000 + 112 ≤ (s.regs 4).toNat + 8 := by
    simp only [outside_cons, outside_nil, and_true] at hout; simp only [B] at *; omega
  have hacc104 : s.mem.accessible ((s.regs 4).toNat - 104) 104 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hraacc0 : s.mem.accessible (s.regs 4).toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hraacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ hraacc0
  have hseg := seg_dr_entry s hpc hal hs48 (by omega) hacc104 hB hspB
  obtain ⟨k0, c, hk0, -, hq⟩ := reachesRet_transfer hp hseg
  obtain ⟨hcpc, hc4, hc5, hc14, hcx, hcdf, hmf0, hsv0, w0, w8, w16, w24, w32, w40, w48⟩ := hq
  have hcs : (c.regs 4).toNat = (s.regs 4).toNat - 96 := by
    rw [hc4, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hLc : (c.regs 4).toNat + 104 = (retFrame (P0 T RPa) s).sp := by
    show (c.regs 4).toNat + 104 = (s.regs 4).toNat + 8; omega
  -- the frame
  have hsaved : saved0 s.mem = if rd s.mem (B + 0x10) = 0 then none else
      some (rd s.mem (B + 0x18), rd s.mem (B + 0x20)) := saved0_eq s.mem
  have hmf : MemFrame s.mem c.mem ((P0 T RPa).priv ++ rtWin (P0 T RPa) (retFrame (P0 T RPa) s) ++
      bitsWin (retFrame (P0 T RPa) s)) := hmf0.mono fun a n h => by
    simp only [outside_append, P0_priv, outside_cons, outside_nil, and_true, rtWin, retFrame, P0_depth, fspOf] at h ⊢
    obtain ⟨⟨h1, h2⟩, -⟩ := h
    simp only [B] at *; omega
  have hlrr : c.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := hmf0.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]; simp only [B] at *; omega)
  have e96 : (retFrame (P0 T RPa) s).sp - 104 = (s.regs 4).toNat - 96 := by
    show (s.regs 4).toNat + 8 - 104 = (s.regs 4).toNat - 96; omega
  have hfm : FrameMem c.mem (retFrame (P0 T RPa) s) .ret (rd s.mem (B + 0x10))
      (s.mem.readLE (s.regs 4).toNat 8) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_⟩
    · rw [e96]; exact w0
    · rw [e96]; exact w8
    · rw [e96]; exact w16
    · rw [e96]; exact w24
    · rw [e96]; exact w32
    · intro ba sa hF
      have hF' : saved0 s.mem = some (ba, sa) := hF
      rw [hsaved] at hF'
      split at hF'
      · cases hF'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hF'
        obtain ⟨rfl, rfl⟩ := hF'
        rw [e96]; exact ⟨w40, w48⟩
    · rw [e96, show (s.regs 4).toNat - 96 + 96 = (s.regs 4).toNat by omega]; exact hlrr
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
    have h := hfo.1.1
    rw [hF] at h
    obtain ⟨-, -, hb3, hb4, -⟩ := h
    refine hmf0.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    simp only [P0_priv, outside_cons, outside_nil, and_true] at hb3
    simp only [retFrame, fspOf] at hb4
    simp only [B] at *; omega
  have hcur : curItems c.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) =
      frameItems s.mem (retFrame (P0 T RPa) s) (defers0 s.mem) := by
    have hc1 : curItems c.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) =
        curItems s.mem (retFrame (P0 T RPa) s) (rd s.mem (B + 0x10)) := by
      refine curItems_congr (m := s.mem) (m' := c.mem) hdefc fun ba sa hF _ => ⟨hba ba sa hF, fun i hi => ?_⟩
      have h := hfo.1.1
      rw [hF] at h
      obtain ⟨-, -, -, -, h5, -⟩ := h
      obtain ⟨-, -, -, a4, a5⟩ := h5 i hi
      refine hmf0.readLE _ _ ?_
      simp only [P0_priv, outside_cons, outside_nil, and_true] at a5
      simp only [outside_cons, outside_nil, and_true]
      simp only [retFrame, fspOf] at a4
      simp only [B] at *; omega
    rw [hc1]
    refine curItems_entry _ _ _ fun h0 => ?_
    show saved0 s.mem = none
    rw [hsaved, if_pos h0]
  have hI := Inv0.init (T := T) (s := s) (c := c) (F := retFrame (P0 T RPa) s) (mode := .ret) (g := s.regs 14)
    (bp := s.regs 5) (lr := s.mem.readLE (s.regs 4).toNat 8) (ph := rd s.mem (B + 0x10))
    (ch := panics0 s.mem) (rm := room0 s.mem) hfo (by show ((s.regs 4).toNat + 8) % 8 = 0; omega)
    (by show (s.regs 4).toNat + 8 ≤ 2 ^ 48; omega) (by show 112 ≤ (s.regs 4).toNat + 8; omega)
    (by show (s.regs 4).toNat + 8 ≤ B ∨ B + 0x1000 + 112 ≤ (s.regs 4).toNat + 8; exact hspB)
    (by show (s.regs 4).toNat + 8 + 8 < 2 ^ 64; omega) (by show (s.regs 4).toNat + 8 ≤ (s.regs 4).toNat + 8; omega)
    (by show (0 : Nat) < 2 ^ 47; omega)
    (fun _ => ⟨hra, by show s.mem.accessible ((s.regs 4).toNat + 8 - 8) 8 false = true
                       rw [show (s.regs 4).toNat + 8 - 8 = (s.regs 4).toNat by omega]; exact hraacc⟩)
    hc14 (fun _ => hc5) (by rw [hcx]; exact hx0) (by rw [hcdf]; exact hdf0)
    (by show s.mem.accessible ((s.regs 4).toNat + 8 - 112) 104 true = true
        rw [show (s.regs 4).toNat + 8 - 112 = (s.regs 4).toNat - 104 by omega]; exact hacc104)
    hmf hfm henvc hpanc (by rw [hroomc]; exact Nat.le_refl _) (fun _ => hsv0) hdefc hba hcur
  have hloop := engine_loop (p := p) (T := T) (m0 := s.mem) (F := retFrame (P0 T RPa) s)
    (items0 := frameItems s.mem (retFrame (P0 T RPa) s) (defers0 s.mem)) (ds0 := defers0 s.mem) (mode := .ret)
    (g := s.regs 14) (bp := s.regs 5) (lr := s.mem.readLE (s.regs 4).toNat 8) hp
    (Fin := RetFin (P0 T RPa) s ((P0 T RPa).defers s.mem (gOf s)))
    (fun ch rm c c' d hm _ hf => RetFin.prefix hm hf)
    (fun c ch rm hpc hL hI _ hend => dr_fin hp s hI hL hpc hend) _ c (panics0 s.mem) (room0 s.mem)
    (rd s.mem (B + 0x10)) rfl hcpc hLc hI (fun h => absurd h (by decide))
  rw [hcur] at hloop
  exact Engine.of_prefix_ret (fun ch rm d hf => RetFin.prefix (hmf) hf) hk0 hmf rfl hloop

end dr

end Janus.Contracts.PanicSatAmd64
