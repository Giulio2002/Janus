import ChainArm.Mid2

/-!
# `Chain`, second segment (arm64): `makeslice`, then `Mid2`

From the join after the first `memmove` (`X7 = n`): `makeslice(type:uint64, n, n)` (the live contract:
a fresh array `t` outside the live set, the invariant for the live set with `t`), then
`ChainArm.mid2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ChainArm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mid1 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl sp sl bx n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hmv : MemmoveLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b L dp dl sp sl bx n s) (S : State) (hrel : Rel R ret dp dl sp sl bx n s S)
    (hpc : S.pc = BitVec.ofNat 64 pcMid1) (h7 : S.regs 7 = n)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b dp dl sp sl bx n s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl,
    hok1, hok2, hok3, hok4, hinv0, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3,
    hgd, hgb, hbud⟩ := hpre'
  obtain ⟨hsp, h28, h29, h18, h_rd1, h_rd2, h_rd3, h_rd4, h_rd5, h_rd6, h_rd7, hfr⟩ := hrel
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hal' : S.sp.toNat % 16 = 0 := by omega
  have hOut : ∀ a k, InRanges a k L → (a + k ≤ s.sp.toNat - 4152 ∨ s.sp.toNat + 72 ≤ a) := by
    intro a k h
    obtain ⟨r, hr, h3, h4⟩ := h
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  unfold Apart at hap1 hap2 hap3 hgd hgb
  have hobx := hOut _ _ hinb
  have hodp := hOut _ _ hind
  have hosp := hOut _ _ hins
  janus_data hd [hw, hacd, hacb]
  janus_eval_nat h_u : u64Type
  rw [h_u] at hty1 hok1
  clear hflag hok2 hok3 hinv0 hdl0 hsl0 hdl hsl
  janus_run until [pcMid2] calls [hmk.pos]
  all_goals (refine mid2 impl R b L dp dl sp sl bx n ret hret s hmv hwb hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals (try janus_simp)
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | exact MemFrame.trans hfr ‹MemFrame S.mem _ _› (by
        intro a n h
        refine ⟨h, ?_⟩
        revert h
        simp only [Janus.outside_cons, Janus.outside_nil, Janus.outside_append, and_true, and_imp]
        intros
        janus_clear_irrel2
        repeat' apply And.intro
        all_goals first | omega | assumption)
    | janus_live

end ChainArm
