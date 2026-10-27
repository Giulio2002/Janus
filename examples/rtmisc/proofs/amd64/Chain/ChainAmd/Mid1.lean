import ChainAmd.Mid2

/-!
# `Chain`, second segment (amd64): `makeslice`, then `Mid2`

From the join after the first `memmove` (`R10 = n`): `makeslice(type:uint64, n, n)` (the live contract:
a fresh array `t` outside the live set, the invariant for the live set with `t`), then
`ChainAmd.mid2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ChainAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mid1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl sp sl bx n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b L dp dl sp sl bx n s) (S : State) (hrel : Rel R ret dp dl sp sl bx n s S)
    (hpc : S.rip = BitVec.ofNat 64 pcMid1) (h10 : S.regs 10 = n)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b dp dl sp sl bx n s s') := by
  have hpre' := hpre
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl,
    hok1, hok2, hok3, hok4, hinv0, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3,
    hgd, hgb, hbud⟩ := hpre'
  obtain ⟨h4, h14, h5, hx, hx0, hdf, h_rd1, h_rd2, h_rd3, h_rd4, h_rd5, h_rd6, h_rd7, hfr⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 40 := by rw [h4, BitVec.toNat_sub]; simp; omega
  have hal' : (S.regs 4).toNat % 8 = 0 := by omega
  have hOut : ∀ a k, InRanges a k L →
      (a + k ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 72 ≤ a) := by
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
  janus64_data hd [hw, hacd, hacb]
  janus_eval_nat h_u : u64Type
  rw [h_u] at hty1 hok1
  clear hflag hok2 hok3 hinv0 hdl0 hsl0 hdl hsl
  janus64_run until [pcMid2] calls [hmk.pos]
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

end ChainAmd
