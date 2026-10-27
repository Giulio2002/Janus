import ChainArm.Tail

/-!
# `Chain`, third segment (arm64): `bx.N = n`, the second `memmove`, then `Tail`

From the return of `makeslice` (the new array `t` in `X0`, its block in the live set): stores `n` in
`bx.N`, copies `min(len src, n)` words of `src` into `t` (the live `memmove`: a live destination, the
view does not change) unless `t = src`, and continues with `ChainArm.tail`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ChainArm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mid2 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl sp sl bx n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hmv : MemmoveLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b L dp dl sp sl bx n s) (S : State) (hrel : Rel R ret dp dl sp sl bx n s S)
    (hpc : S.pc = BitVec.ofNat 64 pcMid2) (h3 : S.regs 3 = n) (h4 : S.regs 4 = bx)
    (htR : InRanges (S.regs 0).toNat (blockSize (8 * n.toNat) true) R.rt)
    (hacc : s.mem.accessible (S.regs 0).toNat (blockSize (8 * n.toNat) true) true = true)
    (hbt : (S.regs 0).toNat + blockSize (8 * n.toNat) true ≤ 2 ^ 48)
    (hat1 : Apart (S.regs 0).toNat (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat))
    (hat2 : Apart (S.regs 0).toNat (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat))
    (hat3 : Apart (S.regs 0).toNat (blockSize (8 * n.toNat) true) bx.toNat 16)
    (hinv : R.inv (b - blockSize (8 * n.toNat) true)
      (L ++ [((S.regs 0).toNat, (S.regs 0).toNat + blockSize (8 * n.toNat) true)]) (s.regs 28).toNat
      (view R.rt (L ++ [((S.regs 0).toNat, (S.regs 0).toNat + blockSize (8 * n.toNat) true)]) S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b dp dl sp sl bx n s s') := by
  obtain ⟨t, h0⟩ : ∃ t, S.regs 0 = t := ⟨_, rfl⟩
  rw [h0] at htR hacc hbt hat1 hat2 hat3 hinv
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
  have hst := htR.apart hout
  have hgt := htR.apart hgr
  unfold Apart at hap1 hap2 hap3 hgd hgb hat1 hat2 hat3 hst hgt
  have hobx := hOut _ _ hinb
  have hodp := hOut _ _ hind
  have hosp := hOut _ _ hins
  clear hd hflag hty1 hok1 hok2 hok3 hn hn2 hdl0 hsl0 hdl hsl hbud hinv0 hap1 hap2 hap3
  janus_run until [pcTail] calls [hmv]
  all_goals (refine tail impl R b L dp dl sp sl bx n ret hret s hwb hpre _ ?_ t ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | exact hat1
    | exact hat2
    | exact hat3
    | exact htR
    | (with_reducible assumption)
    | janus_live
    | (janus_simp; done)
    | janus_frame
    | skip

end ChainArm
