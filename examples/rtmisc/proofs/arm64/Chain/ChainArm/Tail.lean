import ChainArm.Defs

/-!
# `Chain`, last segment (arm64): the bounds check, the barrier flag, `gcWriteBarrier2`, `bx.P = t`, `RET`

From `CBZ X3` (`n` in `X3`, `bx` in `X4`, the new array `t` in `X0`, `bx.N = n` already stored): both
branches of the write-barrier flag, the barrier call (`WbLiveContract`) on the flag-set branch,
and the store of `t` into `bx.P`. The live set is the caller's `L` with `t`'s block.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ChainArm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl sp sl bx n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b L dp dl sp sl bx n s) (S : State) (hrel : Rel R ret dp dl sp sl bx n s S)
    (t : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 pcTail) (h0 : S.regs 0 = t) (h3 : S.regs 3 = n)
    (h4 : S.regs 4 = bx) (h_rdn : S.mem.readLE (bx.toNat + 8) 8 = n.toNat)
    (htR : InRanges t.toNat (blockSize (8 * n.toNat) true) R.rt)
    (hat1 : Apart t.toNat (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat))
    (hat2 : Apart t.toNat (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat))
    (hat3 : Apart t.toNat (blockSize (8 * n.toNat) true) bx.toNat 16)
    (hinv : R.inv (b - blockSize (8 * n.toNat) true)
      (L ++ [(t.toNat, t.toNat + blockSize (8 * n.toNat) true)]) (s.regs 28).toNat
      (view R.rt (L ++ [(t.toNat, t.toNat + blockSize (8 * n.toNat) true)]) S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b dp dl sp sl bx n s s') := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl,
    hok1, hok2, hok3, hok4, hinv0, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3,
    hgd, hgb, hbud⟩ := hpre
  obtain ⟨hsp, h28, h29, h18, h_rd1, h_rd2, h_rd3, h_rd4, h_rd5, h_rd6, h_rd7, hfr⟩ := hrel
  have hOut : ∀ a k, InRanges a k L → (a + k ≤ s.sp.toNat - 4152 ∨ s.sp.toNat + 72 ≤ a) := by
    intro a k h
    obtain ⟨r, hr, h3, h4⟩ := h
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  unfold Apart at hap1 hap2 hap3 hgd hgb hat1 hat2 hat3
  have hst := htR.apart hout
  have hgt := htR.apart hgr
  unfold Apart at hst hgt
  have hobx := hOut _ _ hinb
  have hodp := hOut _ _ hind
  have hosp := hOut _ _ hins
  janus_data hd [hw, hacd, hacb]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  janus_run calls [hwb]
  all_goals (try unfold Post)
  all_goals (refine ⟨t.toNat, ?_, ?_⟩)
  all_goals first | (simp; done) | skip
  all_goals janus_split_and
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (refine ⟨b - blockSize (8 * n.toNat) true, L ++ [(t.toNat, t.toNat + blockSize (8 * n.toNat) true)],
        Nat.le_refl _, ?_⟩)
    | skip
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | janus_live
    | exact InRanges.append_right _ (InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _))
    | exact InRanges.append_left hind _
    | exact InRanges.append_left hins _
    | exact InRanges.append_left hinb _
    | (janus_simp; done)
    | janus_frame

end ChainArm
