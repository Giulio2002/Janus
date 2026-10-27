import ChainAmd.Defs

/-!
# `Chain`, last segment (amd64): the bounds check, the barrier flag, `gcWriteBarrier2`, `bx.P = t`, `RET`

From `TESTQ CX, CX` (`n` in `RCX`, `bx` in `RDX`, the new array `t` in `RAX`, `bx.N = n` already
stored): both branches of the write-barrier flag, the barrier call (`WbLiveContract64`) on the
flag-set branch, and the store of `t` into `bx.P`. The live set is the caller's `L` with `t`'s block.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ChainAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl sp sl bx n : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b L dp dl sp sl bx n s) (S : State) (hrel : Rel R ret dp dl sp sl bx n s S)
    (t : BitVec 64) (hpc : S.rip = BitVec.ofNat 64 pcTail) (h0 : S.regs 0 = t) (h1 : S.regs 1 = n)
    (h2 : S.regs 2 = bx) (h_rdn : S.mem.readLE (bx.toNat + 8) 8 = n.toNat)
    (htR : InRanges t.toNat (blockSize (8 * n.toNat) true) R.rt)
    (hat1 : Apart t.toNat (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat))
    (hat2 : Apart t.toNat (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat))
    (hat3 : Apart t.toNat (blockSize (8 * n.toNat) true) bx.toNat 16)
    (hinv : R.inv (b - blockSize (8 * n.toNat) true)
      (L ++ [(t.toNat, t.toNat + blockSize (8 * n.toNat) true)]) (s.regs 14).toNat
      (view R.rt (L ++ [(t.toNat, t.toNat + blockSize (8 * n.toNat) true)]) S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b dp dl sp sl bx n s s') := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl,
    hok1, hok2, hok3, hok4, hinv0, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3,
    hgd, hgb, hbud⟩ := hpre
  obtain ⟨h4, h14, h5, hx, hx0, hdf, h_rd1, h_rd2, h_rd3, h_rd4, h_rd5, h_rd6, h_rd7, hfr⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hOut : ∀ a k, InRanges a k L →
      (a + k ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 72 ≤ a) := by
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
  janus64_data hd [hw, hacd, hacb]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  janus64_run calls [hwb]
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
    | (janus64_simp; done)
    | janus_frame

end ChainAmd
