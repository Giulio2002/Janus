import ThreeAmd.Defs

/-!
# `Three`, last segment (amd64): the barrier flag, `gcWriteBarrier2`, `c.P = &b[0]`, the results

From the load of the barrier flag (after the second `makeslice` returned `b` in `X0`): both branches
of the flag, the barrier call (`WbLiveContract`) on the flag-set branch, the store of `b` into `c.P`,
and the reload of the three results from their spill slots. `a`, `c`, `b` are in the live set.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ThreeAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n x : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b n s) (S : State) (hrel : Rel R ret n x s S)
    (hpc : S.rip = BitVec.ofNat 64 pcS3)
    (pa pc : Nat) (pb : BitVec 64) (h0 : S.regs 0 = pb)
    (h_rdA : S.mem.readLE ((s.regs 4).toNat - 16) 8 = pa) (h_rdC : S.mem.readLE ((s.regs 4).toNat - 24) 8 = pc)
    (h_rdx : S.mem.readLE pa 8 = x.toNat) (hacC : s.mem.accessible pc 16 true = true) (hbc48 : pc + 16 ≤ 2 ^ 48) (hpa48 : pa + blockSize (8 * n.toNat) true ≤ 2 ^ 48)
    (hRa : InRanges pa (blockSize (8 * n.toNat) true) R.rt)
    (hRb : InRanges pb.toNat (blockSize (8 * n.toNat) true) R.rt) (hRc : InRanges pc 16 R.rt)
    (hab : Apart pa (blockSize (8 * n.toNat) true) pb.toNat (blockSize (8 * n.toNat) true))
    (hac : Apart pa (blockSize (8 * n.toNat) true) pc 16)
    (hbc : Apart pb.toNat (blockSize (8 * n.toNat) true) pc 16)
    (hinv : R.inv (b - blockSize (8 * n.toNat) true - 16 - blockSize (8 * n.toNat) true)
      ([(pa, pa + blockSize (8 * n.toNat) true), (pc, pc + 16)] ++
        [(pb.toNat, pb.toNat + blockSize (8 * n.toNat) true)]) (s.regs 14).toNat
      (view R.rt ([(pa, pa + blockSize (8 * n.toNat) true), (pc, pc + 16)] ++
        [(pb.toNat, pb.toNat + blockSize (8 * n.toNat) true)]) S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R n x s s') := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2,
    hok1, hok2, hok3, hinv0, hbud⟩ := hpre
  obtain ⟨h4, h14, h5, hx, hx0, hdf, h_rd1, h_rd2, h_rd3, h_rd4, hfr⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  have hsa := hRa.apart hout
  have hsb := hRb.apart hout
  have hsc := hRc.apart hout
  unfold Apart at hab hac hbc hsa hsb hsc
  janus64_data hd [hw]
  janus_eval_nat h_f : flagAddr
  rw [h_f] at hflag
  janus64_run calls [hwb]
  all_goals (try unfold Post)
  all_goals (refine ⟨pa, pb.toNat, pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals janus_split_and
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | (janus64_simp; done)
    | janus_frame
    | skip

end ThreeAmd
