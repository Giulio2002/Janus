import ThreeAmd.Tail

/-!
# `Three`, third segment (amd64): the second `makeslice`, then `Tail`

From the spill of `c` after `newobject` (`a` and `c` are in the live set): `makeslice(type:uint64, n, n)`
(the live contract: a fresh array `b` outside the live set, the invariant for the live set with `b`),
then `ThreeAmd.tail`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ThreeAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mid2 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n x : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hmk : MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b n s) (S : State) (hrel : Rel R ret n x s S)
    (hpc : S.rip = BitVec.ofNat 64 pcS2)
    (pa pc : Nat)
    (h_rdA : S.mem.readLE ((s.regs 4).toNat - 16) 8 = pa) (h_rdC : S.mem.readLE ((s.regs 4).toNat - 24) 8 = pc)
    (h_rdx : S.mem.readLE pa 8 = x.toNat) (hacC : s.mem.accessible pc 16 true = true)
    (hbc48 : pc + 16 ≤ 2 ^ 48) (hpa48 : pa + blockSize (8 * n.toNat) true ≤ 2 ^ 48)
    (hRa : InRanges pa (blockSize (8 * n.toNat) true) R.rt) (hRc : InRanges pc 16 R.rt)
    (hac : Apart pa (blockSize (8 * n.toNat) true) pc 16)
    (hLa : InRanges pa (blockSize (8 * n.toNat) true)
      ([(pa, pa + blockSize (8 * n.toNat) true)] ++ [(pc, pc + 16)]))
    (hLc : InRanges pc 16 ([(pa, pa + blockSize (8 * n.toNat) true)] ++ [(pc, pc + 16)]))
    (hLs : ∀ r ∈ ([(pa, pa + blockSize (8 * n.toNat) true)] ++ [(pc, pc + 16)]),
      Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 24)])
    (hinv : R.inv (b - blockSize (8 * n.toNat) true - 16)
      ([(pa, pa + blockSize (8 * n.toNat) true)] ++ [(pc, pc + 16)]) (s.regs 14).toNat
      (view R.rt ([(pa, pa + blockSize (8 * n.toNat) true)] ++ [(pc, pc + 16)]) S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R n x s s') := by
  have hpre' := hpre
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2,
    hok1, hok2, hok3, hinv0, hbud⟩ := hpre'
  obtain ⟨h4, h14, h5, hx, hx0, hdf, h_rd1, h_rd2, h_rd3, h_rd4, hfr⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 48 := by rw [h4, BitVec.toNat_sub]; simp; omega
  have hal' : (S.regs 4).toNat % 8 = 0 := by omega
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  have hsa := hRa.apart hout
  have hsc := hRc.apart hout
  unfold Apart at hac hsa hsc
  janus64_data hd [hw]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_f] at hflag
  clear hok2 hinv0
  janus64_run until [pcS3] calls [hmk.pos]
  all_goals (refine tail impl R b n x ret hret s hwb hpre _ ?_ ?_ pa pc _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals (try janus64_simp)
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | (janus_clear_irrel2; omega)
    | (unfold Apart; janus_split_and; try simp only [Apart, Nat.add_sub_cancel_left] at *; janus_clear_irrel2; omega)
    | janus_live
    | assumption
    | janus_frame

end ThreeAmd
