import ThreeAmd.Mid2

/-!
# `Three`, second segment (amd64): the bounds check, `a[0] = x`, `newobject`, then `Mid2`

From the reload of `n` after the first `makeslice` (the array `a` in `X0`, its block in the live set):
stores `x` in `a[0]`, calls `newobject(type:Cell)` (a fresh 16-byte `c` outside the live set), spills
`c`, then `ThreeAmd.mid2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ThreeAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mid1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n x : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hmk : MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : Pre R b n s) (S : State) (hrel : Rel R ret n x s S)
    (hpc : S.rip = BitVec.ofNat 64 pcS1)
    (hRa : InRanges (S.regs 0).toNat (blockSize (8 * n.toNat) true) R.rt)
    (hacc : s.mem.accessible (S.regs 0).toNat (blockSize (8 * n.toNat) true) true = true)
    (hpa48 : (S.regs 0).toNat + blockSize (8 * n.toNat) true ≤ 2 ^ 48)
    (hinv : R.inv (b - blockSize (8 * n.toNat) true)
      [((S.regs 0).toNat, (S.regs 0).toNat + blockSize (8 * n.toNat) true)] (s.regs 14).toNat
      (view R.rt [((S.regs 0).toNat, (S.regs 0).toNat + blockSize (8 * n.toNat) true)] S.mem)) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R n x s s') := by
  obtain ⟨pa, h0⟩ : ∃ t, S.regs 0 = t := ⟨_, rfl⟩
  rw [h0] at hRa hacc hpa48 hinv
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
  have hga' := hRa.apart hgr
  have hat1 := hRa.apart hty1
  have hat2 := hRa.apart hty2
  unfold Apart at hsa hga' hat1 hat2
  janus64_data hd [hw]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_c : cellType
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_c] at hty2 hok2
  rw [h_f] at hflag
  clear hinv0
  janus64_run until [pcS2] calls [hnew.pos]
  all_goals (refine mid2 impl R b n x ret hret s hmk hwb hpre _ ?_ ?_ pa.toNat ?pcv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (try (simp only [Nat.add_sub_cancel_left]; exact rfl))
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals (try janus64_simp)
  all_goals first
    | (with_reducible assumption)
    | (unfold Apart; with_reducible assumption)
    | janus_live
    | exact InRanges.cons_head _ (Nat.le_refl _) (Nat.le_refl _)
    | exact InRanges.cons_tail _ (InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _))
    | (unfold Apart at *; janus_clear_irrel2; omega)
    | (intro r hr
       simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> (try simp only [Nat.add_sub_cancel_left]) <;>
         (unfold Apart at *; janus_clear_irrel2; omega))
    | janus_frame

end ThreeAmd
