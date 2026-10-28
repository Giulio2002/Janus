import ThreeAmd.Mid1

/-!
# `Three(n, x)`: two slices and a cell, a barrier store, and allocation contracts that compose (amd64)

The main theorem: the prologue, the spills and the first `makeslice`, then `ThreeAmd.mid1` (the
bounds check, `a[0] = x`, `newobject`), `ThreeAmd.mid2` (the second `makeslice`) and `ThreeAmd.tail`
(the write barrier and `c.P = &b[0]`). See `ThreeAmd.Defs` for the statement pieces.

The three runtime calls (`makeslice`, `newobject`, `makeslice`) and the barrier (`gcWriteBarrier2`) are the
**live** contracts of `Janus/Contracts/Live.lean`, all about ONE runtime hypothesis `R`: each call's
postcondition re-establishes the invariant that the next call needs, for the larger live set and the
smaller budget.

**Guarantee.** For every runtime `R` satisfying the four contracts, every budget `b` covering the
three blocks, `0 < n < 2^40` and every call state whose frame is outside `R.rt`, the call returns, and
the three objects A (`pa`, in `X0`), B (`pb`, `X3`) and C (`pc`, `X6`) are inside `R.rt`, pairwise
`Apart` (so disjoint), A holds `x` in its first word **after** B and C were allocated, `C.P = pb`, and
memory changed only in `R.rt` and the stack window. The write barrier flag is read from memory the
runtime may have changed: the proof runs both branches.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ThreeAmd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (n x : BitVec 64)
    (hmk : MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [n, x]
      (fun s => Pre R b n s) (fun s s' => Post R n x s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2,
    hok1, hok2, hok3, hinv, hbud⟩ := hpre'
  have hblk := Janus.Contracts.AllocSat.le_blockSize (8 * n.toNat) true
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  janus64_data hd [hw]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_c : cellType
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_c] at hty2 hok2
  rw [h_f] at hflag
  clear hok2 hok3
  janus64_run until [pcS1] calls [hmk.pos]
  all_goals (refine mid1 impl R b n x ret hret s hmk hnew hwb hpre _ ?_ ?_ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals (try janus64_simp)
  all_goals first
    | (with_reducible assumption)
    | janus_live
    | janus_frame

end ThreeAmd
