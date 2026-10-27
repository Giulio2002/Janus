import ChainArm.Mid1

/-!
# `Chain(dst, src, bx, n)`: `memmove`, `makeslice`, `memmove` and a barrier store, one runtime hypothesis (arm64)

The main theorem: the prologue, the spills and the first `memmove` (`copy(dst, src)`), then
`ChainArm.mid1` (`makeslice`), `ChainArm.mid2` (`bx.N = n`, the second `memmove`) and
`ChainArm.tail` (the write barrier and `bx.P = t`). See `ChainArm.Defs` for the statement pieces.

`runtime.memmove`, `runtime.makeslice` and `runtime.gcWriteBarrier2` are the live contracts of
`Janus/Contracts/Live.lean`, about ONE runtime hypothesis `R`. The caller's objects (`dst`, `src`,
`bx`) are in the live set `L` at the entry: the first `memmove` writes into one of them (a live
destination: the view does not change), `makeslice` returns a new array outside `L` and keeps all
three unchanged, the second `memmove` writes into the new array (live after `makeslice`), and the
barrier store goes through the buffer the barrier returns.

**Guarantee.** For every runtime satisfying the three contracts and every state in which `dst`,
`src` are disjoint non-empty live arrays, `bx` a live 16-byte object apart from both,
`0 < n < 2^40`, and the budget covers the new array: the call returns; `bx.N = n`; `bx.P = t` for an
array `t` inside `R.rt` that is disjoint from `dst`, `src` and `bx`; the runtime invariant holds for
the live set with `t`; memory changed only in `R.rt`, the stack window, the first
`min(len dst, len src)` words of `dst` and `bx`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ChainArm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl dc sp sl sc bx n : BitVec 64)
    (hmv : MemmoveLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc, bx, n]
      (fun s => Pre R b L dp dl sp sl bx n s) (fun s s' => Post R b dp dl sp sl bx n s s') := by
  intro ret hret s hs hpre
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hn, hn2, hdl0, hsl0, hdl, hsl,
    hok1, hok2, hok3, hok4, hinv, hLs, hind, hins, hinb, hacd, hacs, hacb, hbd, hbs, hbb, hap1, hap2, hap3,
    hgd, hgb, hbud⟩ := hpre'
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
  janus_intro hs
  janus_data hd [hw, hacd, hacb]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_f] at hflag
  clear hok2 hok4 hdl hsl hbud
  janus_run until [pcMid1] calls [hmv]
  all_goals (refine mid1 impl R b L dp dl sp sl bx n ret hret s hmv hmk hwb hpre _ ?_ ?_ ?_ ?_)
  all_goals (try unfold Rel)
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals (try janus_simp)
  all_goals first
    | (with_reducible assumption)
    | janus_live
    | janus_frame

end ChainArm
