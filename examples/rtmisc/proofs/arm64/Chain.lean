import Extracted

/-!
# `Chain(dst, src, bx, n)`: `memmove`, `makeslice`, `memmove` and a barrier store, one runtime hypothesis (arm64)

```go
type Box struct{ P *uint64; N uint64 }
func Chain(dst, src []uint64, bx *Box, n int) {
	copy(dst, src)
	t := make([]uint64, n)
	bx.N = uint64(n)
	copy(t, src)
	bx.P = &t[0]
}
```

`runtime.memmove`, `runtime.makeslice` and `runtime.gcWriteBarrier2` are the live contracts of
`Janus/Contracts/Live.lean`, about ONE runtime hypothesis `R`. The caller's objects (`dst`, `src`,
`bx`) are in the live set `L` at the entry: the first `memmove` writes into one of them (a live
destination: the view does not change), `makeslice` returns a new array outside `L` and keeps all
three unchanged, the second `memmove` writes into the new array (live after `makeslice`), and the
barrier store goes through the buffer the barrier returns.

**Guarantee.** For every runtime satisfying the three contracts and every state in which `dst`,
`src` are disjoint live arrays, `bx` a live 16-byte object apart from both, `0 < n < 2^40`, and the
budget covers the new array: the call returns; `bx.N = n`; `bx.P = t` for an array `t` inside
`R.rt` that is disjoint from `dst`, `src` and `bx`; the runtime invariant holds for the live set
with `t`; memory changed only in `R.rt`, the stack window, the first `min(len dst, len src)` words of
`dst` and `bx`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor `Chain` passes to `makeslice` (`ADRP`+`ADD` at `Chain+0x4c`) and the address of
the write-barrier flag (`ADRP`+`MOVWU` at `Chain+0xa0`), recomputed from the extracted words. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x4c) (segWord Extracted.program "example.com/rtmisc/live.Chain" 19)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 20) 0
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0xa0) (segWord Extracted.program "example.com/rtmisc/live.Chain" 40)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 41) 2

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
      (fun s => GuardOK s 4144 ∧ StackOK s 4144 72 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4216 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4216 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
        Outside u64Type 16 R.rt ∧
        0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧ dl.toNat < 2 ^ 40 ∧ sl.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        (∀ dst src k, R.ok (Extracted.program.contractAddr "runtime.memmove") [dst, src, k]) ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4144, s.sp.toNat + 72)]) ∧
        InRanges dp.toNat (8 * dl.toNat) L ∧ InRanges sp.toNat (8 * sl.toNat) L ∧ InRanges bx.toNat 16 L ∧
        s.mem.accessible dp.toNat (8 * dl.toNat) true = true ∧ s.mem.accessible sp.toNat (8 * sl.toNat) false = true ∧
        s.mem.accessible bx.toNat 16 true = true ∧
        dp.toNat + 8 * dl.toNat ≤ 2 ^ 48 ∧ sp.toNat + 8 * sl.toNat ≤ 2 ^ 48 ∧
        Apart dp.toNat (8 * dl.toNat) sp.toNat (8 * sl.toNat) ∧
        Apart bx.toNat 16 dp.toNat (8 * dl.toNat) ∧ Apart bx.toNat 16 sp.toNat (8 * sl.toNat) ∧
        blockSize (8 * n.toNat) true ≤ b)
      (fun s s' => ∃ t : Nat, s'.mem.readLE bx.toNat 8 = t ∧ s'.mem.readLE (bx.toNat + 8) 8 = n.toNat ∧
        InRanges t (blockSize (8 * n.toNat) true) R.rt ∧
        Apart t (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat) ∧
        Apart t (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat) ∧
        Apart t (blockSize (8 * n.toNat) true) bx.toNat 16 ∧
        ∃ L', b - blockSize (8 * n.toNat) true ≤ b - blockSize (8 * n.toNat) true ∧
          R.inv (b - blockSize (8 * n.toNat) true) L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          InRanges t (blockSize (8 * n.toNat) true) L' ∧ InRanges dp.toNat (8 * dl.toNat) L' ∧
          InRanges sp.toNat (8 * sl.toNat) L' ∧ InRanges bx.toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 72),
            (dp.toNat, dp.toNat + 8 * min dl.toNat sl.toNat), (bx.toNat, bx.toNat + 16)])) := by
  intro ret hret s hs hpre
  janus_intro hs
  sorry

end Proof

