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

end Proof
