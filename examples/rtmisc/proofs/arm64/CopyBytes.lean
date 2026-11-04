import Extracted

/-!
# `CopyBytes(dst, src []byte) int` is `copy(dst, src)` (arm64)

```go
func CopyBytes(dst, src []byte) int { return copy(dst, src) }
```

`runtime.memmove` is the **live** contract `MemmoveLive` of `Janus/Contracts/Live.lean`, with the
runtime hypothesis `R`; the call is skipped when `dst` and `src` start at the same address. The point of
the example is its **Witness**: the stub runtime that makes the contract satisfiable at
`Extracted.program`'s own contract address is the generic `Janus.Contracts.LiveStub`
(`LiveStub.memmoveSeg`, `janus_live_memmove`).

**Guarantee.** For every runtime `R` satisfying the contract, every live set `L` and call state whose
frame is outside the runtime-owned ranges, whose slices (of at most `2^63 - 1` elements) are readable
(`src`) and writable (`dst`: inside a live object or outside the runtime's ranges), the call returns
`n = min(len dst, len src)`, the `n` bytes at `dst` are those of `src`, the runtime's invariant holds
again for the same `L`, and memory changed only in the frame and the first `n` bytes of `dst`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (dp dl dc sp sl sc : BitVec 64)
    (hm : MemmoveLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R) :
    Ensures (Extracted.program.link impl) Extracted.entry [dp, dl, dc, sp, sl, sc]
      (fun s => GuardOK s 4144 ∧ StackOK s 4152 40 ∧ Outside (s.sp.toNat - 4152) 4192 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4192 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4152, s.sp.toNat + 40)]) ∧
        dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
        Apart dp.toNat (min dl.toNat sl.toNat) (s.sp.toNat - 4152) 4192 ∧
        Apart sp.toNat (min dl.toNat sl.toNat) (s.sp.toNat - 4152) 4192 ∧
        (dp ≠ sp →
          R.ok (Extracted.program.contractAddr "runtime.memmove")
            [dp.toNat, sp.toNat, min dl.toNat sl.toNat] ∧
          dp.toNat + min dl.toNat sl.toNat ≤ 2 ^ 48 ∧ sp.toNat + min dl.toNat sl.toNat ≤ 2 ^ 48 ∧
          s.mem.accessible dp.toNat (min dl.toNat sl.toNat) true = true ∧
          s.mem.accessible sp.toNat (min dl.toNat sl.toNat) false = true ∧
          (InRanges dp.toNat (min dl.toNat sl.toNat) L ∨
            Outside dp.toNat (min dl.toNat sl.toNat) R.rt)))
      (fun s s' => (s'.regs 0).toNat = min dl.toNat sl.toNat ∧
        Mem.Copied s.mem s'.mem dp.toNat sp.toNat (min dl.toNat sl.toNat) ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4152, s.sp.toNat + 40),
          (dp.toNat, dp.toNat + min dl.toNat sl.toNat)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hinv, hLs, hdl, hsl, hapd, haps, hdest⟩
  janus_intro hs
  by_cases hdp : dp = sp
  · subst hdp
    janus_run
  · obtain ⟨hok, hb48d, hb48s, haccd, haccs, hd2⟩ := hdest hdp
    janus_run calls [hm]

end Proof
