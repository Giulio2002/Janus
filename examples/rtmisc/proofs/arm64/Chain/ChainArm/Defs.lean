import Extracted

/-!
# `Chain(dst, src, bx, n)` (arm64): the statement pieces shared by the segment lemmas

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

The proof is split at the runtime calls, one module (one `Reaches` lemma) per segment, each
about the SAME runtime hypothesis `R`, so that no single elaboration carries the context of all
four calls:

| Module | From | Through |
|---|---|---|
| `ChainArm.Tail` | `CBZ X3` (`bx.N` stored, `t` in `X0`) | the barrier flag, `gcWriteBarrier2`, `bx.P = t`, `RET` |
| `ChainArm.Mid2` | after `makeslice` returns | `bx.N = n`, the second `memmove`, then `Tail` |
| `ChainArm.Mid1` | after the first `memmove` (or none) | `makeslice`, then `Mid2` |
| `ChainArm.Main` | the entry | the first `memmove`, then `Mid1` (the theorem `correctness`) |

`Pre` is the precondition of the theorem; `Rel` relates the state `S` at a segment boundary to the
call state `s` (the frame, the spill slots, the memory frame and the runtime invariant for the
live set); `Post` is the postcondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ChainArm

/-- The type descriptor `Chain` passes to `makeslice` (`ADRP`+`ADD` at `Chain+0x4c`) and the address of
the write-barrier flag (`ADRP`+`MOVWU` at `Chain+0xa0`), recomputed from the extracted words. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x4c) (segWord Extracted.program "example.com/rtmisc/live.Chain" 19)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 20) 0
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0xa0) (segWord Extracted.program "example.com/rtmisc/live.Chain" 40)
    (segWord Extracted.program "example.com/rtmisc/live.Chain" 41) 2

/-- The pc after the first `memmove` (or its skip): `ADRP X0, type:uint64`. -/
abbrev pcMid1 : Nat := Extracted.entry + 0x4c
/-- The pc of `STR X3, [X4, #8]` (`bx.N = n`), after `makeslice` returned and `n`, `bx` were reloaded. -/
abbrev pcMid2 : Nat := Extracted.entry + 0x68
/-- The pc of `CBZ X3` (the bounds check of `&t[0]`). -/
abbrev pcTail : Nat := Extracted.entry + 0x9c

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (dp dl sp sl bx n : BitVec 64) (s : State) : Prop :=
  GuardOK s 4144 ∧ StackOK s 4152 72 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4152) 4224 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4224 ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
    Outside u64Type 16 R.rt ∧
    0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧ 0 < dl.toNat ∧ 0 < sl.toNat ∧ dl.toNat < 2 ^ 40 ∧ sl.toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [dp.toNat, sp.toNat, 8 * min sl.toNat dl.toNat] ∧
    (∀ t, R.ok (Extracted.program.contractAddr "runtime.memmove") [t, sp.toNat, 8 * min sl.toNat n.toNat]) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4152, s.sp.toNat + 72)]) ∧
    InRanges dp.toNat (8 * dl.toNat) L ∧ InRanges sp.toNat (8 * sl.toNat) L ∧ InRanges bx.toNat 16 L ∧
    s.mem.accessible dp.toNat (8 * dl.toNat) true = true ∧ s.mem.accessible sp.toNat (8 * sl.toNat) false = true ∧
    s.mem.accessible bx.toNat 16 true = true ∧
    dp.toNat + 8 * dl.toNat ≤ 2 ^ 48 ∧ sp.toNat + 8 * sl.toNat ≤ 2 ^ 48 ∧ bx.toNat + 16 ≤ 2 ^ 48 ∧
    Apart dp.toNat (8 * dl.toNat) sp.toNat (8 * sl.toNat) ∧
    Apart bx.toNat 16 dp.toNat (8 * dl.toNat) ∧ Apart bx.toNat 16 sp.toNat (8 * sl.toNat) ∧
    Apart ((s.regs 28).toNat + 16) 8 dp.toNat (8 * dl.toNat) ∧ Apart ((s.regs 28).toNat + 16) 8 bx.toNat 16 ∧
    blockSize (8 * n.toNat) true ≤ b

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (b : Nat) (dp dl sp sl bx n : BitVec 64) (s s' : State) : Prop :=
  ∃ t : Nat, s'.mem.readLE bx.toNat 8 = t ∧ s'.mem.readLE (bx.toNat + 8) 8 = n.toNat ∧
    InRanges t (blockSize (8 * n.toNat) true) R.rt ∧
    Apart t (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat) ∧
    Apart t (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat) ∧
    Apart t (blockSize (8 * n.toNat) true) bx.toNat 16 ∧
    ∃ b' L', b - blockSize (8 * n.toNat) true ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
      InRanges t (blockSize (8 * n.toNat) true) L' ∧ InRanges dp.toNat (8 * dl.toNat) L' ∧
      InRanges sp.toNat (8 * sl.toNat) L' ∧ InRanges bx.toNat 16 L' ∧
      MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4152, s.sp.toNat + 72),
        (dp.toNat, dp.toNat + 8 * min sl.toNat dl.toNat), (bx.toNat, bx.toNat + 16)])

/-- What every segment boundary state `S` has in common with the call state `s`: the frame
(`SP`, `X29`, the platform and goroutine registers, the return address, the saved frame pointer
and the five spilled arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (dp dl sp sl bx n : BitVec 64) (s S : State) : Prop :=
  S.sp = s.sp - 48#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 56#64 ∧ S.regs 18 = s.regs 18 ∧
    S.mem.readLE (s.sp.toNat - 48) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat ∧
    S.mem.readLE (s.sp.toNat + 8) 8 = dp.toNat ∧ S.mem.readLE (s.sp.toNat + 56) 8 = bx.toNat ∧
    S.mem.readLE (s.sp.toNat + 64) 8 = n.toNat ∧ S.mem.readLE (s.sp.toNat + 40) 8 = sl.toNat ∧
    S.mem.readLE (s.sp.toNat + 32) 8 = sp.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4152, s.sp.toNat + 72),
      (dp.toNat, dp.toNat + 8 * min sl.toNat dl.toNat), (bx.toNat, bx.toNat + 16)])

end ChainArm
