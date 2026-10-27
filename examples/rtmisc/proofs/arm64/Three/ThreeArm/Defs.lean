import Extracted

/-!
# `Three(n, x)` (arm64): the statement pieces shared by the segment lemmas

```go
type Cell struct{ P *uint64; N uint64 }
func Three(n int, x uint64) ([]uint64, []uint64, *Cell) {
	a := make([]uint64, n); a[0] = x
	c := new(Cell)
	b := make([]uint64, n)
	c.P = &b[0]
	return a, b, c
}
```

The proof is split at the runtime calls, one module (one `Reaches` lemma) per segment, each about
the SAME runtime hypothesis `R`, so that no single elaboration carries the context of all four calls:

| Module | From | Through |
|---|---|---|
| `ThreeArm.Tail` | after the second `makeslice` | the barrier flag, `gcWriteBarrier2`, `c.P = &b[0]`, `RET` |
| `ThreeArm.Mid2` | after `newobject` | the second `makeslice`, then `Tail` |
| `ThreeArm.Mid1` | after the first `makeslice` | the bounds check, `a[0] = x`, `newobject`, then `Mid2` |
| `ThreeArm.Main` | the entry | the first `makeslice`, then `Mid1` (the theorem `correctness`) |

`Pre` is the precondition of the theorem, `Rel` the frame facts every segment boundary state `S`
shares with the call state `s`, `Post` the postcondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace ThreeArm

/-- The type descriptors `Three` passes to `makeslice` (`ADRP`+`ADD` at `Three+0x28`, `+0x48`) and the
address of the write-barrier flag `runtime.writeBarrier` (`ADRP`+`MOVWU` at `Three+0x6c`), recomputed
from the extracted words. -/
def u64Type : Nat :=
  adrpLdTarget (Extracted.entry + 0x28) (segWord Extracted.program "example.com/rtmisc/live.Three" 10)
    (segWord Extracted.program "example.com/rtmisc/live.Three" 11) 0
def cellType : Nat :=
  adrpLdTarget (Extracted.entry + 0x48) (segWord Extracted.program "example.com/rtmisc/live.Three" 18)
    (segWord Extracted.program "example.com/rtmisc/live.Three" 19) 0
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x6c) (segWord Extracted.program "example.com/rtmisc/live.Three" 27)
    (segWord Extracted.program "example.com/rtmisc/live.Three" 28) 2

/-- The pc after the first `makeslice` and the reload of `n` (`CBZ X1`). -/
abbrev pcS1 : Nat := Extracted.entry + 0x38
/-- The pc after `newobject` returned and `c` was spilled (`ADRP X0, type:uint64`). -/
abbrev pcS2 : Nat := Extracted.entry + 0x58
/-- The pc after the second `makeslice` returned and the flag page was loaded (`LDR W1, [X27, #3104]`). -/
abbrev pcS3 : Nat := Extracted.entry + 0x70

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (n : BitVec 64) (s : State) : Prop :=
  GuardOK s 4160 ∧ StackOK s 4168 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4168) 4192 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4168) 4192 ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside u64Type 16 R.rt ∧ Outside cellType 16 R.rt ∧
    0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [cellType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
    blockSize (8 * n.toNat) true + 16 + blockSize (8 * n.toNat) true ≤ b

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (n x : BitVec 64) (s s' : State) : Prop :=
  ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 3).toNat = pb ∧ (s'.regs 6).toNat = pc ∧
    s'.regs 1 = n ∧ s'.regs 2 = n ∧ s'.regs 4 = n ∧ s'.regs 5 = n ∧
    InRanges pa (blockSize (8 * n.toNat) true) R.rt ∧ InRanges pb (blockSize (8 * n.toNat) true) R.rt ∧
    InRanges pc 16 R.rt ∧
    Apart pa (blockSize (8 * n.toNat) true) pb (blockSize (8 * n.toNat) true) ∧
    Apart pa (blockSize (8 * n.toNat) true) pc 16 ∧ Apart pb (blockSize (8 * n.toNat) true) pc 16 ∧
    s'.mem.readLE pa 8 = x.toNat ∧ s'.mem.readLE pc 8 = pb ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 24)])

/-- What every segment boundary state `S` has in common with the call state `s`: the frame (`SP`,
`X29`, the platform and goroutine registers, the return address, the saved frame pointer and the two
spilled arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (n x : BitVec 64) (s S : State) : Prop :=
  S.sp = s.sp - 64#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 72#64 ∧ S.regs 18 = s.regs 18 ∧
    S.mem.readLE (s.sp.toNat - 64) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat ∧
    S.mem.readLE (s.sp.toNat + 8) 8 = n.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = x.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4168, s.sp.toNat + 24)])

end ThreeArm
