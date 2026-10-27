import Janus
import Extracted

/-!
# `Three(n, x)` (amd64): the statement pieces shared by the segment lemmas

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

The proof is split at the runtime calls, one module per segment (`ThreeAmd.Tail`, `Mid2`, `Mid1`,
`Main`), each about the SAME runtime hypothesis `R`, as on arm64 (see `ThreeArm.Defs`).
`Pre` is the precondition of the theorem, `Rel` the frame facts every segment boundary state `S`
shares with the call state `s`, `Post` the postcondition.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ThreeAmd

/-- The type descriptors `Three` passes to `makeslice` and `newobject` (the RIP-relative `LEAQ`s at
`Three+0x22`, `+0x45`) and the address of the write-barrier flag `runtime.writeBarrier` (the
`CMPL` at `Three+0x6a`), recomputed from the extracted code. -/
def u64Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x22)
def cellType : Nat := ripTarget Extracted.program (Extracted.entry + 0x45)
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x6a)

/-- The pc after the first `makeslice` returned (`MOVQ 56(SP), DX`). -/
abbrev pcS1 : Nat := Extracted.entry + 0x2e
/-- The pc after `newobject` returned (`LEAQ type:uint64, AX`, after `c` was spilled). -/
abbrev pcS2 : Nat := Extracted.entry + 0x56
/-- The pc of the barrier flag test (`CMPL runtime.writeBarrier, $0`), after the second `makeslice`. -/
abbrev pcS3 : Nat := Extracted.entry + 0x6a

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4152 ∧ StackWritable s 4152 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4152) 4176 R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4152) 4176 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside u64Type 16 R.rt ∧ Outside cellType 16 R.rt ∧
    0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [cellType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
    blockSize (8 * n.toNat) true + 16 + blockSize (8 * n.toNat) true ≤ b

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (n x : BitVec 64) (s s' : State) : Prop :=
  ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 7).toNat = pb ∧ (s'.regs 9).toNat = pc ∧
    s'.regs 3 = n ∧ s'.regs 1 = n ∧ s'.regs 6 = n ∧ s'.regs 8 = n ∧
    InRanges pa (blockSize (8 * n.toNat) true) R.rt ∧ InRanges pb (blockSize (8 * n.toNat) true) R.rt ∧
    InRanges pc 16 R.rt ∧
    Apart pa (blockSize (8 * n.toNat) true) pb (blockSize (8 * n.toNat) true) ∧
    Apart pa (blockSize (8 * n.toNat) true) pc 16 ∧ Apart pb (blockSize (8 * n.toNat) true) pc 16 ∧
    s'.mem.readLE pa 8 = x.toNat ∧ s'.mem.readLE pc 8 = pb ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 24)])

/-- What every segment boundary state `S` has in common with the call state `s`: the frame (`RSP`,
`RBP`, `g`, `X15`, the direction flag, the return address, the saved frame pointer and the two spilled
arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (n x : BitVec 64) (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 48#64 ∧ S.regs 14 = s.regs 14 ∧ S.regs 5 = s.regs 4 - 8#64 ∧
    S.xmm 15 = s.xmm 15 ∧ s.xmm 15 = 0 ∧ S.df = false ∧
    S.mem.readLE (s.regs 4).toNat 8 = ret ∧ S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 8) 8 = n.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = x.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 24)])

end ThreeAmd
