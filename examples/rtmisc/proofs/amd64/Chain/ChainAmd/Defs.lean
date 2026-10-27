import Janus
import Extracted

/-!
# `Chain(dst, src, bx, n)` (amd64): the statement pieces shared by the segment lemmas

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
four calls (`ChainAmd.Tail`, `Mid2`, `Mid1`, `Main`, as on arm64: see `ChainArm.Defs`).
`Pre` is the precondition of the theorem, `Rel` relates the state `S` at a segment boundary to the
call state `s`, `Post` is the postcondition.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace ChainAmd

/-- The type descriptor `Chain` passes to `makeslice` (the RIP-relative `LEAQ` at `Chain+0x4b`) and the
address of the write-barrier flag (the `CMPL` at `Chain+0xaa`), recomputed from the extracted code. -/
def u64Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x4b)
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0xaa)

/-- The pc after the first `memmove` (or its skip): `LEAQ type:uint64, AX`. -/
abbrev pcMid1 : Nat := Extracted.entry + 0x4b
/-- The pc of `MOVQ CX, 8(DX)` (`bx.N = n`), after `makeslice` returned and `n`, `bx` were reloaded. -/
abbrev pcMid2 : Nat := Extracted.entry + 0x67
/-- The pc of `TESTQ CX, CX` (the bounds check of `&t[0]`). -/
abbrev pcTail : Nat := Extracted.entry + 0xa5

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (dp dl sp sl bx n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4144 ∧ StackWritable s 4144 72 ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4144) 4216 R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4144) 4216 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside u64Type 16 R.rt ∧
    0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧ 0 < dl.toNat ∧ 0 < sl.toNat ∧ dl.toNat < 2 ^ 40 ∧ sl.toNat < 2 ^ 40 ∧
    R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [dp.toNat, sp.toNat, min sl.toNat dl.toNat * 8] ∧
    (∀ t, R.ok (Extracted.program.contractAddr "runtime.memmove") [t, sp.toNat, min sl.toNat n.toNat * 8]) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 72)]) ∧
    InRanges dp.toNat (8 * dl.toNat) L ∧ InRanges sp.toNat (8 * sl.toNat) L ∧ InRanges bx.toNat 16 L ∧
    s.mem.accessible dp.toNat (8 * dl.toNat) true = true ∧ s.mem.accessible sp.toNat (8 * sl.toNat) false = true ∧
    s.mem.accessible bx.toNat 16 true = true ∧
    dp.toNat + 8 * dl.toNat ≤ 2 ^ 48 ∧ sp.toNat + 8 * sl.toNat ≤ 2 ^ 48 ∧ bx.toNat + 16 ≤ 2 ^ 48 ∧
    Apart dp.toNat (8 * dl.toNat) sp.toNat (8 * sl.toNat) ∧
    Apart bx.toNat 16 dp.toNat (8 * dl.toNat) ∧ Apart bx.toNat 16 sp.toNat (8 * sl.toNat) ∧
    Apart ((s.regs 14).toNat + 16) 8 dp.toNat (8 * dl.toNat) ∧ Apart ((s.regs 14).toNat + 16) 8 bx.toNat 16 ∧
    blockSize (8 * n.toNat) true ≤ b

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (b : Nat) (dp dl sp sl bx n : BitVec 64) (s s' : State) : Prop :=
  ∃ t : Nat, s'.mem.readLE bx.toNat 8 = t ∧ s'.mem.readLE (bx.toNat + 8) 8 = n.toNat ∧
    InRanges t (blockSize (8 * n.toNat) true) R.rt ∧
    Apart t (blockSize (8 * n.toNat) true) dp.toNat (8 * dl.toNat) ∧
    Apart t (blockSize (8 * n.toNat) true) sp.toNat (8 * sl.toNat) ∧
    Apart t (blockSize (8 * n.toNat) true) bx.toNat 16 ∧
    ∃ b' L', b - blockSize (8 * n.toNat) true ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      InRanges t (blockSize (8 * n.toNat) true) L' ∧ InRanges dp.toNat (8 * dl.toNat) L' ∧
      InRanges sp.toNat (8 * sl.toNat) L' ∧ InRanges bx.toNat 16 L' ∧
      MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 72),
        (dp.toNat, dp.toNat + 8 * min sl.toNat dl.toNat), (bx.toNat, bx.toNat + 16)])

/-- What every segment boundary state `S` has in common with the call state `s`: the frame
(`RSP`, `RBP`, `g`, `X15`, the return address, the saved frame pointer and the five spilled
arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (dp dl sp sl bx n : BitVec 64) (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 40#64 ∧ S.regs 14 = s.regs 14 ∧ S.regs 5 = s.regs 4 - 8#64 ∧
    S.xmm 15 = s.xmm 15 ∧ s.xmm 15 = 0 ∧ S.df = false ∧
    S.mem.readLE (s.regs 4).toNat 8 = ret ∧ S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 8) 8 = dp.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 56) 8 = bx.toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 64) 8 = n.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 40) 8 = sl.toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 32) 8 = sp.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 72),
      (dp.toNat, dp.toNat + 8 * min sl.toNat dl.toNat), (bx.toNat, bx.toNat + 16)])

end ChainAmd
