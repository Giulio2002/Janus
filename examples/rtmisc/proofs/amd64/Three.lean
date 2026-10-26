import Janus
import Extracted

/-!
# `Three(n, x)`: two slices and a cell, a barrier store, and allocation contracts that compose (amd64)

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

The three runtime calls (`makeslice`, `newobject`, `makeslice`) and the barrier (`gcWriteBarrier2`) are the
**live** contracts of `Janus/Contracts/Live.lean`, all about ONE runtime hypothesis `R`: each call's
postcondition re-establishes the invariant that the next call needs, for the larger live set and the
smaller budget.

**Guarantee.** For every runtime `R` satisfying the four contracts, every budget `b` covering the
three blocks, `0 < n < 2^40` and every call state whose frame is outside `R.rt`, the call returns, and
the three objects A (`pa`, in `RAX`), B (`pb`, `RDI`) and C (`pc`, `R9`) are inside `R.rt`, pairwise
`Apart` (so disjoint), A holds `x` in its first word **after** B and C were allocated (the later
allocations did not touch A), `C.P = pb`, and memory changed only in `R.rt` and the stack window.
The write barrier flag is read from memory the runtime may have changed: the proof runs both
branches.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptors `Three` passes to `makeslice` and `newobject` (the RIP-relative `LEAQ`s at
`Three+0x22`, `+0x45`) and the address of the write-barrier flag `runtime.writeBarrier` (the
`CMPL` at `Three+0x6a`), recomputed from the extracted code. -/
def u64Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x22)
def cellType : Nat := ripTarget Extracted.program (Extracted.entry + 0x45)
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x6a)

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
      (fun s => StackGuardOK s 4152 ∧ StackWritable s 4152 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4152) 4176 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4152) 4176 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside u64Type 16 R.rt ∧ Outside cellType 16 R.rt ∧
        0 < n.toNat ∧ n.toNat < 2 ^ 40 ∧
        R.ok (Extracted.program.contractAddr "runtime.makeslice") [u64Type, n.toNat, n.toNat] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [cellType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
        blockSize (8 * n.toNat) true + 16 + blockSize (8 * n.toNat) true ≤ b)
      (fun s s' => ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 7).toNat = pb ∧ (s'.regs 9).toNat = pc ∧
        s'.regs 3 = n ∧ s'.regs 1 = n ∧ s'.regs 6 = n ∧ s'.regs 8 = n ∧
        InRanges pa (blockSize (8 * n.toNat) true) R.rt ∧ InRanges pb (blockSize (8 * n.toNat) true) R.rt ∧
        InRanges pc 16 R.rt ∧
        Apart pa (blockSize (8 * n.toNat) true) pb (blockSize (8 * n.toNat) true) ∧
        Apart pa (blockSize (8 * n.toNat) true) pc 16 ∧ Apart pb (blockSize (8 * n.toNat) true) pc 16 ∧
        s'.mem.readLE pa 8 = x.toNat ∧ s'.mem.readLE pc 8 = pb ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4152, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hn, hn2, hok1, hok2, hok3, hinv, hbud⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgrd := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgrd hb ha hw hout hal hga hgr ⊢
  janus64_data hd [hw]
  janus_eval_nat h_u : u64Type
  janus_eval_nat h_c : cellType
  janus_eval_nat h_f : flagAddr
  rw [h_u] at hty1 hok1
  rw [h_c] at hty2 hok2
  rw [h_f] at hflag
  janus64_run calls [hmk.pos, hnew.pos, hwb]
  all_goals (refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩)
  all_goals (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals janus_split_and
  all_goals first | janus_live_disch | (unfold Apart; janus_apart) | janus_simp | skip
  all_goals janus_frame

end Proof
