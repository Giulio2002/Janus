import Janus
import Extracted

/-! `example.com/basic/avx.MaxU32x8(p *[8]uint32) uint32` on amd64: the largest of eight words,
by an AVX2 reduction tree.

```go
func MaxU32x8(p *[8]uint32) uint32 { return maxU32x8(p) }
```

`maxU32x8` is Go assembly (ABI0, `examples/basic/avx/avx_amd64.s`): `VMOVDQU (SI), Y0` loads the
32 bytes, `VEXTRACTI128 $1, Y0, X1` takes the upper 128-bit lane, `VPMAXUD X1, X0, X0` the
lane-wise unsigned maximum of the two halves (a VEX.128 instruction: it zeroes bits 255:128 of
`YMM0`), then `VPSHUFD $0x4E`/`VPMAXUD` (quadwords swapped) and `VPSHUFD $0xB1`/`VPMAXUD` (dwords
swapped within quadwords) fold the four lanes; `VMOVD X0, AX` returns lane 0.

**Guarantee.** For every pointer `p` to 32 readable bytes outside the stack window, every call
whose stack-growth check falls through returns `maxWords s.mem p 8`, the largest of the eight
32-bit words at `p`, `p + 4`, …, `p + 28`.

**How.** `janus64_run` steps the code; the element lemmas (`elem_pintOp_maxu`, `elem_elem128_32`,
`elem_pshufd_*`, `elem_readLE_32`) turn lane 0 of the result into a `max` tree over the eight
words, which is `maxWords` up to associativity and commutativity. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Janus.Arm64 (elem)

/-- The largest of the `n` 32-bit words at `a` (0 for `n = 0`). -/
def maxWords (m : Janus.Arm64.Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxWords m a n) (m.readLE (a + 4 * n) 4)

set_option maxHeartbeats 3000000 in
theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => Buffer s p 32 false ∧ StackGuardOK s 0 ∧ StackWritable s 32 8 ∧ TlsG s ∧
        ((s.regs 4).toNat + 8 ≤ p.toNat ∨ p.toNat + 32 ≤ (s.regs 4).toNat - 32) ∧
        ((s.regs 4).toNat + 8 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat ≤ (s.regs 4).toNat - 32))
      (fun s s' => (s'.regs 0).toNat = maxWords s.mem p.toNat 8) := by
  intro ret hret s hs ⟨⟨hpb, hp⟩, hg, ⟨hle, hnw, hacc⟩, htls, hd, hdt⟩
  janus64_intro hs
  have hfsa := htls.addr
  have hfs := htls.base
  have hfsr := htls.readable
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run [hfsa]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · rw [htls.g]; simp [regG]
  rw [← elem_32_zero]
  janus64_simp [maxWords]
  rw [Nat.zero_max]
  generalize s.mem.readLE p.toNat 4 = w0
  generalize s.mem.readLE (p.toNat + 4) 4 = w1
  generalize s.mem.readLE (p.toNat + 8) 4 = w2
  generalize s.mem.readLE (p.toNat + 12) 4 = w3
  generalize s.mem.readLE (p.toNat + 16) 4 = w4
  generalize s.mem.readLE (p.toNat + 20) 4 = w5
  generalize s.mem.readLE (p.toNat + 24) 4 = w6
  generalize s.mem.readLE (p.toNat + 28) 4 = w7
  simp only [Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]

end Proof
