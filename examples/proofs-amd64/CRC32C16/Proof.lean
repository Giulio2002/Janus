import Janus
import Extracted

/-! `example.com/basic/sse.CRC32C16(crc uint32, p *[16]byte) uint32` on amd64: the CRC-32C
(Castagnoli) checksum of a 16-byte block with the SSE4.2 `CRC32` instruction.

```go
func CRC32C16(crc uint32, p *[16]byte) uint32 { return ^crc32cBlock(^crc, p) }
```

`crc32cBlock` is Go assembly (ABI0, `examples/basic/sse/sse_amd64.s`): `MOVL crc+0(FP), AX;
MOVQ p+8(FP), SI; CRC32Q (SI), AX; CRC32Q 8(SI), AX; MOVL AX, ret+16(FP)`. The Go function
calls it directly with its arguments on the stack.

**Guarantee.** For every `crc` and every pointer `p` to 16 readable bytes outside the stack
window, every call whose stack-growth check falls through returns
`Janus.Spec.CRC32C.checksum crc [p[0], …, p[15]]` (zero-extended into `RAX`): the textbook
bytewise CRC-32C of `hash/crc32.Update(crc, MakeTable(Castagnoli), p[:])`, which is independent
of the instruction's model (`crc32c_eq_update` relates the two). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.CRC32C

set_option maxHeartbeats 3000000 in
theorem correctness (crc p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [crc, p]
      (fun s => Buffer s p 16 false ∧ StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ TlsG s ∧
        ((s.regs 4).toNat + 8 ≤ p.toNat ∨ p.toNat + 16 ≤ (s.regs 4).toNat - 40) ∧
        ((s.regs 4).toNat + 8 ≤ s.fsBase.toNat - 8 ∨ s.fsBase.toNat ≤ (s.regs 4).toNat - 40))
      (fun s s' => (s'.regs 0).toNat =
        checksum (crc.toNat % 2 ^ 32) (bytesOf s.mem p.toNat 16)) := by
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
  · have hc : (~~~BitVec.setWidth 32 crc).toNat = crc.toNat % 2 ^ 32 ^^^ 4294967295 := by
      rw [BitVec.toNat_not, BitVec.toNat_setWidth, xor_ones32 _ (Nat.mod_lt _ (by decide))]
    have hlt := crc32c_lt 64 (ExecSSE.crc32c 64 ((~~~BitVec.setWidth 32 crc).toNat % 4294967296)
      (s.mem.readLE p.toNat 8)) (s.mem.readLE (p.toNat + 8) 8) (crc32c_lt _ _ _ (Nat.mod_lt _ (by decide)))
    rw [BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      crc32c_two_qwords, checksum, hc]
    rw [crc32c_two_qwords] at hlt
    have hx : crc.toNat % 4294967296 ^^^ 4294967295 < 4294967296 :=
      Nat.xor_lt_two_pow (n := 32) (Nat.mod_lt _ (by decide)) (by decide)
    simp only [show (2 : Nat) ^ 32 = 4294967296 by rfl, show (2 : Nat) ^ 64 = 18446744073709551616 by rfl] at hc hlt ⊢
    rw [hc, Nat.mod_eq_of_lt hx] at hlt
    rw [Nat.mod_eq_of_lt hx, xor_ones32 _ hlt]
    omega

end Proof
