import Janus
import Extracted

/-! `example.com/basic.HashTwice(h, x)` on amd64: `ApplyTwice(h.Hash, x)`, a method value called
twice through `CALL CX` with the funcval in `DX`.

For every call state whose stack-growth checks fall through (`StackGuardOK s 72`, the deepest
check is in the wrapper `(*MulHasher).Hash-fm`), with `[RSP-104, RSP+8)` writable, the guard word
and the receiver's field `K` (8 bytes at `h`) readable outside it, the call returns `x · K · K`.

`HashTwice` stores the funcval (the address of `Hash-fm`, then `h`) in its own frame, so the
dynamic call target is read back from that store: no hypothesis about it is needed. The
extractor copies `Hash-fm` because `HashTwice` computes its address. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [h, x]
      (fun s => Buffer s h 8 false ∧ StackGuardOK s 72 ∧ StackWritable s 104 8 ∧
        ((s.regs 4).toNat + 8 ≤ h.toNat ∨ h.toNat + 8 ≤ (s.regs 4).toNat - 104) ∧
        ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 104))
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  intro ret hret s hs ⟨⟨hhb, hh⟩, hg, ⟨hle, hnw, hacc⟩, hd, hgd⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_run
  generalize BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem h.toNat 8) = k
  rw [BitVec.mul_comm k x, BitVec.mul_comm k]

end Proof
