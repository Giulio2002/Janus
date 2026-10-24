import Extracted

/-!
# `HashTwice(h *MulHasher, x uint64) uint64` hashes twice through the method value `h.Hash`

**Guarantee.** For every `h` in `X0`, `x` in `X1` and every Go call state `s` of
`example.com/basic.HashTwice` such that the receiver's field `K` (8 bytes at `h`) is readable
and outside `[SP-120, SP)`, the stack-growth prologues of all three frames fall through
(`GuardOK s 80`; the guard word is outside the window) and `SP` is aligned with
`[SP-120, SP)` writable (the frames of `HashTwice`, `ApplyTwice` and the method value wrapper
`(*MulHasher).Hash-fm`), the call returns, obeys the ABI, and `X0 = x · K · K`.

**How the dynamic calls are resolved.** `HashTwice` builds the method value on its own stack (a
funcval: the address of `(*MulHasher).Hash-fm`, then `h`) and passes it to `ApplyTwice`, which
calls it twice with `BLR` and `X26` pointing at it. The funcval is written by the code being
proved, so no hypothesis is needed: the executor reads the code address back from the stack
store, and the `BLR` target is a literal. The extractor finds `Hash-fm` because `HashTwice`
computes its address (an inferred dynamic target, recorded in `identity.json`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (h x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [h, x]
      (fun s => Ptr s.mem h 8 false ∧ Disjoint h.toNat 8 (s.sp.toNat - 120) 120 ∧
        GuardOK s 80 ∧ StackOK s 120 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 120) 120)
      (fun s s' => s'.regs 0 = x * BitVec.ofNat 64 (s.mem.readLE h.toNat 8) *
        BitVec.ofNat 64 (s.mem.readLE h.toNat 8)) := by
  intro ret hret s hs ⟨⟨hh, hhb⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hd hgd
  janus_run

end Proof
