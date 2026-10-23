import Extracted

/-!
# `Get(xs []uint64, i int) uint64` returns `xs[i]` in bounds and panics out of bounds

**Guarantee.** For every slice header `(ptr, len, cap)` in `X0`–`X2`, index `i` in `X3` and every
Go call state `s` of `example.com/basic.Get` in which the stack-growth prologue falls through
(`GuardOK s 0`) and `SP` is aligned with `[SP-24, SP+16)` writable (`StackOK s 24 16`: the frame
below `SP` and the spill slot of `xs.ptr` above it):

* if `i < len` (as unsigned 64-bit numbers, which is what the compiled `cmp; b.cs` checks), the
  `8·len` bytes at `ptr` are readable and do not overlap that stack window, then the call
  returns, obeys the ABI, and `X0` is the 64-bit little-endian word at `ptr + 8·i` in the memory
  **before** the call (and it never panics);
* if `len ≤ i` (unsigned, so this includes negative `i`), the call reaches the bounds-check panic
  stub `runtime.panicBounds`, whatever the buffer.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (ptr len cap i : BitVec 64) (s : State)
    (hs : CallSetup Extracted.program Extracted.entry [ptr, len, cap, i] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 16) :
    (i.toNat < len.toNat → Ptr s.mem ptr (8 * len.toNat) false →
      Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40 →
      Returns Extracted.program s (fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)) ∧
    (len.toNat ≤ i.toNat → Panics Extracted.program s) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  constructor
  · intro hi ⟨hp, hp'⟩ hd
    simp only [Disjoint] at hd
    janus_run
  · intro hi
    janus_run

end Proof
