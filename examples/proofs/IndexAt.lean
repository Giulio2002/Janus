import Extracted

/-!
# `IndexAt(xs []uint64, i int) uint64` panics out of range (arm64)

**Guarantee (example 4 of docs/COVERAGE.md R6).** For every slice header `(ptr, len, cap)` in
`X0`–`X2`, index `i` in `X3`, every panic-runtime model `P`, every admissible return address and
every Go call state of `example.com/basic.IndexAt` in which the stack-growth prologue falls
through and the frame is writable:

* if `len ≤ i` (unsigned, as the compiled `cmp; b.cs` checks), the call **panics** with a
  `runtime.Error` of kind `bounds` (`P.boundsError`), whatever the buffer — it reaches
  `runtime.panicBounds`, the Go bounds-check panic;
* if `i < len` and the `8·len` bytes at `ptr` are readable and disjoint from the stack window,
  the call **returns** `xs[i]` (never panics).

The two outcomes are the `.panicked`/`.returned` cases of `EnsuresGo` (`Janus.GoABI`): the
classification is `Janus.Contracts.Panic.goClass P`, which sends the `runtime.panicBounds` stub
to the model's bounds error (`panicStubErr`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (ptr len cap i : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => GuardOK s 0 ∧ StackOK s 24 16 ∧
        (len.toNat ≤ i.toNat ∨
          (i.toNat < len.toNat ∧ Ptr s.mem ptr (8 * len.toNat) false ∧
            Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat - 24) 40)))
      (fun _ => goClass P)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (ptr.toNat + 8 * i.toNat) 8)
      (fun _ v _ => v = P.boundsError) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hcase⟩
  janus_intro hs
  refine GoReturns.of_reaches ?_
  rcases hcase with hi | ⟨hi, ⟨hp, hp'⟩, hd⟩
  · -- out of range: reaches runtime.panicBounds
    simp only
    janus_run
    exact ⟨P.boundsError, goClass_panicStub P _ rfl (by decide), rfl⟩
  · -- in range: returns xs[i]
    simp only [Disjoint] at hd
    janus_run

end Proof
