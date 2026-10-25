import Extracted

/-!
# `Compose(a, b, x uint64) uint64`: a non-escaping closure

**Guarantee.** For all 64-bit `a`, `b`, `x` and every Go call state `s` of
`example.com/basic.Compose` whose stack-growth prologues (of `Compose` and of the callee `twice`)
fall through (`GuardOK s 64`, the guard word outside the stack window) and whose `SP` is aligned
with `[SP-112, SP)` writable (`StackOK`), the call returns (never faulting or panicking), obeys
the ABI, and `X0 = f(f(x)) = a·(a·x + b) + b mod 2^64` for the closure `f(v) = a·v + b`.

**What is exercised.** The closure captures `a` and `b`; escape analysis keeps it on the stack,
so `Compose` builds the funcval (the code address of `Compose.func1`, then `a`, `b`) in its own
frame, with no call to the allocator. `twice` calls it twice through `blr` with the context
register `X26` pointing at it, and `Compose.func1` reads the captured variables through `X26`.
Everything the indirect calls depend on is written by the code being proved, so the theorem
needs no hypothesis about the closure.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b, x]
      (fun s => GuardOK s 64 ∧ StackOK s 112 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat * (a.toNat * x.toNat + b.toNat) + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_run
  janus_arith

end Proof
