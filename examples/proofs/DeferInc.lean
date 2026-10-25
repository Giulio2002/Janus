import Extracted

/-!
# `DeferInc(p *uint64, x uint64) uint64` runs an open-coded defer on return (arm64)

**Guarantee (example 2 of docs/COVERAGE.md R6).** `DeferInc` is `defer func(){ *p++ }(); return x`.
Go 1.26 open-codes the defer: the closure's funcval is built in the frame (with a `deferBits`
byte), and at the normal exit the function clears the byte and calls the closure with `BLR`
(context `X26` = the funcval, which captured `p`). For every `p`, `x`, every panic-runtime
model `P`, every admissible return address and every Go call state in which the stack-growth
prologue falls through, the 64-byte frame is writable, and `p` points at a writable word
disjoint from that frame, the call **returns** `x` and, as a side effect of the deferred closure
having run, the word at `p` is incremented by one. It never panics, so this is `EnsuresGo` with
the panic outcome ruled out — an `Ensures` lifted by `Ensures.toGo`.

The deferred closure is extracted (`DeferInc.func1`, inferred as a computed code address) and run
inline by `janus_run`; the `bl runtime.deferreturn` that `DeferInc` also contains is reached only
after a recovered panic (out of scope here) and is omitted from the extraction.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (p x : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [p, x]
      (fun s => GuardOK s 0 ∧ StackOK s 72 0 ∧ Ptr s.mem p 8 true ∧
        Disjoint p.toNat 8 (s.sp.toNat - 72) 72)
      (fun _ => goClass P)
      (fun s s' => (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE p.toNat 8 = (s.mem.readLE p.toNat 8 + 1) % 2 ^ 64)
      (fun _ _ _ => False) := by
  apply Ensures.toGo
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hp, hp'⟩, hd⟩
  simp only [Disjoint] at hd
  janus_intro hs
  janus_run

end Proof
