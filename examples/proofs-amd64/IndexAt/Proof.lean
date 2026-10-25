import Janus
import Extracted

/-! `example.com/basic.IndexAt(xs, i)` on amd64: out of range (`len ≤ i`, unsigned) panics with a
runtime bounds error (reaches `runtime.panicBounds`). Example 4 of docs/COVERAGE.md R6. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.PanicAmd64

theorem correctness (P : Spec.PanicRuntime) (ptr len cap i : BitVec 64) (hi : len.toNat ≤ i.toNat) :
    EnsuresGo Extracted.program Extracted.entry [ptr, len, cap, i]
      (fun s => StackWritable s 16 24)
      (fun _ => goClass P)
      (fun _ _ => True)
      (fun _ v _ => v = P.boundsError) := by
  intro ret hret s hs ⟨hle, hnw, hacc⟩
  janus64_intro hs
  simp only [regSP] at hacc hle hnw
  refine GoReturns.of_reaches ?_
  janus64_run
  exact ⟨P.boundsError, goClass_panicStub P _ rfl (by decide), rfl⟩

end Proof
