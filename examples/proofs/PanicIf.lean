import Extracted

/-!
# `PanicIf(x uint64, e any) uint64` returns or panics with `e` (arm64)

**Guarantee (example 1 of docs/COVERAGE.md R6).** `PanicIf` is `if x > 10 { panic(e) }; return x+1`.
The argument `e` is an empty interface (`any`), so `panic(e)` passes it straight to
`runtime.gopanic`. For every `x`, every interface value `e = (etyp, edata)` in `X1`/`X2`, every
panic-runtime model `P`, every admissible return address and every Go call state in which the
stack-growth prologue falls through and the frame is writable:

* if `x ≤ 10` (unsigned, as the compiled `cmp $10; b.hi` checks) the call **returns** `x + 1`;
* if `x > 10` the call **panics** with exactly the interface value `e` — it reaches
  `runtime.gopanic` with `e`'s type word in `X0` and data word in `X1`, which `goClass`
  classifies as `.panicked ⟨etyp, edata⟩`.

This is the literal `panic(v) → .panicked v`, the `.panicked`/`.returned` cases of `EnsuresGo`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Panic

namespace Proof

theorem correctness (P : PanicRuntime) (x etyp edata : BitVec 64) :
    EnsuresGo Extracted.program Extracted.entry [x, etyp, edata]
      (fun s => GuardOK s 0 ∧ StackOK s 40 32)
      (fun _ => goClass P)
      (fun _ s' => x.toNat ≤ 10 → s'.regs 0 = x + 1)
      (fun _ v _ => 10 < x.toNat → v = ⟨etyp.toNat, edata.toNat⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  janus_intro hs
  refine GoReturns.of_reaches ?_
  by_cases hx : x.toNat ≤ 10
  · -- x ≤ 10: returns x + 1
    janus_run
    exact fun _ => trivial
  · -- x > 10: panics with e
    have hx' : 10 < x.toNat := by omega
    janus_run
    refine ⟨⟨etyp.toNat, edata.toNat⟩, ?_, ?_⟩
    · show (⟨etyp.toNat, edata.toNat⟩ : Eface) = ⟨_, _⟩
      simp [setReg]
    · first | (intro _; rfl) | rfl | trivial
end Proof
