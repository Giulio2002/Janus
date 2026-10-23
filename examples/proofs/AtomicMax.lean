import Extracted

/-!
# `AtomicMax(p *uint64, v uint64) uint64`: a compare-and-swap loop that raises `*p` to `v`

**Guarantee.** For every pointer `p` and value `v` and every Go call state `s` of
`example.com/basic.AtomicMax` such that
* the byte `runtime.arm64HasATOMICS` (writable `.noptrbss` global at `hasAtomics`, set by the Go
  runtime at start-up when the CPU implements the LSE atomics) is readable with bit 0 set,
* the 8 bytes at `p` are writable and `p` is 8-byte aligned,

the call returns (never faulting or panicking), obeys the ABI, returns the old value
`old = *p` in `X0`, and afterwards `*p = max old v`: memory is unchanged if `old ≥ v`, and
otherwise exactly the word at `p` becomes `v`.

**What this covers.** The loop is `LDAR` (atomic load), a comparison, and a `CASAL` that
retries from the load when the swap fails. In the single-threaded model nothing can change
`*p` between the load and the `CASAL`, so the swap succeeds the first time and the loop runs
once; the theorem is a total-correctness statement (the call returns). As for `AtomicAdd`, the
precondition selects the LSE path; the `LDAXR`/`STLXR` fallback is not modelled.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `runtime.arm64HasATOMICS`: the byte the `ADRP` + `LDRB` pair at offset 12
reads, recomputed from the extracted words (`identity.json`, `skippedData`, names
the symbol). -/
def hasAtomics : Nat :=
  adrpLdTarget (Extracted.entry + 12) (segWord Extracted.program "example.com/basic.AtomicMax" 3)
    (segWord Extracted.program "example.com/basic.AtomicMax" 4) 0

theorem correctness (p v : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, v]
      (fun s => s.mem.accessible hasAtomics 1 false = true ∧ s.mem.readLE hasAtomics 1 % 2 = 1 ∧
        Ptr s.mem p 8 true ∧ p.toNat % 8 = 0)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        s'.mem = if v.toNat ≤ s.mem.readLE p.toNat 8 then s.mem
                 else s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨hfa, hf, ⟨hp, hp'⟩, hal⟩
  janus_intro hs
  janus_eval_nat h_ha : hasAtomics
  rw [h_ha] at hfa hf
  janus_run
