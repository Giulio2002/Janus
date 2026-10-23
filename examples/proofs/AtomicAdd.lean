import Extracted

/-!
# `AtomicAdd(p *uint64, d uint64) uint64` is `atomic.AddUint64(p, d)`: `*p += d`, returning the new value

**Guarantee.** For every pointer `p` and addend `d` and every Go call state `s` of
`example.com/basic.AtomicAdd` such that
* the byte `runtime.arm64HasATOMICS` (a writable `.noptrbss` global at `hasAtomics`, which the Go
  runtime sets at start-up when the CPU implements the LSE atomics) is readable and has bit 0 set,
* the 8 bytes at `p` are writable and `p` is 8-byte aligned (Go aligns `uint64`s that are used
  atomically; an unaligned atomic access faults on hardware without FEAT_LSE2),

the call returns (never faulting or panicking), obeys the ABI, returns `old + d` (mod `2^64`) in
`X0` where `old` is the word at `p` before the call, and the only change to memory is that word,
which becomes `old + d`.

**What this covers.** The compiler inlines `atomic.AddUint64` as a test of
`runtime.arm64HasATOMICS` followed by either one `LDADDAL` (LSE) or an `LDAXR`/`STLXR` retry loop.
The precondition selects the LSE path, which is what runs on every Armv8.1+ CPU. The other path
is not covered: the model rejects store-exclusives (`STXR` may fail spuriously on hardware, see
`docs/SOUNDNESS.md`), so with the flag clear the run faults and no theorem about it is provable.
The model is single-threaded: "atomic" here means only the read-modify-write semantics.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `runtime.arm64HasATOMICS`: the byte the function's first two instructions
(`ADRP` + `LDRB`) read, recomputed from the extracted words (`identity.json`, `skippedData`, names
the symbol). -/
def hasAtomics : Nat :=
  adrpLdTarget Extracted.entry (segWord Extracted.program "example.com/basic.AtomicAdd" 0)
    (segWord Extracted.program "example.com/basic.AtomicAdd" 1) 0

theorem correctness (p d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, d]
      (fun s => s.mem.accessible hasAtomics 1 false = true ∧ s.mem.readLE hasAtomics 1 % 2 = 1 ∧
        Ptr s.mem p 8 true ∧ p.toNat % 8 = 0)
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE p.toNat 8 ((s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64)) := by
  intro ret hret s hs ⟨hfa, hf, ⟨hp, hp'⟩, hal⟩
  janus_intro hs
  janus_eval_nat h_ha : hasAtomics
  rw [h_ha] at hfa hf
  janus_run
