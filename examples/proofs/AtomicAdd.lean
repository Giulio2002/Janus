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
which becomes `old + d` (`correctness`). `anyCPU` states the same with the flag only readable,
under the hypothesis that some store-exclusive of the LL/SC path passes (below).

**What this covers.** The compiler (default `GOARM64=v8.0`) inlines `atomic.AddUint64` as a test
of `runtime.arm64HasATOMICS` followed by either one `LDADDAL` (LSE) or an `LDAXR`/`ADD`/`STLXR`/
`CBNZ` retry loop. `correctness` takes the flag as a precondition and so covers the LSE path, which
is what runs on every Armv8.1+ CPU. `anyCPU` covers both paths, with a weaker precondition on the
flag (only readable) and one more hypothesis for the LL/SC path:

* **The store-exclusive is nondeterministic.** A store-exclusive to the bytes the exclusive monitor
  marks may pass or fail (hardware may fail one spuriously, with no other thread: an interrupt, an
  eviction, an IMPLEMENTATION DEFINED event); its outcome is `s.exclPass`, the environment's choice
  stream of the initial state, which the theorem quantifies over like every other part of `s`. So
  `loop` holds for every sequence of outcomes in which some attempt passes.
* **Termination needs an eventual pass.** If every attempt fails, the loop runs forever and no
  theorem can say it returns. `anyCPU` therefore assumes `∃ k, s.exclPass k = true` when the flag is
  clear: the `k+1`-th store-exclusive passes. This is the fairness property the Arm ARM's forward
  progress guidance gives an LL/SC loop like this one (no other memory access between the exclusives,
  a few instructions, nothing that clears the monitor), stated as a visible hypothesis rather than
  built into the model. Without it the statement would be false: under the all-fail stream
  (`exclPass k = false` for every `k`) each attempt returns to the loop head with memory unchanged
  (the failing case of `loop`), so the call never returns (not stated as a theorem here).
* What it does not need: anything about the initial monitor (`s.excl` is arbitrary; `LDAXR` marks
  it) or the number of failed attempts (the memory is unchanged by a failed one and the value is
  re-read).

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

/-- The loop head `ldaxr x2, [x0]` of the LL/SC path. -/
abbrev head : Nat := Extracted.entry + 0x18

/-- The LL/SC retry loop: from the loop head, if the store-exclusive passes on the `n+1`-th
attempt at the latest (`S.exclPass n`), the call returns with the word at `p` incremented by `d`.
By induction on `n`: an attempt either passes (then the loop exits) or fails, leaving memory
unchanged and the outcome stream advanced by one, which is the induction hypothesis. -/
theorem loop (p d : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hp : s.mem.accessible p.toNat 8 true = true) (hp' : p.toNat + 8 ≤ 2 ^ 48)
    (hal : p.toNat % 8 = 0) :
    ∀ n (S : State), S.exclPass n = true →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = p → S.regs 1 = d → S.mem = s.mem →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = (s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE p.toNat 8 ((s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64)) := by
  intro n
  induction n with
  | zero =>
    intro S hpass hpc h0 h1 hm h30 hsp h28 h29 h18
    janus_run [hpass]
  | succ n ih =>
    intro S hpass hpc h0 h1 hm h30 hsp h28 h29 h18
    by_cases h00 : S.exclPass 0 = true
    · janus_run [h00]
    · have h00' : S.exclPass 0 = false := by simpa using h00
      janus_run [h00'] until [head]
      apply ih
      all_goals janus_simp [hpass]

/-- Both paths: on a CPU with LSE (`runtime.arm64HasATOMICS` set) the `LDADDAL`, on any other
the LL/SC retry loop, which returns once a store-exclusive passes; that it eventually does is the
hypothesis `∃ k, s.exclPass k = true` (the `k+1`-th store-exclusive of the call that the monitor
allows passes; see the module comment). -/
theorem anyCPU (p d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, d]
      (fun s => s.mem.accessible hasAtomics 1 false = true ∧ Ptr s.mem p 8 true ∧ p.toNat % 8 = 0 ∧
        (s.mem.readLE hasAtomics 1 % 2 = 1 ∨ ∃ k, s.exclPass k = true))
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE p.toNat 8 ((s.mem.readLE p.toNat 8 + d.toNat) % 2 ^ 64)) := by
  intro ret hret s hs ⟨hfa, ⟨hp, hp'⟩, hal, hcpu⟩
  by_cases hf : s.mem.readLE hasAtomics 1 % 2 = 1
  · exact correctness p d ret hret s hs ⟨hfa, hf, ⟨hp, hp'⟩, hal⟩
  · obtain ⟨k, hk⟩ := hcpu.resolve_left hf
    janus_intro hs
    janus_eval_nat h_ha : hasAtomics
    rw [h_ha] at hfa hf
    janus_run until [head]
    apply loop p d ret hret s hp hp' hal k
    all_goals janus_simp [hk]
