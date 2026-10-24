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
precondition of `correctness` selects the LSE path. `anyCPU` covers the other path too: there the
swap is an `LDAXR`/`CMP`/`B.NE`/`STLXR`/`CBNZ` loop, whose store-exclusive may fail any number
of times (the outcome is the environment's, `s.exclPass`), so it assumes that one of them passes,
`∃ k, s.exclPass k = true`, when the flag is clear (`loop`; docs/SOUNDNESS.md, "Retry loops
terminate only under a stated progress hypothesis").
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

/-- The head `ldaxr x27, [x0]` of the LL/SC compare-and-swap loop. -/
abbrev head : Nat := Extracted.entry + 0x2c

/-- The LL/SC compare-and-swap loop (`ldaxr`; `cmp`; `b.ne`; `stlxr`; `cbnz`), entered with
`X2 = old`: if the store-exclusive passes on the `n+1`-th attempt at the latest, the call
returns `old` with the word at `p` set to `v`. A failed attempt returns to the head with memory
unchanged and the outcome stream advanced (the induction step). -/
theorem loop (p v : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hp : s.mem.accessible p.toNat 8 true = true) (hp' : p.toNat + 8 ≤ 2 ^ 48)
    (hal : p.toNat % 8 = 0) :
    ∀ n (S : State), S.exclPass n = true →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = p → S.regs 1 = v →
      S.regs 2 = BitVec.ofNat 64 (s.mem.readLE p.toNat 8) → S.mem = s.mem →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧ s'.mem = s.mem.writeLE p.toNat 8 v.toNat) := by
  intro n
  induction n with
  | zero =>
    intro S hpass hpc h0 h1 h2 hm h30 hsp h28 h29 h18
    janus_run [hpass]
  | succ n ih =>
    intro S hpass hpc h0 h1 h2 hm h30 hsp h28 h29 h18
    by_cases h00 : S.exclPass 0 = true
    · janus_run [h00]
    · have h00' : S.exclPass 0 = false := by simpa using h00
      janus_run [h00'] until [head]
      apply ih
      all_goals janus_simp [hpass]

/-- Both paths: the `CASAL` on a CPU with LSE, the LL/SC loop on any other, under the hypothesis
that some store-exclusive of the call passes (see `AtomicAdd.anyCPU` and docs/SOUNDNESS.md). -/
theorem anyCPU (p v : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, v]
      (fun s => s.mem.accessible hasAtomics 1 false = true ∧ Ptr s.mem p 8 true ∧ p.toNat % 8 = 0 ∧
        (s.mem.readLE hasAtomics 1 % 2 = 1 ∨ ∃ k, s.exclPass k = true))
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE p.toNat 8 ∧
        s'.mem = if v.toNat ≤ s.mem.readLE p.toNat 8 then s.mem
                 else s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨hfa, ⟨hp, hp'⟩, hal, hcpu⟩
  by_cases hf : s.mem.readLE hasAtomics 1 % 2 = 1
  · exact correctness p v ret hret s hs ⟨hfa, hf, ⟨hp, hp'⟩, hal⟩
  · obtain ⟨k, hk⟩ := hcpu.resolve_left hf
    janus_intro hs
    janus_eval_nat h_ha : hasAtomics
    rw [h_ha] at hfa hf
    janus_run until [head]
    refine Reaches.mono (loop p v ret hret s hp hp' hal k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    all_goals try janus_simp [hk]
    rintro (_ | _) ⟨habi, h0, hm⟩ <;> simp_all
