import Extracted

/-!
# `Bump(d uint64) uint64`: a writable package variable (`counter += d`)

**Guarantee.** For every 64-bit `d` and every Go call state `s` of `example.com/basic.Bump` whose
memory makes the 8 bytes of the package variable `example.com/basic.counter` writable, the call
returns (never faulting or panicking), obeys the ABI, `X0 = counter + d mod 2^64` (with
`counter` read before the call), and afterwards `counter` holds that value: memory is `s.mem`
with exactly that store.

The extractor does not copy writable globals (their contents are not fixed by the binary), so
the precondition states the variable's bytes at the address the code computes; `counter`
recomputes it from the extracted `ADRP`/`LDR` words (`adrpLdTarget`), so the statement does not
depend on where the linker put the variable.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `example.com/basic.counter` (`.noptrbss`): the word the first two instructions
(`ADRP` + `LDR`) read. -/
def counter : Nat :=
  adrpLdTarget Extracted.entry (segWord Extracted.program "example.com/basic.Bump" 0)
    (segWord Extracted.program "example.com/basic.Bump" 1) 3

theorem correctness (d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d] (fun s => s.mem.accessible counter 8 true = true)
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE counter 8 + d.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE counter 8 ((s.mem.readLE counter 8 + d.toNat) % 2 ^ 64)) := by
  intro ret hret s hs hc
  janus_intro hs
  janus_eval_nat h_c : counter
  rw [h_c] at hc ⊢
  janus_run

end Proof
