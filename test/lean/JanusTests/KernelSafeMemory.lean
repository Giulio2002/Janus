import Janus.Arm64.MemoryLemmas

/-! Kernel-safety of the `writeLE` frame facts (regression for U16).

`accessible_writeLE` / `regions_writeLE` hold by `rfl`. A simp lemma proved by `rfl` is applied as a
`dsimp` step that leaves no proof, so the kernel has to re-establish `(m.writeLE a n v).accessible b k w
= m.accessible b k w` by unfolding when it checks the proof. With a symbolic store address such as
`A + (2^64 - nib - c)` that unfolding ended in "(kernel) deep recursion detected" (arm64 `Hex`: two
stores at `sp - 74 + (64 - nib)` and `+ 1`, then `exact hfr.accessible`). The lemmas are now proved
by `Eq.symm (Eq.symm rfl)`, so `simp` rewrites with a proof term that has the lemma's own type.
These examples are kernel-checked when the module builds. -/

namespace JanusTests.KernelSafeMemory

open Janus.Arm64

set_option maxRecDepth 2000 in
example (m S : Memory) (A nib : Nat)
    (hfr : ∀ a n w, m.accessible a n w = S.accessible a n w) :
    ∀ a n, ((m.writeLE (A + (18446744073709551616 - nib - 18446744073709551552)) 1 48).writeLE
      (A + (18446744073709551616 - nib - 18446744073709551551)) 1 120).accessible a n false =
      S.accessible a n false := fun a n => by
  simp only [Memory.accessible_writeLE]
  exact hfr a n false

example (m : Memory) (A nib : Nat) :
    ((m.writeLE (A + (18446744073709551616 - nib - 18446744073709551552)) 1 48).writeLE
      (A + (18446744073709551616 - nib - 18446744073709551551)) 1 120).regions = m.regions := by
  simp only [Memory.regions_writeLE]

end JanusTests.KernelSafeMemory
