import Lean

/-!
# Shared `Nat` address-normalisation lemma

`add_sub_norm`: `a + d - c = d + (a - c)` when `c ≤ a`. A byte address written `K + ptr - 1` (a literal and a pointer, minus a literal) is
`ptr + (K - 1)`; the lemma moves the truncated subtraction onto the literals so that the address has the form
`ptr + literal` that the memory rules (`readLE_writeLE_of_disjoint`, `_self`) and `omega` read. It is an ordinary public theorem, not in
any simp set (that would change the goal shape of existing proofs); a consumer passes it to `simp only [..., add_sub_norm]`, with the side
condition `c ≤ a` discharged by `omega` (`simp (disch := omega) only [...]`).
-/

namespace Janus.Tactic

theorem add_sub_norm (a d c : Nat) (h : c ≤ a) : a + d - c = d + (a - c) := by omega

end Janus.Tactic
