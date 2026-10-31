import Lean

/-!
# Kernel-safe zero/identity rewrites

`Nat.add_zero`, `Nat.mul_zero` and `Nat.zero_mod` are proved by `rfl`, so `simp` applies them as
`dsimp` steps and leaves NO proof term: the kernel must then re-establish `e + 0 ≡ e` by
definitional unfolding. For `e = X % 2 ^ 64` (or any term the kernel can try to evaluate) it first
whnf's the arguments of the `Nat` operation to literals (the `Nat.add`/`Nat.mod` literal
extension), which evaluates `X` -- e.g. `revContainersNat 8 1 (readLE (m.writeLE …) a 8)` through
the whole write chain -- and dies with "(kernel) deep recursion detected" (arm64
`(*Int).SetBytes1..31`: a store of zero limbs before a load). These copies have propositional
(non-`rfl`) proofs, so `simp` records an `Eq` step that the kernel checks syntactically.

## `reduceCtorEq`

The default simproc `reduceCtorEq` treats `(e + 1022) * 2 ^ 52` as a constructor application
(`Nat.succ …`, after `whnf` unfolds the multiplication along the literal) and proves
`(e + 1022) * 2 ^ 52 = 0` false by `Nat.noConfusion`; the kernel then has to compute
`Nat.ctorIdx` of that term, i.e. unfold `Nat.mul` 2^52 times: "(kernel) deep recursion detected"
(amd64 `(*Int).Float64`). The executor's simp contexts (`janus_run`, `janus64_run`) do not use it.
A proof that calls `simp` itself on such an equation should write `simp [-reduceCtorEq]`.
-/

namespace Janus.Tactic

theorem nat_add_zero' (n : Nat) : n + 0 = n := (Nat.add_comm n 0).trans (Nat.zero_add n)
theorem nat_mul_zero' (n : Nat) : n * 0 = 0 := (Nat.mul_comm n 0).trans (Nat.zero_mul n)
theorem nat_zero_mod' (n : Nat) : 0 % n = 0 := by rw [Nat.zero_mod]

end Janus.Tactic
