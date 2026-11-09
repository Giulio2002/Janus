import Janus

/-!
# Regression test: no `rfl` Nat zero rewrites in the janus simp sets

`Nat.add_zero` (and `mul_zero`, `zero_mod`) are `rfl` theorems, so `simp` applies them as proof-free
`dsimp` steps and the KERNEL then has to re-establish `e + 0 ≡ e` by evaluation. For
`e = revContainersNat 8 1 (readLE (writeLE-chain) p 8) % 2^64` (a load after several zero-limb
stores, e.g. arm64/amd64 `(*uint256.Int).SetBytesN`) that dies with "(kernel) deep recursion
detected" (or runs for minutes). `Janus.Tactic.nat_add_zero'` & co. have ordinary proofs.

* the theorems below must elaborate AND kernel-check quickly (the kernel check is part of `theorem`);
* the meta checks fail if any of the three `rfl` lemmas (or any lemma of these three shapes that
  `isRflTheorem`) is registered in `janus_exec/janus_post/janus64_exec/janus64_post`.
-/

namespace JanusTests.KernelSafe
open Janus.Arm64 Lean Meta

def W (m : Memory) (z : Nat) : Memory :=
  (((((((m.writeLE z 8 0).writeLE (z+8) 8 0).writeLE (z+16) 8 0).writeLE (z+24) 8 0).writeLE (z+32) 8 0).writeLE (z+40) 8 0).writeLE (z+48) 8 0).writeLE (z+56) 8 0
def X (m : Memory) (z p : Nat) : Nat := revContainersNat 8 1 ((W m z).readLE p 8) % 2^64

theorem add_zero_arm (m : Memory) (z p : Nat) : X m z p + 0 = X m z p := by simp only [janus_post]
theorem mul_zero_arm (m : Memory) (z p : Nat) : X m z p * 0 = 0 := by simp only [janus_post]
theorem zero_mod_arm (m : Memory) (z p : Nat) : 0 % X m z p = 0 := by simp only [janus_post]
theorem add_zero_amd (m : Memory) (z p : Nat) : X m z p + 0 = X m z p := by simp only [janus64_post]
theorem mul_zero_amd (m : Memory) (z p : Nat) : X m z p * 0 = 0 := by simp only [janus64_post]
theorem zero_mod_amd (m : Memory) (z p : Nat) : 0 % X m z p = 0 := by simp only [janus64_post]

/- No `rfl` Nat/arith identity lemma that the kernel would have to evaluate is in the sets. -/
run_meta do
  let env ← getEnv
  for ext in [`janus_exec, `janus_post, `janus64_exec, `janus64_post] do
    let some e ← getSimpExtension? ext | throwError "missing simp set {ext}"
    for nm in [``Nat.add_zero, ``Nat.mul_zero, ``Nat.zero_mod] do
      if (e.getState env).lemmaNames.contains (.decl nm) then
        throwError "{nm} (an rfl lemma) is in {ext}: kernel deep recursion hazard (see test/lean/JanusTests/KernelSafe.lean)"
    -- the three replacements are present and are NOT rfl theorems
    for nm in [``Janus.Tactic.nat_add_zero', ``Janus.Tactic.nat_mul_zero', ``Janus.Tactic.nat_zero_mod'] do
      unless (e.getState env).lemmaNames.contains (.decl nm) do throwError "{nm} missing from {ext}"
      if ← isRflTheorem nm then throwError "{nm} must not be an rfl theorem"

end JanusTests.KernelSafe
