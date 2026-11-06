import Lean
import Janus.Amd64.Exec
import Janus.Arm64.CarryNorm
import Janus.Tactic.Carry
import Janus.Arm64.MemoryLemmas

/-!
# `janus_carry_simp`: borrow chains in the vocabulary of `janus_carry`

After `janus64_run` on multi-limb subtraction (`SBB`, `CMP`), the symbolic state holds, for each limb,

* `(subFlags (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) c).fst.toNat`  (the limb), and
* `(decide (a < b + (decide …).toNat)).toNat`  (the borrow, nested one level per limb).

Neither is something `janus_carry` or `omega` can chain: the limb is an opaque atom, and the borrow is
a comparison, so a four-limb difference needs a case split per limb. The lemmas below (the opt-in tactic `janus_carry_simp`) rewrite them into the carry vocabulary:

* limb:   `(a + 2^w - b - c) % 2^w`,
* borrow: `1 - (a + (2^w - b - c)) / 2^w`   (`b < 2^w`, `c ≤ 1`),

so that a chain of borrows is a chain of floors (`janus_carry` flattens nested floors) and `omega` sees
one `/ 2^w` and one `% 2^w` per limb instead of a case split. Every lemma is an ordinary kernel-checked
theorem; the set is never part of `janus_run`'s default simp sets, so no existing goal shape changes.
-/

namespace Janus.Amd64

/-- The limb of a subtraction with borrow-in `c` (any `a`, `b`: the operands are reduced mod `2^w` first). -/
theorem subFlags_fst_toNat_ofNat (w a b : Nat) (c : Bool) :
    (subFlags (BitVec.ofNat w a) (BitVec.ofNat w b) c).fst.toNat =
      (a % 2 ^ w + 2 ^ w - b % 2 ^ w - c.toNat) % 2 ^ w := by
  simp only [subFlags, BitVec.toNat_ofNat]

/-- The borrow out of the 64-bit `a - b` (no borrow in). -/
theorem borrow64_toNat (a b : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    (decide (a < b)).toNat = 1 - (a + (18446744073709551616 - b)) / 18446744073709551616 := by
  by_cases h : a < b
  · simp only [h, decide_true, Bool.toNat_true]
    have : (a + (18446744073709551616 - b)) / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · simp only [h, decide_false, Bool.toNat_false]
    have : (a + (18446744073709551616 - b)) / 18446744073709551616 = 1 := by
      rw [Nat.div_eq_iff (by omega)]; constructor <;> omega
    omega

/-- The borrow out of the 64-bit `a - b - c` (borrow in `c ≤ 1`). -/
theorem borrow64_in_toNat (a b c : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) (hc : c ≤ 1) :
    (decide (a < b + c)).toNat = 1 - (a + (18446744073709551616 - b - c)) / 18446744073709551616 := by
  by_cases h : a < b + c
  · simp only [h, decide_true, Bool.toNat_true]
    have : (a + (18446744073709551616 - b - c)) / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · simp only [h, decide_false, Bool.toNat_false]
    have : (a + (18446744073709551616 - b - c)) / 18446744073709551616 = 1 := by
      rw [Nat.div_eq_iff (by omega)]; constructor <;> omega
    omega

end Janus.Amd64

namespace Janus.Tactic

open Lean Meta Elab Tactic in
/-- `janus_bounds_only`: clear every hypothesis except the bound facts `a < n`, `a ≤ n` (`n` a numeral), so that
`omega` on a carry-sized side condition (`A < 2 * 2^64` for a sum of two limbs and a carry) sees only the ranges of its
atoms and not the branch conditions, the equations of the run or their disjunctions. -/
elab "janus_bounds_only" : tactic => do
  let mut g ← getMainGoal
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← g.withContext (isProp ty) do continue
    let isBound := match ty.getAppFnArgs with
      | (``LT.lt, #[t, _, _, b]) | (``LE.le, #[t, _, _, b]) => t.isConstOf ``Nat && (Janus.Carry.evalLit b).isSome
      | _ => false
    unless isBound do g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-- Side conditions of the `janus_carry_simp` lemmas, closed without `omega` (which would read the whole
context of a run): a hypothesis, the range of a memory read or a `BitVec.toNat`, a truncated
subtraction or a remainder bounded by its operands, a flag. -/
macro "janus_carry_disch" : tactic =>
  `(tactic| first
    | assumption
    | exact Nat.sub_le _ _
    | exact Bool.toNat_le _
    | exact Nat.mod_lt _ (by decide)
    | exact Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ _) (by decide)
    | exact Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)
    | exact Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.le_refl _))

/-- `janus_carry_disch` and, as the last resort, `omega` on the bound facts alone (`janus_bounds_only`): for the
arm64 vocabulary of `janus_carry_simp_b`. It is a separate discharger because proving more side conditions makes the
amd64 borrow lemmas fire on some occurrences of a borrow and not on others (Fv256 `RecipG`, 3c0c6f9a), so
`janus_carry_simp` keeps the discharger it always had. -/
macro "janus_carry_disch_b" : tactic =>
  `(tactic| first
    | janus_carry_disch
    | (janus_bounds_only; omega))

/-- `janus_carry_simp` rewrites the borrow chains of the goal into floors and remainders (see
`Janus.Amd64.CarryNorm`); `janus_carry_simp at h₁ h₂ ⊢` or `at *` for hypotheses. Fails if nothing
changes. Opt-in: `janus64_run` does not use it. -/
macro "janus_carry_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := janus_carry_disch) only [Janus.Amd64.subFlags_fst_toNat_ofNat, Janus.Amd64.borrow64_toNat, Janus.Amd64.borrow64_in_toNat, Nat.reducePow,
      Janus.Arm64.addWithCarry_fst_toNat, Janus.Arm64.addWithCarry_c64, Janus.Arm64.dec_le_div, Janus.Arm64.dec_add_div,
      Janus.Arm64.ngc_flag, Janus.Arm64.flag_mod, Janus.Arm64.sbc_num, Janus.Arm64.not_sub_flag, Janus.Arm64.not_flag, Bool.toNat_false] $[$loc]?)

/-- `janus_carry_simp` with the bounds discharger `janus_carry_disch_b`: the arm64 `adds`/`adcs`/`subs`/`sbcs`/`ngc`
vocabulary whose side conditions follow from the bound facts in the context (`a < 2^64`). -/
macro "janus_carry_simp_b" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := janus_carry_disch_b) only [Janus.Amd64.subFlags_fst_toNat_ofNat, Janus.Amd64.borrow64_toNat, Janus.Amd64.borrow64_in_toNat, Nat.reducePow,
      Janus.Arm64.addWithCarry_fst_toNat, Janus.Arm64.addWithCarry_c64, Janus.Arm64.dec_le_div, Janus.Arm64.dec_add_div,
      Janus.Arm64.ngc_flag, Janus.Arm64.flag_mod, Janus.Arm64.sbc_num, Janus.Arm64.not_sub_flag, Janus.Arm64.not_flag, Bool.toNat_false] $[$loc]?)

end Janus.Tactic
