import ArmASL
import Init.Internal.Order.While

/-! # `while` loops of the generated ASL

Sail's Lean backend writes an ASL `while` loop as `forIn Loop.mk` (Lean's `Loop.forIn`, which is
`repeatM`). Lean unfolds `repeatM` one step for any monad with a `Lean.Order.MonadTail` instance
(`Lean.Loop.forIn_eq_of_monadTail`). The ASL monad `SailM` is an `EStateM`, which has none in
Lean's library; `instMonadTailEStateM` below is one: every `EStateM ε σ β` ordered pointwise (per
initial state) by the flat order on results, whose least element is an arbitrary fixed result.
Bind is monotone in its continuation. This is a lemma-level device for reasoning about the
existing definitions: it changes no definition of the generated model, and it uses no axioms
beyond `propext`, `Classical.choice` and `Quot.sound` (`Classical.ofNonempty` for the least
element). `SailME` is `ExceptT` over `SailM`, which Lean's library instance covers.

`forIn_loop_pure`: a loop whose body is pure (`yield (g r)` while `c r`, else `done r`) that
reaches `r` after `n` steps returns `pure r`. -/

namespace JanusASL.Proofs
open Lean.Order

/-- The least element of the flat order on `EStateM.Result ε σ α`. -/
noncomputable def estBot {ε σ α : Type u} [Nonempty α] [Nonempty σ] : EStateM.Result ε σ α :=
  .ok Classical.ofNonempty Classical.ofNonempty

noncomputable instance instCCPOEStateM {ε σ α : Type u} [Nonempty α] [Nonempty σ] :
    CCPO (EStateM ε σ α) where
  rel := PartialOrder.rel (α := ∀ _ : σ, @FlatOrder (EStateM.Result ε σ α) (estBot (ε := ε) (σ := σ) (α := α)))
  rel_refl := PartialOrder.rel_refl
  rel_antisymm := PartialOrder.rel_antisymm
  rel_trans := PartialOrder.rel_trans
  has_csup hchain :=
    CCPO.has_csup (α := ∀ _ : σ, @FlatOrder (EStateM.Result ε σ α) (estBot (ε := ε) (σ := σ) (α := α))) hchain

noncomputable instance instMonadTailEStateM {ε σ : Type u} [Nonempty σ] : MonadTail (EStateM ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right {_ _ a f₁ f₂} _ h := by
    intro s
    change FlatOrder.rel (EStateM.bind a f₁ s) (EStateM.bind a f₂ s)
    simp only [EStateM.bind]
    split
    · exact h _ _
    · exact FlatOrder.rel.refl

/-- `n` applications of `g`. -/
def iter {β : Type u} (g : β → β) : Nat → β → β
  | 0, b => b
  | n + 1, b => iter g n (g b)

/-- A loop with a pure body: `n` steps of `g` from `b` reach `r`, the condition holds before each
step and fails at `r`. -/
theorem forIn_loop_pure {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadTail m] {β : Type u}
    (c : β → Bool) (g : β → β) (f : Unit → β → m (ForInStep β))
    (hf : ∀ x, f () x = pure (if c x then .yield (g x) else .done x)) :
    ∀ (n : Nat) (b : β), (∀ i < n, c (iter g i b) = true) → c (iter g n b) = false →
      forIn Lean.Loop.mk b f = pure (iter g n b) := by
  intro n
  induction n with
  | zero =>
    intro b _ hr
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hf]
    simp only [iter] at hr ⊢
    simp [hr]
  | succ n ih =>
    intro b hc hr
    show Lean.Loop.forIn _ _ _ = _
    rw [Lean.Loop.forIn_eq_of_monadTail, hf]
    have h0 : c b = true := hc 0 (Nat.succ_pos _)
    simp only [h0, ite_true, pure_bind]
    exact ih (g b) (fun i hi => hc (i + 1) (by omega)) hr

end JanusASL.Proofs
