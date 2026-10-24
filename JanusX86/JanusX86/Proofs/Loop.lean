import JanusX86.Proofs.Monad

/-! # `for` loops of the generated model

Sail's `foreach` becomes a step-1 `IntRange` loop (lean-sail `IntRange.forIn'`, a well-founded
recursion). `run_forIn_gen` turns such a loop into its invariant: if every iteration, from a
state satisfying `S i b`, yields a state satisfying `S (i + 1) b'`, the loop ends in a state
satisfying `S (stop + 1) b`. (Adapted from JanusASL's `run_forIn_inv`, Rev.lean, which only
covers bodies that do not change the state.) -/

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_forIn_gen {β : Type} (start stop : Int) (hsp : (1 : Int) ≠ 0) (init : β)
    (f : Int → β → SailM (ForInStep β)) (S : Int → β → SState → Prop) (s : SState)
    (hle : start ≤ stop + 1) (h0 : S start init s)
    (hstep : ∀ i b σ, start ≤ i → i ≤ stop → S i b σ →
      ∃ b' σ', (f i b).run σ = .ok (.yield b') σ' ∧ S (i + 1) b' σ') :
    ∃ b σ, (forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init f).run s =
      .ok b σ ∧ S (stop + 1) b σ := by
  rw [show forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init f =
    IntRange.forIn' ({ start := start, stop := stop, step_pos := hsp } : IntRange) init (fun a _ b => f a b) from rfl]
  unfold IntRange.forIn'
  simp only
  suffices H : ∀ (n : Nat) (i : Int) (hs) (b : β) (σ : SState), start ≤ i → i ≤ stop + 1 → S i b σ →
      (stop - i + 1).toNat = n →
      ∃ b' σ', (IntRange.forIn'.loop ({ start := start, stop := stop, step_pos := hsp } : IntRange)
        (fun a _ b => f a b) b i hs).run σ = .ok b' σ' ∧ S (stop + 1) b' σ' from
    H _ start _ init s (Int.le_refl _) hle h0 rfl
  intro n
  induction n with
  | zero =>
    intro i hs b σ hi hi2 hp hn
    rw [IntRange.forIn'.loop]
    have : ¬ i ≤ stop := by omega
    have e : i = stop + 1 := by omega
    subst e
    exact ⟨b, σ, by simp [Membership.mem, this], hp⟩
  | succ n ih =>
    intro i hs b σ hi hi2 hp hn
    rw [IntRange.forIn'.loop]
    have hle : i ≤ stop := by omega
    have hm : i ∈ ({ start := start, stop := stop, step_pos := hsp } : IntRange) := by
      simp only [Membership.mem]; simp; omega
    obtain ⟨b', σ', hf, hp'⟩ := hstep i b σ hi hle hp
    simp only [hm, dite_true, run_bind, hf]
    exact ih (i + 1) _ b' σ' (by omega) (by omega) hp' (by omega)

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- `run_forIn_gen` in the shape of a goal `(forIn r init f >>= g).run s = R`, so that `refine`
reads `f` and `g` off the goal. -/
theorem run_forIn_bind {β γ : Type} (start stop : Int) (hsp : (1 : Int) ≠ 0) (init : β)
    (f : Int → β → SailM (ForInStep β)) (g : β → SailM γ) (S : Int → β → SState → Prop) (s : SState)
    (R : EStateM.Result (Sail.Error exception) SState γ)
    (hle : start ≤ stop + 1) (h0 : S start init s)
    (hstep : ∀ i b σ, start ≤ i → i ≤ stop → S i b σ →
      ∃ b' σ', (f i b).run σ = .ok (.yield b') σ' ∧ S (i + 1) b' σ')
    (hfin : ∀ b σ, S (stop + 1) b σ → (g b).run σ = R) :
    ((forIn ({ start := start, stop := stop, step_pos := hsp } : IntRange) init f) >>= g).run s = R := by
  obtain ⟨b, σ, h1, h2⟩ := run_forIn_gen start stop hsp init f S s hle h0 hstep
  rw [run_bind, h1]
  exact hfin b σ h2

end JanusX86.Proofs
