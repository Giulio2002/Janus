import Janus.Contracts.Live

/-!
# Cost bounds of the live allocation contracts

An allocating call costs its block size (`Live.lean`); a theorem whose allocation count depends on
its input sums these costs. The bounds here are linear in the request, so a theorem states its
budget as `b ≥ Σ (2·size + 24)` instead of case-splitting on size classes.
-/

namespace Janus.Contracts

open Janus Janus.Arm64

private def ChainOK : Nat → List Nat → Bool
  | _, [] => true
  | p, c :: cs => decide (c ≤ 2 * p + 10) && ChainOK c cs

private theorem firstAtLeast_le (cs : List Nat) : ∀ p, ChainOK p cs = true → ∀ n, p < n →
    classSize.firstAtLeast cs n ≤ 2 * n + 8 := by
  induction cs with
  | nil => intro p _ n _; simp [classSize.firstAtLeast]; omega
  | cons c cs ih =>
    intro p h n hn
    simp only [ChainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [classSize.firstAtLeast]
    split
    · omega
    · exact ih c h2 n (by omega)

theorem classSize_le (n : Nat) : classSize n ≤ 2 * n + 8 := by
  unfold classSize
  split
  · omega
  · exact firstAtLeast_le sizeClasses 0 (by decide) n (by omega)

/-- The block of a request is at most `2·size + 24` bytes. -/
theorem roundupsize_le (size : Nat) (noscan : Bool) : roundupsize size noscan ≤ 2 * size + 24 := by
  unfold roundupsize
  split
  · have := classSize_le (if !noscan && size > minSizeForMallocHeader then size + mallocHeaderSize else size)
    simp only [mallocHeaderSize] at *
    split at this <;> split <;> simp_all <;> omega
  · simp only [maxSmallSize, mallocHeaderSize, pageSize] at *; omega

theorem blockSize_le (size : Nat) (noscan : Bool) : blockSize size noscan ≤ 2 * size + 24 := by
  unfold blockSize
  split
  · omega
  · exact roundupsize_le size noscan

private theorem go_le (newLen : Nat) : ∀ c, c < newLen → nextslicecap.go newLen c ≤ 2 * newLen + 192 := by
  intro c
  induction c using nextslicecap.go.induct newLen with
  | case1 c c' hc' => intro h; unfold nextslicecap.go; simp only [c'] at *; split <;> omega
  | case2 c c' hc' ih => intro h; unfold nextslicecap.go; simp only [c'] at *; split
                         · omega
                         · exact ih (by omega)

/-- `nextslicecap` grows a shorter slice to at most `2·newLen + 192`. -/
theorem nextslicecap_le (newLen oldCap : Nat) (h : oldCap < newLen) :
    nextslicecap newLen oldCap ≤ 2 * newLen + 192 := by
  unfold nextslicecap
  split
  · omega
  · split
    · omega
    · exact go_le newLen oldCap h

/-- `growslice`'s block is at most `32·newLen + 3096` bytes (for `oldCap < newLen`). -/
theorem growsliceRound_le (newLen oldCap : Nat) (h : oldCap < newLen) :
    8 * growCap8 newLen oldCap ≤ 32 * newLen + 3096 := by
  unfold growCap8
  have h1 := roundupsize_le (nextslicecap newLen oldCap * 8) true
  have h2 := nextslicecap_le newLen oldCap h
  omega

theorem mallocgcRound_le (s : State) : mallocgcRound s ≤ 2 * (s.regs 0).toNat + 24 := blockSize_le _ _
theorem newobjectRound_le (s : State) : newobjectRound s ≤ 2 * typSize s.mem (s.regs 0).toNat + 24 :=
  blockSize_le _ _
theorem makesliceRound_le (s : State) :
    makesliceRound s ≤ 2 * (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat) + 24 := blockSize_le _ _

/-- A summary can relax the budget it hands back: `R.inv` need not be monotone in `b`. A theorem
that allocates at most `bound` bytes states its result as `∃ b', b - bound ≤ b' ∧ R.inv b' …`. -/
theorem RtInv.relax {R : RtInv} {b c bound : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory}
    (h : R.inv (b - c) L g v) (hc : c ≤ bound) : ∃ b', b - bound ≤ b' ∧ R.inv b' L g v :=
  ⟨b - c, by omega, h⟩

end Janus.Contracts
