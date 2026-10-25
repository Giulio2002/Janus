import Extracted

/-!
# `Fact(n uint64) uint64`: recursion, by well-founded induction over calls

**Guarantee.** For every 64-bit `n` and every Go call state `s` of `example.com/basic.Fact` such
that the stack has room for the `n + 1` nested frames, i.e. the deepest stack-growth check
falls through (`GuardOK s (32·n)`: `g.stackguard0 + 32·n < SP`, the guard word outside the
stack window) and `SP` is aligned with `[SP - (32·n + 40), SP + 16)` writable (`n + 1` frames of
32 bytes, the saved frame pointer of the deepest one, and the spill slot of `n` in the caller's
frame), the call returns (never faulting or panicking; the recursion terminates), obeys the ABI,
and `X0 = n! mod 2^64`.

**How (the template for recursion).** `summary` is a callee contract (`Summary`) of `Fact` from
any state at its entry, proved by strong induction on the argument `X0`
(`Summary.induction`, `Janus/Tactic/Recursion.lean`): in the case `X0 = n` the induction
hypothesis is the summary itself for all states with `X0 < n`, and `janus_run calls [ih]`
uses it at the recursive `bl Fact`, where the executor proves its precondition from the current
state (`X0 - 1 < n`, the smaller stack window one frame down, the guard check one frame
deeper). The summary says which registers the call changes and that memory changes only in the
stack window (`MemFrame`), so the caller's own frame (the saved `X29`/`X30` and the spilled `n`)
is read back through the recursive call. `correctness` applies the summary to the call state
(`Summary.returns`).

What is assumed about the stack is exactly what Go's runtime would otherwise ensure by growing
it (`morestack`); the grown-stack case itself is not covered (docs/COVERAGE.md, R7).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- `n!`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- The precondition of a call `Fact(n)`, `n = X0`: a well-formed return address, the stack
guard `32·n` bytes below `SP` (the deepest of the `n + 1` prologue checks falls through), the
stack window `[SP - (32·n + 40), SP + 16)` (`n + 1` frames of 32 bytes, the saved frame pointer of the deepest) writable (the frames, and the spill slot of `n` in the
caller's frame), and the guard word outside it. -/
abbrev Pre (s : State) : Prop :=
  ((s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56) ∧
  GuardOK s (32 * (s.regs 0).toNat) ∧ StackOK s ((32 * (s.regs 0).toNat + 40)) 16 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (32 * (s.regs 0).toNat + 40)) ((32 * (s.regs 0).toNat + 40) + 16)

/-- What a call `Fact(n)` does: it returns to `X30` with `X0 = n! mod 2^64`, scratch `X1`, `X16`
and flags, `SP`, `X29`, `X30` restored, and memory changed only in its stack window. -/
abbrev Post (s s' : State) : Prop :=
  ∃ v1 v16 f m,
    s' = { s with
      regs := setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (factorial (s.regs 0).toNat))) 1 v1) 16 v16
      pc := s.regs 30
      flags := f
      mem := m } ∧
    MemFrame s.mem m [(s.sp.toNat - (32 * (s.regs 0).toNat + 40), s.sp.toNat - 16),
      (s.sp.toNat + 8, s.sp.toNat + 16)]

/-- The recursive step `n · (n-1)! = n!`, modulo `2^64`. -/
theorem fact_step (x : BitVec 64) (h : x.toNat ≠ 0) :
    x * BitVec.ofNat 64 (factorial (x.toNat - 1)) = BitVec.ofNat 64 (factorial x.toNat) := by
  obtain ⟨m, hm⟩ : ∃ m, x.toNat = m + 1 := ⟨x.toNat - 1, by omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hm, Nat.add_sub_cancel, factorial,
    Nat.mul_mod_mod]

theorem summary : Summary Extracted.program Extracted.entry Pre Post := by
  apply Summary.induction (fun s => (s.regs 0).toNat)
  intro n ih s hpc ⟨⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩, hn⟩
  simp only [Disjoint] at hd hb ha hw hg3
  janus_step
  janus_run calls [ih]
  · refine ⟨s.regs 1, ?v16, ?f, ?m, ?eq, ?fr⟩
    case eq =>
      congr 1
      all_goals try rfl
      congr 1
      all_goals try rfl
      have hz : (s.regs 0).toNat = 0 := by assumption
      rw [hz]
      funext i; simp only [setReg_apply]
      split <;> split <;> first | rfl | (exfalso; omega) | (subst_vars; rfl)
    case fr => janus_frame
  · unfold Post
    refine ⟨s.regs 0, ?_, ?_, ?_, ?_, ?_⟩
    case refine_4 =>
      congr 1
      all_goals try rfl
      congr 1
      all_goals try rfl
      have hz : (s.regs 0).toNat ≠ 0 := by assumption
      rw [fact_step _ hz]
    case refine_5 => janus_frame

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => GuardOK s (32 * n.toNat) ∧ StackOK s (32 * n.toNat + 40) 16 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (32 * n.toNat + 40)) (32 * n.toNat + 56))
      (fun _ s' => (s'.regs 0).toNat = factorial n.toNat % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  janus_intro hs
  refine Summary.returns summary hret (by rw [h_pc]; rfl) h_lr ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [h_lr, hret.toNat_ofNat]; exact hret.aligned
    · rw [h_lr, hret.toNat_ofNat]; have := hret.user; omega
    all_goals simpa only [h_x0] using ‹_›
  · rintro s' ⟨v1, v16, f, m, rfl, -⟩
    refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setReg, regG, regFP, regPlatform, h_x0]

end Proof
