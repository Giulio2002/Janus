import Extracted

/-!
# `IsEven` / `IsOdd`: mutual recursion, by `Summary.induction_mutual`

**Guarantee.** For every 64-bit `n` and every Go call state of `example.com/basic.IsEven` (resp.
`IsOdd`) such that the stack has room for the `n + 1` nested frames (the deepest stack-growth
check falls through, `GuardOK s (32·n)`; `SP` aligned and `[SP - (32·n + 40), SP)` writable; the
guard word outside that window), the call returns (never faulting or panicking; the mutual
recursion terminates), obeys the ABI, and `X0 = 1` iff `n` is even (resp. odd), else `0`.

**How (the template for a strongly connected component).** The two functions call each other,
so neither summary can be proved first. `summary` proves both at once, indexed by `Member`, by
strong induction on the shared measure `X0` (`Summary.induction_mutual`,
`Janus/Tactic/Recursion.lean`): in the case `X0 = n` the induction hypothesis gives the summary
of **both** members for every state with `X0 < n`, and `janus_run calls [ihO]` (in `IsEven`) or
`calls [ihE]` (in `IsOdd`) uses the other member's at its `bl`, where the executor proves the
callee precondition, including `X0 - 1 < n` and the stack window one frame down. Both functions
have a 32-byte frame; `CycA.lean` is a 3-cycle with three different frames.

What is assumed about the stack is what Go's runtime would otherwise ensure by growing it
(`morestack`); the grown-stack case is not covered. `Witness.nonvacuous` shows the
precondition holds for concrete calls `IsEven(3)` and `IsOdd(3)`, `Witness.returns` that they
return `0` and `1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The two members of the component. -/
inductive Member | even | odd

/-- The entry of each member. -/
def entryOf : Member → Nat
  | .even => segAddr Extracted.program "example.com/basic.IsEven"
  | .odd => segAddr Extracted.program "example.com/basic.IsOdd"

/-- What member `i` returns for `n`: `1` for true, `0` for false. -/
def res : Member → Nat → Nat
  | .even, n => if n % 2 = 0 then 1 else 0
  | .odd, n => if n % 2 = 0 then 0 else 1

abbrev Pre (s : State) : Prop :=
  ((s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56) ∧
  GuardOK s (32 * (s.regs 0).toNat) ∧ StackOK s (32 * (s.regs 0).toNat + 40) 0 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (32 * (s.regs 0).toNat + 40))
    (32 * (s.regs 0).toNat + 40)

abbrev Post (i : Member) (s s' : State) : Prop :=
  ∃ v16 f m,
    s' = { s with
      regs := setReg (setReg s.regs 0 (BitVec.ofNat 64 (res i (s.regs 0).toNat))) 16 v16
      pc := s.regs 30
      flags := f
      mem := m } ∧
    MemFrame s.mem m [(s.sp.toNat - (32 * (s.regs 0).toNat + 40), s.sp.toNat - 24)]

theorem res_odd_step {x : Nat} (h : x ≠ 0) : res .odd (x - 1) = res .even x := by
  simp only [res]
  by_cases ha : (x - 1) % 2 = 0 <;> by_cases hb : x % 2 = 0 <;> simp only [ha, hb, ↓reduceIte] <;> omega

theorem res_even_step {x : Nat} (h : x ≠ 0) : res .even (x - 1) = res .odd x := by
  simp only [res]
  by_cases ha : (x - 1) % 2 = 0 <;> by_cases hb : x % 2 = 0 <;> simp only [ha, hb, ↓reduceIte] <;> omega

theorem summary : ∀ i, Summary Extracted.program (entryOf i) Pre (Post i) := by
  apply Summary.induction_mutual (fun _ s => (s.regs 0).toNat)
  intro n ih i s hpc ⟨⟨⟨h1, h2⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩, hn⟩
  simp only [Disjoint] at hd hb ha hw hg3
  have ihE : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsEven") _ _ :=
    ih .even
  have ihO : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsOdd") _ _ :=
    ih .odd
  cases i
  · simp only [entryOf] at hpc
    janus_step
    janus_run calls [ihO]
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 3
      · have hz : (s.regs 0).toNat = 0 := by assumption
        rw [hz]; rfl
      · janus_frame
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 3
      · have hz : (s.regs 0).toNat ≠ 0 := by assumption
        rw [← res_odd_step hz]
      · janus_frame
  · simp only [entryOf] at hpc
    janus_step
    janus_run calls [ihE]
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 3
      · have hz : (s.regs 0).toNat = 0 := by assumption
        rw [hz]; rfl
      · janus_frame
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 3
      · have hz : (s.regs 0).toNat ≠ 0 := by assumption
        rw [← res_even_step hz]
      · janus_frame

/-- The precondition of a call `IsEven(n)` / `IsOdd(n)` from its call state (the stack for the
`n + 1` frames and the guard word outside it). -/
abbrev CallPre (n : BitVec 64) (s : State) : Prop :=
  GuardOK s (32 * n.toNat) ∧ StackOK s (32 * n.toNat + 40) 0 ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (32 * n.toNat + 40)) (32 * n.toNat + 40)

/-- A member's summary applied to its own call state. -/
theorem member_returns (i : Member) (n : BitVec 64) (hpc0 : entryOf i < 2 ^ 64) :
    Ensures Extracted.program (entryOf i) [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = res i n.toNat) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  have h_pc := hs.pc
  have h_lr : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  have h_x0 : s.regs 0 = n := hs.args 0 (by simp)
  refine Summary.returns (summary i) hret h_pc h_lr ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [h_lr, hret.toNat_ofNat]; exact hret.aligned
    · rw [h_lr, hret.toNat_ofNat]; have := hret.user; omega
    all_goals simpa only [h_x0] using ‹_›
  · rintro s' ⟨v16, f, m, rfl, -⟩
    have hr : res i n.toNat < 2 ^ 64 := by cases i <;> simp only [res] <;> split <;> omega
    refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [setReg, regG, regFP, regPlatform, h_x0, Nat.mod_eq_of_lt hr]

/-- `IsEven(n)` returns `1` iff `n` is even, and `IsOdd(n)` returns `1` iff `n` is odd (`0`
otherwise), given the stack for `n + 1` frames. -/
theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat % 2 = 0 then 1 else 0) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.IsOdd") [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat % 2 = 0 then 0 else 1) :=
  ⟨member_returns .even n (by decide), member_returns .odd n (by decide)⟩

namespace Witness

open Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def n : BitVec 64 := 3#64

/-- The witness call state `IsEven(3)` (and, at `IsOdd`'s entry, `IsOdd(3)`) on
`IfaceModel.wmem`: goroutine `wg` (stack guard 0), `SP = wsp`, return address `wret`. -/
def s0 (pc : Nat) : State :=
  { regs := fun i => if i = 0 then n else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 pc,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [n] (s0 pc) :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre0 : CallPre n (s0 0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [Disjoint]; decide

/-- The precondition does not read `pc`. -/
theorem hpre (pc : Nat) : CallPre n (s0 pc) := hpre0

/-- All hypotheses of `correctness` hold together, for both members. -/
theorem nonvacuous : ∃ (ret : Nat) (s s' : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [n] s ∧ CallPre n s ∧
    CallSetup (Extracted.program.withExit ret) (segAddr Extracted.program "example.com/basic.IsOdd")
      [n] s' ∧ CallPre n s' :=
  ⟨ret, s0 _, s0 _, hret, setup _, hpre _, setup _, hpre _⟩

/-- So the guarantee is reached: `IsEven(3)` returns `0` and `IsOdd(3)` returns `1`. -/
theorem returns :
    Returns (Extracted.program.withExit ret) (s0 Extracted.entry) (fun s' =>
      ABIReturn (s0 Extracted.entry) s' ∧ (s'.regs 0).toNat = 0) ∧
    Returns (Extracted.program.withExit ret) (s0 (segAddr Extracted.program "example.com/basic.IsOdd"))
      (fun s' => ABIReturn (s0 (segAddr Extracted.program "example.com/basic.IsOdd")) s' ∧
        (s'.regs 0).toNat = 1) := by
  refine ⟨((correctness n).1 ret hret _ (setup _) (hpre _)).mono ?_,
    ((correctness n).2 ret hret _ (setup _) (hpre _)).mono ?_⟩
  all_goals intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
