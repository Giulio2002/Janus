import Janus

/-! Tests for the instruction-count bounds (`ReturnsWithin`, `RunsAtLeast`, `EnsuresWithin`,
`RunsAtLeastOnCall`; arm64 and amd64, `Janus/GoABI.lean`, `Janus/Amd64/GoABI.lean`):

* the lemmas (`ReturnsWithin.returns`, `.mono`, `Returns.within`, `RunsAtLeast.mono`, `exact_count`,
  `EnsuresWithin.ensures`, `.mono_bound`, `.mono`, `RunsAtLeastOnCall.mono`);
* `janus_run` / `janus64_run` as the fuel-counted prover: `ReturnsWithin n` on the longest path, a
  bound one too small is NOT provable (off by one), `RunsAtLeast m` on the shortest path, a bound
  one too large is not provable, a state-dependent bound `fun s => …` that evaluates to a numeral;
* the unit: instructions of the model (`Program.run` fuel), `ReturnsWithin n` is `run (n + 1)`. -/

namespace JanusTests.Within.Arm

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-- `Max`: `CMP X1, X0; B.CS +8; RET; MOV X0, X1; RET`: 3 instructions on one path, 4 on the other. -/
def maxProg : Program :=
  { segments := [⟨"max", 0x1000, [0xeb00003f, 0x54000042, 0xd65f03c0, 0xaa0103e0, 0xd65f03c0]⟩],
    stubs := [], exitAddr := 0 }

/-- `ReturnsWithin n` is a run with fuel `n + 1`. -/
example (n : Nat) (p : Program) (s : State) (Q : State → Prop) :
    ReturnsWithin n p s Q ↔ ∃ s', p.run (n + 1) s = .ok (.returned s') ∧ Q s' := Iff.rfl

/-- ... and `RunsAtLeast m` a run that is still going with fuel `m`. -/
example (m : Nat) (p : Program) (s : State) :
    RunsAtLeast m p s ↔ p.run m s = .error .outOfFuel := Iff.rfl

theorem within4 (x y : W64) : EnsuresWithin (fun _ => 4) maxProg 0x1000 [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

/-- A state-dependent bound that evaluates to a numeral. -/
theorem within4' (x y : W64) : EnsuresWithin (fun s => 2 + (s.regs 30).toNat * 0 + 2) maxProg 0x1000 [x, y] (fun _ => True)
    (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  simp only [Nat.zero_add, Nat.mul_zero]
  janus_run
  all_goals split <;> first | rfl | omega

/-- A budget of 3 is NOT enough (the path through `MOV` executes 4 instructions): the proof fails. -/
example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) : True := by
  fail_if_success
    have : ReturnsWithin 3 (maxProg.withExit ret) s (fun _ => True) := by
      janus_intro hs; janus_run
  trivial

/-- ... and a budget of 5 is (a larger budget is still a bound). -/
example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) :
    ReturnsWithin 5 (maxProg.withExit ret) s (fun _ => True) := by
  janus_intro hs; janus_run

theorem atLeast3 (x y : W64) : RunsAtLeastOnCall (fun _ => 3) maxProg 0x1000 [x, y] (fun _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

/-- A lower bound of 4 is false (the short path returns after 3 instructions): the proof fails. -/
example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) : True := by
  fail_if_success
    have : RunsAtLeast 4 (maxProg.withExit ret) s := by
      janus_intro hs; janus_run
  trivial

/-- On the short path both bounds are tight: the call executes exactly 3 instructions (`exact_count`). -/
example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) (h : y.toNat < x.toNat) :
    ∃ s', Program.Steps (maxProg.withExit ret) s 3 s' ∧ s'.pc.toNat = (maxProg.withExit ret).exitAddr ∧ s'.regs 0 = s.regs 0 := by
  have hl : RunsAtLeast 3 (maxProg.withExit ret) s := by
    janus_intro hs; janus_run
  have hu : ReturnsWithin 3 (maxProg.withExit ret) s (fun s' => s'.regs 0 = s.regs 0) := by
    janus_intro hs; janus_run
    all_goals first | rfl | omega
  exact exact_count hl hu

section Lemmas

variable {p : Program} {s : State} {n m : Nat}

example {Q : State → Prop} (h : ReturnsWithin n p s Q) : Returns p s Q := h.returns
example {Q : State → Prop} (h : ReturnsWithin n p s Q) (hle : n ≤ m) : ReturnsWithin m p s Q := h.mono hle
example {Q : State → Prop} (h : Returns p s Q) : ∃ n, ReturnsWithin n p s Q := h.within
example (h : RunsAtLeast m p s) (hle : n ≤ m) : RunsAtLeast n p s := h.mono hle
/-- Lower and upper bound together: the upper bound is at least the lower bound. -/
example {Q : State → Prop} (hl : RunsAtLeast m p s) (hu : ReturnsWithin n p s Q) : m ≤ n :=
  hl.le_of_returnsWithin hu
example {bound : State → Nat} {entry : Nat} {args : List W64} {pre : State → Prop} {post : State → State → Prop}
    (h : EnsuresWithin bound p entry args pre post) : Ensures p entry args pre post := h.ensures
example {bound : State → Nat} {entry : Nat} {args : List W64} {pre : State → Prop} {post : State → State → Prop}
    (h : EnsuresWithin bound p entry args pre post) : EnsuresWithin (fun s => bound s + 1) p entry args pre post :=
  h.mono_bound fun _ _ => Nat.le_succ _
example {lower : State → Nat} {entry : Nat} {args : List W64} {pre : State → Prop}
    (h : RunsAtLeastOnCall lower p entry args pre) : RunsAtLeastOnCall (fun s => lower s - 1) p entry args pre :=
  h.mono fun _ _ => Nat.sub_le _ _

end Lemmas

end JanusTests.Within.Arm

namespace JanusTests.Within.Amd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `Max`: `CMPQ BX, AX; JAE +1; RET; MOVQ BX, AX; RET` (Go 1.26): 3 instructions on one path, 4 on the other. -/
def maxProg : Janus.Amd64.Program :=
  { segments := [⟨"max", 0x1000, [0x48, 0x39, 0xc3, 0x73, 0x01, 0xc3, 0x48, 0x89, 0xd8, 0xc3]⟩],
    stubs := [], exitAddr := 0 }

example (n : Nat) (p : Janus.Amd64.Program) (s : Janus.Amd64.State) (Q : State → Prop) :
    ReturnsWithin n p s Q ↔ ∃ s', p.run (n + 1) s = .ok (.returned s') ∧ Q s' := Iff.rfl

theorem within4 (x y : W64) : EnsuresWithin (fun _ => 4) maxProg 0x1000 [x, y] (fun s => StackWritable s 0 8)
    (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) (hpre : StackWritable s 0 8) : True := by
  fail_if_success
    have : ReturnsWithin 3 (maxProg.withExit ret) s (fun _ => True) := by
      obtain ⟨-, hnw, hacc⟩ := hpre
      janus64_intro hs
      simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
      janus64_run
  trivial

theorem atLeast3 (x y : W64) : RunsAtLeastOnCall (fun _ => 3) maxProg 0x1000 [x, y] (fun s => StackWritable s 0 8) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

example (x y : W64) (ret : Nat) (hret : RetAddr maxProg ret) (s : State)
    (hs : CallSetup (maxProg.withExit ret) 0x1000 [x, y] s) (hpre : StackWritable s 0 8) : True := by
  fail_if_success
    have : RunsAtLeast 4 (maxProg.withExit ret) s := by
      obtain ⟨-, hnw, hacc⟩ := hpre
      janus64_intro hs
      simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
      janus64_run
  trivial

end JanusTests.Within.Amd
