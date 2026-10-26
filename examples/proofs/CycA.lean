import Extracted

/-!
# `CycA` → `CycB` → `CycC` → `CycA`: a 3-cycle with three frame sizes

**Guarantee.** For every 64-bit `n` (and `k`, `j`), given the stack the calls use: `CycA(n)`
returns `cA n`, and for `n ≠ 0` `CycB(n)` returns `cB n (cA (n-1))` and `CycC(n, k, j)` returns
`cC n k j (cA (n-1))`, where `cA`, `cB`, `cC` are the Lean transcriptions below of the Go source
(`examples/basic/zmutual.go`), all modulo `2^64`. Each call returns (never faulting or
panicking; the cycle terminates), obeys the ABI, and changes memory only in its stack window.

**The component.** `A(n)` calls `B(n)` with the same argument, `B(n)` calls `C(n, t, n+t)`, and
`C` calls `A(n-1)`, so the argument decreases only once per round. The shared measure weights
the members (`μ`: `3n+2`, `3n+1`, `3n`), and `Summary.induction_mutual` gives, in the case
`μ = m`, the summaries of all three members for every smaller measure. The frames differ:
32 bytes (`CycA` keeps nothing across its call), 48 (`CycB` keeps `n` in its caller's spill
slot and passes three arguments), 64 (`CycC` keeps a four-word array in its frame), so one round
uses 144 bytes, and each member's stack window, stack-guard depth and written ranges (`below`,
`adj`, `frame`) are stated per member. `janus_run calls [ihB]` (in `CycA`), `[ihC]`, `[ihA]`
proves each callee's precondition at its `bl`, including the decrease of `μ`.

The stack hypotheses say the stack already has room for every frame (the grown-stack case,
`morestack`, is not covered). `Witness.nonvacuous` shows the preconditions hold for concrete
calls with `n = 2`, `Witness.returns` the values they return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- `CycC(n, k, j)` given `r = CycA(n - 1)`. -/
def cC (x k j r : BitVec 64) : BitVec 64 := r + x + k * j + (k ^^^ j)

/-- `CycB(n)` given `r = CycA(n - 1)`. -/
def cB (x r : BitVec 64) : BitVec 64 := cC x (x ^^^ 0x5a#64) (x + (x ^^^ 0x5a#64)) r ^^^ (x ^^^ 0x5a#64)

/-- `CycA(n)`. -/
def cA : Nat → BitVec 64
  | 0 => 1
  | n + 1 => cB (BitVec.ofNat 64 (n + 1)) (cA n) + 1

inductive Member | a | b | c

def entryOf : Member → Nat
  | .a => segAddr Extracted.program "example.com/basic.CycA"
  | .b => segAddr Extracted.program "example.com/basic.CycB"
  | .c => segAddr Extracted.program "example.com/basic.CycC"

/-- The shared measure: one round `A(n) → B(n) → C(n) → A(n - 1)` decreases it three times. -/
def μ : Member → Nat → Nat
  | .a, n => 3 * n + 2
  | .b, n => 3 * n + 1
  | .c, n => 3 * n

/-- Stack bytes below `SP` a member's calls use, for `X0 = n`. -/
def below : Member → Nat → Nat
  | .a, n => 144 * n + 40
  | .b, n => 144 * n + 8
  | .c, n => 144 * n - 40

/-- Stack bytes above `SP` (the caller's spill slot `CycB` writes). -/
def above : Member → Nat
  | .b => 16
  | _ => 0

/-- The depth of the deepest stack-growth check below `SP`. -/
def adj : Member → Nat → Nat
  | .a, n => 144 * n
  | .b, n => 144 * n - 32
  | .c, n => 144 * n - 80

/-- The byte ranges a member writes. -/
def frame : Member → Nat → Nat → List (Nat × Nat)
  | .a, sp, n => [(sp - (144 * n + 40), sp - 16)]
  | .b, sp, n => [(sp - (144 * n + 8), sp - 40), (sp + 8, sp + 16)]
  | .c, sp, n => [(sp - (144 * n - 40), sp - 8)]

/-- What a member returns from its entry state. -/
def result : Member → State → BitVec 64
  | .a, s => cA (s.regs 0).toNat
  | .b, s => cB (s.regs 0) (cA ((s.regs 0).toNat - 1))
  | .c, s => cC (s.regs 0) (s.regs 1) (s.regs 2) (cA ((s.regs 0).toNat - 1))

abbrev Pre (i : Member) (s : State) : Prop :=
  ((s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56) ∧
  (match i with | .a => True | _ => (s.regs 0).toNat ≠ 0) ∧
  GuardOK s (adj i (s.regs 0).toNat) ∧ StackOK s (below i (s.regs 0).toNat) (above i) ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - below i (s.regs 0).toNat)
    (below i (s.regs 0).toNat + above i)

abbrev Post (i : Member) (s s' : State) : Prop :=
  ∃ v1 v2 v3 v4 v16 f m,
    s' = { s with
      regs := setReg (setReg (setReg (setReg (setReg (setReg s.regs 0 (result i s)) 1 v1) 2 v2) 3 v3)
        4 v4) 16 v16
      pc := s.regs 30
      flags := f
      mem := m } ∧
    MemFrame s.mem m (frame i s.sp.toNat (s.regs 0).toNat)

theorem setReg_congr {f g : Nat → W64} {r : Nat} {v w : W64} (h : f = g) (hv : v = w) :
    setReg f r v = setReg g r w := by rw [h, hv]

theorem cA_rec {x : BitVec 64} (h : x.toNat ≠ 0) :
    cA x.toNat = cB x (cA (x.toNat - 1)) + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, x.toNat = m + 1 := ⟨x.toNat - 1, by omega⟩
  rw [hm, cA, Nat.add_sub_cancel, ← hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem xor_ofNat (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat ^^^ b.toNat) % 18446744073709551616) = a ^^^ b := by
  have h := (a ^^^ b).isLt
  rw [BitVec.toNat_xor] at h
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h]

set_option maxHeartbeats 2000000 in
theorem summary : ∀ i, Summary Extracted.program (entryOf i) (Pre i) (Post i) := by
  apply Summary.induction_mutual (fun i s => μ i (s.regs 0).toNat)
  intro n ih i s hpc hp
  have ihA : Summary Extracted.program (segAddr Extracted.program "example.com/basic.CycA") _ _ := ih .a
  have ihB : Summary Extracted.program (segAddr Extracted.program "example.com/basic.CycB") _ _ := ih .b
  have ihC : Summary Extracted.program (segAddr Extracted.program "example.com/basic.CycC") _ _ := ih .c
  simp only [Pre, adj, below, above, μ] at ihA ihB ihC
  cases i
  all_goals
    obtain ⟨⟨⟨h1, h2⟩, hnz, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd⟩, hn⟩ := hp
    simp only [entryOf, μ, adj, below, above, Disjoint] at hpc hn hnz hd hb ha hw hg3
  · janus_step
    janus_run [frame, result] calls [ihB]
    · unfold Post
      refine ⟨s.regs 1, s.regs 2, s.regs 3, s.regs 4, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left 3
      · have hz : (s.regs 0).toNat = 0 := by assumption
        congr 1
        all_goals try rfl
        refine setReg_congr ?_ ?_
        · funext i
          simp only [setReg, result, hz, cA]
          repeat' split
          all_goals first | rfl | (exfalso; omega) | (subst_vars; rfl)
        · rfl
      · simp only [frame]; janus_frame
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left 7
      · congr 1
        all_goals try rfl
        repeat' apply setReg_congr
        all_goals try rfl
        have hz : (s.regs 0).toNat ≠ 0 := by assumption
        simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
        all_goals first | rfl | rw [BitVec.mul_comm (s.regs 1) (s.regs 2)]
      · simp only [frame]; janus_frame
  · janus_step
    janus_run [frame, result] calls [ihC]
    unfold Post
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 7
    · congr 1
      all_goals try rfl
      repeat' apply setReg_congr
      all_goals try rfl
      have hz : (s.regs 0).toNat ≠ 0 := by assumption
      simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
      all_goals first | rfl | rw [BitVec.mul_comm (s.regs 1) (s.regs 2)]
    · simp only [frame]; janus_frame
  · janus_step
    janus_run [frame, result] calls [ihA]
    unfold Post
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 7
    · congr 1
      all_goals try rfl
      repeat' apply setReg_congr
      all_goals try rfl
      have hz : (s.regs 0).toNat ≠ 0 := by assumption
      simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
      all_goals first | rfl | rw [BitVec.mul_comm (s.regs 1) (s.regs 2)]
    · simp only [frame]; janus_frame

/-- The precondition of a call of member `i` with first argument `n`, from its call state. -/
abbrev CallPre (i : Member) (n : BitVec 64) (s : State) : Prop :=
  (match i with | .a => True | _ => n.toNat ≠ 0) ∧
  GuardOK s (adj i n.toNat) ∧ StackOK s (below i n.toNat) (above i) ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - below i n.toNat) (below i n.toNat + above i)

/-- The call precondition of `CycA(n)`: the stack for `n` rounds of 144 bytes and the final
`CycA(0)` frame (with its saved frame pointer), and the deepest stack check `144·n` below `SP`. -/
def PreA (n : BitVec 64) (s : State) : Prop :=
  GuardOK s (144 * n.toNat) ∧ StackOK s (144 * n.toNat + 40) 0 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (144 * n.toNat + 40)) (144 * n.toNat + 40)

/-- The call precondition of `CycB(n)`, `n ≠ 0` (it also writes its caller's spill slot
`[SP + 8, SP + 16)`). -/
def PreB (n : BitVec 64) (s : State) : Prop :=
  n.toNat ≠ 0 ∧ GuardOK s (144 * n.toNat - 32) ∧ StackOK s (144 * n.toNat + 8) 16 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (144 * n.toNat + 8)) (144 * n.toNat + 8 + 16)

/-- The call precondition of `CycC(n, k, j)`, `n ≠ 0`. -/
def PreC (n : BitVec 64) (s : State) : Prop :=
  n.toNat ≠ 0 ∧ GuardOK s (144 * n.toNat - 80) ∧ StackOK s (144 * n.toNat - 40) 0 ∧
  Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - (144 * n.toNat - 40)) (144 * n.toNat - 40)

theorem preA (n : BitVec 64) (s : State) (h : PreA n s) : CallPre .a n s := ⟨trivial, h⟩
theorem preB (n : BitVec 64) (s : State) (h : PreB n s) : CallPre .b n s := h
theorem preC (n : BitVec 64) (s : State) (h : PreC n s) : CallPre .c n s := h

/-- A member's summary applied to its own call state. -/
theorem member_returns (i : Member) (n : BitVec 64) (rest : List (BitVec 64)) :
    Ensures Extracted.program (entryOf i) (n :: rest) (CallPre i n)
      (fun s s' => s'.regs 0 = result i s ∧
        ∀ k (h : k < (n :: rest).length), s.regs k = (n :: rest)[k]) := by
  intro ret hret s hs hpre
  have h_lr : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  have h_x0 : s.regs 0 = n := hs.args 0 (by simp)
  refine Summary.returns (summary i) hret hs.pc h_lr ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h_lr, hret.toNat_ofNat]; exact hret.aligned
    · rw [h_lr, hret.toNat_ofNat]; have := hret.user; omega
    · rw [h_x0]; exact hpre
  · rintro s' ⟨v1, v2, v3, v4, v16, f, m, rfl, -⟩
    refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, hs.args⟩
    all_goals simp [setReg, regG, regFP, regPlatform]

/-- `CycA(n) = cA n` for every `n`; `CycB(n) = cB n (cA (n-1))` and
`CycC(n, k, j) = cC n k j (cA (n-1))` for `n ≠ 0`; each given the stack its calls use. -/
theorem correctness (n k j : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (PreA n)
      (fun _ s' => s'.regs 0 = cA n.toNat) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.CycB") [n] (PreB n)
      (fun _ s' => s'.regs 0 = cB n (cA (n.toNat - 1))) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.CycC") [n, k, j]
      (PreC n) (fun _ s' => s'.regs 0 = cC n k j (cA (n.toNat - 1))) := by
  refine ⟨(member_returns .a n []).mono (preA n) fun s s' _ ⟨h, ha⟩ => ?_,
    (member_returns .b n []).mono (preB n) fun s s' _ ⟨h, ha⟩ => ?_,
    (member_returns .c n [k, j]).mono (preC n) fun s s' _ ⟨h, ha⟩ => ?_⟩
  all_goals
    have h0 := ha 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h]; simp only [result, h0]
  have h1 := ha 1 (by simp)
  have h2 := ha 2 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h1 h2
  rw [h1, h2]

namespace Witness

open Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness call state at `pc` with `X0 = 2`, `X1 = 5`, `X2 = 7` on `IfaceModel.wmem`:
goroutine `wg` (stack guard 0), `SP = wsp`, return address `wret`. -/
def s0 (pc : Nat) : State :=
  { regs := fun i => if i = 0 then 2#64 else if i = 1 then 5#64 else if i = 2 then 7#64
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 pc,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup1 (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [2#64] (s0 pc) :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem setup3 (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [2#64, 5#64, 7#64] (s0 pc) :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpreA0 : PreA 2#64 (s0 0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [Disjoint]; decide

theorem hpreB0 : PreB 2#64 (s0 0) := by
  refine ⟨by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [Disjoint]; decide

theorem hpreC0 : PreC 2#64 (s0 0) := by
  refine ⟨by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [Disjoint]; decide

/-- The preconditions do not read `pc`. -/
theorem hpreA (pc : Nat) : PreA 2#64 (s0 pc) := hpreA0
theorem hpreB (pc : Nat) : PreB 2#64 (s0 pc) := hpreB0
theorem hpreC (pc : Nat) : PreC 2#64 (s0 pc) := hpreC0

/-- All hypotheses of `correctness` hold together, for the three members. -/
theorem nonvacuous : ∃ (ret : Nat) (sa sb sc : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [2#64] sa ∧ PreA 2#64 sa ∧
    CallSetup (Extracted.program.withExit ret) (segAddr Extracted.program "example.com/basic.CycB")
      [2#64] sb ∧ PreB 2#64 sb ∧
    CallSetup (Extracted.program.withExit ret) (segAddr Extracted.program "example.com/basic.CycC")
      [2#64, 5#64, 7#64] sc ∧ PreC 2#64 sc :=
  ⟨ret, s0 _, s0 _, s0 _, hret, setup1 _, hpreA _, setup1 _, hpreB _, setup3 _, hpreC _⟩

/-- So the guarantee is reached: `CycA(2) = 16260`, `CycB(2) = 16259`, `CycC(2, 5, 7) = 8462`. -/
theorem returns :
    Returns (Extracted.program.withExit ret) (s0 Extracted.entry) (fun s' =>
      ABIReturn (s0 Extracted.entry) s' ∧ s'.regs 0 = 16260#64) ∧
    Returns (Extracted.program.withExit ret) (s0 (segAddr Extracted.program "example.com/basic.CycB"))
      (fun s' => ABIReturn (s0 (segAddr Extracted.program "example.com/basic.CycB")) s' ∧
        s'.regs 0 = 16259#64) ∧
    Returns (Extracted.program.withExit ret) (s0 (segAddr Extracted.program "example.com/basic.CycC"))
      (fun s' => ABIReturn (s0 (segAddr Extracted.program "example.com/basic.CycC")) s' ∧
        s'.regs 0 = 8462#64) := by
  obtain ⟨ha, hb, hc⟩ := correctness 2#64 5#64 7#64
  refine ⟨(ha ret hret _ (setup1 _) (hpreA _)).mono ?_, (hb ret hret _ (setup1 _) (hpreB _)).mono ?_,
    (hc ret hret _ (setup3 _) (hpreC _)).mono ?_⟩
  all_goals intro s' h; exact ⟨h.1, by rw [h.2]; decide⟩

end Witness

end Proof
