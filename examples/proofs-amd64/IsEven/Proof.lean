import Janus
import Extracted

/-!
# `IsEven` / `IsOdd` (amd64): mutual recursion, by `Summary.induction_mutual`

**Guarantee.** For every 64-bit `n` and every Go call state of `example.com/basic.IsEven` (resp.
`IsOdd`) such that the stack has room for the `n + 1` nested frames (the deepest stack-growth
check falls through, `StackGuardOK s (24·n)`; `[RSP - (24·n + 8), RSP + 8)` writable; the guard
word outside that window), the call returns to `[RSP]` (never faulting or panicking; the mutual
recursion terminates), obeys the ABI, and `RAX = 1` iff `n` is even (resp. odd), else `0`.

**How.** As on arm64 (`examples/proofs/IsEven.lean`): `summary` proves both members' summaries at
once by strong induction on the shared measure `RAX` (`Summary.induction_mutual`,
`Janus/Amd64/Recursion.lean`), each member using the other's summary (`ih`) at its `CALL`. Each
frame is 24 bytes (return address, saved `RBP`, 8 bytes of locals). `Witness.nonvacuous`: the
precondition holds for `IsEven(3)` and `IsOdd(3)`; `Witness.returns`: they return `0` and `1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Proof

inductive Member | even | odd

def entryOf : Member → Nat
  | .even => segAddr Extracted.program "example.com/basic.IsEven"
  | .odd => segAddr Extracted.program "example.com/basic.IsOdd"

def res : Member → Nat → Nat
  | .even, n => if n % 2 = 0 then 1 else 0
  | .odd, n => if n % 2 = 0 then 0 else 1

theorem res_odd_step {x : Nat} (h : x ≠ 0) : res .odd (x - 1) = res .even x := by
  simp only [res]
  by_cases ha : (x - 1) % 2 = 0 <;> by_cases hb : x % 2 = 0 <;> simp only [ha, hb, ↓reduceIte] <;> omega

theorem res_even_step {x : Nat} (h : x ≠ 0) : res .even (x - 1) = res .odd x := by
  simp only [res]
  by_cases ha : (x - 1) % 2 = 0 <;> by_cases hb : x % 2 = 0 <;> simp only [ha, hb, ↓reduceIte] <;> omega

abbrev Pre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  StackGuardOK s (24 * (s.regs 0).toNat) ∧ StackWritable s (24 * (s.regs 0).toNat + 8) 8 ∧
  ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨
    (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (24 * (s.regs 0).toNat + 8))

abbrev Post (i : Member) (s s' : State) : Prop :=
  ∃ f m,
    s' = { s with
      regs := setRegF (setRegF s.regs 0 (BitVec.ofNat 64 (res i (s.regs 0).toNat))) 4 (s.regs 4 + 8)
      rip := retAddrOf s
      flags := f
      mem := m } ∧
    MemFrame s.mem m [((s.regs 4).toNat - (24 * (s.regs 0).toNat + 8), (s.regs 4).toNat)]

theorem summary : ∀ i, Summary Extracted.program (entryOf i) Pre (Post i) := by
  apply Summary.induction_mutual (fun _ s => (s.regs 0).toNat)
  intro n ih i s hpc ⟨⟨⟨hra, hra'⟩, hg, ⟨hle, hnw, hacc⟩, hd⟩, hn⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  have ihE : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsEven") _ _ :=
    ih .even
  have ihO : Summary Extracted.program (segAddr Extracted.program "example.com/basic.IsOdd") _ _ :=
    ih .odd
  cases i
  all_goals simp only [entryOf] at hpc
  · janus64_step
    janus64_run calls [ihO]
    all_goals
      unfold Post
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · congr 1
        all_goals try rfl
        first
        | (have hz : (s.regs 0).toNat = 0 := by assumption
           rw [hz]; rfl)
        | (have hz : (s.regs 0).toNat ≠ 0 := by assumption
           rw [res_odd_step hz]; try rfl)
      · janus_frame
  · janus64_step
    janus64_run calls [ihE]
    all_goals
      unfold Post
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · congr 1
        all_goals try rfl
        first
        | (have hz : (s.regs 0).toNat = 0 := by assumption
           rw [hz]; rfl)
        | (have hz : (s.regs 0).toNat ≠ 0 := by assumption
           rw [res_even_step hz]; try rfl)
      · janus_frame

/-- The precondition of a call `IsEven(n)` / `IsOdd(n)` from its call state: the stack guard
`24·n` bytes below `RSP` (the deepest of the `n + 1` prologue checks), the window
`[RSP - (24·n + 8), RSP + 8)` writable (the `n` return addresses and saved `RBP`s, and the
caller's return-address slot), and the guard word outside it. -/
def CallPre (n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s (24 * n.toNat) ∧ StackWritable s (24 * n.toNat + 8) 8 ∧
    ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨
      (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (24 * n.toNat + 8))

theorem returns_even (n : BitVec 64) :
    Ensures Extracted.program (entryOf .even) [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = res .even n.toNat) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  simp only [entryOf] at hs
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns (summary .even) hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨f, m, rfl, -⟩
    have hr : ∀ i, res i n.toNat < 2 ^ 64 := by intro i; cases i <;> simp only [res] <;> split <;> omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, h_a0, Nat.mod_eq_of_lt (hr _)]

theorem returns_odd (n : BitVec 64) :
    Ensures Extracted.program (entryOf .odd) [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = res .odd n.toNat) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  simp only [entryOf] at hs
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns (summary .odd) hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨f, m, rfl, -⟩
    have hr : ∀ i, res i n.toNat < 2 ^ 64 := by intro i; cases i <;> simp only [res] <;> split <;> omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, h_a0, Nat.mod_eq_of_lt (hr _)]

/-- `IsEven(n)` returns `1` iff `n` is even, and `IsOdd(n)` returns `1` iff `n` is odd (`0`
otherwise), given the stack for `n + 1` frames. -/
theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat % 2 = 0 then 1 else 0) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.IsOdd") [n] (CallPre n)
      (fun _ s' => (s'.regs 0).toNat = if n.toNat % 2 = 0 then 0 else 1) :=
  ⟨returns_even n, returns_odd n⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def n : BitVec 64 := 3#64

/-- The witness call state `IsEven(3)` (at `IsOdd`'s entry, `IsOdd(3)`) on
`EqHashModel.wmem64` (return address `wret` at `[wsp]`): goroutine `wg` (stack guard 0). -/
def s0 (pc : Nat) : State :=
  { regs := fun i => if i = 0 then n else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 pc, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [n] (s0 pc) :=
  ⟨rfl, wmem64_ret, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre (pc : Nat) : CallPre n (s0 pc) := by
  unfold CallPre s0
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [regSP, regG, stackguard0, stackguard0Offset] <;> decide

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
