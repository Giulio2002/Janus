import Janus
import Extracted

/-!
# `CycA` → `CycB` → `CycC` → `CycA` (amd64): a 3-cycle with three frame sizes

**Guarantee.** As on arm64 (`examples/proofs/CycA.lean`): for every 64-bit `n` (and `k`, `j`),
given the stack the calls use, `CycA(n) = cA n`, and for `n ≠ 0` `CycB(n) = cB n (cA (n-1))` and
`CycC(n, k, j) = cC n k j (cA (n-1))`, modulo `2^64`; each call returns to `[RSP]`, obeys the ABI
and changes memory only in its stack window.

**The component.** `Summary.induction_mutual` (`Janus/Amd64/Recursion.lean`) with the weighted
measure `3n+2`, `3n+1`, `3n`. The frames differ: 16 bytes for `CycA` (saved `RBP`, 8 bytes of
locals), 32 for `CycB` (it spills `n` into its caller's frame and keeps three outgoing argument
registers), 48 for `CycC` (a four-word array), so one round uses 120 bytes with the return
addresses. `Witness.nonvacuous` / `Witness.returns`: concrete calls with `n = 2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Proof

def cC (x k j r : BitVec 64) : BitVec 64 := r + x + k * j + (k ^^^ j)

def cB (x r : BitVec 64) : BitVec 64 := cC x (x ^^^ 0x5a#64) (x + (x ^^^ 0x5a#64)) r ^^^ (x ^^^ 0x5a#64)

def cA : Nat → BitVec 64
  | 0 => 1
  | n + 1 => cB (BitVec.ofNat 64 (n + 1)) (cA n) + 1

theorem cA_rec {x : BitVec 64} (h : x.toNat ≠ 0) :
    cA x.toNat = cB x (cA (x.toNat - 1)) + 1 := by
  obtain ⟨m, hm⟩ : ∃ m, x.toNat = m + 1 := ⟨x.toNat - 1, by omega⟩
  rw [hm, cA, Nat.add_sub_cancel, ← hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

inductive Member | a | b | c

def entryOf : Member → Nat
  | .a => segAddr Extracted.program "example.com/basic.CycA"
  | .b => segAddr Extracted.program "example.com/basic.CycB"
  | .c => segAddr Extracted.program "example.com/basic.CycC"

def μ : Member → Nat → Nat
  | .a, n => 3 * n + 2
  | .b, n => 3 * n + 1
  | .c, n => 3 * n

def below : Member → Nat → Nat
  | .a, n => 120 * n + 8
  | .b, n => 120 * n - 16
  | .c, n => 120 * n - 56

def above : Member → Nat
  | .b => 16
  | _ => 8

def adj : Member → Nat → Nat
  | .a, n => 120 * n
  | .b, n => 120 * n - 24
  | .c, n => 120 * n - 64

def frame : Member → Nat → Nat → List (Nat × Nat)
  | .a, sp, n => [(sp - (120 * n + 8), sp)]
  | .b, sp, n => [(sp - (120 * n - 16), sp), (sp + 8, sp + 16)]
  | .c, sp, n => [(sp - (120 * n - 56), sp)]

def result : Member → State → BitVec 64
  | .a, s => cA (s.regs 0).toNat
  | .b, s => cB (s.regs 0) (cA ((s.regs 0).toNat - 1))
  | .c, s => cC (s.regs 0) (s.regs 3) (s.regs 1) (cA ((s.regs 0).toNat - 1))

abbrev Pre (i : Member) (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  (match i with | .a => True | _ => (s.regs 0).toNat ≠ 0) ∧
  StackGuardOK s (adj i (s.regs 0).toNat) ∧ StackWritable s (below i (s.regs 0).toNat) (above i) ∧
  ((s.regs 4).toNat + above i ≤ (s.regs 14).toNat + 16 ∨
    (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - below i (s.regs 0).toNat)

abbrev Post (i : Member) (s s' : State) : Prop :=
  ∃ v1 v2 v3 f m,
    s' = { s with
      regs := setRegF (setRegF (setRegF (setRegF (setRegF s.regs 0 (result i s)) 1 v1) 2 v2) 3 v3) 4
        (s.regs 4 + 8)
      rip := retAddrOf s
      flags := f
      mem := m } ∧
    MemFrame s.mem m (frame i (s.regs 4).toNat (s.regs 0).toNat)

theorem setRegF_congr {f g : Nat → BitVec 64} {r : Nat} {v w : BitVec 64} (h : f = g) (hv : v = w) :
    setRegF f r v = setRegF g r w := by rw [h, hv]

theorem xor_ofNat (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat ^^^ b.toNat) % 18446744073709551616) = a ^^^ b := by
  have h := (a ^^^ b).isLt
  rw [BitVec.toNat_xor] at h
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h]

set_option linter.unusedSimpArgs false in
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
    obtain ⟨⟨hra, hra'⟩, hnz, hg, ⟨hle, hnw, hacc⟩, hd⟩ := hp.1
    have hn := hp.2
    have hgl := hg.load
    have hgb := hg.below
    have hnw2 := hg.noWrap
    have hgr := hg.readable
    simp only [entryOf, μ, adj, below, above, regSP, regG, stackguard0Offset, stackguard0] at hpc hn hnz hd hacc hle hnw hgl hgb hnw2 hgr
  · janus64_step
    janus64_run [frame, result] calls [ihB]
    · unfold Post
      refine ⟨s.regs 1, s.regs 2, s.regs 3, ?_, ?_, ?_, ?_⟩
      rotate_left 2
      · have hz : (s.regs 0).toNat = 0 := by assumption
        congr 1
        all_goals try rfl
        refine setRegF_congr ?_ ?_
        · funext i
          simp only [setRegF, result, hz, cA]
          repeat' split
          all_goals first | rfl | (exfalso; omega) | (subst_vars; rfl)
        · rfl
      · simp only [frame]; janus_frame
    · unfold Post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left 5
      · congr 1
        all_goals try rfl
        repeat' apply setRegF_congr
        all_goals try rfl
        all_goals
          have hz : (s.regs 0).toNat ≠ 0 := by assumption
          simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
          try first | rfl | rw [BitVec.mul_comm (s.regs 3) (s.regs 1)]
      · simp only [frame]; janus_frame
  · janus64_step
    janus64_run [frame, result] calls [ihC]
    unfold Post
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 5
    · congr 1
      all_goals try rfl
      repeat' apply setRegF_congr
      all_goals try rfl
      all_goals
        have hz : (s.regs 0).toNat ≠ 0 := by assumption
        simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
        try first | rfl | rw [BitVec.mul_comm (s.regs 3) (s.regs 1)]
    · simp only [frame]; janus_frame
  · janus64_step
    janus64_run [frame, result] calls [ihA]
    unfold Post
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 5
    · congr 1
      all_goals try rfl
      repeat' apply setRegF_congr
      all_goals try rfl
      all_goals
        have hz : (s.regs 0).toNat ≠ 0 := by assumption
        simp only [result, cA_rec hz, cB, cC, xor_ofNat, BitVec.xor_assoc]
        try first | rfl | rw [BitVec.mul_comm (s.regs 3) (s.regs 1)]
    · simp only [frame]; janus_frame

/-- The call precondition of `CycA(n)`: the stack for `n` rounds of 120 bytes and the final `CycA(0)` frame, the deepest stack check `120·n` below `RSP`. -/
def PreA (n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s (120 * n.toNat) ∧ StackWritable s (120 * n.toNat + 8) 8 ∧
    ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (120 * n.toNat + 8))

/-- The call precondition of `CycB(n)`, `n ≠ 0` (it also writes its caller's spill slot `[RSP + 8, RSP + 16)`). -/
def PreB (n : BitVec 64) (s : State) : Prop :=
  n.toNat ≠ 0 ∧ StackGuardOK s (120 * n.toNat - 24) ∧ StackWritable s (120 * n.toNat - 16) 16 ∧
    ((s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (120 * n.toNat - 16))

/-- The call precondition of `CycC(n, k, j)`, `n ≠ 0`. -/
def PreC (n : BitVec 64) (s : State) : Prop :=
  n.toNat ≠ 0 ∧ StackGuardOK s (120 * n.toNat - 64) ∧ StackWritable s (120 * n.toNat - 56) 8 ∧
    ((s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16 ∨ (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (120 * n.toNat - 56))

theorem returnsA (n k j : BitVec 64) :
    Ensures Extracted.program (entryOf .a) [n] (PreA n) (fun _ s' => s'.regs 0 = cA n.toNat) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  simp only [entryOf] at hs
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns (summary .a) hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, trivial, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0, adj, below, above]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨v1, v2, v3, f, m, rfl, -⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, result, h_a0]

theorem returnsB (n k j : BitVec 64) :
    Ensures Extracted.program (entryOf .b) [n] (PreB n) (fun _ s' => s'.regs 0 = cB n (cA (n.toNat - 1))) := by
  intro ret hret s hs ⟨hnz, hg, hst, hd⟩
  simp only [entryOf] at hs
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns (summary .b) hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, by simpa only [h_a0] using hnz, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0, adj, below, above]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨v1, v2, v3, f, m, rfl, -⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, result, h_a0]

theorem returnsC (n k j : BitVec 64) :
    Ensures Extracted.program (entryOf .c) [n, k, j] (PreC n) (fun _ s' => s'.regs 0 = cC n k j (cA (n.toNat - 1))) := by
  intro ret hret s hs ⟨hnz, hg, hst, hd⟩
  simp only [entryOf] at hs
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns (summary .c) hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, by simpa only [h_a0] using hnz, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0, adj, below, above]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨v1, v2, v3, f, m, rfl, -⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, result, h_a0, h_a1, h_a2]

/-- `CycA(n) = cA n` for every `n`; `CycB(n) = cB n (cA (n-1))` and
`CycC(n, k, j) = cC n k j (cA (n-1))` for `n ≠ 0`; each given the stack its calls use. -/
theorem correctness (n k j : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (PreA n) (fun _ s' => s'.regs 0 = cA n.toNat) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.CycB") [n] (PreB n)
      (fun _ s' => s'.regs 0 = cB n (cA (n.toNat - 1))) ∧
    Ensures Extracted.program (segAddr Extracted.program "example.com/basic.CycC") [n, k, j]
      (PreC n) (fun _ s' => s'.regs 0 = cC n k j (cA (n.toNat - 1))) :=
  ⟨returnsA n k j, returnsB n k j, returnsC n k j⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness call state at `pc` with `RAX = 2`, `RBX = 5`, `RCX = 7` on `EqHashModel.wmem64`
(return address `wret` at `[wsp]`), goroutine `wg` (stack guard 0). -/
def s0 (pc : Nat) : State :=
  { regs := fun i => if i = 0 then 2#64 else if i = 3 then 5#64 else if i = 1 then 7#64
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 pc, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup1 (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [2#64] (s0 pc) :=
  ⟨rfl, wmem64_ret, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem setup3 (pc : Nat) : CallSetup (Extracted.program.withExit ret) pc [2#64, 5#64, 7#64] (s0 pc) :=
  ⟨rfl, wmem64_ret, rfl, by decide, by
    intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpreA (pc : Nat) : PreA 2#64 (s0 pc) := by
  unfold PreA s0
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [regSP, regG, stackguard0, stackguard0Offset] <;> decide

theorem hpreB (pc : Nat) : PreB 2#64 (s0 pc) := by
  unfold PreB s0
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [regSP, regG, stackguard0, stackguard0Offset] <;> decide

theorem hpreC (pc : Nat) : PreC 2#64 (s0 pc) := by
  unfold PreC s0
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [regSP, regG, stackguard0, stackguard0Offset] <;> decide

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
