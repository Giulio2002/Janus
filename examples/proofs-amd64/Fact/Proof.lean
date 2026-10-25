import Janus
import Extracted

/-! `example.com/basic.Fact(n uint64) uint64` on amd64: recursion, by well-founded induction over
calls.

For every 64-bit `n` and every call state with room for the `n + 1` nested frames (the deepest
stack-growth check falls through, `StackGuardOK s (24·n)`, and `[RSP - (24·n + 8), RSP + 16)` is
writable with the guard word outside it: per level the pushed `RBP`, the 8-byte frame and the
return address of the recursive `CALL`, plus the spill slot of `n` in the caller's frame), the
call returns `n! mod 2^64`.

`summary` is `Fact`'s callee contract from any state at its entry, proved by strong induction on
`RAX` (`Summary.induction`, `Janus/Amd64/Recursion.lean`); the induction hypothesis is used at the
recursive call with `janus64_run calls [ih]`, which proves its precondition there (`RAX - 1 < n`,
the stack one frame down). `correctness` applies it to the call state (`Summary.returns`). The
grown-stack case is not covered (docs/COVERAGE.md, R7). -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `n!`. -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- The precondition of a call `Fact(n)`, `n = RAX`: the return address readable at `[RSP]` and
below `2^47`, the stack guard `24·n` bytes below `RSP`, the stack window writable and the guard
word outside it. -/
abbrev Pre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  StackGuardOK s (24 * (s.regs 0).toNat) ∧ StackWritable s (24 * (s.regs 0).toNat + 8) 16 ∧
  ((s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16 ∨
    (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (24 * (s.regs 0).toNat + 8))

/-- What a call `Fact(n)` does: it returns (to `[RSP]`, popping it) with `RAX = n! mod 2^64`,
scratch `RCX` and flags, `RBP` restored, and memory changed only in its stack window. -/
abbrev Post (s s' : State) : Prop :=
  ∃ v1 f m,
    s' = { s with
      regs := setRegF (setRegF (setRegF s.regs 0 (BitVec.ofNat 64 (factorial (s.regs 0).toNat))) 1 v1) 4
        (s.regs 4 + 8)
      rip := retAddrOf s
      flags := f
      mem := m } ∧
    MemFrame s.mem m [((s.regs 4).toNat - (24 * (s.regs 0).toNat + 8), (s.regs 4).toNat),
      ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]

/-- The recursive step `(n-1)! · n = n!`, modulo `2^64`. -/
theorem fact_step (x : BitVec 64) (h : x.toNat ≠ 0) :
    BitVec.ofNat 64 (factorial (x.toNat - 1)) * x = BitVec.ofNat 64 (factorial x.toNat) := by
  obtain ⟨m, hm⟩ : ∃ m, x.toNat = m + 1 := ⟨x.toNat - 1, by omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hm, Nat.add_sub_cancel, factorial,
    Nat.mod_mul_mod, Nat.mul_comm]

theorem summary : Summary Extracted.program Extracted.entry Pre Post := by
  apply Summary.induction (fun s => (s.regs 0).toNat)
  intro n ih s hpc ⟨⟨⟨hra, hra'⟩, hg, ⟨hle, hnw, hacc⟩, hd⟩, hn⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr
  janus64_step
  janus64_run calls [ih]
  · refine ⟨s.regs 1, ?_, ?_, ?_, ?_⟩
    case refine_3 =>
      congr 1
      all_goals try rfl
      congr 1
      all_goals try rfl
      have hz : (s.regs 0).toNat = 0 := by assumption
      rw [hz]
      funext i; simp only [setRegF]
      split <;> split <;> first | rfl | (exfalso; omega) | (subst_vars; rfl)
    case refine_4 => janus_frame
  · unfold Post
    refine ⟨s.regs 0, ?_, ?_, ?_, ?_⟩
    case refine_3 =>
      congr 1
      all_goals try rfl
      congr 1
      all_goals try rfl
      have hz : (s.regs 0).toNat ≠ 0 := by assumption
      rw [fact_step _ hz]
    case refine_4 => janus_frame

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n]
      (fun s => StackGuardOK s (24 * n.toNat) ∧ StackWritable s (24 * n.toNat + 8) 16 ∧
        ((s.regs 4).toNat + 16 ≤ (s.regs 14).toNat + 16 ∨
          (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - (24 * n.toNat + 8)))
      (fun _ s' => (s'.regs 0).toNat = factorial n.toNat % 2 ^ 64) := by
  intro ret hret s hs ⟨hg, hst, hd⟩
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hst
  refine Summary.returns summary hret (by rw [h_rip]; rfl) (by rw [retAddrOf, h_ret]) ?_ ?_
  · refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact accessible_sub hacc (by decide) (by simp only [regSP] at *; omega) (by simp only [regSP] at *; omega)
    · rw [h_ret]; exact hret.user
    all_goals simp only [h_a0]; first | exact hg | exact ⟨hle, hnw, hacc⟩ | exact hd
  · rintro s' ⟨v1, f, m, rfl, -⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setRegF, regSP, regFP, regG, xmmZero, h_a0]

end Proof
