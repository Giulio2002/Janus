import Extracted

/-!
# `runtime.memequal128` meets the `MemequalN … 16` contract

**Guarantee.** For every stack bound `d`, the machine code of Go 1.26's `runtime.memequal128(a, b)`
(the equality function of 16-byte memory types) satisfies `Janus.Contracts.Mem.MemequalN … d 16`:
from every call state with the contract's precondition (the stack guard and ABI conditions, the
16 bytes at `a` and at `b` readable) it returns to `X30` without faulting, keeps `SP`, `X18`,
`X28`, `X29` and `FPCR`, changes no memory, and returns in the low byte of `X0` whether the 16
bytes at `a` equal the 16 bytes at `b`.

**What the code does.** It compares the first words (`CMP`, `BNE` to a `false` result), then the second words (`CSET EQ`); no frame, no stack check.

**Assumptions.** Only the contract's precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

/-- 16 bytes compare equal iff both words do. -/
theorem beq16 (m : Memory) (a b : Nat) :
    (m.readLE a 16 == m.readLE b 16) = (m.readLE a 8 == m.readLE b 8 && m.readLE (a + 8) 8 == m.readLE (b + 8) 8) := by
  rw [Bool.eq_iff_iff]; simp [readLE_16_eq_iff]

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 16 := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run
  all_goals
    refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      (MemFrame.refl _ _) ?_
    simp [BoolRes, setReg]
  all_goals
    rw [beq16]
    generalize s.mem.readLE (s.regs 0).toNat 8 = x0 at *
    generalize s.mem.readLE (s.regs 1).toNat 8 = y0 at *
    generalize s.mem.readLE ((s.regs 0).toNat + 8) 8 = x1 at *
    generalize s.mem.readLE ((s.regs 1).toNat + 8) 8 = y1 at *
    by_cases e0 : x0 = y0 <;> by_cases e1 : x1 = y1
    all_goals
      first
      | (subst e0; subst e1; simp_all)
      | (have e0' : ¬ y0 = x0 := fun h => e0 h.symm; rw [beq_false_of_ne e0]; simp_all)
      | (have e1' : ¬ y1 = x1 := fun h => e1 h.symm; subst e0; rw [beq_false_of_ne e1]; simp_all)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal128(VAL, VAL)` on `EqHashModel.wmem` (`VAL` holds 42), goroutine `wg`
(its stack guard word is 0), stack pointer `wsp`, return address `wret`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 VAL else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 16 ∧ Input s0 64 2 (s0.regs 1).toNat 16 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (EqPre 64 2 s ∧ Input s 64 2 (s.regs 0).toNat 16 ∧ Input s 64 2 (s.regs 1).toNat 16) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true` (the same bytes). -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  have h01 : s0.regs 1 = s0.regs 0 := rfl
  obtain ⟨k, s', h1, h2, h3⟩ := correctness 64 s0 rfl pre
  exact ⟨k, s', h1, h2, by simpa only [h01, beq_self_eq_true] using h3⟩

end Witness

end Proof
