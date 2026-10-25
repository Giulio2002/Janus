import Extracted

/-!
# `runtime.memequal32` meets the `MemequalN … 4` contract

**Guarantee.** For every stack bound `d`, the machine code of Go 1.26's `runtime.memequal32(a, b)`
(the equality function of 4-byte memory types) satisfies `Janus.Contracts.Mem.MemequalN … d 4`:
from every call state with the contract's precondition (the stack guard and ABI conditions, the
4 bytes at `a` and at `b` readable) it returns to `X30` without faulting, keeps `SP`, `X18`,
`X28`, `X29` and `FPCR`, changes no memory, and returns in the low byte of `X0` whether the 4
bytes at `a` equal the 4 bytes at `b`.

**What the code does.** It `MOVW` loads the two 32-bit words (sign-extended), `CMPW` compares their low halves, `CSET EQ`; no frame, no stack check.

**Assumptions.** Only the contract's precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 4 := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run
  refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
    (MemFrame.refl _ _) ?_
  simp [BoolRes, setReg]
  have h0 := s.mem.readLE_lt (s.regs 0).toNat 4
  have h1 := s.mem.readLE_lt (s.regs 1).toNat 4
  generalize s.mem.readLE (s.regs 0).toNat 4 = x at *
  generalize s.mem.readLE (s.regs 1).toNat 4 = y at *
  by_cases h : y = x
  · subst h; simp
  · have h' : (x == y) = false := beq_false_of_ne (Ne.symm h)
    simp only [h']
    split <;> split <;> split <;> simp_all <;> omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal32(VAL, VAL)` on `EqHashModel.wmem` (`VAL` holds 42), goroutine `wg`
(its stack guard word is 0), stack pointer `wsp`, return address `wret`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 VAL else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 4 ∧ Input s0 64 2 (s0.regs 1).toNat 4 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (EqPre 64 2 s ∧ Input s 64 2 (s.regs 0).toNat 4 ∧ Input s 64 2 (s.regs 1).toNat 4) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true` (the same bytes). -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  have h01 : s0.regs 1 = s0.regs 0 := rfl
  obtain ⟨k, s', h1, h2, h3⟩ := correctness 64 s0 rfl pre
  exact ⟨k, s', h1, h2, by simpa only [h01, beq_self_eq_true] using h3⟩

end Witness

end Proof
