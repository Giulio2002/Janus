import Extracted

/-!
# `runtime.f32equal` meets the `Fequal binary32 4` contract

**Guarantee.** For every stack bound `d`, the machine code of Go 1.26's `runtime.f32equal(a, b)`
(the equality function of `float32`) satisfies `Janus.Contracts.Mem.Fequal … d binary32 4`: from every
call state with the contract's precondition (stack guard and ABI conditions, `FPCR = 0`, the 4
bytes at `a` and at `b` readable) it returns to `X30` without faulting, keeps `SP`, `X18`,
`X28`, `X29` and `FPCR`, changes no memory, and the low byte of `X0` is `feq binary32 x y` (Go's `==`: false if either is a NaN, `+0 == -0`) for the floats `x`, `y` at `a` and `b`.

**What the code does.** `FMOVS` loads the two floats into `S0`, `S1`, `FCMPS`, `CSET EQ` (`Z` is set exactly for Go's `==`: `fpCompare_z`); no frame, no stack check. The comparison may set cumulative
exception bits in `FPSR` (which the contract leaves arbitrary).

**Assumptions.** Only the contract's precondition; `FPCR = 0` is what the comparison's flags
are computed under (round to nearest, no flush-to-zero, no traps).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts Janus.Contracts.Mem

namespace Proof

theorem correctness (d : Nat) : Fequal Extracted.program Extracted.entry d binary32 4 := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run [hf]
  refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl hf.symm
    (MemFrame.refl _ _) ?_
  simp [BoolRes, setReg]
  have h0 := s.mem.readLE_lt (s.regs 0).toNat 4
  have h1 := s.mem.readLE_lt (s.regs 1).toNat 4
  rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 0).toNat 4 < 4294967296),
    Nat.mod_eq_of_lt (by omega : s.mem.readLE (s.regs 1).toNat 4 < 4294967296)]
  cases feq binary32 (s.mem.readLE (s.regs 0).toNat 4) (s.mem.readLE (s.regs 1).toNat 4) <;> rfl

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `f32equal(VAL, VAL)` on `EqHashModel.wmem` (`VAL` holds 42), goroutine `wg`
(its stack guard word is 0), stack pointer `wsp`, return address `wret`, `FPCR = 0`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 VAL else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ s0.fpcr = 0 ∧ Input s0 64 2 (s0.regs 0).toNat 4 ∧
      Input s0 64 2 (s0.regs 1).toNat 4 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, rfl, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ s.fpcr = 0 ∧ Input s 64 2 (s.regs 0).toNat 4 ∧
      Input s 64 2 (s.regs 1).toNat 4) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns Go's `==` of the value at `VAL` with itself. -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r (feq binary32 (s0.mem.readLE (s0.regs 0).toNat 4) (s0.mem.readLE (s0.regs 0).toNat 4))) := by
  have h01 : s0.regs 1 = s0.regs 0 := rfl
  obtain ⟨k, s', h1, h2, h3⟩ := correctness 64 s0 rfl pre
  exact ⟨k, s', h1, h2, by simpa only [h01] using h3⟩

end Witness

end Proof
