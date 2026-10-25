import Extracted

/-!
# `runtime.memequal0` meets the `MemequalN … 0` contract

**Guarantee.** For every stack bound `d`, the machine code of Go 1.26's `runtime.memequal0(a, b)`
(the equality function of zero-size types) satisfies `Janus.Contracts.Mem.MemequalN … d 0`: from
every call state with the contract's precondition it returns to `X30` without faulting, keeps
`SP`, `X18`, `X28`, `X29` and `FPCR`, changes no memory, and returns `true` in `X0` (the zero
bytes at `a` and `b` always agree).

**What the code does.** `ORR $1, ZR, R0; RET`: it reads nothing.

**Assumptions.** Only the contract's precondition (which this code does not even need).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 0 := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, _, _⟩
  janus_run
  refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
    (MemFrame.refl _ _) ?_
  simp [BoolRes, setReg]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- The witness call state: `memequal0(VAL, VAL)` on `EqHashModel.wmem`, goroutine `wg` (its
stack guard word is 0), stack pointer `wsp`, return address `wret`. -/
def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 VAL else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

/-- The precondition holds at `s0` (stack bound 64). -/
theorem pre : EqPre 64 2 s0 ∧ Input s0 64 2 (s0.regs 0).toNat 0 ∧ Input s0 64 2 (s0.regs 1).toNat 0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, outside_cons, outside_nil] <;> decide

theorem nonvacuous : ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧
    (EqPre 64 2 s ∧ Input s 64 2 (s.regs 0).toNat 0 ∧ Input s 64 2 (s.regs 1).toNat 0) :=
  ⟨s0, rfl, pre⟩

/-- `correctness` at `s0`: the call returns `true`. -/
theorem returns : ReachesRet Extracted.program (s0.regs 30) s0
    (fun s' => EqRet 64 2 s0 s' fun r => BoolRes r true) := by
  obtain ⟨k, s', h1, h2, h3⟩ := correctness 64 s0 rfl pre
  exact ⟨k, s', h1, h2, by simpa using h3⟩

end Witness

end Proof
