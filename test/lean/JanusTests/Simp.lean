import Janus.Arm64.Exec

/-!
# `step` on symbolic states

`step` on a literal word must reduce by `simp` (for proof automation) and by `rfl` once the
decoding is known. These lemma lists are what such automation needs to unfold: the decoder
(`decode` and its class decoders, `bits`, `bit`, the `ofBits` field decoders), the executor
(`exec` and the `exec*` helper of the instruction class), the pseudocode helpers
(`addSub`, `shiftReg`, ...) and the register accessors.
-/

namespace JanusTests.Simp
open Janus.Arm64

/-- `add x0, x0, x1` (Go: `ADD R1, R0, R0`), fully by `simp`. -/
example (s : State) : step 0x8b010000 s =
    .ok { s with regs := fun i => if i = 0 then s.regs 0 + s.regs 1 else s.regs i,
                 pc := s.pc + 4 } := by
  simp [step, decodeAll, decode, decodeDPReg, bits, bit, ShiftType.ofBits, exec, execAddSubShifted,
    shiftReg, State.getX, State.setX, State.readZR, State.writeZR, State.next]

/-- The same via `step_of_decode`, with the decoding discharged by `rfl`. -/
example (s : State) : step 0x8b010000 s =
    .ok { s with regs := fun i => if i = 0 then s.regs 0 + s.regs 1 else s.regs i,
                 pc := s.pc + 4 } := by
  rw [step_of_decode (i := .addSubShifted true false false .lsl 1 0 0 0) rfl]
  simp [exec, execAddSubShifted, shiftReg, State.getX, State.setX, State.readZR,
    State.writeZR, State.next]

/-- `sub sp, sp, #0x20` (function prologue). -/
example (s : State) : step 0xd10083ff s = .ok { s with sp := s.sp - 32, pc := s.pc + 4 } := by
  simp [step, decodeAll, decode, decodeDPImm, bits, bit, exec, execAddSubImm, State.getXSP,
    State.setXSP, State.readSP, State.writeSP, State.next]

/-- `cmp x1, x2` sets the flags from `AddWithCarry(x1, NOT x2, 1)` and writes no register. -/
example (s : State) : step 0xeb02003f s =
    .ok { s with flags := (addSub (s.regs 1) (s.regs 2) true).2, pc := s.pc + 4 } := by
  simp [step, decodeAll, decode, decodeDPReg, bits, bit, ShiftType.ofBits, exec, execAddSubShifted,
    shiftReg, State.getX, State.setX, State.readZR, State.writeZR, State.setFlags, State.next]

/-- `b.gt` taken / not taken, with the condition left symbolic. -/
example (s : State) : step 0x54ffff8c s =
    .ok (if conditionHolds 12 s.flags then { s with pc := s.pc + 0xfffffffffffffff0 }
         else { s with pc := s.pc + 4 }) := by
  simp [step, decodeAll, decode, decodeBranchSys, bits, bit, exec, State.next, sext64]
  split <;> rfl

/-- `ldr x16, [x28, #16]` (Go stack-bound check) on a symbolic state, given that the checked
load at `X28 + 16` succeeds. -/
example (s : State) (v : Nat) (h : load s.mem (s.regs 28 + 16).toNat 8 = .ok v) :
    step 0xf9400b90 s =
      .ok { s with regs := fun i => if i = 16 then BitVec.ofNat 64 v else s.regs i,
                   pc := s.pc + 4 } := by
  simp at h
  simp [step, decodeAll, decode, decodeLdSt, bits, bit, validSizeOpc, exec, memIndexed, baseAddr,
    memSingle, State.writeZR, State.next, h]

/-- The same load faults exactly when the checked load does. -/
example (s : State) (e : Fault) (h : load s.mem (s.regs 28 + 16).toNat 8 = .error e) :
    step 0xf9400b90 s = .error e := by
  simp at h
  simp [step, decodeAll, decode, decodeLdSt, bits, bit, validSizeOpc, exec, memIndexed, baseAddr,
    memSingle, h]

end JanusTests.Simp
