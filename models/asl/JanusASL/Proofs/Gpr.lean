import JanusASL.Proofs.Monad


/-! General-purpose registers of the generated model: `read_gpr`/`write_gpr` dispatch on the
register number to the 31 Sail registers `R0`..`R30`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The value of `X<i>` held in a Sail state (`none` if the register is missing), `i < 31`. -/
def gprVal (s : SState) : Nat → Option (BitVec 64)
  | 0 => s.regs.get? .R0
  | 1 => s.regs.get? .R1
  | 2 => s.regs.get? .R2
  | 3 => s.regs.get? .R3
  | 4 => s.regs.get? .R4
  | 5 => s.regs.get? .R5
  | 6 => s.regs.get? .R6
  | 7 => s.regs.get? .R7
  | 8 => s.regs.get? .R8
  | 9 => s.regs.get? .R9
  | 10 => s.regs.get? .R10
  | 11 => s.regs.get? .R11
  | 12 => s.regs.get? .R12
  | 13 => s.regs.get? .R13
  | 14 => s.regs.get? .R14
  | 15 => s.regs.get? .R15
  | 16 => s.regs.get? .R16
  | 17 => s.regs.get? .R17
  | 18 => s.regs.get? .R18
  | 19 => s.regs.get? .R19
  | 20 => s.regs.get? .R20
  | 21 => s.regs.get? .R21
  | 22 => s.regs.get? .R22
  | 23 => s.regs.get? .R23
  | 24 => s.regs.get? .R24
  | 25 => s.regs.get? .R25
  | 26 => s.regs.get? .R26
  | 27 => s.regs.get? .R27
  | 28 => s.regs.get? .R28
  | 29 => s.regs.get? .R29
  | 30 => s.regs.get? .R30
  | _ => none

/-- `X<d> := v` in a Sail state. -/
def setGpr (s : SState) (v : BitVec 64) : Nat → SState
  | 0 => s.set .R0 v
  | 1 => s.set .R1 v
  | 2 => s.set .R2 v
  | 3 => s.set .R3 v
  | 4 => s.set .R4 v
  | 5 => s.set .R5 v
  | 6 => s.set .R6 v
  | 7 => s.set .R7 v
  | 8 => s.set .R8 v
  | 9 => s.set .R9 v
  | 10 => s.set .R10 v
  | 11 => s.set .R11 v
  | 12 => s.set .R12 v
  | 13 => s.set .R13 v
  | 14 => s.set .R14 v
  | 15 => s.set .R15 v
  | 16 => s.set .R16 v
  | 17 => s.set .R17 v
  | 18 => s.set .R18 v
  | 19 => s.set .R19 v
  | 20 => s.set .R20 v
  | 21 => s.set .R21 v
  | 22 => s.set .R22 v
  | 23 => s.set .R23 v
  | 24 => s.set .R24 v
  | 25 => s.set .R25 v
  | 26 => s.set .R26 v
  | 27 => s.set .R27 v
  | 28 => s.set .R28 v
  | 29 => s.set .R29 v
  | 30 => s.set .R30 v
  | _ => s

theorem run_read_gpr {s : SState} {i : Nat} (hi : i < 31) {v : BitVec 64}
    (h : gprVal s i = some v) : (read_gpr i).run s = .ok v s := by
  match i, hi with
  | 0, _ => exact run_readReg h
  | 1, _ => exact run_readReg h
  | 2, _ => exact run_readReg h
  | 3, _ => exact run_readReg h
  | 4, _ => exact run_readReg h
  | 5, _ => exact run_readReg h
  | 6, _ => exact run_readReg h
  | 7, _ => exact run_readReg h
  | 8, _ => exact run_readReg h
  | 9, _ => exact run_readReg h
  | 10, _ => exact run_readReg h
  | 11, _ => exact run_readReg h
  | 12, _ => exact run_readReg h
  | 13, _ => exact run_readReg h
  | 14, _ => exact run_readReg h
  | 15, _ => exact run_readReg h
  | 16, _ => exact run_readReg h
  | 17, _ => exact run_readReg h
  | 18, _ => exact run_readReg h
  | 19, _ => exact run_readReg h
  | 20, _ => exact run_readReg h
  | 21, _ => exact run_readReg h
  | 22, _ => exact run_readReg h
  | 23, _ => exact run_readReg h
  | 24, _ => exact run_readReg h
  | 25, _ => exact run_readReg h
  | 26, _ => exact run_readReg h
  | 27, _ => exact run_readReg h
  | 28, _ => exact run_readReg h
  | 29, _ => exact run_readReg h
  | 30, _ => exact run_readReg h
  | _ + 31, hi => exact absurd hi (by omega)

theorem run_write_gpr (s : SState) {i : Nat} (hi : i < 31) (v : BitVec 64) :
    (write_gpr i v).run s = .ok () (setGpr s v i) := by
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_0 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 0) i = if i = 0 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_1 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 1) i = if i = 1 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_2 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 2) i = if i = 2 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_3 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 3) i = if i = 3 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_4 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 4) i = if i = 4 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_5 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 5) i = if i = 5 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_6 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 6) i = if i = 6 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_7 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 7) i = if i = 7 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_8 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 8) i = if i = 8 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_9 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 9) i = if i = 9 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_10 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 10) i = if i = 10 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_11 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 11) i = if i = 11 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_12 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 12) i = if i = 12 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_13 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 13) i = if i = 13 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_14 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 14) i = if i = 14 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_15 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 15) i = if i = 15 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_16 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 16) i = if i = 16 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_17 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 17) i = if i = 17 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_18 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 18) i = if i = 18 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_19 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 19) i = if i = 19 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_20 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 20) i = if i = 20 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_21 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 21) i = if i = 21 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_22 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 22) i = if i = 22 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_23 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 23) i = if i = 23 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_24 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 24) i = if i = 24 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_25 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 25) i = if i = 25 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_26 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 26) i = if i = 26 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_27 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 27) i = if i = 27 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_28 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 28) i = if i = 28 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_29 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 29) i = if i = 29 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_30 (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v 30) i = if i = 30 then some v else gprVal s i := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 1, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 2, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 3, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 4, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 5, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 6, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 7, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 8, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 9, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 10, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 11, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 12, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 13, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 14, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 15, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 16, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 17, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 18, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 19, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 20, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 21, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 22, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 23, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 24, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 25, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 26, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 27, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 28, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 29, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | 30, _ => simp [gprVal, setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  | _ + 31, hi => exact absurd hi (by omega)

theorem gprVal_setGpr (s : SState) (v : BitVec 64) {d : Nat} (hd : d < 31) {i : Nat} (hi : i < 31) :
    gprVal (setGpr s v d) i = if i = d then some v else gprVal s i := by
  match d, hd with
  | 0, _ => exact gprVal_setGpr_0 s v hi
  | 1, _ => exact gprVal_setGpr_1 s v hi
  | 2, _ => exact gprVal_setGpr_2 s v hi
  | 3, _ => exact gprVal_setGpr_3 s v hi
  | 4, _ => exact gprVal_setGpr_4 s v hi
  | 5, _ => exact gprVal_setGpr_5 s v hi
  | 6, _ => exact gprVal_setGpr_6 s v hi
  | 7, _ => exact gprVal_setGpr_7 s v hi
  | 8, _ => exact gprVal_setGpr_8 s v hi
  | 9, _ => exact gprVal_setGpr_9 s v hi
  | 10, _ => exact gprVal_setGpr_10 s v hi
  | 11, _ => exact gprVal_setGpr_11 s v hi
  | 12, _ => exact gprVal_setGpr_12 s v hi
  | 13, _ => exact gprVal_setGpr_13 s v hi
  | 14, _ => exact gprVal_setGpr_14 s v hi
  | 15, _ => exact gprVal_setGpr_15 s v hi
  | 16, _ => exact gprVal_setGpr_16 s v hi
  | 17, _ => exact gprVal_setGpr_17 s v hi
  | 18, _ => exact gprVal_setGpr_18 s v hi
  | 19, _ => exact gprVal_setGpr_19 s v hi
  | 20, _ => exact gprVal_setGpr_20 s v hi
  | 21, _ => exact gprVal_setGpr_21 s v hi
  | 22, _ => exact gprVal_setGpr_22 s v hi
  | 23, _ => exact gprVal_setGpr_23 s v hi
  | 24, _ => exact gprVal_setGpr_24 s v hi
  | 25, _ => exact gprVal_setGpr_25 s v hi
  | 26, _ => exact gprVal_setGpr_26 s v hi
  | 27, _ => exact gprVal_setGpr_27 s v hi
  | 28, _ => exact gprVal_setGpr_28 s v hi
  | 29, _ => exact gprVal_setGpr_29 s v hi
  | 30, _ => exact gprVal_setGpr_30 s v hi
  | _ + 31, hd => exact absurd hd (by omega)

end JanusASL.Proofs
