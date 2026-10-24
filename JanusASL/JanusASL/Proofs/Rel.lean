import Janus
import JanusASL.Proofs.Basic

/-! # Janus states against Sail states

`Rel js s`: the Sail state `s` holds Janus' architectural state `js` (the part Janus models for
the integer subset: X0-X30, SP (as SP_EL0, with PSTATE.SP = 0, i.e. EL0t), PC, NZCV) and is at EL0. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- `R0`..`R30`. -/
def isGprReg : Register → Bool
  | .R0 => true
  | .R1 => true
  | .R2 => true
  | .R3 => true
  | .R4 => true
  | .R5 => true
  | .R6 => true
  | .R7 => true
  | .R8 => true
  | .R9 => true
  | .R10 => true
  | .R11 => true
  | .R12 => true
  | .R13 => true
  | .R14 => true
  | .R15 => true
  | .R16 => true
  | .R17 => true
  | .R18 => true
  | .R19 => true
  | .R20 => true
  | .R21 => true
  | .R22 => true
  | .R23 => true
  | .R24 => true
  | .R25 => true
  | .R26 => true
  | .R27 => true
  | .R28 => true
  | .R29 => true
  | .R30 => true
  | _ => false

structure PState (f : Janus.Arm64.Flags) (p : ProcState) : Prop where
  sp : p.SP = 0#1
  el : p.EL = 0#2
  nrw : p.nRW = 0#1
  n : p.N = BitVec.ofBool f.n
  z : p.Z = BitVec.ofBool f.z
  c : p.C = BitVec.ofBool f.c
  v : p.V = BitVec.ofBool f.v

structure Rel (js : Janus.Arm64.State) (s : SState) : Prop where
  gpr : ∀ i < 31, gprVal s i = some (js.regs i)
  sp : s.regs.get? .SP_EL0 = some js.sp
  pc : s.regs.get? ._PC = some js.pc
  pstate : ∃ p, s.regs.get? .PSTATE = some p ∧ PState js.flags p

theorem get?_setGpr_0 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 0).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R0 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_1 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 1).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R1 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_2 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 2).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R2 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_3 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 3).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R3 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_4 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 4).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R4 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_5 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 5).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R5 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_6 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 6).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R6 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_7 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 7).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R7 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_8 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 8).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R8 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_9 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 9).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R9 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_10 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 10).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R10 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_11 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 11).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R11 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_12 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 12).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R12 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_13 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 13).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R13 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_14 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 14).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R14 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_15 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 15).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R15 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_16 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 16).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R16 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_17 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 17).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R17 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_18 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 18).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R18 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_19 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 19).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R19 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_20 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 20).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R20 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_21 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 21).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R21 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_22 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 22).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R22 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_23 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 23).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R23 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_24 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 24).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R24 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_25 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 25).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R25 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_26 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 26).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R26 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_27 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 27).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R27 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_28 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 28).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R28 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_29 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 29).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R29 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr_30 (s : SState) (v : BitVec 64) (r : Register) (hr : isGprReg r = false) :
    (setGpr s v 30).regs.get? r = s.regs.get? r := by
  simp only [setGpr, SState.set, Std.ExtDHashMap.get?_insert]
  have : (Register.R30 == r) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
  simp [this]

theorem get?_setGpr (s : SState) (v : BitVec 64) {d : Nat} (hd : d < 31) (r : Register)
    (hr : isGprReg r = false) : (setGpr s v d).regs.get? r = s.regs.get? r := by
  match d, hd with
  | 0, _ => exact get?_setGpr_0 s v r hr
  | 1, _ => exact get?_setGpr_1 s v r hr
  | 2, _ => exact get?_setGpr_2 s v r hr
  | 3, _ => exact get?_setGpr_3 s v r hr
  | 4, _ => exact get?_setGpr_4 s v r hr
  | 5, _ => exact get?_setGpr_5 s v r hr
  | 6, _ => exact get?_setGpr_6 s v r hr
  | 7, _ => exact get?_setGpr_7 s v r hr
  | 8, _ => exact get?_setGpr_8 s v r hr
  | 9, _ => exact get?_setGpr_9 s v r hr
  | 10, _ => exact get?_setGpr_10 s v r hr
  | 11, _ => exact get?_setGpr_11 s v r hr
  | 12, _ => exact get?_setGpr_12 s v r hr
  | 13, _ => exact get?_setGpr_13 s v r hr
  | 14, _ => exact get?_setGpr_14 s v r hr
  | 15, _ => exact get?_setGpr_15 s v r hr
  | 16, _ => exact get?_setGpr_16 s v r hr
  | 17, _ => exact get?_setGpr_17 s v r hr
  | 18, _ => exact get?_setGpr_18 s v r hr
  | 19, _ => exact get?_setGpr_19 s v r hr
  | 20, _ => exact get?_setGpr_20 s v r hr
  | 21, _ => exact get?_setGpr_21 s v r hr
  | 22, _ => exact get?_setGpr_22 s v r hr
  | 23, _ => exact get?_setGpr_23 s v r hr
  | 24, _ => exact get?_setGpr_24 s v r hr
  | 25, _ => exact get?_setGpr_25 s v r hr
  | 26, _ => exact get?_setGpr_26 s v r hr
  | 27, _ => exact get?_setGpr_27 s v r hr
  | 28, _ => exact get?_setGpr_28 s v r hr
  | 29, _ => exact get?_setGpr_29 s v r hr
  | 30, _ => exact get?_setGpr_30 s v r hr
  | _ + 31, hd => exact absurd hd (by omega)

theorem Rel.writeZR {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {d : Nat} (hd : d < 31)
    (v : BitVec 64) : Rel (js.writeZR d v) (setGpr s v d) where
  gpr i hi := by
    rw [gprVal_setGpr s v hd hi, h.gpr i hi]
    simp only [Janus.Arm64.State.writeZR, show d ≠ 31 by omega, ite_false]
    by_cases e : i = d <;> simp [e]
  sp := by
    rw [get?_setGpr s v hd _ rfl]; simpa [Janus.Arm64.State.writeZR, show d ≠ 31 by omega] using h.sp
  pc := by
    rw [get?_setGpr s v hd _ rfl]; simpa [Janus.Arm64.State.writeZR, show d ≠ 31 by omega] using h.pc
  pstate := by
    rw [get?_setGpr s v hd _ rfl]
    simpa [Janus.Arm64.State.writeZR, show d ≠ 31 by omega] using h.pstate

theorem gprVal_set (s : SState) (r : Register) (v : RegisterType r) (hr : isGprReg r = false) {i : Nat}
    (hi : i < 31) : gprVal (s.set r v) i = gprVal s i := by
  match i, hi with
  | 0, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 1, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R1) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 2, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 3, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R3) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 4, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R4) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 5, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R5) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 6, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R6) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 7, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R7) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 8, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 9, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R9) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 10, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R10) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 11, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R11) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 12, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R12) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 13, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R13) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 14, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R14) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 15, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R15) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 16, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R16) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 17, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R17) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 18, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R18) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 19, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R19) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 20, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R20) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 21, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R21) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 22, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R22) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 23, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R23) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 24, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R24) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 25, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R25) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 26, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R26) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 27, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R27) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 28, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R28) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 29, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R29) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | 30, _ =>
    simp only [gprVal, SState.set, Std.ExtDHashMap.get?_insert]
    have : (r == Register.R30) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; subst e; simp [isGprReg] at hr
    simp [this]
  | _ + 31, hi => exact absurd hi (by omega)

@[simp] theorem get?_set_self (s : SState) (r : Register) (v : RegisterType r) :
    (s.set r v).regs.get? r = some v := by
  simp [SState.set]

theorem get?_set_ne (s : SState) {r r' : Register} (v : RegisterType r) (h : r ≠ r') :
    (s.set r v).regs.get? r' = s.regs.get? r' := by
  simp [SState.set, Std.ExtDHashMap.get?_insert, h]

@[simp] theorem run_readReg_set_self (s : SState) (r : Register) (v : RegisterType r) :
    (readReg r).run (s.set r v) = .ok v (s.set r v) := run_readReg (get?_set_self s r v)

/-- `SP := v` (Janus `writeSP 31`) is `SP_EL0 := v`. -/
theorem Rel.writeSP31 {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (v : BitVec 64) :
    Rel (js.writeSP 31 v) (s.set .SP_EL0 v) where
  gpr i hi := by rw [gprVal_set s .SP_EL0 v rfl hi]; simpa [Janus.Arm64.State.writeSP] using h.gpr i hi
  sp := by simp [Janus.Arm64.State.writeSP]
  pc := by rw [get?_set_ne s (r := .SP_EL0) v (by decide)]; simpa [Janus.Arm64.State.writeSP] using h.pc
  pstate := by rw [get?_set_ne s (r := .SP_EL0) v (by decide)]; simpa [Janus.Arm64.State.writeSP] using h.pstate

/-- Writing NZCV into PSTATE. -/
theorem Rel.setFlags {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {p : ProcState}
    (hp : s.regs.get? .PSTATE = some p) (f : Janus.Arm64.Flags) :
    Rel (js.setFlags f) (s.set .PSTATE
      { p with N := BitVec.ofBool f.n, Z := BitVec.ofBool f.z, C := BitVec.ofBool f.c, V := BitVec.ofBool f.v }) where
  gpr i hi := by rw [gprVal_set s .PSTATE _ rfl hi]; simpa [Janus.Arm64.State.setFlags] using h.gpr i hi
  sp := by rw [get?_set_ne s (r := .PSTATE) _ (by decide)]; simpa [Janus.Arm64.State.setFlags] using h.sp
  pc := by rw [get?_set_ne s (r := .PSTATE) _ (by decide)]; simpa [Janus.Arm64.State.setFlags] using h.pc
  pstate := by
    obtain ⟨q, hq, hpq⟩ := h.pstate
    rw [hp] at hq; cases hq
    exact ⟨_, get?_set_self .., hpq.sp, hpq.el, hpq.nrw, rfl, rfl, rfl, rfl⟩

@[simp] theorem SState.set_set (s : SState) (r : Register) (a b : RegisterType r) :
    (s.set r a).set r b = s.set r b := by
  cases s
  simp only [SState.set, Sail.ConcurrencyInterfaceV1.SequentialState.mk.injEq, and_true]
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split <;> rfl

@[simp] theorem run_readReg_set_PSTATE (s : SState) (v : ProcState) :
    (readReg .PSTATE).run (s.set .PSTATE v) = .ok v (s.set .PSTATE v) := run_readReg_set_self s .PSTATE v
@[simp] theorem set_set_PSTATE (s : SState) (a b : ProcState) :
    (s.set .PSTATE a).set .PSTATE b = s.set .PSTATE b := SState.set_set s .PSTATE a b
@[simp] theorem get?_set_PSTATE (s : SState) (v : ProcState) :
    (s.set .PSTATE v).regs.get? .PSTATE = some v := get?_set_self s .PSTATE v

@[simp] theorem run_readReg_set_SEE (s : SState) (v : Int) :
    (readReg .SEE).run (s.set .SEE v) = .ok v (s.set .SEE v) := run_readReg_set_self s .SEE v
@[simp] theorem set_set_SEE (s : SState) (a b : Int) :
    (s.set .SEE a).set .SEE b = s.set .SEE b := SState.set_set s .SEE a b
@[simp] theorem get?_set_SEE (s : SState) (v : Int) :
    (s.set .SEE v).regs.get? .SEE = some v := get?_set_self s .SEE v

@[simp] theorem run_readReg_set_BranchTaken (s : SState) (v : Bool) :
    (readReg .__BranchTaken).run (s.set .__BranchTaken v) = .ok v (s.set .__BranchTaken v) := run_readReg_set_self s .__BranchTaken v
@[simp] theorem set_set_BranchTaken (s : SState) (a b : Bool) :
    (s.set .__BranchTaken a).set .__BranchTaken b = s.set .__BranchTaken b := SState.set_set s .__BranchTaken a b
@[simp] theorem get?_set_BranchTaken (s : SState) (v : Bool) :
    (s.set .__BranchTaken v).regs.get? .__BranchTaken = some v := get?_set_self s .__BranchTaken v

@[simp] theorem run_readReg_set_PC (s : SState) (v : BitVec 64) :
    (readReg ._PC).run (s.set ._PC v) = .ok v (s.set ._PC v) := run_readReg_set_self s ._PC v
@[simp] theorem set_set_PC (s : SState) (a b : BitVec 64) :
    (s.set ._PC a).set ._PC b = s.set ._PC b := SState.set_set s ._PC a b
@[simp] theorem get?_set_PC (s : SState) (v : BitVec 64) :
    (s.set ._PC v).regs.get? ._PC = some v := get?_set_self s ._PC v

@[simp] theorem run_readReg_set_SP_EL0 (s : SState) (v : BitVec 64) :
    (readReg .SP_EL0).run (s.set .SP_EL0 v) = .ok v (s.set .SP_EL0 v) := run_readReg_set_self s .SP_EL0 v
@[simp] theorem set_set_SP_EL0 (s : SState) (a b : BitVec 64) :
    (s.set .SP_EL0 a).set .SP_EL0 b = s.set .SP_EL0 b := SState.set_set s .SP_EL0 a b
@[simp] theorem get?_set_SP_EL0 (s : SState) (v : BitVec 64) :
    (s.set .SP_EL0 v).regs.get? .SP_EL0 = some v := get?_set_self s .SP_EL0 v

@[simp] theorem run_readReg_set_janus_exc_taken (s : SState) (v : Bool) :
    (readReg .__janus_exc_taken).run (s.set .__janus_exc_taken v) = .ok v (s.set .__janus_exc_taken v) := run_readReg_set_self s .__janus_exc_taken v
@[simp] theorem set_set_janus_exc_taken (s : SState) (a b : Bool) :
    (s.set .__janus_exc_taken a).set .__janus_exc_taken b = s.set .__janus_exc_taken b := SState.set_set s .__janus_exc_taken a b
@[simp] theorem get?_set_janus_exc_taken (s : SState) (v : Bool) :
    (s.set .__janus_exc_taken v).regs.get? .__janus_exc_taken = some v := get?_set_self s .__janus_exc_taken v

@[simp] theorem run_readReg_set_ExclusiveMonitorSet (s : SState) (v : Bool) :
    (readReg .__ExclusiveMonitorSet).run (s.set .__ExclusiveMonitorSet v) = .ok v (s.set .__ExclusiveMonitorSet v) := run_readReg_set_self s .__ExclusiveMonitorSet v
@[simp] theorem set_set_ExclusiveMonitorSet (s : SState) (a b : Bool) :
    (s.set .__ExclusiveMonitorSet a).set .__ExclusiveMonitorSet b = s.set .__ExclusiveMonitorSet b := SState.set_set s .__ExclusiveMonitorSet a b
@[simp] theorem get?_set_ExclusiveMonitorSet (s : SState) (v : Bool) :
    (s.set .__ExclusiveMonitorSet v).regs.get? .__ExclusiveMonitorSet = some v := get?_set_self s .__ExclusiveMonitorSet v

end JanusASL.Proofs
