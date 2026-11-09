import Janus

/-! `Janus.Arm64.decode` on whole encoding classes (words given by their fixed bits). -/

namespace JanusASL.Proofs
open Janus.Arm64

theorem bits_def (w hi lo : Nat) : bits w hi lo = (w / 2 ^ lo) % 2 ^ (hi + 1 - lo) := by
  simp [bits, Nat.shiftRight_eq_div_pow]

/-- Add/subtract (immediate): `sf op S 100010 sh imm12 Rn Rd`. -/
theorem decode_addSubImm_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100010) :
    decode w = some (.addSubImm (bit w 31) (bit w 30) (bit w 29) (bit w 22) (bits w 21 10)
      (bits w 9 5) (bits w 4 0)) := by
  have h1 : ¬ w ≥ 2 ^ 32 := by omega
  have h2 : bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have h3 : bits w 25 23 = 0b010 := by simp only [bits_def]; omega
  simp only [decode, h1, h2, if_false, if_true, decodeDPImm, h3]
  simp

theorem bit_def (w i : Nat) : bit w i = ((w / 2 ^ i) % 2 == 1) := by
  simp [bit, Nat.shiftRight_eq_div_pow]

/-- ADC/ADCS/SBC/SBCS: `sf op S 11010000 Rm 000000 Rn Rd`. -/
theorem decode_addSubCarry_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 256 = 0b11010000)
    (h2 : (w / 2 ^ 10) % 64 = 0) :
    decode w = some (.addSubCarry (bit w 31) (bit w 30) (bit w 29) (bits w 20 16) (bits w 9 5) (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0 := by simp only [bits_def]; omega
  have a8 : ¬ bits w 15 10 ≠ 0 := by simp only [bits_def]; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8,
    Bool.not_true]

/-- CSEL/CSINC/CSINV/CSNEG: `sf op 0 11010100 Rm cond 0 o2 Rn Rd`. -/
theorem decode_condSel_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b011010100)
    (h2 : (w / 2 ^ 11) % 2 = 0) :
    decode w = some (.condSel (bit w 31) (bit w 30) (bits w 20 16) (bits w 15 12) (bit w 10) (bits w 9 5)
      (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0b0100 := by simp only [bits_def]; omega
  have a8 : bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : bit w 11 = false := by simp only [bit_def]; simp; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    Bool.not_true, Bool.false_or]
  simp

theorem decode_condCmpReg_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 0) :
    decode w = some (.condCmpReg (bit w 31) (bit w 30) (bits w 20 16) (bits w 15 12) (bits w 9 5) (bits w 3 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0b0010 := by simp only [bits_def]; omega
  have a8 : bit w 29 = true := by simp only [bit_def]; simp; omega
  have a9 : bit w 10 = false := by simp only [bit_def]; simp; omega
  have a10 : bit w 4 = false := by simp only [bit_def]; simp; omega
  have a11 : bit w 11 = false := by simp only [bit_def]; simp; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    a10, a11, Bool.not_true, Bool.false_or, Bool.or_false, Bool.not_false]
  all_goals simp

theorem decode_condCmpImm_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 512 = 0b111010010)
    (h2 : (w / 2 ^ 10) % 2 = 0) (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 1) :
    decode w = some (.condCmpImm (bit w 31) (bit w 30) (bits w 20 16) (bits w 15 12) (bits w 9 5) (bits w 3 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0b0010 := by simp only [bits_def]; omega
  have a8 : bit w 29 = true := by simp only [bit_def]; simp; omega
  have a9 : bit w 10 = false := by simp only [bit_def]; simp; omega
  have a10 : bit w 4 = false := by simp only [bit_def]; simp; omega
  have a11 : bit w 11 = true := by simp only [bit_def]; simp; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    a10, a11, Bool.not_true, Bool.false_or, Bool.or_false, Bool.not_false]
  all_goals simp

/-- MADD/MSUB: `sf 00 11011 000 Rm o0 Ra Rn Rd`. -/
theorem decode_madd_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011011000) :
    decode w = some (.madd (bit w 31) (bit w 15) (bits w 20 16) (bits w 14 10) (bits w 9 5) (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0b1000 := by simp only [bits_def]; omega
  have a8 : bits w 30 29 = 0 := by simp only [bits_def]; omega
  have a9 : bits w 23 21 = 0 := by simp only [bits_def]; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    Bool.not_true]
  all_goals simp

/-- ADD/SUB (shifted register): `sf op S 01011 shift 0 Rm imm6 Rn Rd`, `shift ≠ 11`, imm6 < 32 if sf = 0. -/
theorem decode_addSubShifted_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 2 = 0) (h3 : (w / 2 ^ 22) % 4 ≠ 3)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) :
    decode w = some (.addSubShifted (bit w 31) (bit w 30) (bit w 29) (ShiftType.ofBits (bits w 23 22))
      (bits w 20 16) (bits w 15 10) (bits w 9 5) (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = false := by simp only [bit_def]; simp; omega
  have a7 : bit w 24 = true := by simp only [bit_def]; simp; omega
  have a8 : bit w 21 = false := by simp only [bit_def]; simp; omega
  have a9 : ¬ bits w 23 22 = 3 := by simp only [bits_def]; omega
  have a10 : (!bit w 31 && decide (bits w 15 10 ≥ 32)) = false := by
    simp only [bit_def, bits_def]; simp; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    Bool.not_true, Bool.not_false, a10]
  all_goals simp

/-- Logical (shifted register): `sf opc 01010 shift N Rm imm6 Rn Rd`, imm6 < 32 if sf = 0. -/
theorem decode_logicalShifted_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01010)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) :
    decode w = some (.logicalShifted (bit w 31) (LogicOp.ofBits (bits w 30 29)) (ShiftType.ofBits (bits w 23 22))
      (bit w 21) (bits w 20 16) (bits w 15 10) (bits w 9 5) (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = false := by simp only [bit_def]; simp; omega
  have a7 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have a10 : (!bit w 31 && decide (bits w 15 10 ≥ 32)) = false := by
    simp only [bit_def, bits_def]; simp; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7,
    Bool.not_true, Bool.not_false, a10]
  all_goals simp

/-- LSLV/LSRV/ASRV/RORV: `sf 0 0 11010110 Rm 0010 op2 Rn Rd`. -/
theorem decode_shiftV_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110)
    (h2 : (w / 2 ^ 12) % 16 = 0b0010) :
    decode w = some (.shiftV (bit w 31) (ShiftType.ofBits (bits w 11 10)) (bits w 20 16) (bits w 9 5)
      (bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (bits w 28 25 % 2 = 0 && bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : bit w 30 = false := by simp only [bit_def]; simp; omega
  have hop : bits w 15 10 = 8 + bits w 11 10 := by simp only [bits_def]; omega
  have hlt : bits w 11 10 < 4 := by simp only [bits_def]; omega
  simp only [decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true, decodeDPReg, a6, a7, a8, a9,
    Bool.not_true, Bool.not_false, hop]
  generalize bits w 11 10 = c at hlt
  match c, hlt with
  | 0, _ => simp [ShiftType.ofBits]
  | 1, _ => simp [ShiftType.ofBits]
  | 2, _ => simp [ShiftType.ofBits]
  | 3, _ => simp [ShiftType.ofBits]
  | _ + 4, hl => exact absurd hl (by omega)

end JanusASL.Proofs
