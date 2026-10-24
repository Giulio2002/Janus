import JanusASL.Proofs.Maddl

/-! # Proved: SMULH/UMULH, the whole encoding class

Words `1 00 11011 U 10 Rm 0 11111 Rn Rd` (bits 31:24 = `10011011`, bits 22:21 = `10`, `o0 = 0`,
`Ra = 11111`; 2^16 words). Other `Ra` values are CONSTRAINED UNPREDICTABLE in ASL and rejected by
Janus' decoder. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem isr_hi (P : Int) : (integer_subrange P 127 64 : BitVec 64) = BitVec.extractLsb' 64 64 (BitVec.ofInt 128 P) := by
  apply BitVec.eq_of_toNat_eq
  show (Sail.get_slice_int 64 P 64).toNat = _
  simp only [Sail.get_slice_int, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  have h1 : (P % ((2 ^ 128 : Nat) : Int)).toNat = (P % ((2 ^ (64 + 64 + 1) : Nat) : Int)).toNat % 2 ^ 128 := by
    have hd : ((2 ^ 128 : Nat) : Int) ∣ ((2 ^ (64 + 64 + 1) : Nat) : Int) := ⟨2, by decide⟩
    rw [← Int.emod_emod_of_dvd P hd]
    have hn : 0 ≤ P % ((2 ^ (64 + 64 + 1) : Nat) : Int) := Int.emod_nonneg _ (by decide)
    generalize P % ((2 ^ (64 + 64 + 1) : Nat) : Int) = Q at hn ⊢
    omega
  have e2 : (BitVec.extractLsb' 64 64 (BitVec.ofInt 128 P)).toNat = (P % ((2 ^ 128 : Nat) : Int)).toNat / 2 ^ 64 % 2 ^ 64 := by
    simp [Nat.shiftRight_eq_div_pow]
  erw [e2]
  rw [h1, show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by decide, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod]

theorem mulh_ofInt (a b : BitVec 64) (u : Bool) :
    ((if u then a.setWidth 128 else a.signExtend 128) * (if u then b.setWidth 128 else b.signExtend 128)) =
      BitVec.ofInt 128 ((if u then (a.toNat : Int) else a.toInt) * (if u then (b.toNat : Int) else b.toInt)) := by
  have e : ∀ x : BitVec 64, x.setWidth 128 = BitVec.ofNat 128 x.toNat := by
    intro x; apply BitVec.eq_of_toNat_eq; simp
  cases u
  · simp [BitVec.signExtend, BitVec.ofInt_mul]
  · simp only [ite_true, BitVec.ofInt_mul, BitVec.ofInt_natCast, e]

set_option maxHeartbeats 4000000 in
theorem run_execute_mulh {js : Janus.Arm64.State} {s : SState} (h : Rel js s)
    {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (u : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi d 64 m n u).run s = .ok () s' ∧
      Rel (Janus.Arm64.execMulh js u m n d) s' ∧ Frame s s' := by
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd (Or.inr rfl)
    (BitVec.extractLsb' 64 64 (BitVec.ofInt 128 ((if u then ((js.getX 64 n).toNat : Int) else (js.getX 64 n).toInt) *
      (if u then ((js.getX 64 m).toNat : Int) else (js.getX 64 m).toInt))))
  refine ⟨s', ?_, ?_, hf⟩
  · simp only [execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi, run_bind,
      run_X_read_rel h hn (Or.inr rfl), run_X_read_rel h hm (Or.inr rfl), run_pure,
      run_asl_Int (by decide : 0 < 64)]
    rw [isr_hi]; exact hs'
  · have e := mulh_ofInt (js.getX 64 n) (js.getX 64 m) u
    simp only [Janus.Arm64.execMulh]
    rw [show (fun v : BitVec 64 => if u then v.setWidth 128 else v.signExtend 128) (js.getX 64 n) *
        (fun v : BitVec 64 => if u then v.setWidth 128 else v.signExtend 128) (js.getX 64 m) = _ from e]
    exact hr
set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 861 (`decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi`). -/
theorem run_DataProcReg_mulh_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 256 = 155) (h1 : (w / 2 ^ 21) % 4 = 2) (h2 : (w / 2 ^ 23) % 2 = 0) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (fld w 0 5) (fld w 5 5) (fld w 10 5) (fld w 16 5) (fld w 23 1)).run (s.set .SEE 861) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f53 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 11 == (743425#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486849#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3584002#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1488#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f58 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f59 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 15 == (29696#17 : BitVec 17)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f60 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1241#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f61 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1241#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f62 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1245#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f63 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1245#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t66_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1242#11 : BitVec 11)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t66_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (31#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s10 : Sail.BitVec.access (BitVec.ofNat 32 w) 10 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s11 : Sail.BitVec.access (BitVec.ofNat 32 w) 11 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s12 : Sail.BitVec.access (BitVec.ofNat 32 w) 12 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s13 : Sail.BitVec.access (BitVec.ofNat 32 w) 13 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s14 : Sail.BitVec.access (BitVec.ofNat 32 w) 14 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, t66_0, t66_1, s10, s11, s12, s13, s14, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 861) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 862 (`decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi`). -/
theorem run_DataProcReg_mulh_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 256 = 155) (h1 : (w / 2 ^ 21) % 4 = 2) (h2 : (w / 2 ^ 23) % 2 = 1) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (fld w 0 5) (fld w 5 5) (fld w 10 5) (fld w 16 5) (fld w 23 1)).run (s.set .SEE 862) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486856#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (208#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (464#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (720#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (976#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (11#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f14 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f15 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (10#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f16 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (106#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f17 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f18 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (74#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f19 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f20 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (42#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f25 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f26 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f27 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f28 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f29 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f30 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f31 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (466#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f32 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (978#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f33 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486853#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f34 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486852#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f35 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486855#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f38 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f39 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (212#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f40 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f41 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (724#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f42 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486854#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1238#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f50 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f51 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f52 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486848#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f53 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 11 == (743425#20 : BitVec 20)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f54 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 10 == (1486849#21 : BitVec 21)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f55 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 10 == (3584002#22 : BitVec 22)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f56 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1488#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f58 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f59 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 15 == (29696#17 : BitVec 17)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f60 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1241#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f61 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1241#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f62 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1245#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f63 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1245#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f64 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f65 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f66 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1242#11 : BitVec 11)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t67_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 21 == (1246#11 : BitVec 11)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t67_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (31#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have s10 : Sail.BitVec.access (BitVec.ofNat 32 w) 10 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s11 : Sail.BitVec.access (BitVec.ofNat 32 w) 11 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s12 : Sail.BitVec.access (BitVec.ofNat 32 w) 12 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s13 : Sail.BitVec.access (BitVec.ofNat 32 w) 13 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  have s14 : Sail.BitVec.access (BitVec.ofNat 32 w) 14 = 1#1 := access_ofNat32 _ _ (by decide) (by omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, t67_0, t67_1, s10, s11, s12, s13, s14, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg, bne_self_eq_false, Bool.or_false,
    show ((-1 : Int) < 862) = True from by decide]
  all_goals rfl


theorem run_decode_smulh_mh (Rd Rn Ra Rm : BitVec 5) (U : BitVec 1) (s : SState) :
    (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U).run s =
      (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd.toNat 64 Rm.toNat Rn.toNat
        (U == 1#1)).run s := by
  unfold decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
  rfl

theorem run_decode_umulh_mh (Rd Rn Ra Rm : BitVec 5) (U : BitVec 1) (s : SState) :
    (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U).run s =
      (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd.toNat 64 Rm.toNat Rn.toNat
        (U == 1#1)).run s := by
  unfold decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
  rfl

theorem decode_mulh_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 256 = 0b10011011)
    (h2 : (w / 2 ^ 21) % 4 = 2) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31) :
    Janus.Arm64.decode w = some (.mulh (Janus.Arm64.bit w 23) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a8 : Janus.Arm64.bits w 30 29 = 0 := by simp only [bits_def]; omega
  have a10 : Janus.Arm64.bit w 31 = true := by simp only [bit_def]; simp; omega
  have a12 : Janus.Arm64.bit w 15 = false := by simp only [bit_def]; simp; omega
  have a13 : Janus.Arm64.bits w 14 10 = 31 := by simp only [bits_def]; omega
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with e | e
  · have a7 : Janus.Arm64.bits w 24 21 = 0b1010 := by simp only [bits_def]; omega
    have a9 : Janus.Arm64.bits w 23 21 = 0b010 := by simp only [bits_def]; omega
    have a11 : Janus.Arm64.bit w 23 = false := by simp only [bit_def]; simp; omega
    simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
      Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, a12, a13, Bool.not_true]
    all_goals simp
  · have a7 : Janus.Arm64.bits w 24 21 = 0b1110 := by simp only [bits_def]; omega
    have a9 : Janus.Arm64.bits w 23 21 = 0b110 := by simp only [bits_def]; omega
    have a11 : Janus.Arm64.bit w 23 = true := by simp only [bit_def]; simp; omega
    simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
      Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, a11, a12, a13, Bool.not_true]
    all_goals simp

set_option maxHeartbeats 8000000 in
theorem asl_mulh {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 256 = 0b10011011)
    (h2 : (w / 2 ^ 21) % 4 = 2) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execMulh js (fld w 23 1 == 1#1) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 23) % 2 = 0 ∨ (w / 2 ^ 23) % 2 = 1 by omega) with hu | hu
  · rw [run_DataProcReg_mulh_0 hw hc h2 hu h3 h4 (see_entry _ _), run_decode_smulh_mh]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_mulh (h.entry (BitVec.ofNat 32 w) 861)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 23 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_mulh_1 hw hc h2 hu h3 h4 (see_entry _ _), run_decode_umulh_mh]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_mulh (h.entry (BitVec.ofNat 32 w) 862)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 23 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

/-- **SMULH/UMULH**: for every word of the encoding class and every related pair of states,
Janus' `step` and the generated ASL agree. -/
theorem mulh_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 24) % 256 = 0b10011011)
    (h2 : (w / 2 ^ 21) % 4 = 2) (h3 : (w / 2 ^ 15) % 2 = 0) (h4 : (w / 2 ^ 10) % 32 = 31)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_mulh hw hc h2 h3 h4 h (js.pc.toNat : Int)
  have hpc : ∀ u rm rn rd, (Janus.Arm64.execMulh js u rm rn rd).pc = js.pc := by
    intro u rm rn rd
    simp [Janus.Arm64.execMulh, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  refine step_agree h ⟨s2, hrun, hrel, hbt⟩ (hpc _ _ _ _) ?_
  rw [Janus.Arm64.step_of_decode (decode_mulh_class hw hc h2 h3 h4)]
  simp only [Janus.Arm64.exec, ← fld_bit w 23 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  simp [Janus.Arm64.State.next, hpc]

end JanusASL.Proofs
