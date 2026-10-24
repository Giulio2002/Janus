import JanusASL.Proofs.Maddl

/-! # Proved: UDIV/SDIV, the whole encoding class

Words `sf 0 0 11010110 Rm 00001 o1 Rn Rd` (bits 30:21 = `0011010110`, bits 15:11 = `00001`;
2^17 words). ASL computes `RoundTowardsZero(Real(a) / Real(b))` over the reals (exact rationals,
see docs/ASL.md); `rtz` proves that this is `Int.tdiv`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem rat_floor_div (a b : Int) (hb : 0 < b) : ((a : Rat) / (b : Rat)).floor = a / b := by
  have hbq : (0 : Rat) < (b : Rat) := Rat.intCast_pos.mpr hb
  have e := Int.emod_add_ediv_mul a b
  have h0 := Int.emod_nonneg a (show b ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos a hb
  have h1 : a / b * b ≤ a := by omega
  have h2 : a < (a / b + 1) * b := by rw [Int.add_mul, Int.one_mul]; omega
  apply Int.le_antisymm
  · have : ((a : Rat) / b).floor < a / b + 1 := by
      rw [Rat.floor_lt_iff, Rat.div_lt_iff hbq]
      have := Rat.intCast_lt_intCast.mpr h2
      simpa [Rat.intCast_mul, Rat.intCast_add] using this
    omega
  · rw [Rat.le_floor_iff]
    apply Classical.byContradiction; intro hn
    have hlt : (a : Rat) / b < ((a / b : Int) : Rat) := Rat.not_le.mp hn
    rw [Rat.div_lt_iff hbq] at hlt
    have : a < a / b * b := by
      have := hlt; rw [← Rat.intCast_mul] at this; exact Rat.intCast_lt_intCast.mp this
    omega


theorem rtz_pos (a b : Int) (hb : 0 < b) :
    RoundTowardsZero (div_real (to_real a) (to_real b)) = a.tdiv b := by
  have hbq : (0 : Rat) < (b : Rat) := Rat.intCast_pos.mpr hb
  have ht : to_real = (fun x : Int => (x : Rat)) := rfl
  simp only [RoundTowardsZero, div_real, ht, lt_real, round_up, round_down]
  by_cases ha : 0 ≤ a
  · have hn : ¬ ((a : Rat) / b < ((0 : Int) : Rat)) := by
      rw [Rat.div_lt_iff hbq]; intro h
      have : a < 0 * b := by rw [← Rat.intCast_mul] at h; exact Rat.intCast_lt_intCast.mp h
      omega
    simp only [hn, decide_false, Bool.false_eq_true, ite_false, rat_floor_div a b hb,
      Int.tdiv_eq_ediv_of_nonneg ha]
  · have hp : ((a : Rat) / b < ((0 : Int) : Rat)) := by
      rw [Rat.div_lt_iff hbq, ← Rat.intCast_mul]; exact Rat.intCast_lt_intCast.mpr (by omega)
    have e : -((a : Rat) / b) = ((-a : Int) : Rat) / b := by
      rw [← Rat.divInt_eq_div, Rat.neg_divInt, Rat.divInt_eq_div]
    simp only [hp, decide_true, ite_true, Rat.ceil_eq_neg_floor_neg, e, rat_floor_div (-a) b hb]
    rw [← Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -a), Int.neg_tdiv, Int.neg_neg]

theorem rtz (a b : Int) (hb : b ≠ 0) :
    RoundTowardsZero (div_real (to_real a) (to_real b)) = a.tdiv b := by
  rcases (show 0 < b ∨ b < 0 by omega) with h | h
  · exact rtz_pos a b h
  · have e : div_real (to_real a) (to_real b) = div_real (to_real (-a)) (to_real (-b)) := by
      show ((a : Rat) / b) = ((-a : Int) : Rat) / ((-b : Int) : Rat)
      rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div, Rat.neg_divInt_neg]
    rw [e, rtz_pos (-a) (-b) (by omega), Int.neg_tdiv_neg]

theorem div_val {N : Nat} (hN : 0 < N) (x y : BitVec N) (u : Bool) (hy : y ≠ 0) :
    BitVec.ofInt N (RoundTowardsZero (div_real (to_real (if u then (x.toNat : Int) else x.toInt))
      (to_real (if u then (y.toNat : Int) else y.toInt)))) =
    (if !u then BitVec.ofInt N (Int.tdiv x.toInt y.toInt) else BitVec.ofNat N (x.toNat / y.toNat)) := by
  cases u
  · have : y.toInt ≠ 0 := by intro h; apply hy; exact BitVec.eq_of_toInt_eq (by simpa using h)
    simp [rtz _ _ this]
  · have : (y.toNat : Int) ≠ 0 := by intro h; apply hy; apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [ite_true, rtz _ _ this, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [← Int.ofNat_tdiv, BitVec.ofInt_natCast]

set_option maxHeartbeats 4000000 in
theorem run_execute_div {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (u : Bool) :
    ∃ s', (execute_aarch64_instrs_integer_arithmetic_div d N m n u).run s = .ok () s' ∧
      Rel (Janus.Arm64.execDiv N js (!u) m n d) s' ∧ Frame s s' := by
  have hN0 : 0 < N := by omega
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN
    (if js.getX N m = 0 then 0 else if !u then BitVec.ofInt N (Int.tdiv (js.getX N n).toInt (js.getX N m).toInt)
      else BitVec.ofNat N ((js.getX N n).toNat / (js.getX N m).toNat))
  refine ⟨s', ?_, by simpa [Janus.Arm64.execDiv] using hr, hf⟩
  simp only [execute_aarch64_instrs_integer_arithmetic_div, run_bind, run_X_read_rel h hn hN,
    run_X_read_rel h hm hN, run_undefined_int, run_pure, run_asl_Int hN0]
  have hz : IsZero (js.getX N m) = decide (js.getX N m = 0) := by
    simp only [IsZero, Sail.BitVec.length, BitVec.zero]
    cases js.getX N m == 0#N <;> rfl
  rw [hz]
  by_cases hy : js.getX N m = 0
  · simp only [hy, decide_true, ite_true, run_pure, integer_subrange_eq N hN0] at hs' ⊢
    simpa using hs'
  · simp only [hy, decide_false, Bool.false_eq_true, ite_false, run_bind, run_asl_Int hN0, run_pure,
      integer_subrange_eq N hN0] at hs' ⊢
    rw [div_val hN0 _ _ u hy]; exact hs'
set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 782 (`decode_udiv_aarch64_instrs_integer_arithmetic_div`). -/
theorem run_DataProcReg_div_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 214) (h1 : (w / 2 ^ 11) % 32 = 1) (h2 : (w / 2 ^ 10) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_udiv_aarch64_instrs_integer_arithmetic_div (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 16 5) (fld w 31 1)).run (s.set .SEE 782) := by
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
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (9#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (11#6 : BitVec 6)) = false := by
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
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 12 == (4#4 : BitVec 4)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 12 == (5#4 : BitVec 4)) = false := by
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
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
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
  have f57 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (3#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t58_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t58_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (2#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, t58_0, t58_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 782) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 781 (`decode_sdiv_aarch64_instrs_integer_arithmetic_div`). -/
theorem run_DataProcReg_div_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 21) % 1024 = 214) (h1 : (w / 2 ^ 11) % 32 = 1) (h2 : (w / 2 ^ 10) % 2 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_sdiv_aarch64_instrs_integer_arithmetic_div (fld w 0 5) (fld w 5 5) (fld w 10 1) (fld w 16 5) (fld w 31 1)).run (s.set .SEE 781) := by
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
  have f21 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (10#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f22 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (8#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f23 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (9#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f24 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (11#6 : BitVec 6)) = false := by
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
  have f36 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 12 == (4#4 : BitVec 4)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f37 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 12 == (5#4 : BitVec 4)) = false := by
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
  have f43 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (5#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f44 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (4#6 : BitVec 6)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f45 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f46 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (216#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f47 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f48 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 14 == (224004#18 : BitVec 18)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f49 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (12#6 : BitVec 6)) = false := by
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
  have t57_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (214#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t57_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 15 10 == (3#6 : BitVec 6)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, t57_0, t57_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 781) = True from by decide]
  all_goals rfl


theorem run_decode_udiv_dv (Rd Rn : BitVec 5) (o1 : BitVec 1) (Rm : BitVec 5) (sf : BitVec 1) (s : SState) :
    (decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_div Rd.toNat (if sf == 1#1 then 64 else 32) Rm.toNat Rn.toNat
        (o1 == 0#1)).run s := by
  unfold decode_udiv_aarch64_instrs_integer_arithmetic_div
  rfl

theorem run_decode_sdiv_dv (Rd Rn : BitVec 5) (o1 : BitVec 1) (Rm : BitVec 5) (sf : BitVec 1) (s : SState) :
    (decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_div Rd.toNat (if sf == 1#1 then 64 else 32) Rm.toNat Rn.toNat
        (o1 == 0#1)).run s := by
  unfold decode_sdiv_aarch64_instrs_integer_arithmetic_div
  rfl

theorem decode_div_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110)
    (h2 : (w / 2 ^ 11) % 32 = 1) :
    Janus.Arm64.decode w = some (.div (Janus.Arm64.bit w 31) (Janus.Arm64.bit w 10) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = true := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bits w 24 21 = 0b0110 := by simp only [bits_def]; omega
  have a8 : Janus.Arm64.bit w 29 = false := by simp only [bit_def]; simp; omega
  have a9 : Janus.Arm64.bit w 30 = false := by simp only [bit_def]; simp; omega
  rcases (show (w / 2 ^ 10) % 2 = 0 ∨ (w / 2 ^ 10) % 2 = 1 by omega) with e | e
  · have hop : Janus.Arm64.bits w 15 10 = 2 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bit w 10 = false := by simp only [bit_def]; simp; omega
    simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
      Janus.Arm64.decodeDPReg, a6, a7, a8, a9, Bool.not_true, Bool.not_false, hop, hb]
    all_goals simp
  · have hop : Janus.Arm64.bits w 15 10 = 3 := by simp only [bits_def]; omega
    have hb : Janus.Arm64.bit w 10 = true := by simp only [bit_def]; simp; omega
    simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
      Janus.Arm64.decodeDPReg, a6, a7, a8, a9, Bool.not_true, Bool.not_false, hop, hb]
    all_goals simp

set_option maxHeartbeats 8000000 in
theorem asl_div {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110)
    (h2 : (w / 2 ^ 11) % 32 = 1) {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execDiv (if fld w 31 1 == 1#1 then 64 else 32) js (!(fld w 10 1 == 0#1))
        (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  rcases (show (w / 2 ^ 10) % 2 = 0 ∨ (w / 2 ^ 10) % 2 = 1 by omega) with ho | ho
  · rw [run_DataProcReg_div_0 hw h1 h2 ho (see_entry _ _), run_decode_udiv_dv]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_div (h.entry (BitVec.ofNat 32 w) 782) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 10 1 == 0#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩
  · rw [run_DataProcReg_div_1 hw h1 h2 ho (see_entry _ _), run_decode_sdiv_dv]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_div (h.entry (BitVec.ofNat 32 w) 781) (width_cases w)
      (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) (fld w 10 1 == 0#1)
    exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem not_fld_eq0 (w i : Nat) (hw : w < 2 ^ 32) : (!(fld w i 1 == 0#1)) = Janus.Arm64.bit w i := by
  rw [← fld_bit w i hw]
  have := fld_lt w i 1
  generalize fld w i 1 = x at this
  revert x; decide

/-- **UDIV/SDIV**: for every word of the encoding class and every related pair of states, Janus'
`step` and the generated ASL agree (including division by zero and `INT_MIN / -1`). -/
theorem div_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110)
    (h2 : (w / 2 ^ 11) % 32 = 1) {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_div hw h1 h2 h (js.pc.toNat : Int)
  have hpc : ∀ N sg rm rn rd, (Janus.Arm64.execDiv N js sg rm rn rd).pc = js.pc := by
    intro N sg rm rn rd
    simp [Janus.Arm64.execDiv, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  rw [not_fld_eq0 w 10 hw] at hrel
  have e : Janus.Arm64.execDiv (if fld w 31 1 == 1#1 then 64 else 32) js (Janus.Arm64.bit w 10)
      (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat =
    if fld w 31 1 == 1#1 then Janus.Arm64.execDiv 64 js (Janus.Arm64.bit w 10) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat
    else Janus.Arm64.execDiv 32 js (Janus.Arm64.bit w 10) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat := by
    split <;> rfl
  rw [e] at hrel
  refine step_agree h ⟨s2, hrun, hrel, hbt⟩ (by split <;> exact hpc _ _ _ _ _) ?_
  have p64 := hpc 64 (Janus.Arm64.bit w 10) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  have p32 := hpc 32 (Janus.Arm64.bit w 10) (fld w 16 5).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  clear hpc
  rw [Janus.Arm64.step_of_decode (decode_div_class hw h1 h2)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next]

end JanusASL.Proofs
