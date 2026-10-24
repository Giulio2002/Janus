import JanusASL.Proofs.AddSubImmClass

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Close `(decide p && …) = (decide q && …)` over linear arithmetic. -/
macro "bool_omega" : tactic =>
  `(tactic| first | omega | (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.or_eq_true]; omega))
open ArmASL ArmASL.Functions

theorem uext (v : BitVec 64) (N len k L : Nat) (hN : N ≤ 64) (hl : len ≤ 64) (hL : L + 1 = min len (N - k)) (hk : k < N) :
    BitVec.zeroExtend N (BitVec.extractLsb L 0 (BitVec.setWidth N v) ++ (0#k)) =
      BitVec.setWidth N (BitVec.setWidth len v) <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_zero, hi, decide_true, Bool.true_and]
  rw [Nat.min_def] at hL
  by_cases hX : v.getLsbD (i - k) <;> by_cases hik : i < k <;> simp [hX, hik] <;> split at hL <;> (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])) <;> omega

theorem sext (v : BitVec 64) (N len k L : Nat) (hN : N ≤ 64) (hl : len ≤ 64) (hlN : len ≤ N) (hL : L + 1 = min len (N - k)) (hk : k < N) :
    BitVec.signExtend N (BitVec.extractLsb L 0 (BitVec.setWidth N v) ++ (0#k)) =
      BitVec.signExtend N (BitVec.setWidth len v) <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_zero, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, hi, decide_true, Bool.true_and]
  simp only [Nat.sub_zero, Nat.zero_add]
  have e1 : L + 1 + k - 1 - k = L := by omega
  simp only [e1]
  rw [Nat.min_def] at hL
  split at hL
  · have e2 : len - 1 = L := by omega
    rw [e2]
    by_cases h1 : i < L + 1 + k <;> by_cases h2 : i < k <;> simp [h1, h2] <;> (try omega)
    · rw [ite_cond_eq_true _ _ (eq_true (by omega))]
      cases v.getLsbD (i - k) <;> simp <;> bool_omega
    · rw [ite_cond_eq_false _ _ (eq_false (by omega))]
      cases v.getLsbD L <;> simp <;> bool_omega
  · by_cases h1 : i < L + 1 + k <;> by_cases h2 : i < k <;> simp [h1, h2] <;> (try omega)
    rw [ite_cond_eq_true _ _ (eq_true (by omega))]
    cases v.getLsbD (i - k) <;> simp <;> bool_omega

theorem sextx (v : BitVec 64) (N k L : Nat) (hN : N ≤ 64) (hL : L + 1 = min 64 (N - k)) (hk : k < N) :
    BitVec.signExtend N (BitVec.extractLsb L 0 (BitVec.setWidth N v) ++ (0#k)) = BitVec.signExtend N v <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_zero, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, hi, decide_true, Bool.true_and]
  simp only [Nat.sub_zero, Nat.zero_add]
  rw [Nat.min_def] at hL
  split at hL <;>
  · by_cases h1 : i < L + 1 + k <;> by_cases h2 : i < k <;> simp [h1, h2] <;> (try omega)
    rw [ite_cond_eq_true _ _ (eq_true (by omega))]
    cases v.getLsbD (i - k) <;> simp <;> bool_omega

def aslExtendType : Janus.Arm64.ExtendType → ExtendType
  | .uxtb => .ExtendType_UXTB
  | .uxth => .ExtendType_UXTH
  | .uxtw => .ExtendType_UXTW
  | .uxtx => .ExtendType_UXTX
  | .sxtb => .ExtendType_SXTB
  | .sxth => .ExtendType_SXTH
  | .sxtw => .ExtendType_SXTW
  | .sxtx => .ExtendType_SXTX

theorem run_Extend {M : Nat} (x : BitVec M) (N : Nat) (u : Bool) (hM : 0 < M) (hMN : M ≤ N) (s : SState) :
    (Extend x N u).run s = .ok (if u then Sail.BitVec.zeroExtend x N else sign_extend x N) s := by
  cases u
  · simp only [Extend, Bool.false_eq_true, ite_false, run_bind]
    rw [run_sail_assert_of (by simp [Sail.BitVec.length]; omega)]; rfl
  · simp only [Extend, ite_true, run_bind]
    rw [run_sail_assert_of (by simp [Sail.BitVec.length]; omega)]; rfl

set_option maxHeartbeats 40000000 in
theorem run_ExtendReg {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {m : Nat} (hm : m < 32)
    {N : Nat} (hN : N = 32 ∨ N = 64) (t : Janus.Arm64.ExtendType) {k : Nat} (hk : k ≤ 4) :
    (ExtendReg (m : Int) (aslExtendType t) (k : Int) N).run s =
      .ok (Janus.Arm64.extendReg N (js.readZR m) t k) s := by
  have hx := run_X_read_rel h hm hN
  simp only [Janus.Arm64.State.getX] at hx
  obtain e | e | e | e | e : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  all_goals subst e
  all_goals rcases hN with rfl | rfl
  all_goals cases t
  all_goals
    simp (config := { decide := true }) only [ExtendReg, aslExtendType, run_bind, hx, run_pure, run_undefined_bool,
      run_undefined_int, Janus.Arm64.extendReg, run_sail_assert_true, Int.min_def,
      decide_true, Bool.and_self, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or, ite_true, ite_false,
      Bool.false_eq_true, Bool.not_true, Bool.or_false]
    rw [run_Extend _ _ _ (by decide) (by decide)]
  all_goals
    simp only [ite_true, ite_false, Bool.false_eq_true]
    congr 1
    simp only [Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Zeros, BitVec.zero]
  all_goals first
    | exact uext _ _ 8 _ _ (by decide) (by decide) (by decide) (by decide)
    | exact uext _ _ 16 _ _ (by decide) (by decide) (by decide) (by decide)
    | exact uext _ _ 32 _ _ (by decide) (by decide) (by decide) (by decide)
    | exact (uext _ _ 64 _ _ (by decide) (by decide) (by decide) (by decide)).trans (by simp [BitVec.setWidth_eq])
    | exact sext _ _ 8 _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact sext _ _ 16 _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact sext _ _ 32 _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    | exact sextx _ _ _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
theorem run_execute_ext_eq {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n : Nat} (hm : m < 32) (hn : n < 32) (t : Janus.Arm64.ExtendType) {k : Nat}
    (hk : k ≤ 4) (S sub : Bool) :
    (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d N (aslExtendType t) m n S k sub).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate d N (Janus.Arm64.extendReg N (js.readZR m) t k)
        n S sub).run s := by
  obtain ⟨p, hp, hps⟩ := h.pstate
  by_cases hn31 : n = 31
  · subst hn31
    simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg,
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate, run_bind, run_undefined_bitvector, run_pure,
      beq_self_eq_true, ite_true, run_SP_read hp hps.sp h.sp, run_ExtendReg h hm hN t hk]
  · have hnb : ((n : Nat) == 31) = false := by simp; omega
    simp only [execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg,
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate, run_bind, run_undefined_bitvector, run_pure,
      hnb, Bool.false_eq_true, ite_false, run_X_read_rel h hn hN, run_ExtendReg h hm hN t hk]

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 22 (`decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg`). -/
theorem run_DataProcReg_ext_0 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 8 = 1) (h2 : (w / 2 ^ 29) % 4 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (fld w 0 5) (fld w 5 5) (fld w 10 3) (fld w 13 3) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 22) := by
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
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (43#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t9_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, t9_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 22) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 23 (`decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg`). -/
theorem run_DataProcReg_ext_1 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 8 = 1) (h2 : (w / 2 ^ 29) % 4 = 1) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (fld w 0 5) (fld w 5 5) (fld w 10 3) (fld w 13 3) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 23) := by
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
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (75#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t10_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, t10_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 23) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 24 (`decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg`). -/
theorem run_DataProcReg_ext_2 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 8 = 1) (h2 : (w / 2 ^ 29) % 4 = 2) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (fld w 0 5) (fld w 5 5) (fld w 10 3) (fld w 13 3) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 24) := by
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
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 24 == (107#7 : BitVec 7)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t11_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, t11_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 24) = True from by decide]
  all_goals rfl

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcReg` on its encoding class reaches clause SEE 25 (`decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg`). -/
theorem run_DataProcReg_ext_3 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 32 = 11) (h1 : (w / 2 ^ 21) % 8 = 1) (h2 : (w / 2 ^ 29) % 4 = 3) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcReg pc (BitVec.ofNat 32 w)).run s =
      (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (fld w 0 5) (fld w 5 5) (fld w 10 3) (fld w 13 3) (fld w 16 5) (fld w 29 1) (fld w 30 1) (fld w 31 1)).run (s.set .SEE 25) := by
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
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (89#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (345#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (601#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t12_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 21 == (857#10 : BitVec 10)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcReg]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, t12_0, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 25) = True from by decide]
  all_goals rfl


theorem run_DecodeRegExtend (op : BitVec 3) (s : SState) :
    (DecodeRegExtend op).run s = .ok (aslExtendType (Janus.Arm64.ExtendType.ofBits op.toNat)) s := by
  have e : op = BitVec.ofNat 3 op.toNat := by simp
  have hl := op.isLt
  rw [e]; generalize op.toNat = c at hl
  match c, hl with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | _ + 8, hl => exact absurd hl (by omega)

theorem run_decode_add_ext (Rd Rn : BitVec 5) (imm3 opt : BitVec 3) (Rm : BitVec 5) (S op sf : BitVec 1)
    (hk : imm3.toNat ≤ 4) (s : SState) :
    (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 opt Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat)) Rm.toNat Rn.toNat (S == 1#1) imm3.toNat
        (op == 1#1)).run s := by
  have hb : (imm3.toNat >b 4) = false := by simp; omega
  unfold decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
  simp only [run_bind, run_DecodeRegExtend, hb, Bool.false_eq_true, ite_false, run_pure]

theorem run_decode_adds_ext (Rd Rn : BitVec 5) (imm3 opt : BitVec 3) (Rm : BitVec 5) (S op sf : BitVec 1)
    (hk : imm3.toNat ≤ 4) (s : SState) :
    (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 opt Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat)) Rm.toNat Rn.toNat (S == 1#1) imm3.toNat
        (op == 1#1)).run s := by
  have hb : (imm3.toNat >b 4) = false := by simp; omega
  unfold decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
  simp only [run_bind, run_DecodeRegExtend, hb, Bool.false_eq_true, ite_false, run_pure]

theorem run_decode_sub_ext (Rd Rn : BitVec 5) (imm3 opt : BitVec 3) (Rm : BitVec 5) (S op sf : BitVec 1)
    (hk : imm3.toNat ≤ 4) (s : SState) :
    (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 opt Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat)) Rm.toNat Rn.toNat (S == 1#1) imm3.toNat
        (op == 1#1)).run s := by
  have hb : (imm3.toNat >b 4) = false := by simp; omega
  unfold decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
  simp only [run_bind, run_DecodeRegExtend, hb, Bool.false_eq_true, ite_false, run_pure]

theorem run_decode_subs_ext (Rd Rn : BitVec 5) (imm3 opt : BitVec 3) (Rm : BitVec 5) (S op sf : BitVec 1)
    (hk : imm3.toNat ≤ 4) (s : SState) :
    (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 opt Rm S op sf).run s =
      (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd.toNat (if sf == 1#1 then 64 else 32)
        (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat)) Rm.toNat Rn.toNat (S == 1#1) imm3.toNat
        (op == 1#1)).run s := by
  have hb : (imm3.toNat >b 4) = false := by simp; omega
  unfold decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg
  simp only [run_bind, run_DecodeRegExtend, hb, Bool.false_eq_true, ite_false, run_pure]

theorem decode_addSubExt_class {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 8 = 1) (h3 : (w / 2 ^ 10) % 8 ≤ 4) :
    Janus.Arm64.decode w = some (.addSubExt (Janus.Arm64.bit w 31) (Janus.Arm64.bit w 30) (Janus.Arm64.bit w 29)
      (Janus.Arm64.bits w 20 16) (Janus.Arm64.ExtendType.ofBits (Janus.Arm64.bits w 15 13)) (Janus.Arm64.bits w 12 10)
      (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : ¬ Janus.Arm64.bits w 28 25 / 2 = 0b101 := by simp only [bits_def]; omega
  have a4 : (Janus.Arm64.bits w 28 25 % 2 = 0 && Janus.Arm64.bits w 28 25 / 4 % 2 = 1) = false := by
    simp only [bits_def]; simp; omega
  have a5 : Janus.Arm64.bits w 28 25 % 8 = 0b101 := by simp only [bits_def]; omega
  have a6 : Janus.Arm64.bit w 28 = false := by simp only [bit_def]; simp; omega
  have a7 : Janus.Arm64.bit w 24 = true := by simp only [bit_def]; simp; omega
  have a8 : Janus.Arm64.bit w 21 = true := by simp only [bit_def]; simp; omega
  have a9 : ¬ Janus.Arm64.bits w 23 22 ≠ 0 := by simp only [bits_def]; omega
  have a10 : ¬ Janus.Arm64.bits w 12 10 > 4 := by simp only [bits_def]; omega
  simp only [Janus.Arm64.decode, a1, a2, a3, a4, a5, ite_false, ite_true, Bool.false_eq_true,
    Janus.Arm64.decodeDPReg, a6, a7, a8, a9, a10, Bool.not_true, Bool.not_false]
  all_goals simp

set_option maxHeartbeats 8000000 in
theorem asl_addSubExt {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 8 = 1) (h3 : (w / 2 ^ 10) % 8 ≤ 4)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execAddSubExt (if fld w 31 1 == 1#1 then 64 else 32) js (fld w 30 1 == 1#1)
        (fld w 29 1 == 1#1) (fld w 16 5).toNat (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
        (fld w 10 3).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      s2.regs.get? .__BranchTaken = some false := by
  rw [run_DecodeA64_DPReg hw (by omega)]
  have hk : (fld w 10 3).toNat ≤ 4 := by rw [fld_toNat w 10 3 hw]; omega
  rcases (show (w / 2 ^ 29) % 4 = 0 ∨ (w / 2 ^ 29) % 4 = 1 ∨ (w / 2 ^ 29) % 4 = 2 ∨ (w / 2 ^ 29) % 4 = 3 by omega)
    with hk1 | hk1 | hk1 | hk1
  · have hR := h.entry (BitVec.ofNat 32 w) 22
    rw [run_DataProcReg_ext_0 hw h1 h2 hk1 (see_entry _ _), run_decode_add_ext _ _ _ _ _ _ _ _ hk,
      run_execute_ext_eq hR (width_cases w) (fld_lt w 16 5) (fld_lt w 5 5) _ hk]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm hR (width_cases w) (fld_lt w 0 5) (fld_lt w 5 5)
      (Janus.Arm64.extendReg _ (js.readZR (fld w 16 5).toNat) (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
        (fld w 10 3).toNat) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · have hR := h.entry (BitVec.ofNat 32 w) 23
    rw [run_DataProcReg_ext_1 hw h1 h2 hk1 (see_entry _ _), run_decode_adds_ext _ _ _ _ _ _ _ _ hk,
      run_execute_ext_eq hR (width_cases w) (fld_lt w 16 5) (fld_lt w 5 5) _ hk]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm hR (width_cases w) (fld_lt w 0 5) (fld_lt w 5 5)
      (Janus.Arm64.extendReg _ (js.readZR (fld w 16 5).toNat) (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
        (fld w 10 3).toNat) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · have hR := h.entry (BitVec.ofNat 32 w) 24
    rw [run_DataProcReg_ext_2 hw h1 h2 hk1 (see_entry _ _), run_decode_sub_ext _ _ _ _ _ _ _ _ hk,
      run_execute_ext_eq hR (width_cases w) (fld_lt w 16 5) (fld_lt w 5 5) _ hk]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm hR (width_cases w) (fld_lt w 0 5) (fld_lt w 5 5)
      (Janus.Arm64.extendReg _ (js.readZR (fld w 16 5).toNat) (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
        (fld w 10 3).toNat) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩
  · have hR := h.entry (BitVec.ofNat 32 w) 25
    rw [run_DataProcReg_ext_3 hw h1 h2 hk1 (see_entry _ _), run_decode_subs_ext _ _ _ _ _ _ _ _ hk,
      run_execute_ext_eq hR (width_cases w) (fld_lt w 16 5) (fld_lt w 5 5) _ hk]
    obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_addsub_imm hR (width_cases w) (fld_lt w 0 5) (fld_lt w 5 5)
      (Janus.Arm64.extendReg _ (js.readZR (fld w 16 5).toNat) (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
        (fld w 10 3).toNat) (fld w 29 1 == 1#1) (fld w 30 1 == 1#1)
    exact ⟨s2, hrun, hrel, bt_after _ _ hfr⟩

/-- **ADD/ADDS/SUB/SUBS (extended register)**: for every word of the encoding class that Janus
decodes (`opt = 00`, `imm3 ≤ 4`) and every related pair of states, Janus' `step` and the
generated ASL agree. -/
theorem addSubExt_agree {w : Nat} (hw : w < 2 ^ 32) (h1 : (w / 2 ^ 24) % 32 = 0b01011)
    (h2 : (w / 2 ^ 21) % 8 = 1) (h3 : (w / 2 ^ 10) % 8 ≤ 4)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execAddSubExt N js (fld w 30 1 == 1#1)
    (fld w 29 1 == 1#1) (fld w 16 5).toNat (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)
    (fld w 10 3).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp only [F, Janus.Arm64.execAddSubExt]
    split <;> simp [Janus.Arm64.State.setX, Janus.Arm64.State.setXSP, Janus.Arm64.State.writeZR,
      Janus.Arm64.State.writeSP, Janus.Arm64.State.setFlags] <;> split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_addSubExt hw h1 h2 h3 h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_addSubExt_class hw h1 h2 h3)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw, ← fld_bit w 30 hw, ← fld_bit w 29 hw,
    bits_eq_fld w 15 13 hw, bits_eq_fld w 20 16 hw, bits_eq_fld w 12 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

end JanusASL.Proofs
