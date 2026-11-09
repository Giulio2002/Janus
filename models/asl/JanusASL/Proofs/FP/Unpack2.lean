import JanusASL.Proofs.FP.Exec

/-! # `FPUnpack__1` with `fpexc = FALSE` (used by `FPNeg` and `FPAbs`): no state change -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPUnpack32_nox {s : SState} (hc : LinuxEL0Config s) (x : BitVec 32) (fpcr : BitVec 64) :
    (FPUnpack__1 x fpcr false).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat false x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) s := by
  have hp0 : (Janus.Arm64.FP.unpack Janus.Float.binary32 fpcr.toNat false x.toNat).2.proc = 0 := by
    simp only [Janus.Arm64.FP.unpack]; split <;> (try split) <;> simp [Janus.Arm64.FP.raise]
  cfg_simp [FPUnpack__1, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
    undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
  simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 31 (by decide),
    access_eq (w := 23) _ 22 (by decide), get_FZ, get_AH, get_FIZ,
    upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
    Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
    Janus.Float.binary32, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
    Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] at hp0 ⊢
  generalize hn : x.toNat = n at hp0 ⊢
  have hn32 : n < 2 ^ 32 := hn ▸ x.isLt
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
    Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
    Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary32, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
    Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit] at hp0 ⊢
  by_cases he0 : n / 8388608 % 256 = 0
  · by_cases hm0 : n % 8388608 = 0
    · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
    · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
      by_cases hfiz : fpcr.toNat % 2 = 1 <;>
      simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
        Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] at hp0 ⊢ <;>
      first | rfl | (constructor; rfl; (by_cases hs : n / 2147483648 % 2 = 1 <;>
        simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
  · by_cases he1 : n / 8388608 % 256 = 255
    · by_cases hm0 : n % 8388608 = 0
      · by_cases hs : n / 2147483648 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
        first | rfl
      · by_cases hq : n % 8388608 / 4194304 % 2 = 1 <;>
        simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
    · by_cases hs : n / 2147483648 % 2 = 1 <;>
      simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val32, Rat.neg_mul,
        show (↑n / 8388608 % 256 - 127 - 23 : Int) = ↑n / 8388608 % 256 - 127 - 23 from rfl] <;>
      first | rfl


theorem run_FPUnpack64_nox {s : SState} (hc : LinuxEL0Config s) (x : BitVec 64) (fpcr : BitVec 64) :
    (FPUnpack__1 x fpcr false).run s =
      let r := Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat false x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) s := by
  have hp0 : (Janus.Arm64.FP.unpack Janus.Float.binary64 fpcr.toNat false x.toNat).2.proc = 0 := by
    simp only [Janus.Arm64.FP.unpack]; split <;> (try split) <;> simp [Janus.Arm64.FP.raise]
  cfg_simp [FPUnpack__1, FPUnpackBase, FPUnpackBase__1, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
    undefined_FPType, undefined_real, Sail.BitVec.length, run_internal_pick]
  simp only [isZero_toNat, isOnes_eq, extractLsb_toNat', access_eq x 63 (by decide),
    access_eq (w := 52) _ 51 (by decide), get_FZ, get_AH, get_FIZ,
    upd26_bit fpcr 24 (by decide), upd26_bit fpcr 1 (by decide), upd26_bit fpcr 0 (by decide), ofBool_eq_one,
    Janus.Arm64.FP.unpack, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
    Janus.Float.binary64, Janus.Float.Fmt.expMax, Janus.Float.Fmt.quietBit, Janus.Float.Fmt.signBit,
    Janus.Arm64.FP.fz, Janus.Arm64.FP.fiz, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] at hp0 ⊢
  generalize hn : x.toNat = n at hp0 ⊢
  have hn64 : n < 2 ^ 64 := hn ▸ x.isLt
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.pow_zero, Nat.div_one,
    Janus.Float.valueOf, Janus.Float.classify, Janus.Float.expOf, Janus.Float.fracOf, Janus.Float.signOf,
    Janus.Float.mantOf, Janus.Float.ulpExpOf, Janus.Float.binary64, Janus.Float.Fmt.emin, Janus.Float.Fmt.bias,
    Janus.Float.Fmt.expMax, Janus.Float.Fmt.signBit, Janus.Float.Fmt.quietBit] at hp0 ⊢
  by_cases he0 : n / 4503599627370496 % 2048 = 0
  · by_cases hm0 : n % 4503599627370496 = 0
    · simp [he0, hm0, aslFPType, valRat, neg_real]; rfl
    · by_cases hfz : fpcr.toNat / 16777216 % 2 = 1 <;> by_cases hah : fpcr.toNat / 2 % 2 = 1 <;>
      by_cases hfiz : fpcr.toNat % 2 = 1 <;>
      simp [he0, hm0, hfz, hah, hfiz, aslFPType, valRat, neg_real, run_map,
        Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC, fpExcBit] at hp0 ⊢ <;>
      first | rfl | (constructor; rfl; (by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
        simp [hs, subnormal_val, Rat.intCast_neg, Rat.neg_mul]))
  · by_cases he1 : n / 4503599627370496 % 2048 = 2047
    · by_cases hm0 : n % 4503599627370496 = 0
      · by_cases hs : n / 9223372036854775808 % 2 = 1 <;> simp [he0, he1, hm0, hs, aslFPType, valRat, neg_real] <;>
        first | rfl
      · by_cases hq : n % 4503599627370496 / 2251799813685248 % 2 = 1 <;>
        simp [he0, he1, hm0, hq, aslFPType, valRat, neg_real] <;> first | rfl
    · by_cases hs : n / 9223372036854775808 % 2 = 1 <;>
      simp [he0, he1, hs, aslFPType, valRat, neg_real, normal_val64, Rat.neg_mul,
        show (↑n / 4503599627370496 % 2048 - 1023 - 52 : Int) = ↑n / 4503599627370496 % 2048 - 1023 - 52 from rfl] <;>
      first | rfl

theorem run_FPCR_read_of {c : BitVec 32} {s : SState} (hf : s.regs.get? .FPCR = some (c.setWidth 64))
    (hk : c.toNat &&& fpcrKeep = c.toNat) : (FPCR_read ()).run s = .ok (c.setWidth 64) s := by
  simp only [FPCR_read, __get_FPCR, run_bind, run_pure, run_readReg hf, impdef_fp_io, impdef_fp_dz,
    impdef_fp_of, impdef_fp_uf, impdef_fp_ix, impdef_fp_id, impdef_fp_len, Mk_FPCR_Type, Mk_FPCRType,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hl : c.toNat < 2 ^ 32 := c.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp only [fpcrKeep] at hk
  rw [Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega),
    show 2 ^ 64 - 1 - 18446744073575350520 % 2 ^ 64 = 134201095 by decide]
  exact hk

theorem unpack_isNaN (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    (Janus.Arm64.FP.unpack f fpcr e x).1.1.isNaN = Janus.Float.isNaN f x := by
  unfold Janus.Arm64.FP.unpack Janus.Float.isNaN
  cases hk : Janus.Float.classify f x <;> simp only [hk, Janus.Arm64.FP.FPType.isNaN]
  by_cases hcnd : Janus.Arm64.FP.fz fpcr = true ∧ Janus.Arm64.FP.ah fpcr = false ∨ Janus.Arm64.FP.fiz fpcr = true
  · simp [hcnd]
  · simp [hcnd]

theorem neg_concat (w : Nat) (hw : 1 < w) (op : BitVec w) :
    ((~~~Sail.BitVec.access op (w - 1) +++ Sail.BitVec.extractLsb op (w - 2) 0 : BitVec (1 + (w - 2 - 0 + 1))).toNat) =
      if op.toNat / 2 ^ (w - 1) % 2 = 1 then op.toNat % 2 ^ (w - 1) else op.toNat % 2 ^ (w - 1) + 2 ^ (w - 1) := by
  have h := op.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_not, Sail.BitVec.access, BitVec.toNat_ofNat, extractLsb_toNat']
  have e : w - 2 - 0 + 1 = w - 1 := by omega
  rw [e]
  have hb : (BitVec.ofBool op[w - 1]!).toNat = op.toNat / 2 ^ (w - 1) % 2 := by
    have := toNat_bit_eq_getLsbD op (w - 1)
    have hlt : w - 1 < w := by omega
    have hg : op[w - 1]! = op.getLsbD (w - 1) := by simp [getElem!_def, hlt, BitVec.getLsbD_eq_getElem hlt]
    rw [hg]
    cases hx : op.getLsbD (w - 1) <;> simp [hx] at this ⊢ <;> omega
  rw [hb, Nat.pow_zero, Nat.div_one]
  have hlt2 : op.toNat % 2 ^ (w - 1) < 2 ^ (w - 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by exact hlt2), Nat.shiftLeft_eq]
  have hbit : op.toNat / 2 ^ (w - 1) % 2 = 0 ∨ op.toNat / 2 ^ (w - 1) % 2 = 1 := by omega
  rcases hbit with h0 | h1
  · rw [h0]; simp; omega
  · rw [h1]; simp

theorem ofBool_true : BitVec.ofBool true = 1#1 := rfl

theorem neg_concat32 (op : BitVec 32) :
    (~~~Sail.BitVec.access op 31 +++ Sail.BitVec.extractLsb op 30 0 : BitVec 32) =
      BitVec.ofNat 32 (Janus.Float.flipSign Janus.Float.binary32 op.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h := neg_concat 32 (by decide) op
  have h2 : (~~~Sail.BitVec.access op 31 +++ Sail.BitVec.extractLsb op 30 0 : BitVec 32).toNat =
      (~~~Sail.BitVec.access op (32 - 1) +++ Sail.BitVec.extractLsb op (32 - 2) 0 : BitVec (1 + (32 - 2 - 0 + 1))).toNat := rfl
  rw [h2, h]
  simp only [Janus.Float.flipSign, Janus.Float.signOf, Janus.Float.Fmt.signBit, Janus.Float.binary32, BitVec.toNat_ofNat]
  have hl : op.toNat < 2 ^ 32 := op.isLt
  by_cases hs : op.toNat / 2 ^ (8 + 23) % 2 = 1
  · simp [hs]; omega
  · simp [hs]; omega

theorem run_FPNeg32 {js : Janus.Arm64.State} {s : SState} (hc : LinuxEL0Config s)
    (hfpcr : s.regs.get? .FPCR = some (js.fpcr.setWidth 64)) (hk : js.fpcr.toNat &&& fpcrKeep = js.fpcr.toNat)
    (op : BitVec 32) :
    (FPNeg op).run s = .ok (BitVec.ofNat 32 (Janus.Arm64.FP.fpNeg Janus.Float.binary32 js.fpcr.toNat op.toNat)) s := by
  have ha : (32 == 16 || (32 == 32 || 32 == 64)) = true := by decide
  unfold FPNeg
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_FPType, run_internal_pick,
    Sail.BitVec.length, run_sail_assert_true, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
    run_FPCR_read_of hfpcr hk, get_AH, run_FPUnpack32_nox hc]
  have hl : js.fpcr.toNat % 18446744073709551616 = js.fpcr.toNat := Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)
  rw [hl]
  have hsn : ∀ t : Janus.Arm64.FP.FPType, (aslFPType t == FPType.FPType_SNaN) = decide (t = .snan) := by
    intro t; cases t <;> decide
  have hqn : ∀ t : Janus.Arm64.FP.FPType, (aslFPType t == FPType.FPType_QNaN) = decide (t = .qnan) := by
    intro t; cases t <;> decide
  have hnn : ∀ t : Janus.Arm64.FP.FPType, (t = .snan ∨ t = .qnan) ↔ t.isNaN = true := by
    intro t; cases t <;> simp [Janus.Arm64.FP.FPType.isNaN]
  by_cases hah : js.fpcr.toNat / 2 % 2 = 1
  · simp only [hah, decide_true, ite_true, ofBool_true]
    cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, run_FPUnpack32_nox hc, hsn, hqn, hnn,
      unpack_isNaN]
    by_cases hn : Janus.Float.isNaN Janus.Float.binary32 op.toNat = true
    · simp only [hn, ite_true, run_ME_throw, run_ME_pure]
      simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, hn, Except.map]
    · simp only [hn, ite_false, run_ME_pure]
      simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, hn, Except.map]
      exact neg_concat32 op
  · simp only [hah, decide_false, ite_false, run_ME_pure]
    simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, Except.map]
    exact neg_concat32 op

theorem neg_concat64 (op : BitVec 64) :
    (~~~Sail.BitVec.access op 63 +++ Sail.BitVec.extractLsb op 62 0 : BitVec 64) =
      BitVec.ofNat 64 (Janus.Float.flipSign Janus.Float.binary64 op.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h := neg_concat 64 (by decide) op
  have h2 : (~~~Sail.BitVec.access op 63 +++ Sail.BitVec.extractLsb op 62 0 : BitVec 64).toNat =
      (~~~Sail.BitVec.access op (64 - 1) +++ Sail.BitVec.extractLsb op (64 - 2) 0 : BitVec (1 + (64 - 2 - 0 + 1))).toNat := rfl
  rw [h2, h]
  simp only [Janus.Float.flipSign, Janus.Float.signOf, Janus.Float.Fmt.signBit, Janus.Float.binary64, BitVec.toNat_ofNat]
  have hl : op.toNat < 2 ^ 64 := op.isLt
  by_cases hs : op.toNat / 2 ^ (11 + 52) % 2 = 1
  · simp [hs]; omega
  · simp [hs]; omega

theorem run_FPNeg64 {js : Janus.Arm64.State} {s : SState} (hc : LinuxEL0Config s)
    (hfpcr : s.regs.get? .FPCR = some (js.fpcr.setWidth 64)) (hk : js.fpcr.toNat &&& fpcrKeep = js.fpcr.toNat)
    (op : BitVec 64) :
    (FPNeg op).run s = .ok (BitVec.ofNat 64 (Janus.Arm64.FP.fpNeg Janus.Float.binary64 js.fpcr.toNat op.toNat)) s := by
  have ha : (64 == 16 || (64 == 32 || 64 == 64)) = true := by decide
  unfold FPNeg
  rw [run_SailME_run]
  cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, undefined_FPType, run_internal_pick,
    Sail.BitVec.length, run_sail_assert_true, HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc,
    run_FPCR_read_of hfpcr hk, get_AH, run_FPUnpack64_nox hc]
  have hl : js.fpcr.toNat % 18446744073709551616 = js.fpcr.toNat := Nat.mod_eq_of_lt (by have := js.fpcr.isLt; omega)
  rw [hl]
  have hsn : ∀ t : Janus.Arm64.FP.FPType, (aslFPType t == FPType.FPType_SNaN) = decide (t = .snan) := by
    intro t; cases t <;> decide
  have hqn : ∀ t : Janus.Arm64.FP.FPType, (aslFPType t == FPType.FPType_QNaN) = decide (t = .qnan) := by
    intro t; cases t <;> decide
  have hnn : ∀ t : Janus.Arm64.FP.FPType, (t = .snan ∨ t = .qnan) ↔ t.isNaN = true := by
    intro t; cases t <;> simp [Janus.Arm64.FP.FPType.isNaN]
  by_cases hah : js.fpcr.toNat / 2 % 2 = 1
  · simp only [hah, decide_true, ite_true, ofBool_true]
    cfg_simp [run_ME_bind, run_ME_lift, run_ME_pure, run_ME_map, run_ME_throw, run_FPUnpack64_nox hc, hsn, hqn, hnn,
      unpack_isNaN]
    by_cases hn : Janus.Float.isNaN Janus.Float.binary64 op.toNat = true
    · simp only [hn, ite_true, run_ME_throw, run_ME_pure]
      simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, hn, Except.map]
    · simp only [hn, ite_false, run_ME_pure]
      simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, hn, Except.map]
      exact neg_concat64 op
  · simp only [hah, decide_false, ite_false, run_ME_pure]
    simp [Janus.Arm64.FP.fpNeg, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah, Except.map]
    exact neg_concat64 op

end JanusASL.Proofs
