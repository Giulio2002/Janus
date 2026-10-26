import JanusASL.Proofs.FP.Round64
import JanusASL.Proofs.FP.Rel

/-! # Primitives of the scalar floating-point arithmetic, width-generic (`N = 32` or `64`)

`FPUnpack`, `FPInfinity`, `FPZero`, `FPDefaultNaN`, `FPProcessNaN(s)`, `FPProcessDenorms`,
`FPRoundingMode` and `FPRound` on states `s.set .FPSR v`, against Janus' `Janus.Arm64.FP`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The format of an ASL width. -/
def fmtN (N : Nat) : Janus.Float.Fmt := if N = 32 then Janus.Float.binary32 else Janus.Float.binary64
theorem fmtN32 : fmtN 32 = Janus.Float.binary32 := rfl
theorem fmtN64 : fmtN 64 = Janus.Float.binary64 := rfl

/-- The raised exceptions of `e` do not trap under `fpcr`. -/
def NT (fpcr : Nat) (e : Janus.Arm64.FP.Exc) : Prop := e.proc &&& Janus.Arm64.FP.trapEnables fpcr = 0

theorem nt_bit {fpcr : Nat} {e : Janus.Arm64.FP.Exc} (h : NT fpcr e) {k : Nat}
    (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 7) (hp : Nat.testBit e.proc k = true) :
    Nat.testBit fpcr (k + 8) = false := by
  have h1 : Nat.testBit (e.proc &&& Janus.Arm64.FP.trapEnables fpcr) k = false := by
    unfold NT at h; rw [h]; simp
  rw [Nat.testBit_and, hp, Bool.true_and] at h1
  have h9 : Nat.testBit 0x9F k = true := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hk8 : k < 8 := by omega
  simp only [Janus.Arm64.FP.trapEnables, Nat.testBit_and, h9, Bool.and_true, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, hk8, decide_true] at h1
  simpa using h1

theorem nt_append {fpcr : Nat} {a b : Janus.Arm64.FP.Exc} : NT fpcr (a ++ b) → NT fpcr a ∧ NT fpcr b := by
  intro h
  unfold NT at *
  simp only [exc_append_proc] at h
  constructor <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
  · have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at this ⊢
    cases hi : Nat.testBit (Janus.Arm64.FP.trapEnables fpcr) i <;> simp_all

theorem nt_left {fpcr : Nat} {a b : Janus.Arm64.FP.Exc} (h : NT fpcr (a ++ b)) : NT fpcr a := (nt_append h).1
theorem nt_right {fpcr : Nat} {a b : Janus.Arm64.FP.Exc} (h : NT fpcr (a ++ b)) : NT fpcr b := (nt_append h).2

theorem ofBool_ite (b : Bool) : BitVec.ofBool b = if b then 1#1 else 0#1 := by cases b <;> rfl

theorem update_one_or_w {w : Nat} (x : BitVec w) (i : Nat) (_hi : i < w) :
    Sail.BitVec.update x i 1#1 = x ||| BitVec.ofNat w (2 ^ i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp [hj]; right; omega
  · simp only [hj, h]
    by_cases hji : j < i
    · simp [hji]
    · have h0 : decide (j - i = 0) = false := by simp; omega
      simp [hji, h0]

theorem FPInf_pure {N : Nat} (hN : N = 32 ∨ N = 64) (neg : Bool) :
    FPInfinity (if neg then 1#1 else 0#1) N = pure (BitVec.ofNat N (Janus.Float.inf (fmtN N) neg)) := by
  rcases hN with rfl | rfl
  · exact FPInf32_pure neg
  · exact FPInf64_pure neg
theorem FPMax_pure {N : Nat} (hN : N = 32 ∨ N = 64) (neg : Bool) :
    FPMaxNormal (if neg then 1#1 else 0#1) N = pure (BitVec.ofNat N (Janus.Float.maxNormal (fmtN N) neg)) := by
  rcases hN with rfl | rfl
  · exact FPMax32_pure neg
  · exact FPMax64_pure neg
theorem FPZero_pure {N : Nat} (hN : N = 32 ∨ N = 64) (neg : Bool) :
    FPZero (if neg then 1#1 else 0#1) N = pure (BitVec.ofNat N (Janus.Float.zero (fmtN N) neg)) := by
  rcases hN with rfl | rfl
  · exact FPZero32_pure neg
  · exact FPZero64_pure neg
theorem FPInf_ofBool {N : Nat} (hN : N = 32 ∨ N = 64) (neg : Bool) :
    FPInfinity (BitVec.ofBool neg) N = pure (BitVec.ofNat N (Janus.Float.inf (fmtN N) neg)) := by
  rw [ofBool_ite]; exact FPInf_pure hN neg
theorem FPZero_ofBool {N : Nat} (hN : N = 32 ∨ N = 64) (neg : Bool) :
    FPZero (BitVec.ofBool neg) N = pure (BitVec.ofNat N (Janus.Float.zero (fmtN N) neg)) := by
  rw [ofBool_ite]; exact FPZero_pure hN neg

theorem run_FPUnpackN {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (x : BitVec N)
    (fpcr v : BitVec 64)
    (hen : (Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true x.toNat).2.proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPUnpack__1 x fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.unpack (fmtN N) fpcr.toNat true x.toNat
      .ok (aslFPType r.1.1, BitVec.ofBool r.1.2.1, valRat r.1.2.2) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  rcases hN with rfl | rfl
  · rw [fmtN32] at hen ⊢
    have := run_FPUnpack32' (hc.set_FPSR v) x fpcr (get?_set_FPSR s v) hen
    exact this.trans (by simp only [set_set_FPSR])
  · rw [fmtN64] at hen ⊢
    have := run_FPUnpack64' (hc.set_FPSR v) x fpcr (get?_set_FPSR s v) hen
    exact this.trans (by simp only [set_set_FPSR])

theorem run_FPRoundingMode {s : SState} (fpcr : BitVec 64) :
    (FPRoundingMode fpcr).run s = .ok (aslRM (Janus.Arm64.FP.roundingMode fpcr.toNat)) s := by
  have h : _get_FPCRType_RMode fpcr = BitVec.ofNat 2 (fpcr.toNat / 2 ^ 22 % 4) := by
    apply BitVec.eq_of_toNat_eq
    show (Sail.BitVec.extractLsb fpcr 23 22).toNat = _
    rw [extractLsb_toNat']
    simp [BitVec.toNat_ofNat]
  unfold FPRoundingMode FPDecodeRounding Janus.Arm64.FP.roundingMode Janus.Arm64.FP.decodeRounding
  rw [h]
  have : fpcr.toNat / 2 ^ 22 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize fpcr.toNat / 2 ^ 22 % 4 = k at *
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem run_FPDefaultNaN32 {s : SState} (hc : LinuxEL0Config s) (fpcr : BitVec 64) :
    (FPDefaultNaN__1 fpcr 32).run s = .ok (BitVec.ofNat 32 (Janus.Arm64.FP.defaultNaN Janus.Float.binary32 fpcr.toNat)) s := by
  unfold FPDefaultNaN__1
  cfg_simp [HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc, get_AH]
  simp only [Janus.Arm64.FP.defaultNaN, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, Nat.pow_one]
  generalize decide (fpcr.toNat / 2 % 2 = 1) = b
  cases b <;> decide

theorem run_FPDefaultNaN64 {s : SState} (hc : LinuxEL0Config s) (fpcr : BitVec 64) :
    (FPDefaultNaN__1 fpcr 64).run s = .ok (BitVec.ofNat 64 (Janus.Arm64.FP.defaultNaN Janus.Float.binary64 fpcr.toNat)) s := by
  unfold FPDefaultNaN__1
  cfg_simp [HaveAltFP, run_IsFeatureImplemented hc, run_UsingAArch32 hc, get_AH]
  simp only [Janus.Arm64.FP.defaultNaN, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, Nat.pow_one]
  generalize decide (fpcr.toNat / 2 % 2 = 1) = b
  cases b <;> decide

theorem run_FPDefaultNaN {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (fpcr : BitVec 64) :
    (FPDefaultNaN__1 fpcr N).run s = .ok (BitVec.ofNat N (Janus.Arm64.FP.defaultNaN (fmtN N) fpcr.toNat)) s := by
  rcases hN with rfl | rfl
  · exact run_FPDefaultNaN32 hc fpcr
  · exact run_FPDefaultNaN64 hc fpcr

theorem run_FPProcessNaN32 {s : SState} (hc : LinuxEL0Config s) (t : Janus.Arm64.FP.FPType)
    (ht : t = .snan ∨ t = .qnan) (op : BitVec 32) (fpcr v : BitVec 64) (hen : t = .snan → fpcr.getLsbD 8 = false) :
    (FPProcessNaN__1 (aslFPType t) op fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.processNaN Janus.Float.binary32 fpcr.toNat t op.toNat
      .ok (BitVec.ofNat 32 r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  have a2 : Sail.BitVec.access (1#1) 0 = 1#1 := by decide
  rcases ht with rfl | rfl
  · unfold FPProcessNaN__1
    have hfpe : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := hen rfl
    have a1 : (FPType.FPType_SNaN == FPType.FPType_QNaN || FPType.FPType_SNaN == FPType.FPType_SNaN) = true := by decide
    cfg_simp [aslFPType, Sail.BitVec.length, run_PE_set hc _ fpcr hfpe, run_FPDefaultNaN32 (hc.set_FPSR _), get_DN, Bit,
      update_one_or_w, fpExcBit, a1, a2, run_sail_assert_true, ofBool_eq_one]
    simp only [Janus.Arm64.FP.processNaN, Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit, Janus.Arm64.FP.raise,
      Janus.Arm64.FP.IOC, ite_true]
    by_cases hd : fpcr.toNat / 33554432 % 2 = 1
    · have : fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this, run_FPDefaultNaN32 (hc.set_FPSR _)]
    · have : ¬ fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this]
      rfl
  · unfold FPProcessNaN__1
    have a1 : (FPType.FPType_QNaN == FPType.FPType_QNaN || FPType.FPType_QNaN == FPType.FPType_SNaN) = true := by decide
    cfg_simp [aslFPType, Sail.BitVec.length, run_FPDefaultNaN32 (hc.set_FPSR _), get_DN, Bit,
      a1, a2, run_sail_assert_true, ofBool_eq_one]
    simp only [Janus.Arm64.FP.processNaN, Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit]
    by_cases hd : fpcr.toNat / 33554432 % 2 = 1
    · have : fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this, run_FPDefaultNaN32 (hc.set_FPSR _)]
    · have : ¬ fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this]

theorem run_FPProcessNaN64 {s : SState} (hc : LinuxEL0Config s) (t : Janus.Arm64.FP.FPType)
    (ht : t = .snan ∨ t = .qnan) (op : BitVec 64) (fpcr v : BitVec 64) (hen : t = .snan → fpcr.getLsbD 8 = false) :
    (FPProcessNaN__1 (aslFPType t) op fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.processNaN Janus.Float.binary64 fpcr.toNat t op.toNat
      .ok (BitVec.ofNat 64 r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  have a2 : Sail.BitVec.access (1#1) 0 = 1#1 := by decide
  rcases ht with rfl | rfl
  · unfold FPProcessNaN__1
    have hfpe : fpcr.getLsbD (fpExcBit .FPExc_InvalidOp + 8) = false := hen rfl
    have a1 : (FPType.FPType_SNaN == FPType.FPType_QNaN || FPType.FPType_SNaN == FPType.FPType_SNaN) = true := by decide
    cfg_simp [aslFPType, Sail.BitVec.length, run_PE_set hc _ fpcr hfpe, run_FPDefaultNaN64 (hc.set_FPSR _), get_DN, Bit,
      update_one_or_w, fpExcBit, a1, a2, run_sail_assert_true, ofBool_eq_one]
    simp only [Janus.Arm64.FP.processNaN, Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit, Janus.Arm64.FP.raise,
      Janus.Arm64.FP.IOC, ite_true]
    by_cases hd : fpcr.toNat / 33554432 % 2 = 1
    · have : fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this, run_FPDefaultNaN64 (hc.set_FPSR _)]
    · have : ¬ fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this]
      rfl
  · unfold FPProcessNaN__1
    have a1 : (FPType.FPType_QNaN == FPType.FPType_QNaN || FPType.FPType_QNaN == FPType.FPType_SNaN) = true := by decide
    cfg_simp [aslFPType, Sail.BitVec.length, run_FPDefaultNaN64 (hc.set_FPSR _), get_DN, Bit,
      a1, a2, run_sail_assert_true, ofBool_eq_one]
    simp only [Janus.Arm64.FP.processNaN, Janus.Arm64.FP.dn, Janus.Arm64.FP.fpcrBit]
    by_cases hd : fpcr.toNat / 33554432 % 2 = 1
    · have : fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this, run_FPDefaultNaN64 (hc.set_FPSR _)]
    · have : ¬ fpcr.toNat / 2 ^ 25 % 2 = 1 := hd
      simp [hd, this]


theorem run_FPProcessNaN {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s)
    (t : Janus.Arm64.FP.FPType) (ht : t = .snan ∨ t = .qnan) (op : BitVec N) (fpcr v : BitVec 64)
    (hen : t = .snan → fpcr.getLsbD 8 = false) :
    (FPProcessNaN__1 (aslFPType t) op fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.processNaN (fmtN N) fpcr.toNat t op.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) := by
  rcases hN with rfl | rfl
  · exact run_FPProcessNaN32 hc t ht op fpcr v hen
  · exact run_FPProcessNaN64 hc t ht op fpcr v hen

theorem nt_raise_ioc {fpcr : Nat} (h : NT fpcr (Janus.Arm64.FP.raise Janus.Arm64.FP.IOC)) : fpcr.testBit 8 = false :=
  nt_bit h (k := 0) (Or.inl rfl) (by decide)

theorem getLsbD_of_testBit {fpcr : BitVec 64} {i : Nat} (h : fpcr.toNat.testBit i = false) : fpcr.getLsbD i = false := h

theorem processNaNs_snan (f : Janus.Float.Fmt) (fpcr : Nat) (t1 t2 : Janus.Arm64.FP.FPType) (a b : Nat)
    (hs : t1 = .snan ∨ t2 = .snan) :
    ∃ r, Janus.Arm64.FP.processNaNs f fpcr t1 t2 a b = some (r, Janus.Arm64.FP.raise Janus.Arm64.FP.IOC) := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;> simp at hs <;>
    simp [Janus.Arm64.FP.processNaNs, Janus.Arm64.FP.processNaN, Janus.Arm64.FP.FPType.isNaN, hah]

theorem nan_ioc {N : Nat} {fpcr : BitVec 64} {t1 t2 : Janus.Arm64.FP.FPType} {op1 op2 : BitVec N}
    (hen : ∀ r e, Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat = some (r, e) →
      NT fpcr.toNat e) (hs : t1 = .snan ∨ t2 = .snan) : fpcr.getLsbD 8 = false := by
  obtain ⟨r, hr⟩ := processNaNs_snan (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat hs
  exact getLsbD_of_testBit (nt_raise_ioc (hen _ _ hr))

theorem run_FPProcessNaN_s {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s)
    (op : BitVec N) (fpcr v : BitVec 64) (hen : fpcr.getLsbD 8 = false) :
    (FPProcessNaN__1 FPType.FPType_SNaN op fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.processNaN (fmtN N) fpcr.toNat .snan op.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) :=
  run_FPProcessNaN hN hc .snan (Or.inl rfl) op fpcr v (fun _ => hen)

theorem run_FPProcessNaN_q {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s)
    (op : BitVec N) (fpcr v : BitVec 64) :
    (FPProcessNaN__1 FPType.FPType_QNaN op fpcr true).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.processNaN (fmtN N) fpcr.toNat .qnan op.toNat
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 r.2.proc)) :=
  run_FPProcessNaN hN hc .qnan (Or.inr rfl) op fpcr v (fun h => by cases h)

theorem run_FPProcessNaNs {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s)
    (t1 t2 : Janus.Arm64.FP.FPType) (op1 op2 : BitVec N) (fpcr v : BitVec 64)
    (hen : ∀ r e, Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat = some (r, e) →
      NT fpcr.toNat e) :
    (FPProcessNaNs__1 (aslFPType t1) (aslFPType t2) op1 op2 fpcr true).run (s.set .FPSR v) =
      match Janus.Arm64.FP.processNaNs (fmtN N) fpcr.toNat t1 t2 op1.toNat op2.toNat with
      | some (r, e) => .ok (true, BitVec.ofNat N r) (s.set .FPSR (v ||| BitVec.ofNat 64 e.proc))
      | none => .ok (false, 0#N) (s.set .FPSR v) := by
  have ha : (N == 16 || (N == 32 || N == 64)) = true := by rcases hN with rfl | rfl <;> decide
  have h8 := fun hs => nan_ioc hen hs
  have hz : (Zeros : BitVec N) = 0#N := rfl
  unfold FPProcessNaNs__1
  cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH,
    Sail.BitVec.length, ofBool_eq_one, ha, run_sail_assert_true]
  have Lq1 := run_FPProcessNaN_q hN hc op1 fpcr v
  have Lq2 := run_FPProcessNaN_q hN hc op2 fpcr v
  by_cases hb : fpcr.getLsbD 8 = false
  · have Ls1 := run_FPProcessNaN_s hN hc op1 fpcr v hb
    have Ls2 := run_FPProcessNaN_s hN hc op2 fpcr v hb
    by_cases hah : fpcr.toNat / 2 % 2 = 1 <;> cases t1 <;> cases t2 <;>
    cfg_simp [aslFPType, Janus.Arm64.FP.processNaNs, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Ls1, Ls2, Lq1, Lq2, hz]
  · have hns : ¬(t1 = .snan ∨ t2 = .snan) := fun hs => hb (h8 hs)
    by_cases hah : fpcr.toNat / 2 % 2 = 1 <;> cases t1 <;> cases t2 <;> simp at hns <;>
    cfg_simp [aslFPType, Janus.Arm64.FP.processNaNs, Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit, hah,
      Lq1, Lq2, hz]

theorem nt_idc {fpcr : Nat} (h : NT fpcr (Janus.Arm64.FP.raise Janus.Arm64.FP.IDC)) : fpcr.testBit 15 = false :=
  nt_bit h (k := 7) (by decide) (by decide)

theorem asl_beq_den (t : Janus.Arm64.FP.FPType) :
    (aslFPType t == FPType.FPType_Denormal) = decide (t = .denormal) := by cases t <;> decide

theorem run_FPProcessDenorms {s : SState} (hc : LinuxEL0Config s) (t1 t2 : Janus.Arm64.FP.FPType) (N : Int)
    (hN : N ≠ 16) (fpcr v : BitVec 64)
    (hen : (Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2).proc ≠ 0 → fpcr.getLsbD 15 = false) :
    (FPProcessDenorms (aslFPType t1) (aslFPType t2) N fpcr).run (s.set .FPSR v) =
      .ok () (s.set .FPSR (v ||| BitVec.ofNat 64 (Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2).proc)) := by
  unfold FPProcessDenorms
  have hN' : (N != 16) = true := by simpa using hN
  by_cases hd : Janus.Arm64.FP.ah fpcr.toNat = true ∧ (t1 = .denormal ∨ t2 = .denormal)
  · have hpd : Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2 = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC := by
      unfold Janus.Arm64.FP.processDenorms
      rcases hd with ⟨h1, h2 | h2⟩ <;> simp [h1, h2]
    rw [hpd] at hen ⊢
    have h15 : fpcr.getLsbD 15 = false := hen (by simp [Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC])
    have hfpe : fpcr.getLsbD (fpExcBit .FPExc_InputDenorm + 8) = false := h15
    obtain ⟨hah, hden⟩ := hd
    have hah' : fpcr.toNat / 2 % 2 = 1 := by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using hah
    rcases hden with rfl | rfl <;>
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, hah', run_PE_set hc _ fpcr hfpe, aslFPType, fpExcBit, Janus.Arm64.FP.raise, Janus.Arm64.FP.IDC]
  · have hpd : Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2 = {} := by
      unfold Janus.Arm64.FP.processDenorms
      by_cases h1 : Janus.Arm64.FP.ah fpcr.toNat = true
      · have : ¬ (t1 = .denormal ∨ t2 = .denormal) := fun h => hd ⟨h1, h⟩
        simp [h1] at this ⊢; simp [this]
      · simp [h1]
    rw [hpd]
    cfg_simp [HaveAltFP, run_IsFeatureImplemented (hc.set_FPSR v), run_UsingAArch32 (hc.set_FPSR v), get_AH, hN',
      ofBool_eq_one, asl_beq_den]
    have : ¬ (fpcr.toNat / 2 % 2 = 1 ∧ (t1 = .denormal ∨ t2 = .denormal)) := fun h =>
      hd ⟨by simpa [Janus.Arm64.FP.ah, Janus.Arm64.FP.fpcrBit] using h.1, h.2⟩
    simp [this]

theorem SMZero.set_FPSR {s : SState} (h : SMZero s) (v : BitVec 64) : SMZero (s.set .FPSR v) := by
  obtain ⟨p, hp, hs⟩ := h
  exact ⟨p, by rw [get?_set_ne _ _ (by decide)]; exact hp, hs⟩

theorem run_InStreamingMode {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s) :
    (InStreamingMode ()).run s = .ok false s := by
  obtain ⟨p, hp, hs⟩ := hsm
  cfg_simp [InStreamingMode, HaveSME, run_IsFeatureImplemented hc, run_readReg hp, hs]

theorem upd26_getLsbD (fpcr : BitVec 64) (i : Nat) (hi : i ≠ 26) :
    (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD i = fpcr.getLsbD i := by
  have h := upd26_bit fpcr i hi
  have h1 := toNat_bit_eq_getLsbD (Sail.BitVec.updateSubrange fpcr 26 26 0#1) i
  have h2 := toNat_bit_eq_getLsbD fpcr i
  rw [h] at h1
  cases hb : fpcr.getLsbD i <;> cases hb' : (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD i <;> simp_all

theorem fpRound_upd26 (f : Janus.Float.Fmt) (fpcr : BitVec 64) (rm : Janus.Float.RM) (neg : Bool) (m : Nat) (e : Int) :
    Janus.Arm64.FP.fpRound f (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg m e =
      Janus.Arm64.FP.fpRound f fpcr.toNat rm neg m e := by
  unfold Janus.Arm64.FP.fpRound Janus.Arm64.FP.ah Janus.Arm64.FP.fz Janus.Arm64.FP.ufe Janus.Arm64.FP.fpcrBit
  rw [upd26_bit fpcr 1 (by decide), upd26_bit fpcr 24 (by decide), upd26_bit fpcr 11 (by decide)]

theorem run_FPRound {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (fpcr v : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg m e).2) :
    (FPRound__2 (sval neg m e) fpcr (aslRM rm) true N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg m e
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hism := run_InStreamingMode (hc.set_FPSR v) (hsm.set_FPSR v)
  unfold FPRound__2
  simp only [run_bind, run_pure]
  have hb : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4) →
      Nat.testBit (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg m e).2.proc k = true →
      (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD (k + 8) = false := by
    intro k hk hp
    rw [upd26_getLsbD fpcr _ (by omega)]
    exact getLsbD_of_testBit (nt_bit hnt (by omega) hp)
  rcases hN with rfl | rfl
  · have := run_FPRoundBase32 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg m hm e
      (get?_set_FPSR s v)
      (by rw [fpRound_upd26]; exact hb 2 (by decide)) (by rw [fpRound_upd26]; exact hb 3 (by decide))
      (by rw [fpRound_upd26]; exact hb 4 (by decide))
    simp only [fpRound_upd26, set_set_FPSR, fmtN32] at this ⊢
    exact this
  · have := run_FPRoundBase64 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg m hm e
      (get?_set_FPSR s v)
      (by rw [fpRound_upd26]; exact hb 2 (by decide)) (by rw [fpRound_upd26]; exact hb 3 (by decide))
      (by rw [fpRound_upd26]; exact hb 4 (by decide))
    simp only [fpRound_upd26, set_set_FPSR, fmtN64] at this ⊢
    exact this

theorem sval_ofInt {z k : Int} {neg : Bool} {m : Nat} {ex : Int} (h : Janus.Float.ofInt z k = some (neg, m, ex)) :
    m ≠ 0 ∧ sval neg m ex = (z : Rat) * 2 ^ k := by
  unfold Janus.Float.ofInt at h
  by_cases hz : z = 0
  · simp [hz] at h
  · simp only [hz, ite_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by omega, ?_⟩
    by_cases hn : z < 0
    · have h1 : ((z.natAbs : Nat) : Int) = -z := Int.ofNat_natAbs_of_nonpos (by omega)
      have h2 : (z.natAbs : Rat) = -(z : Rat) := by
        rw [← Rat.intCast_natCast, h1, Rat.intCast_neg]
      simp [sval, hn, h2, Rat.neg_mul]
    · have h1 : ((z.natAbs : Nat) : Int) = z := Int.natAbs_of_nonneg (by omega)
      have h2 : (z.natAbs : Rat) = (z : Rat) := by
        rw [← Rat.intCast_natCast, h1]
      simp [sval, hn, h2]

theorem ofInt_none {z k : Int} (h : Janus.Float.ofInt z k = none) : z = 0 := by
  unfold Janus.Float.ofInt at h
  by_cases hz : z = 0
  · exact hz
  · simp [hz] at h

theorem addExact_sum (n e n' e' : Int) :
    (n : Rat) * 2 ^ e + (n' : Rat) * 2 ^ e' =
      ((n * 2 ^ (e - min e e').toNat + n' * 2 ^ (e' - min e e').toNat : Int) : Rat) * 2 ^ (min e e') := by
  rw [num_split n e (min e e') (Int.min_le_left _ _), num_split n' e' (min e e') (Int.min_le_right _ _),
    Rat.intCast_add, Rat.add_mul]

theorem addExact_none {n e n' e' : Int} (h : Janus.Float.addExact n e n' e' = none) :
    (n : Rat) * 2 ^ e + (n' : Rat) * 2 ^ e' = 0 := by
  unfold Janus.Float.addExact Janus.Float.align at h
  have := ofInt_none h
  rw [addExact_sum, this]; simp

theorem addExact_some {n e n' e' : Int} {neg : Bool} {m : Nat} {ex : Int}
    (h : Janus.Float.addExact n e n' e' = some (neg, m, ex)) :
    m ≠ 0 ∧ sval neg m ex = (n : Rat) * 2 ^ e + (n' : Rat) * 2 ^ e' := by
  unfold Janus.Float.addExact Janus.Float.align at h
  obtain ⟨h1, h2⟩ := sval_ofInt h
  exact ⟨h1, by rw [h2, addExact_sum]⟩

theorem mul_zpow (n n' e e' : Int) :
    ((n : Rat) * 2 ^ e) * ((n' : Rat) * 2 ^ e') = ((n * n' : Int) : Rat) * 2 ^ (e + e') := by
  rw [Rat.intCast_mul, Rat.zpow_add two_ne_zero_rat]
  generalize (2 : Rat) ^ e = a; generalize (2 : Rat) ^ e' = b
  generalize (n : Rat) = x; generalize (n' : Rat) = y
  rw [Rat.mul_assoc, ← Rat.mul_assoc a, Rat.mul_comm a y, Rat.mul_assoc y, ← Rat.mul_assoc x]

theorem mulExact_none {n e n' e' : Int} (h : Janus.Float.mulExact n e n' e' = none) :
    ((n : Rat) * 2 ^ e) * ((n' : Rat) * 2 ^ e') = 0 := by
  unfold Janus.Float.mulExact at h
  rw [mul_zpow, ofInt_none h]; simp

theorem mulExact_some {n e n' e' : Int} {neg : Bool} {m : Nat} {ex : Int}
    (h : Janus.Float.mulExact n e n' e' = some (neg, m, ex)) :
    m ≠ 0 ∧ sval neg m ex = ((n : Rat) * 2 ^ e) * ((n' : Rat) * 2 ^ e') := by
  unfold Janus.Float.mulExact at h
  obtain ⟨h1, h2⟩ := sval_ofInt h
  exact ⟨h1, by rw [h2, mul_zpow]⟩

theorem unpack_spec (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    ((Janus.Arm64.FP.unpack f fpcr e x).1.1 = .infinity → ∃ s', (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .inf s') ∧
    ((Janus.Arm64.FP.unpack f fpcr e x).1.1 ≠ .infinity → ∃ n e', (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .num n e') ∧
    ((Janus.Arm64.FP.unpack f fpcr e x).1.1 = .zero → (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .num 0 0) := by
  unfold Janus.Arm64.FP.unpack
  split
  · simp
  · cases Janus.Arm64.FP.fz fpcr <;> cases Janus.Arm64.FP.ah fpcr <;> cases Janus.Arm64.FP.fiz fpcr <;> cases e <;>
      simp <;> (try (unfold Janus.Float.valueOf; split <;> simp_all))
  · unfold Janus.Float.valueOf; split <;> simp_all
  · simp
  · simp
  · simp

theorem unpack_direct' (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat) :
    (Janus.Arm64.FP.unpack f fpcr e x).2.direct = 0 := by
  unfold Janus.Arm64.FP.unpack
  split <;> (try simp) <;>
  cases Janus.Arm64.FP.fz fpcr <;> cases Janus.Arm64.FP.ah fpcr <;> cases Janus.Arm64.FP.fiz fpcr <;> cases e <;>
    simp [Janus.Arm64.FP.raise]

theorem asl_beq_inf (t : Janus.Arm64.FP.FPType) :
    (aslFPType t == FPType.FPType_Infinity) = decide (t = .infinity) := by cases t <;> decide
theorem asl_beq_zero (t : Janus.Arm64.FP.FPType) :
    (aslFPType t == FPType.FPType_Zero) = decide (t = .zero) := by cases t <;> decide

theorem nt_unpack {f : Janus.Float.Fmt} {fpcr : BitVec 64} {x : Nat}
    (h : NT fpcr.toNat (Janus.Arm64.FP.unpack f fpcr.toNat true x).2) :
    (Janus.Arm64.FP.unpack f fpcr.toNat true x).2.proc ≠ 0 → fpcr.getLsbD 15 = false :=
  fun hne => getLsbD_of_testBit (nt_bit h (k := 7) (by decide) (unpack_bit7 f fpcr.toNat x hne))

theorem ofBool_eq_zero (b : Bool) : (BitVec.ofBool b = 0#1) = (b = false) := by cases b <;> decide
theorem ofBool_eq_one' (b : Bool) : (BitVec.ofBool b = 1#1) = (b = true) := by cases b <;> decide
theorem ofBool_eq_not_old (a b : Bool) : (BitVec.ofBool a = ~~~ BitVec.ofBool b) = (a = !b) := by
  cases a <;> cases b <;> decide
theorem ofBool_eq_ofBool (a b : Bool) : (BitVec.ofBool a = BitVec.ofBool b) = (a = b) := by
  cases a <;> cases b <;> decide
theorem asl_beq_rmi (rm : Janus.Float.RM) : (aslRM rm == FPRounding.FPRounding_NEGINF) = decide (rm = .rmi) := by
  cases rm <;> decide

theorem processNaNs_direct {f : Janus.Float.Fmt} {fpcr : Nat} {t1 t2 : Janus.Arm64.FP.FPType} {a b r : Nat}
    {e : Janus.Arm64.FP.Exc} (h : Janus.Arm64.FP.processNaNs f fpcr t1 t2 a b = some (r, e)) : e.direct = 0 := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;>
    simp [Janus.Arm64.FP.processNaNs, Janus.Arm64.FP.processNaN, Janus.Arm64.FP.FPType.isNaN, hah] at h <;>
    (rw [← h.2] <;> simp [Janus.Arm64.FP.raise])

theorem ofBool_eq_not' (a b : Bool) : (BitVec.ofBool a = ~~~ BitVec.ofBool b) = ¬ (a = b) := by
  cases a <;> cases b <;> decide

theorem eq_not_iff' (a b : Bool) : (a = !b) = ¬ (a = b) := by cases a <;> cases b <;> decide
theorem FPInf_0 {N : Nat} (hN : N = 32 ∨ N = 64) :
    FPInfinity 0#1 N = pure (BitVec.ofNat N (Janus.Float.inf (fmtN N) false)) := FPInf_pure hN false
theorem FPInf_1 {N : Nat} (hN : N = 32 ∨ N = 64) :
    FPInfinity 1#1 N = pure (BitVec.ofNat N (Janus.Float.inf (fmtN N) true)) := FPInf_pure hN true

theorem roundingMode_ne_rna (fpcr : Nat) : Janus.Arm64.FP.roundingMode fpcr ≠ .rna := by
  unfold Janus.Arm64.FP.roundingMode Janus.Arm64.FP.decodeRounding; split <;> (try split) <;> (try split) <;> simp

theorem nt_exc_ioc_of {fpcr : Nat} {a b c d : Janus.Arm64.FP.Exc} (h : NT fpcr (a ++ b ++ c ++ d)) : NT fpcr c :=
  nt_right (nt_left h)

theorem fpAdd_nt (f : Janus.Float.Fmt) (fpcr a b : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpAdd f fpcr a b).2) :
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 ∧ NT fpcr (Janus.Arm64.FP.unpack f fpcr true b).2 ∧
    (∀ r e, Janus.Arm64.FP.processNaNs f fpcr (Janus.Arm64.FP.unpack f fpcr true a).1.1
      (Janus.Arm64.FP.unpack f fpcr true b).1.1 a b = some (r, e) → NT fpcr e) := by
  unfold Janus.Arm64.FP.fpAdd at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split at h
  · next r e heq =>
    refine ⟨nt_left (nt_left h), nt_right (nt_left h), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'
    exact nt_right h
  · next heq =>
    refine ⟨nt_left (nt_left (nt_left h)), nt_right (nt_left (nt_left h)), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'


theorem processDenorms_cases (fpcr : Nat) (t1 t2 : Janus.Arm64.FP.FPType) :
    Janus.Arm64.FP.processDenorms fpcr t1 t2 = Janus.Arm64.FP.raise Janus.Arm64.FP.IDC ∨
      Janus.Arm64.FP.processDenorms fpcr t1 t2 = {} := by
  unfold Janus.Arm64.FP.processDenorms; split <;> simp

theorem nt_pd {fpcr : BitVec 64} {t1 t2 : Janus.Arm64.FP.FPType}
    (h : NT fpcr.toNat (Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2)) :
    (Janus.Arm64.FP.processDenorms fpcr.toNat t1 t2).proc ≠ 0 → fpcr.getLsbD 15 = false := by
  intro hne
  rcases processDenorms_cases fpcr.toNat t1 t2 with h1 | h1
  · rw [h1] at h; exact getLsbD_of_testBit (nt_idc h)
  · rw [h1] at hne; simp at hne

theorem ofNat0 (w : Nat) : BitVec.ofNat w 0 = 0#w := rfl

theorem processDenorms_direct (fpcr : Nat) (t1 t2 : Janus.Arm64.FP.FPType) :
    (Janus.Arm64.FP.processDenorms fpcr t1 t2).direct = 0 := by
  rcases processDenorms_cases fpcr t1 t2 with h | h <;> rw [h] <;> rfl

theorem raise_direct (e : Nat) : (Janus.Arm64.FP.raise e).direct = 0 := rfl
theorem raise_proc (e : Nat) : (Janus.Arm64.FP.raise e).proc = e := rfl
theorem exc_empty_direct : ({ } : Janus.Arm64.FP.Exc).direct = 0 := rfl
theorem exc_empty_proc : ({ } : Janus.Arm64.FP.Exc).proc = 0 := rfl

theorem sval_ne_zero (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int) : sval neg m e ≠ 0 := by
  have hp := mag_pos m hm e
  cases neg
  · simp only [sval, Bool.false_eq_true, ite_false]; exact fun h => Rat.lt_irrefl (h ▸ hp)
  · simp only [sval, ite_true]; intro h
    have : (m : Rat) * 2 ^ e = 0 := by rw [← Rat.neg_neg ((m : Rat) * 2 ^ e), h, Rat.neg_zero]
    exact Rat.lt_irrefl (this ▸ hp)

theorem eq_real_zero_iff (x : Rat) : eq_real x 0 = decide (x = 0) := by
  simp only [eq_real]; by_cases h : x = 0 <;> simp [h]

theorem valRat_num (n e : Int) : valRat (.num n e) = (n : Rat) * 2 ^ e := rfl

set_option hygiene false in
macro "fp_or_close" : tactic => `(tactic| (
  simp only [d1, d2, raise_direct, raise_proc, exc_empty_direct, exc_empty_proc, processDenorms_direct, ofNat0,
    BitVec.or_zero, BitVec.zero_or, ofNat_or, fpExcBit, Janus.Arm64.FP.IOC, Nat.pow_zero] <;> ac_rfl))

theorem fpSub_nt (f : Janus.Float.Fmt) (fpcr a b : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpSub f fpcr a b).2) :
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 ∧ NT fpcr (Janus.Arm64.FP.unpack f fpcr true b).2 ∧
    (∀ r e, Janus.Arm64.FP.processNaNs f fpcr (Janus.Arm64.FP.unpack f fpcr true a).1.1
      (Janus.Arm64.FP.unpack f fpcr true b).1.1 a b = some (r, e) → NT fpcr e) := by
  unfold Janus.Arm64.FP.fpSub at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split at h
  · next r e heq =>
    refine ⟨nt_left (nt_left h), nt_right (nt_left h), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'
    exact nt_right h
  · next heq =>
    refine ⟨nt_left (nt_left (nt_left h)), nt_right (nt_left (nt_left h)), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'



theorem fpMul_nt (f : Janus.Float.Fmt) (fpcr a b : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpMul f fpcr a b).2) :
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 ∧ NT fpcr (Janus.Arm64.FP.unpack f fpcr true b).2 ∧
    (∀ r e, Janus.Arm64.FP.processNaNs f fpcr (Janus.Arm64.FP.unpack f fpcr true a).1.1
      (Janus.Arm64.FP.unpack f fpcr true b).1.1 a b = some (r, e) → NT fpcr e) := by
  unfold Janus.Arm64.FP.fpMul at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split at h
  · next r e heq =>
    refine ⟨nt_left (nt_left h), nt_right (nt_left h), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'
    exact nt_right h
  · next heq =>
    refine ⟨nt_left (nt_left (nt_left h)), nt_right (nt_left (nt_left h)), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'



theorem fpDiv_nt (f : Janus.Float.Fmt) (fpcr a b : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpDiv f fpcr a b).2) :
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 ∧ NT fpcr (Janus.Arm64.FP.unpack f fpcr true b).2 ∧
    (∀ r e, Janus.Arm64.FP.processNaNs f fpcr (Janus.Arm64.FP.unpack f fpcr true a).1.1
      (Janus.Arm64.FP.unpack f fpcr true b).1.1 a b = some (r, e) → NT fpcr e) := by
  unfold Janus.Arm64.FP.fpDiv at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u2 at *
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split at h
  · next r e heq =>
    refine ⟨nt_left (nt_left h), nt_right (nt_left h), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'
    exact nt_right h
  · next heq =>
    refine ⟨nt_left (nt_left (nt_left h)), nt_right (nt_left (nt_left h)), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'



theorem mantOf_ne (f : Janus.Float.Fmt) (x : Nat)
    (h : Janus.Float.classify f x = .subnormal ∨ Janus.Float.classify f x = .normal) : Janus.Float.mantOf f x ≠ 0 := by
  unfold Janus.Float.mantOf
  unfold Janus.Float.classify at h
  by_cases h0 : Janus.Float.expOf f x = 0
  · simp only [h0, ite_true] at h ⊢
    by_cases hm : Janus.Float.fracOf f x = 0
    · simp [hm] at h
    · exact hm
  · simp only [h0, ite_false]
    have : 0 < 2 ^ f.fbits := Nat.two_pow_pos _
    omega

theorem unpack_nz (f : Janus.Float.Fmt) (fpcr : Nat) (e : Bool) (x : Nat)
    (h : (Janus.Arm64.FP.unpack f fpcr e x).1.1 = .nonzero ∨ (Janus.Arm64.FP.unpack f fpcr e x).1.1 = .denormal) :
    ∃ n e', (Janus.Arm64.FP.unpack f fpcr e x).1.2.2 = .num n e' ∧ n ≠ 0 := by
  unfold Janus.Arm64.FP.unpack at h ⊢
  have key : ∀ hk : Janus.Float.classify f x = .subnormal ∨ Janus.Float.classify f x = .normal,
      ∃ n e', Janus.Float.valueOf f x = .num n e' ∧ n ≠ 0 := by
    intro hk
    have hm := mantOf_ne f x hk
    unfold Janus.Float.valueOf
    rcases hk with hk | hk <;> simp only [hk] <;> refine ⟨_, _, rfl, ?_⟩ <;> split <;> omega
  cases hk : Janus.Float.classify f x <;> simp only [hk] at h ⊢ <;> (try simp at h ⊢)
  · by_cases hcnd : Janus.Arm64.FP.fz fpcr = true ∧ Janus.Arm64.FP.ah fpcr = false ∨ Janus.Arm64.FP.fiz fpcr = true
    · simp only [hcnd, ite_true] at h; simp at h
    · simp only [hcnd, ite_false]
      obtain ⟨n, e', hv, hn⟩ := key (Or.inl hk)
      exact ⟨n, ⟨e', hv⟩, hn⟩
  · obtain ⟨n, e', hv, hn⟩ := key (Or.inr hk)
    exact ⟨n, ⟨e', hv⟩, hn⟩

theorem processNaNs_none {f : Janus.Float.Fmt} {fpcr : Nat} {t1 t2 : Janus.Arm64.FP.FPType} {a b : Nat}
    (h : Janus.Arm64.FP.processNaNs f fpcr t1 t2 a b = none) :
    t1 ≠ .snan ∧ t1 ≠ .qnan ∧ t2 ≠ .snan ∧ t2 ≠ .qnan := by
  by_cases hah : Janus.Arm64.FP.ah fpcr = true <;> cases t1 <;> cases t2 <;>
    simp [Janus.Arm64.FP.processNaNs, Janus.Arm64.FP.FPType.isNaN, hah] at h ⊢

theorem run_FPRoundDefault {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (fpcr v : BitVec 64) (neg : Bool) (m : Nat) (hm : m ≠ 0) (e : Int)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat (Janus.Arm64.FP.roundingMode fpcr.toNat) neg m e).2) :
    (FPRound (sval neg m e) fpcr N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat (Janus.Arm64.FP.roundingMode fpcr.toNat) neg m e
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have := run_FPRound hN hc hsm fpcr v _ (roundingMode_ne_rna fpcr.toNat) neg m hm e hnt
  unfold FPRound FPRound__1
  simp only [run_bind, run_FPRoundingMode]
  exact this

theorem xor_ofBool (a b : Bool) : BitVec.ofBool a ^^^ BitVec.ofBool b = BitVec.ofBool (a != b) := by
  cases a <;> cases b <;> decide

theorem fpMulAdd_nt (f : Janus.Float.Fmt) (fpcr a b c : Nat)
    (h : NT fpcr (Janus.Arm64.FP.fpMulAdd f fpcr a b c).2) :
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true a).2 ∧ NT fpcr (Janus.Arm64.FP.unpack f fpcr true b).2 ∧
    NT fpcr (Janus.Arm64.FP.unpack f fpcr true c).2 ∧
    (∀ r e, Janus.Arm64.FP.processNaNs3 f fpcr (Janus.Arm64.FP.unpack f fpcr true a).1.1
      (Janus.Arm64.FP.unpack f fpcr true b).1.1 (Janus.Arm64.FP.unpack f fpcr true c).1.1 a b c = some (r, e) →
      NT fpcr e) := by
  unfold Janus.Arm64.FP.fpMulAdd at h
  generalize Janus.Arm64.FP.unpack f fpcr true a = u0 at *
  generalize Janus.Arm64.FP.unpack f fpcr true b = u1 at *
  generalize Janus.Arm64.FP.unpack f fpcr true c = u2 at *
  rcases u0 with ⟨⟨t0, s0, v0⟩, x0⟩
  rcases u1 with ⟨⟨t1, s1, v1⟩, x1⟩
  rcases u2 with ⟨⟨t2, s2, v2⟩, x2⟩
  simp only at h ⊢
  split at h
  · next r e heq =>
    split at h
    · refine ⟨nt_left (nt_left (nt_left (nt_left h))), nt_right (nt_left (nt_left (nt_left h))),
        nt_right (nt_left (nt_left h)), ?_⟩
      intro r' e' h'
      rw [heq] at h'
      cases h'
      exact nt_right (nt_left h)
    · refine ⟨nt_left (nt_left (nt_left h)), nt_right (nt_left (nt_left h)), nt_right (nt_left h), ?_⟩
      intro r' e' h'
      rw [heq] at h'
      cases h'
      exact nt_right h
  · next heq =>
    refine ⟨nt_left (nt_left (nt_left (nt_left h))), nt_right (nt_left (nt_left (nt_left h))),
      nt_right (nt_left (nt_left h)), ?_⟩
    intro r' e' h'
    rw [heq] at h'
    cases h'

theorem bne_eq_xor' (a b : Bool) : (a != b) = (a ^^ b) := by cases a <;> cases b <;> rfl
