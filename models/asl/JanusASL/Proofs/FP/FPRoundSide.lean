import JanusASL.Proofs.FP.DivSide
import JanusASL.Proofs.FP.Prim

/-! # `FPRound` of a `Side`-equivalent operand -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_FPRound_side {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (fpcr v : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (M : Nat) (hM : M ≠ 0) (x : Int)
    (q : Rat) {g : Int} (hS : Side g q ((M : Rat) * 2 ^ x))
    (hg : g + ((fmtN N).fbits : Int) + 1 ≤ (Nat.log2 M : Int) + x)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x).2) :
    (FPRound__2 (if neg then -q else q) fpcr (aslRM rm) true N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have hism := run_InStreamingMode (hc.set_FPSR v) (hsm.set_FPSR v)
  unfold FPRound__2
  simp only [run_bind, run_pure]
  have hb : ∀ k, (k = 2 ∨ k = 3 ∨ k = 4) →
      Nat.testBit (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat rm neg M x).2.proc k = true →
      (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD (k + 8) = false := by
    intro k hk hp
    rw [upd26_getLsbD fpcr _ (by omega)]
    exact getLsbD_of_testBit (nt_bit hnt (by omega) hp)
  rcases hN with rfl | rfl
  · have hg' : g + 24 ≤ (Nat.log2 M : Int) + x := by
      have := hg; simp [fmtN, Janus.Float.binary32] at this; omega
    have hoF : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 2 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 10 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 2 (by decide)
    have hoU : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 3 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 11 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 3 (by decide)
    have hoI : Nat.testBit (rb32Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 4 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 12 = false := by
      rw [rb32Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 4 (by decide)
    have h1 := run_FPRoundBase32_side (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg M hM x q
      hS hg' (get?_set_FPSR s v) hoF hoU hoI
    have h2 := run_FPRoundBase32 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg M hM x
      (get?_set_FPSR s v) (by rw [fpRound_upd26]; exact hb 2 (by decide)) (by rw [fpRound_upd26]; exact hb 3 (by decide))
      (by rw [fpRound_upd26]; exact hb 4 (by decide))
    rw [h1, h2]
    simp only [fpRound_upd26, set_set_FPSR, fmtN32]
  · have hg' : g + 53 ≤ (Nat.log2 M : Int) + x := by
      have := hg; simp [fmtN, Janus.Float.binary64] at this; omega
    have hoF : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 2 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 10 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 2 (by decide)
    have hoU : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 3 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 11 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 3 (by decide)
    have hoI : Nat.testBit (rb64Of (Sail.BitVec.updateSubrange fpcr 26 26 0#1).toNat rm neg M x).2.1 4 = true →
        (Sail.BitVec.updateSubrange fpcr 26 26 0#1).getLsbD 12 = false := by
      rw [rb64Of_eq _ rm hrm neg M hM x, fpRound_upd26]; exact hb 4 (by decide)
    have h1 := run_FPRoundBase64_side (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg M hM x q
      hS hg' (get?_set_FPSR s v) hoF hoU hoI
    have h2 := run_FPRoundBase64 (hc.set_FPSR v) hism (Sail.BitVec.updateSubrange fpcr 26 26 0#1) rm hrm neg M hM x
      (get?_set_FPSR s v) (by rw [fpRound_upd26]; exact hb 2 (by decide)) (by rw [fpRound_upd26]; exact hb 3 (by decide))
      (by rw [fpRound_upd26]; exact hb 4 (by decide))
    rw [h1, h2]
    simp only [fpRound_upd26, set_set_FPSR, fmtN64]

theorem run_FPRoundDefault_side {N : Nat} (hN : N = 32 ∨ N = 64) {s : SState} (hc : LinuxEL0Config s) (hsm : SMZero s)
    (fpcr v : BitVec 64) (neg : Bool) (M : Nat) (hM : M ≠ 0) (x : Int)
    (q : Rat) {g : Int} (hS : Side g q ((M : Rat) * 2 ^ x))
    (hg : g + ((fmtN N).fbits : Int) + 1 ≤ (Nat.log2 M : Int) + x)
    (hnt : NT fpcr.toNat (Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat (Janus.Arm64.FP.roundingMode fpcr.toNat) neg M x).2) :
    (FPRound (if neg then -q else q) fpcr N).run (s.set .FPSR v) =
      let r := Janus.Arm64.FP.fpRound (fmtN N) fpcr.toNat (Janus.Arm64.FP.roundingMode fpcr.toNat) neg M x
      .ok (BitVec.ofNat N r.1) (s.set .FPSR (v ||| BitVec.ofNat 64 (r.2.proc ||| r.2.direct))) := by
  have := run_FPRound_side hN hc hsm fpcr v _ (roundingMode_ne_rna fpcr.toNat) neg M hM x q hS hg hnt
  unfold FPRound FPRound__1
  simp only [run_bind, run_FPRoundingMode]
  exact this

theorem div_cancel_gen (X Y Z : Rat) (hY : Y ≠ 0) (h : X = Z * Y) : X / Y = Z := by
  rw [h, Rat.mul_div_cancel hY]

theorem div_four (a b X Y q : Rat) (hbY : b * Y ≠ 0) (hq : q * (b * Y) = a * X) :
    ((-a) * X) / ((-b) * Y) = q ∧ ((-a) * X) / (b * Y) = -q ∧ (a * X) / ((-b) * Y) = -q ∧ (a * X) / (b * Y) = q := by
  have hn : (-b) * Y ≠ 0 := by
    rw [Rat.neg_mul]; intro h
    apply hbY
    have := congrArg (fun z => -z) h
    simpa [Rat.neg_neg] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply div_cancel_gen _ _ _ hn
    simp only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, hq]
  · apply div_cancel_gen _ _ _ hbY
    simp only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, hq]
  · apply div_cancel_gen _ _ _ hn
    simp only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, hq]
  · exact div_cancel_gen _ _ _ hbY hq.symm

theorem div_sign (n1 n2 : Int) (h1 : n1 ≠ 0) (h2 : n2 ≠ 0) (e1 e2 : Int) :
    ((n1 : Rat) * 2 ^ e1) / ((n2 : Rat) * 2 ^ e2) =
      if (decide (n1 < 0) != decide (n2 < 0)) = true then
        -((n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2))
      else (n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2) := by
  have hb : (n2.natAbs : Rat) * 2 ^ e2 ≠ 0 :=
    Rat.ne_of_gt (Rat.mul_pos (Rat.natCast_pos.mpr (Int.natAbs_pos.mpr h2)) (rat_pos_zpow _))
  have hq := Rat.div_mul_cancel hb (a := (n1.natAbs : Rat) * 2 ^ e1)
  have c1neg : ∀ n : Int, n < 0 → (n : Rat) = -(n.natAbs : Rat) := by
    intro n hn
    have : ((n.natAbs : Nat) : Int) = -n := Int.ofNat_natAbs_of_nonpos (by omega)
    have h' : (n.natAbs : Rat) = -(n : Rat) := by rw [← Rat.intCast_natCast, this, Rat.intCast_neg]
    rw [h', Rat.neg_neg]
  have c1pos : ∀ n : Int, ¬ n < 0 → (n : Rat) = (n.natAbs : Rat) := by
    intro n hn
    have : ((n.natAbs : Nat) : Int) = n := Int.natAbs_of_nonneg (by omega)
    rw [← Rat.intCast_natCast, this]
  obtain ⟨f1, f2, f3, f4⟩ := div_four (n1.natAbs : Rat) (n2.natAbs : Rat) (2 ^ e1) (2 ^ e2)
    ((n1.natAbs : Rat) * 2 ^ e1 / ((n2.natAbs : Rat) * 2 ^ e2)) hb hq
  by_cases p1 : n1 < 0 <;> by_cases p2 : n2 < 0
  · rw [c1neg n1 p1, c1neg n2 p2]; simpa [p1, p2] using f1
  · rw [c1neg n1 p1, c1pos n2 p2]; simpa [p1, p2] using f2
  · rw [c1pos n1 p1, c1neg n2 p2]; simpa [p1, p2] using f3
  · rw [c1pos n1 p1, c1pos n2 p2]; simpa [p1, p2] using f4

end JanusASL.Proofs
