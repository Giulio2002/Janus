import JanusASL.Proofs.FP.Side

/-! # `FPRoundBase` of a `Side`-equivalent operand equals `FPRoundBase` of the dyadic value -/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem rbq32_dyadic (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (M : Nat) (x : Int) :
    rbq32 fpcr rm neg ((M : Rat) * 2 ^ x) ((Nat.log2 M : Int) + x) = rb32Of fpcr rm neg M x := by
  unfold rbq32 rb32Of
  have e1 : ∀ k : Int, (M : Rat) * 2 ^ x * 2 ^ k = (M : Rat) * 2 ^ (x + k) := fun k => by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  rw [e1, e1]
  have a1 : x + (23 - max ((Nat.log2 M : Int) + x) (-126)) = x - (max ((Nat.log2 M : Int) + x) (-126) - 23) := by omega
  have a2 : x + (23 - ((Nat.log2 M : Int) + x)) = 23 - (Nat.log2 M : Int) := by omega
  rw [a1, a2]

theorem run_FPRoundBase32_side {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (M : Nat) (hM : M ≠ 0) (x : Int)
    (q : Rat) {g : Int} (hS : Side g q ((M : Rat) * 2 ^ x)) (hg : g + 24 ≤ (Nat.log2 M : Int) + x)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rb32Of fpcr.toNat rm neg M x).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rb32Of fpcr.toNat rm neg M x).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rb32Of fpcr.toNat rm neg M x).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (if neg then -q else q) fpcr (aslRM rm) false true 32).run s =
      (FPRoundBase__1 (sval neg M x) fpcr (aslRM rm) false true 32).run s := by
  have hl := mag_lower M hM x
  have hu := mag_upper M x
  have hu' : (M : Rat) * 2 ^ x < (2 : Rat) ^ ((Nat.log2 M : Int) + x + 1) := by
    have := hu; rwa [show (Nat.log2 M : Int) + 1 + x = (Nat.log2 M : Int) + x + 1 by omega] at this
  obtain ⟨b1, b2⟩ := hS.symm.binade (E := (Nat.log2 M : Int) + x) (by omega) hl hu'
  have h := run_FPRoundBase32_q hc hism fpcr rm hrm neg q ((Nat.log2 M : Int) + x) b1 b2 hx (by rw [rbq32_side fpcr.toNat rm neg hS hg, rbq32_dyadic]; exact hOF) (by rw [rbq32_side fpcr.toNat rm neg hS hg, rbq32_dyadic]; exact hUF) (by rw [rbq32_side fpcr.toNat rm neg hS hg, rbq32_dyadic]; exact hIX)
  have hsd := rbq32_side fpcr.toNat rm neg hS hg
  rw [rbq32_dyadic] at hsd
  have h2 := run_FPRoundBase32_rb hc hism fpcr rm hrm neg M hM x hx hOF hUF hIX
  rw [h2, h]
  rw [hsd]

theorem rbq64_dyadic (fpcr : Nat) (rm : Janus.Float.RM) (neg : Bool) (M : Nat) (x : Int) :
    rbq64 fpcr rm neg ((M : Rat) * 2 ^ x) ((Nat.log2 M : Int) + x) = rb64Of fpcr rm neg M x := by
  unfold rbq64 rb64Of
  have e1 : ∀ k : Int, (M : Rat) * 2 ^ x * 2 ^ k = (M : Rat) * 2 ^ (x + k) := fun k => by
    rw [Rat.mul_assoc, ← Rat.zpow_add two_ne_zero_rat]
  rw [e1, e1]
  have a1 : x + (52 - max ((Nat.log2 M : Int) + x) (-1022)) = x - (max ((Nat.log2 M : Int) + x) (-1022) - 52) := by omega
  have a2 : x + (52 - ((Nat.log2 M : Int) + x)) = 52 - (Nat.log2 M : Int) := by omega
  rw [a1, a2]

theorem run_FPRoundBase64_side {s : SState} (hc : LinuxEL0Config s) (hism : (InStreamingMode ()).run s = .ok false s)
    (fpcr : BitVec 64) (rm : Janus.Float.RM) (hrm : rm ≠ .rna) (neg : Bool) (M : Nat) (hM : M ≠ 0) (x : Int)
    (q : Rat) {g : Int} (hS : Side g q ((M : Rat) * 2 ^ x)) (hg : g + 53 ≤ (Nat.log2 M : Int) + x)
    {xs : BitVec 64} (hx : s.regs.get? .FPSR = some xs)
    (hOF : Nat.testBit (rb64Of fpcr.toNat rm neg M x).2.1 2 = true → fpcr.getLsbD 10 = false)
    (hUF : Nat.testBit (rb64Of fpcr.toNat rm neg M x).2.1 3 = true → fpcr.getLsbD 11 = false)
    (hIX : Nat.testBit (rb64Of fpcr.toNat rm neg M x).2.1 4 = true → fpcr.getLsbD 12 = false) :
    (FPRoundBase__1 (if neg then -q else q) fpcr (aslRM rm) false true 64).run s =
      (FPRoundBase__1 (sval neg M x) fpcr (aslRM rm) false true 64).run s := by
  have hl := mag_lower M hM x
  have hu := mag_upper M x
  have hu' : (M : Rat) * 2 ^ x < (2 : Rat) ^ ((Nat.log2 M : Int) + x + 1) := by
    have := hu; rwa [show (Nat.log2 M : Int) + 1 + x = (Nat.log2 M : Int) + x + 1 by omega] at this
  obtain ⟨b1, b2⟩ := hS.symm.binade (E := (Nat.log2 M : Int) + x) (by omega) hl hu'
  have h := run_FPRoundBase64_q hc hism fpcr rm hrm neg q ((Nat.log2 M : Int) + x) b1 b2 hx (by rw [rbq64_side fpcr.toNat rm neg hS hg, rbq64_dyadic]; exact hOF) (by rw [rbq64_side fpcr.toNat rm neg hS hg, rbq64_dyadic]; exact hUF) (by rw [rbq64_side fpcr.toNat rm neg hS hg, rbq64_dyadic]; exact hIX)
  have hsd := rbq64_side fpcr.toNat rm neg hS hg
  rw [rbq64_dyadic] at hsd
  have h2 := run_FPRoundBase64_rb hc hism fpcr rm hrm neg M hM x hx hOF hUF hIX
  rw [h2, h]
  rw [hsd]

end JanusASL.Proofs
