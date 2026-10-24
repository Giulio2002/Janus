import Janus
import Extracted

/-!
# `Dot3(a0, a1, a2, b0, b1, b2 float64) float64` on amd64: not fused

**What Go emits.** With `GOAMD64=v1` there is no FMA, so `a0*b0 + a1*b1 + a2*b2` compiles to
`MULSD X3, X0; MULSD X1, X4; ADDSD X4, X0; MULSD X2, X5; ADDSD X5, X0`: three products and two
sums, **each rounded** (unlike arm64, where the two later products are fused into the sums).

**Guarantee.** For all binary64 encodings `a0 … b2` in the low 64 bits of `X0`–`X5` and an
`MXCSR` with Go's default control bits and any status flags (`GoMXCSR`), the call returns, obeys the ABI, and the low 64 bits of `X0` are the IEEE 754
result of `(a0 × b0 + a1 × b1) + a2 × b2` with every operation rounded to nearest even
(`Janus.Float.mul`, `Janus.Float.add`), or a NaN when an IEEE step is a NaN.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (a0 a1 a2 b0 b1 b2 : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a0.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = a1.toNat ∧ (s.xmm 2).toNat % 2 ^ 64 = a2.toNat ∧
        (s.xmm 3).toNat % 2 ^ 64 = b0.toNat ∧ (s.xmm 4).toNat % 2 ^ 64 = b1.toNat ∧
        (s.xmm 5).toNat % 2 ^ 64 = b2.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary64
        ((mul binary64 .rne a0.toNat b0.toNat).bind fun p =>
          (mul binary64 .rne a1.toNat b1.toNat).bind fun q =>
          (add binary64 .rne p q).bind fun r =>
          (mul binary64 .rne a2.toNat b2.toNat).bind fun w => add binary64 .rne r w)
        ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, h0, h1, h2, h3, h4, h5, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [h0, h1, h2, h3, h4, h5, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  have std : binary64.Std := Or.inr rfl
  have hc : FP.IEEEMode ⟨.rne, false, false⟩ := ⟨rfl, rfl⟩
  obtain ⟨hp, hp'⟩ := FP.binop_mul_ieee hc binary64 std a0.toNat b0.toNat a0.isLt b0.isLt
  generalize (FP.binop .mul binary64 ⟨.rne, false, false⟩ a0.toNat b0.toNat).res = p at *
  have lp : ∀ q, (q * 18446744073709551616 + p % 18446744073709551616) % 18446744073709551616 = p :=
    fun q => by have : p < 2 ^ 64 := hp; omega
  obtain ⟨hq, hq'⟩ := FP.binop_mul_ieee hc binary64 std b1.toNat a1.toNat b1.isLt a1.isLt
  rw [mul_comm] at hq'
  generalize (FP.binop .mul binary64 ⟨.rne, false, false⟩ b1.toNat a1.toNat).res = q at *
  have lq : ∀ k, (k * 18446744073709551616 + q % 18446744073709551616) % 18446744073709551616 = q :=
    fun k => by have : q < 2 ^ 64 := hq; omega
  simp only [lp, lq]
  obtain ⟨hr, hr'⟩ := FP.binop_add_ieee hc binary64 std p q hp hq
  generalize (FP.binop .add binary64 ⟨.rne, false, false⟩ p q).res = r at *
  have lr : ∀ k, (k * 18446744073709551616 + r % 18446744073709551616) % 18446744073709551616 = r :=
    fun k => by have : r < 2 ^ 64 := hr; omega
  obtain ⟨hw, hw'⟩ := FP.binop_mul_ieee hc binary64 std b2.toNat a2.toNat b2.isLt a2.isLt
  rw [mul_comm] at hw'
  generalize (FP.binop .mul binary64 ⟨.rne, false, false⟩ b2.toNat a2.toNat).res = w at *
  have lw : ∀ k, (k * 18446744073709551616 + w % 18446744073709551616) % 18446744073709551616 = w :=
    fun k => by have : w < 2 ^ 64 := hw; omega
  simp only [lr, lw]
  obtain ⟨hv, hv'⟩ := FP.binop_add_ieee hc binary64 std r w hr hw
  generalize (FP.binop .add binary64 ⟨.rne, false, false⟩ r w).res = v at *
  have lv : ∀ k, (k * 18446744073709551616 + v % 18446744073709551616) % 18446744073709551616 = v :=
    fun k => by have : v < 2 ^ 64 := hv; omega
  simp only [lv]
  have nan_mul : ∀ y, isNaN binary64 y = true → ∀ (k : Nat → Option Nat),
      ((mul binary64 .rne a1.toNat b1.toNat).bind fun q => (add binary64 .rne y q).bind k) = none := by
    intro y hy k; cases mul binary64 .rne a1.toNat b1.toNat <;> simp [add_nan_left _ _ _ _ hy]
  rw [resultIs_bind binary64 _ p _ _ (fun y hy => nan_mul y hy _) hp']
  rw [resultIs_bind binary64 _ q _ _ (fun y hy => by simp [add_nan_right _ _ _ _ hy]) hq']
  rw [resultIs_bind binary64 _ r _ _ (fun y hy => by
    cases mul binary64 .rne a2.toNat b2.toNat <;> simp [add_nan_left _ _ _ _ hy]) hr']
  rw [resultIs_bind binary64 _ w _ _ (fun y hy => add_nan_right _ _ _ _ hy) hw']
  exact hv'

end Proof
