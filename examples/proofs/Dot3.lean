import Extracted

/-!
# `Dot3(a0, a1, a2, b0, b1, b2 float64) float64`: fused on arm64

**What Go emits.** `a0*b0 + a1*b1 + a2*b2` compiles to `FMUL D3, D3, D0` followed by two fused
multiply-adds, `FMADD D1, D1, D4, D3` and `FMADD D0, D2, D5, D1`: Go's arm64 backend fuses
`x*y + z` (the Go spec permits fusing). So the second and third products are **not** rounded
on their own; each `FMADD` rounds `addend + x*y` once.

**Guarantee.** For all binary64 encodings `a0 … b2` and every Go call state of
`example.com/basic.Dot3` with the six arguments in `D0`–`D5` (`a0 a1 a2 b0 b1 b2`, Go's
ABIInternal order) and `FPCR = 0` (round to nearest even, no flushing, no default NaN, no
alternate handling), the call returns, obeys the ABI, and leaves in `D0` the IEEE 754 result of
`fma(a2, b2, fma(a1, b1, a0 × b0))` (`Janus.Float.mul`, `Janus.Float.fma`), each operation
rounded to nearest even; when any step's IEEE result is a NaN, `D0` is a NaN.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float
namespace Proof
theorem correctness (a0 a1 a2 b0 b1 b2 : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = a0.toNat ∧ s.getV 1 64 = a1.toNat ∧ s.getV 2 64 = a2.toNat ∧
        s.getV 3 64 = b0.toNat ∧ s.getV 4 64 = b1.toNat ∧ s.getV 5 64 = b2.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64
        ((mul binary64 .rne a0.toNat b0.toNat).bind fun t =>
          (fma binary64 .rne a1.toNat b1.toNat t).bind fun u => fma binary64 .rne a2.toNat b2.toNat u)
        (s'.getV 0 64)) := by
  intro ret hret s hs ⟨h0, h1, h2, h3, h4, h5, hf⟩
  janus_intro hs
  simp only [State.getV] at h0 h1 h2 h3 h4 h5
  janus_run [h0, h1, h2, h3, h4, h5, hf]
  have std : binary64.Std := Or.inr rfl
  have hr : FP.roundingMode 0 = .rne := rfl
  obtain ⟨ht, hm⟩ := FP.fpMul_ieee FP.IEEEMode.zero binary64 std b0.toNat a0.toNat b0.isLt a0.isLt
  rw [hr, mul_comm] at hm
  generalize (FP.fpMul binary64 0 b0.toNat a0.toNat).1 = t at *
  have ht' : t < 2 ^ 64 := ht
  rw [Nat.mod_eq_of_lt ht', Nat.mod_eq_of_lt (by omega : t < 2 ^ 128)]
  obtain ⟨hu, hfu⟩ := FP.fpMulAdd_ieee FP.IEEEMode.zero binary64 std t a1.toNat b1.toNat ht a1.isLt b1.isLt
  rw [hr] at hfu
  generalize (FP.fpMulAdd binary64 0 t a1.toNat b1.toNat).1 = u at *
  have hu' : u < 2 ^ 64 := hu
  rw [Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt (by omega : u < 2 ^ 128)]
  obtain ⟨hv, hfv⟩ := FP.fpMulAdd_ieee FP.IEEEMode.zero binary64 std u a2.toNat b2.toNat hu a2.isLt b2.isLt
  rw [hr] at hfv
  generalize (FP.fpMulAdd binary64 0 u a2.toNat b2.toNat).1 = v at *
  have hv' : v < 2 ^ 64 := hv
  simp only [State.getV, setVReg_apply, ite_true, Nat.mod_eq_of_lt hv',
    Nat.mod_eq_of_lt (by omega : v < 2 ^ 128)]
  rw [resultIs_bind binary64 _ t _ _ (fun y hy => by simp [fma_nan _ _ _ _ _ hy]) hm,
    resultIs_bind binary64 _ u _ _ (fun y hy => fma_nan _ _ _ _ _ hy) hfu]
  have hv128 : v < 2 ^ 128 := by omega
  simpa [Nat.mod_eq_of_lt hv', Nat.mod_eq_of_lt hv128] using hfv
end Proof
