import Extracted

/-!
# `F64ToF32(x float64) float32`: one `FCVT S0, D0`

**Guarantee.** For every binary64 encoding `x` and every Go call state of
`example.com/basic.F64ToF32` with `x` in `D0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns in `S0` the IEEE 754 `convertFormat` of `x` to binary32 rounded to nearest-even
(`Janus.Float.convertFormat binary64 binary32 .rne x`): infinities and zeros keep their sign,
finite values are rounded (overflowing to an infinity, underflowing to a subnormal or a zero),
and a NaN gives a NaN.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary32 (convertFormat binary64 binary32 .rne x.toNat) (s'.getV 0 32)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  obtain ⟨hlt, h⟩ := FP.fpConvert_ieee FP.IEEEMode.zero binary64 binary32 (Or.inl rfl) .rne x.toNat
  have hlt' : (FP.fpConvert binary64 binary32 0 .rne x.toNat).1 < 2 ^ 32 := hlt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, show FP.roundingMode 0 = .rne from rfl]
  generalize (FP.fpConvert binary64 binary32 0 .rne x.toNat).1 = r at *
  rw [show r % 4294967296 % 340282366920938463463374607431768211456 % 2 ^ 128 % 2 ^ 32 = r by omega]
  exact h

end Proof
