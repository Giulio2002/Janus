import Extracted

/-!
# `F32ToF64(x float32) float64`: one `FCVT D0, S0`

**Guarantee.** For every binary32 encoding `x` and every Go call state of
`example.com/basic.F32ToF64` with `x` in `S0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns in `D0` the IEEE 754 `convertFormat` of `x` to binary64
(`Janus.Float.convertFormat binary32 binary64 .rne x`), a NaN for a NaN. Widening is exact:
every binary32 value is a binary64 value, so no rounding happens (`exact`: the result is the
`convertFormat` in **every** rounding direction, by `Janus.Float.convertFormat_32_64`, which also
shows the rounding has no error).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 32 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64 (convertFormat binary32 binary64 .rne x.toNat) (s'.getV 0 64)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  obtain ⟨hlt, h⟩ := FP.fpConvert_ieee FP.IEEEMode.zero binary32 binary64 (Or.inr rfl) .rne x.toNat
  have hlt' : (FP.fpConvert binary32 binary64 0 .rne x.toNat).1 < 2 ^ 64 := hlt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, show FP.roundingMode 0 = .rne from rfl]
  generalize (FP.fpConvert binary32 binary64 0 .rne x.toNat).1 = r at *
  rw [show r % 18446744073709551616 % 340282366920938463463374607431768211456 % 2 ^ 128 % 2 ^ 64 = r by omega]
  exact h

theorem exact (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 32 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => ∀ rm, ResultIs binary64 (convertFormat binary32 binary64 rm x.toNat) (s'.getV 0 64)) :=
  (correctness x).mono (fun _ h => h) (fun _ _ _ h rm => by rw [(convertFormat_32_64 rm _).1]; exact h)

end Proof
