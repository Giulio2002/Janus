import Extracted

/-!
# `I64ToF64(x int64) float64`: one `SCVTF D0, X0`

**Guarantee (`correctness`).** For every 64-bit `x` and every Go call state of
`example.com/basic.I64ToF64` with `x` in `X0` and `FPCR = 0` (Go's default: round to nearest
even, no flushing, no default NaN), the call returns, obeys the ABI, and returns in `D0` the IEEE
754 `convertFromInt` of the signed integer `x` (`Janus.Float.fromInt binary64 .rne x.toInt`):
the integer rounded to nearest-even, `+0` for `0`.

**Exactness (`exact`).** For `|x| < 2^53` the conversion is exact: truncating the result back to
an integer gives `x` (`Janus.Float.truncInt_fromInt`), so `int64(float64(x)) = x`, and the
result does not depend on the rounding direction (`fromInt_b64_rm`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => s'.getV 0 64 = fromInt binary64 .rne x.toInt) := by
  intro ret hret s hs hf
  janus_intro hs
  janus_run [hf]
  have hlt : fromInt binary64 .rne x.toInt < 2 ^ 64 := fromInt_lt binary64 .rne x.toInt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl, Bool.false_or]
  have hi : (if decide (x.toNat < 2 ^ (64 - 1)) = true then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64)
      = x.toInt := by simpa using signed64_toInt x
  rw [hi]; omega

theorem exact (x : BitVec 64) (hx : x.toInt.natAbs < 2 ^ 53) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => truncInt binary64 (s'.getV 0 64) = some x.toInt) := by
  exact (correctness x).mono (fun _ h => h) (fun _ _ _ h => by rw [h]; exact truncInt_fromInt _ _ hx)

end Proof
