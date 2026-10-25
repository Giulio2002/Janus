import Extracted

/-!
# `U64ToF64(x uint64) float64`: one `UCVTF D0, X0`

**Guarantee.** For every 64-bit `x` and every Go call state of `example.com/basic.U64ToF64`
with `x` in `X0` and `FPCR = 0`, the call returns, obeys the ABI, and returns in `D0` the IEEE
754 `convertFromInt` of the unsigned integer `x` rounded to nearest-even
(`Janus.Float.fromInt binary64 .rne x.toNat`), the same result as amd64's multi-instruction
sequence (`examples/proofs-amd64/U64ToF64`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => s'.getV 0 64 = fromInt binary64 .rne x.toNat) := by
  intro ret hret s hs hf
  janus_intro hs
  janus_run [hf]
  have hlt : fromInt binary64 .rne x.toNat < 2 ^ 64 := fromInt_lt binary64 .rne x.toNat
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl]
  simp only [Bool.true_or, ite_true]
  omega

end Proof
