import Extracted

/-!
# `MinF64(a, b float64) float64`: one `FMIND D0, D0, D1`

**Guarantee.** For all binary64 encodings `a`, `b` and every Go call state of
`example.com/basic.MinF64` with `a` in `D0`, `b` in `D1` and `FPCR = 0`, the call returns, obeys
the ABI, and returns in `D0` IEEE 754-2019 `minimum(a, b)` (`Janus.Float.minimum`), which is
exactly Go's rule for `min` on floats: a NaN if either argument is a NaN, `-0` for `min(-0, +0)` and `min(+0, -0)`,
otherwise the smaller argument. Arm's `FMIN` (not `FMINNM`) has exactly these rules
(`Janus.Arm64.FP.fpMin_ieee`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = a.toNat ∧ s.getV 1 64 = b.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64 (minimum binary64 a.toNat b.toNat) (s'.getV 0 64)) := by
  intro ret hret s hs ⟨ha, hb, hf⟩
  janus_intro hs
  simp only [State.getV] at ha hb
  janus_run [ha, hb, hf]
  obtain ⟨hlt, h⟩ := FP.fpMin_ieee FP.IEEEMode.zero a.toNat b.toNat a.isLt b.isLt
  rw [show FP.ah 0 = false from rfl]
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  generalize (FP.fpMaxMin false binary64 0 false a.toNat b.toNat).1 = r at *
  rw [show r % 18446744073709551616 % 340282366920938463463374607431768211456 % 2 ^ 128 % 2 ^ 64 = r by omega]
  exact h

end Proof
