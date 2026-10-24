import Extracted

/-!
# `Abs(x float64) float64`: clearing the sign bit

**Guarantee.** For every binary64 encoding `x` (NaNs included) and every Go call state of
`example.com/basic.Abs` with `x` in `D0` (the low 64 bits of `V0`), the call returns, obeys the
ABI, and leaves in `D0` the encoding of `|x|`: `x` with its sign bit cleared
(`Janus.Float.abs`, IEEE 754 §5.5.1). `FPCR` and `FPSR` play no part: Go compiles
`Float64frombits(Float64bits(x) &^ (1<<63))` to `FMOV X0, D0; AND X0, X0, #0x7fffffffffffffff;
FMOV D0, X0`, integer and move instructions only (no `FABS`, whose NaN behaviour depends on
`FPCR.AH`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat)
      (fun _ s' => s'.getV 0 64 = abs binary64 x.toNat) := by
  intro ret hret s hs hx
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx]
  have hlt := x.isLt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, abs, clearSign, binary64,
    Fmt.signBit]
  omega

end Proof
