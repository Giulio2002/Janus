import Janus
import Extracted

/-!
# `Abs(x float64) float64` on amd64: clearing the sign bit

**Guarantee.** For every binary64 encoding `x` (NaNs included) and every Go call state of
`example.com/basic.Abs` with `x` in the low 64 bits of `X0`, the call returns, obeys the ABI,
and leaves in the low 64 bits of `X0` the encoding of `|x|`: `x` with its sign bit cleared
(`Janus.Float.abs`). Go compiles it to `MOVQ X0, AX; BTRQ $63, AX; MOVQ AX, X0`, so `MXCSR`
plays no part.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = abs binary64 x.toNat) := by
  intro ret hret s hs ⟨hst, hx⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx]
  have hlt := x.isLt
  simp [abs, clearSign, binary64, Fmt.signBit]
  omega

end Proof
