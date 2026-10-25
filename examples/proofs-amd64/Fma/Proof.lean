import Janus
import Extracted

/-!
# `Fma(a, b, c float64) float64` (`math.FMA`) on amd64 built with `GOAMD64=v3`

    VFMADD231SD X1, X0, X2   ; X2 = X0 * X1 + X2, rounded once
    MOVUPS X2, X0
    RET

**Guarantee.** For all binary64 encodings `a`, `b`, `c` and every Go call state of
`example.com/basic/v3.Fma` whose `X0`, `X1`, `X2` hold `a`, `b`, `c` in their low 64 bits, whose
`MXCSR` has the control bits Go's ABIInternal fixes at calls (`GoMXCSR`, any status flags), and
for which the instruction's result is architecturally defined (`FP.FmaDefined`: at most one NaN
operand, and not `0 × ∞ + NaN`, where the IEEE standard leaves the invalid flag and the vendors
their NaN choice open), the call returns, obeys the ABI, and leaves in the low 64 bits of `X0`
the IEEE 754 fused multiply-add `a × b + c` rounded once to nearest even (`Janus.Float.fma`), or a
NaN when the IEEE result is a NaN. The same specification as the arm64 `FMADD`.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (a b c : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ (s.xmm 2).toNat % 2 ^ 64 = c.toNat ∧ GoMXCSR s ∧
        FP.FmaDefined binary64 a.toNat b.toNat c.toNat)
      (fun _ s' => ResultIs binary64 (Janus.Float.fma binary64 .rne a.toNat b.toNat c.toNat)
        ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, ha, hb, hc, hm, hdef⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  have H := FP.fma_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    a.toNat b.toNat c.toNat a.isLt b.isLt c.isLt hdef
  split at H
  next o ho =>
    obtain ⟨hlt, h⟩ := H
    janus64_run [ha, hb, hc, ho, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
    have hlt' : o.res < 18446744073709551616 := hlt
    generalize o.res = x at *
    have e : ((s.xmm 2).toNat / 18446744073709551616 * 18446744073709551616 + x % 18446744073709551616) %
        18446744073709551616 = x := by omega
    rw [e]; exact h
  next => exact H.elim

end Proof
