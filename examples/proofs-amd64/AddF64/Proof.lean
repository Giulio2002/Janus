import Janus
import Extracted

/-!
# `AddF64(a, b float64) float64` on amd64: `ADDSD X1, X0; RET`

**Guarantee.** For all binary64 encodings `a`, `b` and every Go call state of
`example.com/basic.AddF64` whose `X0` and `X1` hold `a` and `b` in their low 64 bits (Go's
ABIInternal passes `float64` arguments in `X0`–`X14`) and whose `MXCSR` is `0x1F80` (the value
Linux gives every process and Go never changes: round to nearest even, no `FTZ`/`DAZ`, every
exception masked), the call returns, obeys the ABI, and leaves in the low 64 bits of `X0` the
IEEE 754 sum `a + b` rounded to nearest even (`Janus.Float.add`), or a NaN when the IEEE result
is a NaN. The same specification as the arm64 theorem.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ s.mxcsr = 0x1F80)
      (fun _ s' => ResultIs binary64 (add binary64 .rne a.toNat b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [ha, hb, hm]
  have h := FP.binop_add_ieee FP.IEEEMode.default binary64 (Or.inr rfl) a.toNat b.toNat a.isLt b.isLt
  rw [show FP.rounding 0x1F80 = .rne from by decide] at h
  obtain ⟨hlt, h⟩ := h
  have hlt' : (FP.binop .add binary64 8064 a.toNat b.toNat).res < 2 ^ 64 := hlt
  generalize (FP.binop .add binary64 8064 a.toNat b.toNat).res = x at *
  have e : ((s.xmm 0).toNat / 18446744073709551616 * 18446744073709551616 + x % 18446744073709551616) %
      18446744073709551616 = x := by omega
  rw [e]; exact h

end Proof
