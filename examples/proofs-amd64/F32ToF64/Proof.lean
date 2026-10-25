import Janus
import Extracted

/-!
# `F32ToF64(x float32) float64` on amd64: one `CVTSS2SD X0, X0`

**Guarantee.** For every binary32 encoding `x` in the low 32 bits of `X0`, `GoMXCSR` and 8
readable bytes at `RSP`, the call returns, obeys the ABI, and the low 64 bits of `X0` are the IEEE
754 `convertFormat` of `x` to binary64 (`Janus.Float.convertFormat binary32 binary64 .rne x`), a
NaN for a NaN. `exact`: the same in every rounding direction (widening never rounds,
`Janus.Float.convertFormat_32_64`).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 32 = x.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary64 (convertFormat binary32 binary64 .rne x.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  obtain ⟨hlt, h⟩ := convert_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary32 binary64 (Or.inr rfl) x.toNat
  have hlt' : (convert binary32 binary64 ⟨.rne, false, false⟩ x.toNat).res < 18446744073709551616 := hlt
  generalize (convert binary32 binary64 ⟨.rne, false, false⟩ x.toNat).res = r at *
  rw [show (BitVec.toNat (s.xmm 0) / 18446744073709551616 * 18446744073709551616 + r % 18446744073709551616) % 18446744073709551616 = r by omega]
  exact h

theorem exact (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 32 = x.toNat ∧ GoMXCSR s)
      (fun _ s' => ∀ rm, ResultIs binary64 (convertFormat binary32 binary64 rm x.toNat)
        ((s'.xmm 0).toNat % 2 ^ 64)) :=
  (correctness x).mono (fun _ h => h) (fun _ _ _ h rm => by rw [(convertFormat_32_64 rm _).1]; exact h)

end Proof
