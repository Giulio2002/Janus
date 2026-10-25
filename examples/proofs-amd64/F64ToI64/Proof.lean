import Janus
import Extracted

/-!
# `F64ToI64(x float64) int64` on amd64: one `CVTTSD2SIQ X0, AX`

**Guarantee (`correctness`).** For every binary64 encoding `x` whose value truncated toward zero
is an integer `i` with `-2^63 ≤ i < 2^63` (`Janus.Float.truncInt`), and every Go call state with
`x` in the low 64 bits of `X0`, `GoMXCSR` and 8 readable bytes at `RSP`, the call returns, obeys
the ABI, and returns `i` in `RAX` (`RAX.toInt = i`): the same result as arm64.

**Out of range (`outOfRange`).** The Go specification leaves the result implementation-specific.
On amd64 it is what `CVTTSD2SI` delivers: for a truncation outside `[-2^63, 2^63)`, an infinity
or a NaN, the integer indefinite `2^63` (`0x8000000000000000`, i.e. `-2^63`). Unlike arm64
(which saturates to `2^63 - 1` above the range and gives `0` for a NaN), the result is the same
for every out-of-range input.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : -(2 ^ 63 : Int) ≤ i) (h1 : i < 2 ^ 63) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ GoMXCSR s)
      (fun _ s' => (s'.regs 0).toInt = i) := by
  intro ret hret s hs ⟨hst, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  rw [(toInt_rz64 ⟨rfl, rfl⟩ x.toNat).1 i hi h0 h1, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have : ((i % (2 ^ 64 : Int)).toNat) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  split <;> omega

/-- The integer indefinite for every input outside the range. -/
theorem outOfRange (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ GoMXCSR s)
      (fun _ s' =>
        (∀ i, truncInt binary64 x.toNat = some i → (i < -(2 ^ 63 : Int) ∨ 2 ^ 63 ≤ i) →
          (s'.regs 0).toNat = 2 ^ 63) ∧
        (truncInt binary64 x.toNat = none → (s'.regs 0).toNat = 2 ^ 63)) := by
  intro ret hret s hs ⟨hst, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  obtain ⟨-, h2, h3⟩ := toInt_rz64 (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ x.toNat
  refine ⟨fun i hi hr => ?_, fun hn => ?_⟩
  · rw [h2 i hi hr]
  · rw [h3 hn]

end Proof
