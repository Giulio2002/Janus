import Extracted

/-!
# `F64ToI64(x float64) int64`: one `FCVTZS X0, D0`

**Guarantee (`correctness`).** For every binary64 encoding `x` whose value truncated toward zero
is an integer `i` with `-2^63 ≤ i < 2^63` (`Janus.Float.truncInt`), and every Go call state of
`example.com/basic.F64ToI64` with `x` in `D0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns `i` in `X0` (as a 64-bit two's-complement value: `X0.toInt = i`).

**Out of range (`saturation`).** The Go specification leaves the result of an out-of-range
float-to-integer conversion implementation-specific. On arm64 it is what `FCVTZS` delivers
(Arm's `FPToFixed(x, 0, signed, FPCR, RZ, 64)`), which saturates: a truncation below `-2^63`
and `-∞` give `-2^63` (`0x8000000000000000`), a truncation at or above `2^63` and `+∞` give
`2^63 - 1`, and a NaN gives `0`. (amd64 differs: see `examples/proofs-amd64/F64ToI64`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : -(2 ^ 63 : Int) ≤ i) (h1 : i < 2 ^ 63) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => (s'.regs 0).toInt = i) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  rw [FP.fpToFixed_rzs_ieee FP.IEEEMode.zero binary64 x.toNat i hi h0 h1]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have : ((i % (2 ^ 64 : Int)).toNat) < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  split <;> omega

/-- Saturation, for `FPCR = 0`. -/
theorem saturation (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' =>
        (∀ i, truncInt binary64 x.toNat = some i → i < -(2 ^ 63 : Int) → (s'.regs 0).toNat = 2 ^ 63) ∧
        (∀ i, truncInt binary64 x.toNat = some i → 2 ^ 63 ≤ i → (s'.regs 0).toNat = 2 ^ 63 - 1) ∧
        (isNaN binary64 x.toNat = true → (s'.regs 0).toNat = 0) ∧
        (classify binary64 x.toNat = .inf →
          (s'.regs 0).toNat = if signOf binary64 x.toNat then 2 ^ 63 else 2 ^ 63 - 1)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  have hsp := FP.fpToFixed_rzs_special FP.IEEEMode.zero binary64 x.toNat
  refine ⟨fun i hi hneg => ?_, fun i hi hbig => ?_, fun hn => ?_, fun hinf => ?_⟩
  · rw [(FP.fpToFixed_rzs_sat FP.IEEEMode.zero binary64 x.toNat i hi).1 hneg]
  · rw [(FP.fpToFixed_rzs_sat FP.IEEEMode.zero binary64 x.toNat i hi).2 hbig]
  · rw [hsp.1 hn]
  · rw [hsp.2 hinf]; split <;> rfl

end Proof
