import Extracted

/-!
# `F64ToU64(x float64) uint64`: one `FCVTZU X0, D0`

**Guarantee (`correctness`).** For every binary64 encoding `x` whose value truncated toward
zero is an integer `i` with `0 ≤ i < 2^64` (`Janus.Float.truncInt`), and every Go call state of
`example.com/basic.F64ToU64` with `x` in `D0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns `i` in `X0`.

**Out of range (`exact`).** Go leaves `uint64(x)` implementation-defined outside that range.
On arm64 it is exactly Arm's `FPToFixed(x, 0, unsigned, FPCR, RZ, 64)`
(`Janus.Arm64.FP.fpToFixed`), for every `FPCR` without trap enables: values below `0` (after
truncation) give `0`, values at or above `2^64` and `+∞` give `2^64 - 1`, NaNs give `0` (all
with `FPSR.IOC`). `saturation` spells this out for `FPCR = 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) (i : Int) (hi : truncInt binary64 x.toNat = some i)
    (h0 : 0 ≤ i) (h1 : i < 2 ^ 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => (s'.regs 0).toNat = i.toNat) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  rw [FP.fpToFixed_rzu_ieee FP.IEEEMode.zero binary64 x.toNat i hi h0 h1]
  exact Nat.mod_eq_of_lt (by omega)

theorem exact (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ FP.trapEnables s.fpcr.toNat = 0)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 (FP.fpToFixed binary64 s.fpcr.toNat true .rz 64 x.toNat).1) := by
  intro ret hret s hs ⟨hx, ht⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, ht]

/-- Saturation, for `FPCR = 0`: a truncation below `0`, a NaN and `-∞` give `0`; a truncation at
or above `2^64` and `+∞` give `2^64 - 1`. -/
theorem saturation (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' =>
        (∀ i, truncInt binary64 x.toNat = some i → i < 0 → (s'.regs 0).toNat = 0) ∧
        (∀ i, truncInt binary64 x.toNat = some i → 2 ^ 64 ≤ i → (s'.regs 0).toNat = 2 ^ 64 - 1) ∧
        (isNaN binary64 x.toNat = true → (s'.regs 0).toNat = 0) ∧
        (classify binary64 x.toNat = .inf →
          (s'.regs 0).toNat = if signOf binary64 x.toNat then 0 else 2 ^ 64 - 1)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  have hsp := FP.fpToFixed_rzu_special FP.IEEEMode.zero binary64 x.toNat
  refine ⟨fun i hi hneg => ?_, fun i hi hbig => ?_, fun hn => ?_, fun hinf => ?_⟩
  · rw [(FP.fpToFixed_rzu_sat FP.IEEEMode.zero binary64 x.toNat i hi).1 hneg]
  · rw [(FP.fpToFixed_rzu_sat FP.IEEEMode.zero binary64 x.toNat i hi).2 hbig]
  · rw [hsp.1 hn]
  · rw [hsp.2 hinf]; split <;> rfl

end Proof
