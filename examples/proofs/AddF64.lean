import Extracted

/-!
# `AddF64(a, b float64) float64`: one `FADD D0, D0, D1`

**Guarantee.** For all binary64 encodings `a`, `b` and every Go call state of
`example.com/basic.AddF64` whose `D0` and `D1` (the low 64 bits of `V0`, `V1`: Go's
ABIInternal passes the two `float64` arguments there) hold `a` and `b`, and whose `FPCR` is 0
(the value Linux starts every process with and Go never changes: round to nearest even, no
flush-to-zero, NaNs propagate, no alternate handling, no traps), the call returns (never
faults or panics), obeys the ABI, and leaves in `D0` (the `float64` result) the IEEE 754 sum
`a + b` rounded to nearest even (`Janus.Float.add`), or a NaN when the IEEE result is a NaN
(a NaN operand or `∞ - ∞`).

`exact` states the result for every `FPCR` without trap enables: `D0` is `FPAdd(a, b, FPCR)`
of the Arm ASL (`Janus.Arm64.FP.fpAdd`, which honours `RMode`, `FZ`, `DN`, `FIZ`, `AH`), and
`FPSR` gains exactly the exceptions it raises.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = a.toNat ∧ s.getV 1 64 = b.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64 (add binary64 .rne a.toNat b.toNat) (s'.getV 0 64)) := by
  intro ret hret s hs ⟨ha, hb, hf⟩
  janus_intro hs
  simp only [State.getV] at ha hb
  janus_run [ha, hb, hf]
  have h := FP.fpAdd_ieee FP.IEEEMode.zero binary64 (Or.inr rfl) a.toNat b.toNat a.isLt b.isLt
  have hr : FP.roundingMode 0 = .rne := rfl
  rw [hr] at h
  obtain ⟨hlt, h⟩ := h
  have hlt' : (FP.fpAdd binary64 0 a.toNat b.toNat).1 < 2 ^ 64 := hlt
  generalize (FP.fpAdd binary64 0 a.toNat b.toNat).1 = x at *
  have h128 : x < 2 ^ 128 := by omega
  simp only [State.getV, setVReg_apply, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt h128]
  unfold ResultIs at *
  split at h <;> simp_all [Nat.mod_eq_of_lt hlt']

theorem exact (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = a.toNat ∧ s.getV 1 64 = b.toNat ∧ FP.trapEnables s.fpcr.toNat = 0)
      (fun s s' => s'.getV 0 64 = (FP.fpAdd binary64 s.fpcr.toNat a.toNat b.toNat).1 % 2 ^ 64 ∧
        s'.fpsr = s.fpsr ||| BitVec.ofNat 32 ((FP.fpAdd binary64 s.fpcr.toNat a.toNat b.toNat).2.proc |||
          (FP.fpAdd binary64 s.fpcr.toNat a.toNat b.toNat).2.direct)) := by
  intro ret hret s hs ⟨ha, hb, ht⟩
  janus_intro hs
  simp only [State.getV] at ha hb
  janus_run [ha, hb, ht]
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  generalize (FP.fpAdd binary64 s.fpcr.toNat a.toNat b.toNat).1 = r
  generalize (if FP.isMerging s.fpcr.toNat = true then (s.vregs 0).toNat % 340282366920938463463374607431768211456
    else 0) = q
  omega

end Proof
