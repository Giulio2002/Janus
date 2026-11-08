import Janus
import Extracted

/-!
# `MinF64(a, b float64) float64` on amd64: Go's `MINSD` sequence

**What Go emits.** `MINSD` alone is not IEEE `minimum` (it returns its second operand for a NaN
or for two zeros), so Go computes `t = MINSD(a, b)`, `u = MINSD(t, a)` and returns `u | t` (`POR`):

```
MOVUPS X0, X2; MINSD X1, X2; MOVUPS X2, X1; MINSD X0, X2; POR X1, X2; MOVUPS X2, X0; RET
```

**Guarantee.** For all binary64 encodings `a`, `b` in the low 64 bits of `X0`, `X1`, `GoMXCSR`
and 8 readable bytes at `RSP`, the call returns, obeys the ABI, and the low 64 bits of `X0` are
IEEE 754-2019 `minimum(a, b)` (`Janus.Float.minimum`): a NaN if either is a NaN (the or of a NaN
with anything is a NaN), `-0` for two zeros of different signs (the or of the two zeros), the
smaller operand otherwise. Same statement as arm64's `FMIN`. The case analysis is
`Janus.Amd64.FP.minsd_seq`; equal non-zero values have equal encodings (`b64_eq_of_not_lt'`).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary64 (minimum binary64 a.toNat b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [ha, hb, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
  obtain ⟨hl, hr⟩ := minsd_seq hc a.toNat b.toNat a.isLt b.isLt
  have htl : (minmax false binary64 ⟨.rne, false, false⟩ a.toNat b.toNat).res < 2 ^ 64 := by
    rw [minmax_min_ieee hc _ _ a.isLt b.isLt]; have := a.isLt; have := b.isLt
    split <;> (try split) <;> (try split) <;> omega
  generalize (minmax false binary64 ⟨.rne, false, false⟩ a.toNat b.toNat).res = t at hl hr htl ⊢
  rw [show (BitVec.toNat (s.xmm 0) / 18446744073709551616 * 18446744073709551616 + t % 18446744073709551616) %
    18446744073709551616 = t by omega]
  have hul : (minmax false binary64 ⟨.rne, false, false⟩ t a.toNat).res < 2 ^ 64 := by
    rw [minmax_min_ieee hc _ _ htl a.isLt]; have := a.isLt
    split <;> (try split) <;> (try split) <;> omega
  generalize (minmax false binary64 ⟨.rne, false, false⟩ t a.toNat).res = u at hl hr hul ⊢
  have key : ∀ A B : Nat, ((A / 18446744073709551616 * 18446744073709551616 + u % 18446744073709551616) %
      340282366920938463463374607431768211456 |||
      (B / 18446744073709551616 * 18446744073709551616 + t % 18446744073709551616) %
      340282366920938463463374607431768211456) % 18446744073709551616 = u ||| t := by
    intro A B
    rw [show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, Nat.or_mod_two_pow]
    first | (with_reducible congr 1 <;> omega) | (congr 1 <;> omega)
  rw [key]
  exact hr

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def a : BitVec 64 := 0x3FF0000000000000#64
def b : BitVec 64 := 0x4000000000000000#64

def s0 : State :=
  { regs := fun r_ => if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun r_ => if r_ = 0 then BitVec.ofNat 128 a.toNat else if r_ = 1 then BitVec.ofNat 128 b.toNat else 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ GoMXCSR s) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR, Janus.Amd64.Program.DataLoaded]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> first | decide | decide +kernel) | decide +kernel

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = Witness.a.toNat ∧ (s.xmm 1).toNat % 2 ^ 64 = Witness.b.toNat ∧ GoMXCSR s) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ResultIs binary64 (minimum binary64 Witness.a.toNat Witness.b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) :=
  ⟨ret, s0, hret, setup, hpre, correctness a b ret hret s0 setup hpre⟩

end Witness

end Proof
