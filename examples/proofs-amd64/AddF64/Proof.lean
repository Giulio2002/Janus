import Janus
import Extracted

/-!
# `AddF64(a, b float64) float64` on amd64: `ADDSD X1, X0; RET`

**Guarantee.** For all binary64 encodings `a`, `b` and every Go call state of
`example.com/basic.AddF64` whose `X0` and `X1` hold `a` and `b` in their low 64 bits (Go's
ABIInternal passes `float64` arguments in `X0`–`X14`) and whose `MXCSR` has the control bits
Go's ABIInternal fixes at calls (`GoMXCSR`: those of `0x1F80`, round to nearest even, no
`FTZ`/`DAZ`, every exception masked) with **any** status flags (they are sticky: a Go program's
`MXCSR` is already `0x1FA0` when `main` starts), the call returns, obeys the ABI, and leaves in the low 64 bits of `X0` the
IEEE 754 sum `a + b` rounded to nearest even (`Janus.Float.add`), or a NaN when the IEEE result
is a NaN. The same specification as the arm64 theorem.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary64 (add binary64 .rne a.toNat b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) := by
  intro ret hret s hs ⟨hst, ha, hb, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [ha, hb, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  have h := FP.binop_add_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    a.toNat b.toNat a.isLt b.isLt
  obtain ⟨hlt, h⟩ := h
  have hlt' : (FP.binop .add binary64 ⟨.rne, false, false⟩ a.toNat b.toNat).res < 2 ^ 64 := hlt
  generalize (FP.binop .add binary64 ⟨.rne, false, false⟩ a.toNat b.toNat).res = x at *
  have e : ((s.xmm 0).toNat / 18446744073709551616 * 18446744073709551616 + x % 18446744073709551616) %
      18446744073709551616 = x := by omega
  rw [e]; exact h

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
theorem hpre : (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = a.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = b.toNat ∧ GoMXCSR s) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = Witness.a.toNat ∧
        (s.xmm 1).toNat % 2 ^ 64 = Witness.b.toNat ∧ GoMXCSR s) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ResultIs binary64 (add binary64 .rne Witness.a.toNat Witness.b.toNat) ((s'.xmm 0).toNat % 2 ^ 64)) :=
  ⟨ret, s0, hret, setup, hpre, correctness a b ret hret s0 setup hpre⟩

end Witness

end Proof
