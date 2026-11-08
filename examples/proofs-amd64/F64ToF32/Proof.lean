import Janus
import Extracted

/-!
# `F64ToF32(x float64) float32` on amd64: one `CVTSD2SS X0, X0`

**Guarantee.** For every binary64 encoding `x` in the low 64 bits of `X0`, `GoMXCSR` and 8
readable bytes at `RSP`, the call returns, obeys the ABI, and the low 32 bits of `X0` are the IEEE
754 `convertFormat` of `x` to binary32 rounded to nearest-even
(`Janus.Float.convertFormat binary64 binary32 .rne x`), a NaN for a NaN: the same result as
arm64 (`CVTSD2SS` leaves bits 32-127 of `X0`; Go reads only the float32).
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ GoMXCSR s)
      (fun _ s' => ResultIs binary32 (convertFormat binary64 binary32 .rne x.toNat) ((s'.xmm 0).toNat % 2 ^ 32)) := by
  intro ret hret s hs ⟨hst, hx, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  obtain ⟨hlt, h⟩ := convert_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 binary32 (Or.inl rfl) x.toNat
  have hlt' : (convert binary64 binary32 ⟨.rne, false, false⟩ x.toNat).res < 4294967296 := hlt
  generalize (convert binary64 binary32 ⟨.rne, false, false⟩ x.toNat).res = r at *
  rw [show (BitVec.toNat (s.xmm 0) / 4294967296 * 4294967296 + r % 4294967296) % 4294967296 = r by omega]
  exact h

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 0x3FF0000000000000#64

def s0 : State :=
  { regs := fun r_ => if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun r_ => if r_ = 0 then BitVec.ofNat 128 x.toNat else 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat ∧ GoMXCSR s) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = Witness.x.toNat ∧ GoMXCSR s) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ResultIs binary32 (convertFormat binary64 binary32 .rne Witness.x.toNat) ((s'.xmm 0).toNat % 2 ^ 32)) :=
  ⟨ret, s0, hret, setup, hpre, correctness x ret hret s0 setup hpre⟩

end Witness

end Proof
