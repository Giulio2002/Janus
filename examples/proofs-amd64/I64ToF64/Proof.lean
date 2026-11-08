import Janus
import Extracted

/-!
# `I64ToF64(x int64) float64` on amd64: `XORPS X0, X0; CVTSI2SDQ AX, X0`

**Guarantee (`correctness`).** For every 64-bit `x` and every Go call state with `x` in `RAX`,
an `MXCSR` with Go's default control bits and any status flags (`GoMXCSR`) and 8 readable bytes
at `RSP`, the call returns, obeys the ABI, and returns in the low 64 bits of `X0` the IEEE 754
`convertFromInt` of the signed integer `x`, rounded to nearest-even
(`Janus.Float.fromInt binary64 .rne x.toInt`): the same result as arm64.

**Exactness (`exact`).** For `|x| < 2^53` truncating the result gives `x` back.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧ GoMXCSR s)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = fromInt binary64 .rne x.toInt) := by
  intro ret hret s hs ⟨hst, hm⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm]
  rw [ofInt_ieee ⟨rfl, rfl⟩]
  have hi : (if x.toNat < 2 ^ (64 - 1) then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64) = x.toInt :=
    signed64_toInt x
  have hlt : fromInt binary64 .rne x.toInt < 2 ^ 64 := fromInt_lt binary64 .rne x.toInt
  simp only at hi ⊢
  rw [hi]; omega

theorem exact (x : BitVec 64) (hx : x.toInt.natAbs < 2 ^ 53) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧ GoMXCSR s)
      (fun _ s' => truncInt binary64 ((s'.xmm 0).toNat % 2 ^ 64) = some x.toInt) :=
  (correctness x).mono (fun _ h => h) (fun _ _ _ h => by rw [h]; exact truncInt_fromInt _ _ hx)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 5#64

def s0 : State :=
  { regs := fun r_ => if r_ = 0 then x else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ GoMXCSR s) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint, Janus.Amd64.GoABI.GoMXCSR]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (StackWritable s 0 8 ∧ GoMXCSR s) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.xmm 0).toNat % 2 ^ 64 = fromInt binary64 .rne x.toInt) :=
  ⟨ret, s0, x, hret, setup, hpre, correctness x ret hret s0 setup hpre⟩

/-- All hypotheses of `exact` hold together, and the call returns. -/
theorem exact : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (x.toInt.natAbs < 2 ^ 53) ∧ (StackWritable s 0 8 ∧ GoMXCSR s) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ truncInt binary64 ((s'.xmm 0).toNat % 2 ^ 64) = some x.toInt) :=
  ⟨ret, s0, x, hret, setup, by decide, hpre, Proof.exact x (by decide) ret hret s0 setup hpre⟩

end Witness

end Proof
