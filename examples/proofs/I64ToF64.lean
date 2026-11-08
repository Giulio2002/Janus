import Extracted

/-!
# `I64ToF64(x int64) float64`: one `SCVTF D0, X0`

**Guarantee (`correctness`).** For every 64-bit `x` and every Go call state of
`example.com/basic.I64ToF64` with `x` in `X0` and `FPCR = 0` (Go's default: round to nearest
even, no flushing, no default NaN), the call returns, obeys the ABI, and returns in `D0` the IEEE
754 `convertFromInt` of the signed integer `x` (`Janus.Float.fromInt binary64 .rne x.toInt`):
the integer rounded to nearest-even, `+0` for `0`.

**Exactness (`exact`).** For `|x| < 2^53` the conversion is exact: truncating the result back to
an integer gives `x` (`Janus.Float.truncInt_fromInt`), so `int64(float64(x)) = x`, and the
result does not depend on the rounding direction (`fromInt_b64_rm`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => s'.getV 0 64 = fromInt binary64 .rne x.toInt) := by
  intro ret hret s hs hf
  janus_intro hs
  janus_run [hf]
  have hlt : fromInt binary64 .rne x.toInt < 2 ^ 64 := fromInt_lt binary64 .rne x.toInt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl, Bool.false_or]
  have hi : (if decide (x.toNat < 2 ^ (64 - 1)) = true then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64)
      = x.toInt := by simpa using signed64_toInt x
  rw [hi]; omega

theorem exact (x : BitVec 64) (hx : x.toInt.natAbs < 2 ^ 53) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => truncInt binary64 (s'.getV 0 64) = some x.toInt) := by
  exact (correctness x).mono (fun _ h => h) (fun _ _ _ h => by rw [h]; exact truncInt_fromInt _ _ hx)


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (s.fpcr = 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.getV 0 64 = fromInt binary64 .rne x.toInt)) := by
  refine ⟨ret, s0, (5), hret, setup, ?pre, correctness (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `exact` hold together at a concrete call, and the call returns. -/
theorem exact : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (x.toInt.natAbs < 2 ^ 53) ∧ (s.fpcr = 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (truncInt binary64 (s'.getV 0 64) = some x.toInt)) := by
  refine ⟨ret, s0, (5), hret, setup, by decide, ?pre, Proof.exact (5) (by decide) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
