import Extracted

/-!
# `U64ToF64(x uint64) float64`: one `UCVTF D0, X0`

**Guarantee.** For every 64-bit `x` and every Go call state of `example.com/basic.U64ToF64`
with `x` in `X0` and `FPCR = 0`, the call returns, obeys the ABI, and returns in `D0` the IEEE
754 `convertFromInt` of the unsigned integer `x` rounded to nearest-even
(`Janus.Float.fromInt binary64 .rne x.toNat`), the same result as amd64's multi-instruction
sequence (`examples/proofs-amd64/U64ToF64`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => s.fpcr = 0)
      (fun _ s' => s'.getV 0 64 = fromInt binary64 .rne x.toNat) := by
  intro ret hret s hs hf
  janus_intro hs
  janus_run [hf]
  have hlt : fromInt binary64 .rne x.toNat < 2 ^ 64 := fromInt_lt binary64 .rne x.toNat
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
  rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl]
  simp only [Bool.true_or, ite_true]
  omega


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
      ABIReturn s s' ∧ (s'.getV 0 64 = fromInt binary64 .rne x.toNat)) := by
  refine ⟨ret, s0, (5), hret, setup, ?pre, correctness (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
