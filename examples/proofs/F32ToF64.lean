import Extracted

/-!
# `F32ToF64(x float32) float64`: one `FCVT D0, S0`

**Guarantee.** For every binary32 encoding `x` and every Go call state of
`example.com/basic.F32ToF64` with `x` in `S0` and `FPCR = 0`, the call returns, obeys the ABI,
and returns in `D0` the IEEE 754 `convertFormat` of `x` to binary64
(`Janus.Float.convertFormat binary32 binary64 .rne x`), a NaN for a NaN. Widening is exact:
every binary32 value is a binary64 value, so no rounding happens (`exact`: the result is the
`convertFormat` in **every** rounding direction, by `Janus.Float.convertFormat_32_64`, which also
shows the rounding has no error).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 32 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => ResultIs binary64 (convertFormat binary32 binary64 .rne x.toNat) (s'.getV 0 64)) := by
  intro ret hret s hs ⟨hx, hf⟩
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx, hf]
  obtain ⟨hlt, h⟩ := FP.fpConvert_ieee FP.IEEEMode.zero binary32 binary64 (Or.inr rfl) .rne x.toNat
  have hlt' : (FP.fpConvert binary32 binary64 0 .rne x.toNat).1 < 2 ^ 64 := hlt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, show FP.roundingMode 0 = .rne from rfl]
  generalize (FP.fpConvert binary32 binary64 0 .rne x.toNat).1 = r at *
  rw [show r % 18446744073709551616 % 340282366920938463463374607431768211456 % 2 ^ 128 % 2 ^ 64 = r by omega]
  exact h

theorem exact (x : BitVec 32) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 32 = x.toNat ∧ s.fpcr = 0)
      (fun _ s' => ∀ rm, ResultIs binary64 (convertFormat binary32 binary64 rm x.toNat) (s'.getV 0 64)) :=
  (correctness x).mono (fun _ h => h) (fun _ _ _ h rm => by rw [(convertFormat_32_64 rm _).1]; exact h)


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def c_x : BitVec 32 := 0x3FC00000

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem,
    vregs := fun i => if i = 0 then BitVec.ofNat 128 (c_x.toNat) else 0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (s.getV 0 32 = c_x.toNat ∧ s.fpcr = 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (ResultIs binary64 (convertFormat binary32 binary64 .rne c_x.toNat) (s'.getV 0 64))) := by
  refine ⟨ret, s0, hret, setup, ?pre, correctness c_x ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `exact` hold together at a concrete call, and the call returns. -/
theorem exact : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (s.getV 0 32 = c_x.toNat ∧ s.fpcr = 0) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (∀ rm, ResultIs binary64 (convertFormat binary32 binary64 rm c_x.toNat) (s'.getV 0 64))) := by
  refine ⟨ret, s0, hret, setup, ?pre, Proof.exact c_x ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
