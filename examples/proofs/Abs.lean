import Extracted

/-!
# `Abs(x float64) float64`: clearing the sign bit

**Guarantee.** For every binary64 encoding `x` (NaNs included) and every Go call state of
`example.com/basic.Abs` with `x` in `D0` (the low 64 bits of `V0`), the call returns, obeys the
ABI, and leaves in `D0` the encoding of `|x|`: `x` with its sign bit cleared
(`Janus.Float.abs`, IEEE 754 §5.5.1). `FPCR` and `FPSR` play no part: Go compiles
`Float64frombits(Float64bits(x) &^ (1<<63))` to `FMOV X0, D0; AND X0, X0, #0x7fffffffffffffff;
FMOV D0, X0`, integer and move instructions only (no `FABS`, whose NaN behaviour depends on
`FPCR.AH`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Float

namespace Proof

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => s.getV 0 64 = x.toNat)
      (fun _ s' => s'.getV 0 64 = abs binary64 x.toNat) := by
  intro ret hret s hs hx
  janus_intro hs
  simp only [State.getV] at hx
  janus_run [hx]
  have hlt := x.isLt
  simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, abs, clearSign, binary64,
    Fmt.signBit]
  omega


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩

def c_x : BitVec 64 := 0xBFF8000000000000

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
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (s.getV 0 64 = c_x.toNat) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ (s'.getV 0 64 = abs binary64 c_x.toNat)) := by
  refine ⟨ret, s0, hret, setup, ?pre, correctness c_x ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness

end Proof
