import Extracted
import Janus.Contracts.SoftFloatSat

/-!
# `Mul(a, b uint64) uint64` built with `-d=softfloat`: a call of `runtime.fmul64` (arm64)

```go
func Mul(a, b uint64) uint64 { return math.Float64bits(math.Float64frombits(a) * math.Float64frombits(b)) }
```

With `-gcflags=…=-d=softfloat` the float64 multiplication is a call of `runtime.fmul64(a, b)` (the
integer registers `X0`, `X1` already hold the bits). The runtime function is left out
(`--contract runtime.fmul64`, pinned to the runtime's code) and its behaviour is the hypothesis
`SoftFmulContract` (`Janus/Contracts/SoftFloat.lean`): the IEEE 754 binary64 product, round to
nearest even, **provided the exact product is not tiny**. Go's `fmul64` is known not to be IEEE for
subnormal results, so that case is excluded by the precondition, not assumed away.

**Guarantee.** For all `a`, `b` such that `a * b` is not a tiny exact result (`¬MulTiny`), every
Go call state with `FPCR = 0` and the stack window the call needs (`CallerOK softEnv`: the
256 bytes the runtime may use below `Mul`'s 48-byte frame, and the argument slots above), the call
returns, obeys the ABI, leaves in `X0` the IEEE 754 product of the two operands (or a NaN where
IEEE has one), and changes memory only inside the stack window.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.SoftFloat

namespace Proof

set_option maxRecDepth 100000 in
theorem correctness (impl : List Segment)
    (hc : SoftFmulContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.fmul64"))
    (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => CallerOK softEnv s 48 16 ∧ s.fpcr = 0 ∧ ¬ MulTiny a.toNat b.toNat)
      (fun s s' => ResultIs binary64 (mul binary64 .rne a.toNat b.toNat) (s'.regs 0).toNat ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - (softDepth + 48), s.sp.toNat + 16)]) := by
  intro ret hret s hs ⟨hcal, hfp, hnt⟩
  have hc' := hcal
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hdp, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.fmul64"]
  refine Reaches.call (Summary.withExit hc hret) rfl
    ⟨⟨RTPre.of_caller softEnv_laws hcal (by janus_frame) (by simp; omega) rfl (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide), rfl⟩, ?_⟩ ?_
  · simpa [setReg, h_x0, h_x1] using hnt
  · intro s' hpc' ⟨r, v, fl, fp, m', ex, ep, hs', hfr, hP⟩
    subst hs'
    simp only [rtWrites, calleeStack, softEnv, softDepth, List.nil_append] at hfr
    janus_run
    refine ⟨?_, by simp only [softDepth]; janus_frame⟩
    simpa [setReg, h_x0, h_x1] using hP

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

An implementation of `SoftFmulContract` at `runtime.fmul64`'s address (the hardware `FMUL` of
`Janus.Contracts.SoftFloatSat`, which meets it: `model`), an admissible return address, and a call
state of `Mul(1.0, 1.0)` with `FPCR = 0` in a memory with the stack window, so the product is `2.0`. -/

namespace Witness

open Janus.Contracts.SoftFloatSat

/-- `runtime.fmul64`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.fmul64"

def implAt : List Segment := [{ name := "model", base := cAddr, words := mulCode }]

def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : SoftFmulContract (Extracted.program.link implAt) cAddr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hpre, hfp⟩, hnt⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine SoftRet.intro 2 s _ _ rfl rfl rfl rfl rfl rfl rfl hfp.symm (MemFrame.refl _ _) ?_
  have ha := (s.regs 0).isLt
  have hb := (s.regs 1).isLt
  have h := FP.fpMul_ieee FP.IEEEMode.zero binary64 (Or.inr rfl) (s.regs 0).toNat (s.regs 1).toNat ha hb
  have hr : FP.roundingMode 0 = .rne := rfl
  rw [hr] at h
  obtain ⟨hlt, h⟩ := h
  simp only [setReg_apply, Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show (s.regs 1).toNat < 2 ^ 128 by omega)]
  have hlt' : (FP.fpMul binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst < 2 ^ 64 := hlt
  generalize (FP.fpMul binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst = x at *
  simp only [ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega)]
  exact h

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

def a1 : BitVec 64 := BitVec.ofNat 64 one

/-- The call state: `Mul(1.0, 1.0)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then a1 else if i = 1 then a1 else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry, flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨wsp - 512, 0x300 + 0x100, true⟩, ⟨wg, 0x100, false⟩]⟩ }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [a1, a1] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre : CallerOK softEnv s0 48 16 ∧ s0.fpcr = 0 ∧ ¬ MulTiny a1.toNat a1.toNat := by
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, rfl, by decide⟩
  · simp [softEnv, outside_nil]
  · unfold Spec.Disjoint; decide
  · simp [softEnv, outside_nil]

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (ret : Nat) (s : State),
    SoftFmulContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.fmul64") ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [a1, a1] s ∧
    (CallerOK softEnv s 48 16 ∧ s.fpcr = 0 ∧ ¬ MulTiny a1.toNat a1.toNat) :=
  ⟨implAt, ret, s0, model, hret, setup, pre⟩

/-- So the guarantee is reached: `1.0 * 1.0` is the IEEE product (`1.0`). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ResultIs binary64 (mul binary64 .rne a1.toNat a1.toNat) (s'.regs 0).toNat :=
  (correctness implAt model a1 a1 ret hret s0 setup pre).mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
