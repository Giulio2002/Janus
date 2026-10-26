import Janus
import Janus.Contracts.SoftFloatSatAmd64
import Extracted

/-!
# `Mul(a, b uint64) uint64` built with `-d=softfloat`: a call of `runtime.fmul64` (amd64)

The amd64 version of `examples/rtmisc/proofs/arm64/SoftMul.lean` (which explains the contract and
why it excludes tiny results): `Mul` calls `runtime.fmul64(a, b)` with the bits in `RAX`, `RBX`.

**Guarantee.** For all `a`, `b` such that the exact product is not tiny (`¬MulTiny`), every Go call
state with Go's `MXCSR` controls (`GoMXCSR`) and the stack window the call needs (`CallerOK64
softEnv`: the 256 bytes the runtime may use below `Mul`'s frame (40 bytes with the return address), and the argument slots
above), the call returns, obeys the ABI, leaves in `RAX` the IEEE 754 product of the two operands (or a
NaN where IEEE has one), and changes memory only inside the stack window.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.SoftFloat

namespace Proof

set_option maxRecDepth 100000 in
theorem correctness (impl : List Janus.Amd64.Segment)
    (hc : SoftFmulContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.fmul64"))
    (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => CallerOK64 softEnv s 40 16 ∧ GoMXCSR s ∧ ¬ MulTiny a.toNat b.toNat)
      (fun s s' => ResultIs binary64 (mul binary64 .rne a.toNat b.toNat) (s'.regs 0).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - (softDepth + 40), (s.regs 4).toNat + 16)]) := by
  intro ret hret s hs ⟨hcal, hmx, hnt⟩
  have hc' := hcal
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hdp, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [softEnv, softDepth, regG, regSP, stackguard0Offset, stackguard0, Spec.Disjoint] at hg1 hg2 hg3 hgd hal hdp hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.fmul64"]
  refine Reaches.call (Summary.withExit hc hret) rfl
    ⟨⟨RTPre64.of_caller softEnv_laws hcal (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df)
      (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide),
      by simpa [GoMXCSR] using hmx⟩, ?_⟩ ?_
  · simp [setRegF, h_a0, h_a1, hnt]
  · intro s' hpc' ⟨r, x', y, fl, m', zh, kr, mx, hs', hmx', hfr, hP⟩
    subst hs'
    simp only [rtWrites64, Contracts.MapAmd64.calleeStack, softEnv, softDepth, setRegF, reduceIte, Nat.reduceEqDiff,
      hsp40, List.nil_append] at hfr
    janus64_run
    refine ⟨?_, by simp only [softDepth]; janus_frame⟩
    simpa [setRegF_apply, h_a0, h_a1] using hP

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

An implementation of `SoftFmulContract64` at `runtime.fmul64`'s address (the hardware `MULSD` of
`Janus.Contracts.SoftFloatSatAmd64`, which meets it: `model`), an admissible return address, and a
call state of `Mul(1.0, 1.0)` with Go's `MXCSR` in a memory with the stack window, so the product is
`1.0`. -/

namespace Witness

open Janus.Contracts.SoftFloatSatAmd64

/-- `runtime.fmul64`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.fmul64"

def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := mulCode }]

def linked : Janus.Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : SoftFmulContract64 (Extracted.program.link implAt) cAddr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hpre, hmx⟩, hnt⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run [GoMXCSR.ctl hmx, GoMXCSR.unmasked hmx, GoMXCSR.mod hmx]
  have ha := (s.regs 0).isLt
  have hb := (s.regs 3).isLt
  have h := FP.binop_mul_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    (s.regs 0).toNat (s.regs 3).toNat ha hb
  obtain ⟨hlt, h⟩ := h
  refine SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
    (by simp [setXmmF_apply]) rfl hdf.symm ?_ (MemFrame.refl _ _) ?_
  · exact mxcsr_ctl _ _ s.mxcsr.isLt
  · simp only [setRegF_apply]
    simp only [Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt (show (s.regs 3).toNat < 2 ^ 128 by omega)]
    have hlt' : (FP.binop FP.BinOp.mul binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res < 2 ^ 64 := hlt
    generalize (FP.binop FP.BinOp.mul binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res = x at *
    have e0 : (s.regs 0).toNat / 18446744073709551616 = 0 := by omega
    simp only [e0, Nat.zero_mul, Nat.zero_add, show (0 : Nat) = 4 ↔ False by decide, ite_false, ite_true,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show x % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 = x by omega]
    exact h

def ret : Nat := 0x1000

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

def a1 : BitVec 64 := BitVec.ofNat 64 one

/-- The stack window and the return address `ret` at `[RSP]`; `g`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 512, 0x300 + 0x100, true⟩, ⟨wg, 0x100, false⟩]⟩

/-- The call state: `Mul(1.0, 1.0)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then a1 else if i = 3 then a1 else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [a1, a1] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre : CallerOK64 softEnv s0 40 16 ∧ GoMXCSR s0 ∧ ¬ MulTiny a1.toNat a1.toNat := by
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    ?_, ?_, ?_⟩, rfl, by decide⟩
  · simp [softEnv, outside_nil]
  · unfold Spec.Disjoint; decide
  · simp [softEnv, outside_nil]

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (ret : Nat) (s : State),
    SoftFmulContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.fmul64") ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [a1, a1] s ∧
    (CallerOK64 softEnv s 40 16 ∧ GoMXCSR s ∧ ¬ MulTiny a1.toNat a1.toNat) :=
  ⟨implAt, ret, s0, model, hret, setup, pre⟩

/-- So the guarantee is reached: `1.0 * 1.0` is the IEEE product (`1.0`). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ResultIs binary64 (mul binary64 .rne a1.toNat a1.toNat) (s'.regs 0).toNat :=
  (correctness implAt model a1 a1 ret hret s0 setup pre).mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
