import Janus.Contracts.SoftFloat
import Janus.Contracts.Sat
import Janus.Arm64.FloatLemmas
import Janus.Spec.ComplexLemmas
import Janus.Tactic.Vector
import Janus.Tactic.Float

/-!
# The soft-float and `KeepAlive` contracts are satisfiable (arm64)

For each contract of `Janus.Contracts.SoftFloat`: an implementation (A64 machine code at `A0` of a
program with no other code) that meets it, proved by running it, and a call state that satisfies
its precondition. The soft-float witnesses are hardware floating point: `FMOV D0, X0; FMOV D1, X1;
FADD/FSUB/FMUL/FDIV D0, D0, D1; FMOV X0, D0; RET`, whose result under `FPCR = 0` is the IEEE 754
round-to-nearest-even result (`Janus.Arm64.FP.fpAdd_ieee` & co.), so the contracts do not ask for
more than code can do, and (with the preconditions that exclude tiny results) not more than the
runtime's own algorithm delivers; the `KeepAlive` witness is `RET`.

The witness call state has a writable stack window of `0x500` bytes below `SP = 0x20000` and
above, a readable `g` at `0x50000` whose `stackguard0` is 0, and a readable zero byte at
`0x60000` standing for `runtime.cgoAlwaysFalse`.
-/

namespace Janus.Contracts.SoftFloatSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.SoftFloat Janus.Contracts.Sat

/-! ## Machine code -/

/-- `FMOV D0, X0; FMOV D1, X1; F<op> D0, D0, D1; FMOV X0, D0; RET` (`op` is the `FADD`, `FSUB`,
`FMUL` or `FDIV` word). -/
def fpCode (op : Nat) : List Nat := [0x9e670000, 0x9e670021, op, 0x9e660000, retW]

def addCode : List Nat := fpCode 0x1e612800
def subCode : List Nat := fpCode 0x1e613800
def mulCode : List Nat := fpCode 0x1e610800
def divCode : List Nat := fpCode 0x1e611800

/-! ## The witness call state -/

def wsp : Nat := 0x20000
def wg : Nat := 0x50000
def wret : Nat := 0x200000
/-- `runtime.cgoAlwaysFalse`. -/
def wcgo : Nat := 0x60000

def wmem : Memory :=
  ⟨fun _ => 0, [⟨wsp - 0x400, 0x500, true⟩, ⟨wg, 0x100, false⟩, ⟨wcgo, 8, false⟩]⟩

/-- Arguments `a`, `b` in `X0`, `X1`; `g = wg`, return address `wret`, `SP = wsp`, `FPCR = 0`. -/
def wstate (a b : Nat) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 a else if i = 1 then BitVec.ofNat 64 b
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem wstate_rtpre (a b : Nat) : RTPre softEnv 2 (wstate a b) := by
  have hw : wmem.accessible (wsp - softDepth) (softDepth + 8 + 8 * 2) true = true := by decide
  have h28 : (wstate a b).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (wstate a b).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (wstate a b).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate a b).mem = wmem := rfl
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, softEnv]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, softEnv]; decide
  · simp only [hsp]; decide
  · simp only [hsp, hm, softEnv, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ hw (by simp [wsp, softDepth]) (by simp [wsp, softDepth])
  · simp [softEnv]

theorem wstate_pre (a b : Nat) : SoftPre (wstate a b) := ⟨wstate_rtpre a b, rfl⟩

/-- `1.0` and `1.0`. -/
def one : Nat := 0x3ff0000000000000

/-! ## The four operations -/

theorem softFadd_impl : SoftFaddContract (toy.link (at0 addCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hfp⟩, hnt⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine SoftRet.intro 2 s _ _ rfl rfl rfl rfl rfl rfl rfl hfp.symm (MemFrame.refl _ _) ?_
  have ha := (s.regs 0).isLt
  have hb := (s.regs 1).isLt
  have h := FP.fpAdd_ieee FP.IEEEMode.zero binary64 (Or.inr rfl) (s.regs 0).toNat (s.regs 1).toNat ha hb
  have hr : FP.roundingMode 0 = .rne := rfl
  rw [hr] at h
  obtain ⟨hlt, h⟩ := h
  simp only [setReg_apply, Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show (s.regs 1).toNat < 2 ^ 128 by omega)]
  have hlt' : (FP.fpAdd binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst < 2 ^ 64 := hlt
  generalize (FP.fpAdd binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst = x at *
  simp only [ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega)]
  exact h

/-- `SoftFaddContract` is satisfiable: `1.0 + 1.0`. -/
theorem softFadd_satisfiable : ∃ impl : List Segment, SoftFaddContract (toy.link impl) A0 ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ SoftPre s ∧ ¬ AddTiny (s.regs 0).toNat (s.regs 1).toNat :=
  ⟨_, softFadd_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFsub_impl : SoftFsubContract (toy.link (at0 subCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hfp⟩, hnt⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine SoftRet.intro 2 s _ _ rfl rfl rfl rfl rfl rfl rfl hfp.symm (MemFrame.refl _ _) ?_
  have ha := (s.regs 0).isLt
  have hb := (s.regs 1).isLt
  have h := FP.fpSub_ieee FP.IEEEMode.zero binary64 (Or.inr rfl) (s.regs 0).toNat (s.regs 1).toNat ha hb
  have hr : FP.roundingMode 0 = .rne := rfl
  rw [hr] at h
  obtain ⟨hlt, h⟩ := h
  simp only [setReg_apply, Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show (s.regs 1).toNat < 2 ^ 128 by omega)]
  have hlt' : (FP.fpSub binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst < 2 ^ 64 := hlt
  generalize (FP.fpSub binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst = x at *
  simp only [ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega)]
  exact h

/-- `SoftFsubContract` is satisfiable: `1.0 - 1.0`. -/
theorem softFsub_satisfiable : ∃ impl : List Segment, SoftFsubContract (toy.link impl) A0 ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ SoftPre s ∧ ¬ SubTiny (s.regs 0).toNat (s.regs 1).toNat :=
  ⟨_, softFsub_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFmul_impl : SoftFmulContract (toy.link (at0 mulCode)) A0 := by
  rw [link_at0]
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

/-- `SoftFmulContract` is satisfiable: `1.0 * 1.0`. -/
theorem softFmul_satisfiable : ∃ impl : List Segment, SoftFmulContract (toy.link impl) A0 ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ SoftPre s ∧ ¬ MulTiny (s.regs 0).toNat (s.regs 1).toNat :=
  ⟨_, softFmul_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFdiv_impl : SoftFdivContract (toy.link (at0 divCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hfp⟩, hnt⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  refine SoftRet.intro 2 s _ _ rfl rfl rfl rfl rfl rfl rfl hfp.symm (MemFrame.refl _ _) ?_
  have ha := (s.regs 0).isLt
  have hb := (s.regs 1).isLt
  have h := FP.fpDiv_ieee FP.IEEEMode.zero binary64 (Or.inr rfl) (s.regs 0).toNat (s.regs 1).toNat ha hb
  have hr : FP.roundingMode 0 = .rne := rfl
  rw [hr] at h
  obtain ⟨hlt, h⟩ := h
  simp only [setReg_apply, Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
    Nat.mod_eq_of_lt (show (s.regs 1).toNat < 2 ^ 128 by omega)]
  have hlt' : (FP.fpDiv binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst < 2 ^ 64 := hlt
  generalize (FP.fpDiv binary64 0 (s.regs 0).toNat (s.regs 1).toNat).fst = x at *
  simp only [ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega)]
  exact h

/-- `SoftFdivContract` is satisfiable: `1.0 / 1.0`. -/
theorem softFdiv_satisfiable : ∃ impl : List Segment, SoftFdivContract (toy.link impl) A0 ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ SoftPre s ∧ ¬ DivTiny (s.regs 0).toNat (s.regs 1).toNat :=
  ⟨_, softFdiv_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

/-! ## `KeepAlive` -/

theorem keepAlive_impl : KeepAliveContract (toy.link (at0 [retW])) A0 wcgo := by
  rw [link_at0]
  intro s hpc ⟨hpre, _, _⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  exact SoftRet.intro 2 s _ _ rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) trivial

/-- `KeepAliveContract` is satisfiable. -/
theorem keepAlive_satisfiable : ∃ impl : List Segment, KeepAliveContract (toy.link impl) A0 wcgo ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre softEnv 2 s ∧ Misc.CgoAlwaysFalse s.mem wcgo ∧
      Spec.Disjoint wcgo 1 (s.sp.toNat - softDepth) (softDepth + 8 + 8 * 2) :=
  ⟨_, keepAlive_impl, wstate 0 0, rfl, wstate_rtpre _ _, ⟨by decide, by decide, by decide⟩, by unfold Spec.Disjoint; decide⟩

end Janus.Contracts.SoftFloatSat
