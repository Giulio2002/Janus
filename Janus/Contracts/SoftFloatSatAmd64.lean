import Janus.Contracts.SoftFloatAmd64
import Janus.Contracts.SatAmd64
import Janus.Amd64.FloatLemmas
import Janus.Spec.ComplexLemmas
import Janus.Amd64.TacticSSE
import Janus.Amd64.TacticFloat

/-!
# The soft-float and `KeepAlive` contracts are satisfiable (amd64)

As `Janus.Contracts.SoftFloatSat` (arm64): for each contract of `Janus.Contracts.SoftFloatAmd64`, an
implementation that meets it, proved by running it (hardware SSE2 floating point: `MOVQ X0, RAX;
MOVQ X1, RBX; ADDSD/SUBSD/MULSD/DIVSD X0, X1; MOVQ RAX, X0; RET`, whose result under Go's `MXCSR`
is the IEEE 754 round-to-nearest-even result, `Janus.Amd64.FP.binop_add_ieee` & co.; `RET` for
`KeepAlive`), and a call state that satisfies its precondition. The witness call state has a
writable stack window of `0x500` bytes below `RSP = 0x20000` (the return address `0` at `[RSP]`), a
readable `g` at `0x50000` whose `stackguard0` is 0, and a readable zero byte at `0x60000` standing
for `runtime.cgoAlwaysFalse`.
-/

namespace Janus.Contracts.SoftFloatSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Float Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.SoftFloat Janus.Contracts.SatAmd64

/-! ## Machine code -/

/-- `MOVQ XMM0, RAX; MOVQ XMM1, RBX; <op> XMM0, XMM1; MOVQ RAX, XMM0; RET` (`op` the bytes of
`ADDSD`, `SUBSD`, `MULSD` or `DIVSD` `XMM0, XMM1`). -/
def fpCode (op : List Nat) : List Nat :=
  [0x66, 0x48, 0x0f, 0x6e, 0xc0, 0x66, 0x48, 0x0f, 0x6e, 0xcb] ++ op ++ [0x66, 0x48, 0x0f, 0x7e, 0xc0, 0xc3]

def addCode : List Nat := fpCode [0xf2, 0x0f, 0x58, 0xc1]
def subCode : List Nat := fpCode [0xf2, 0x0f, 0x5c, 0xc1]
def mulCode : List Nat := fpCode [0xf2, 0x0f, 0x59, 0xc1]
def divCode : List Nat := fpCode [0xf2, 0x0f, 0x5e, 0xc1]

/-! ## The witness call state -/

def wsp : Nat := 0x20000
def wg : Nat := 0x50000
/-- `runtime.cgoAlwaysFalse`. -/
def wcgo : Nat := 0x60000

def wmem : Janus.Arm64.Memory :=
  ⟨fun _ => 0, [⟨wsp - 0x400, 0x500, true⟩, ⟨wg, 0x100, false⟩, ⟨wcgo, 8, false⟩]⟩

/-- Arguments `a`, `b` in `RAX`, `RBX`; `g = wg` in `R14`, `RSP = wsp`, Go's `MXCSR`. -/
def wstate (a b : Nat) : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 a else if i = 3 then BitVec.ofNat 64 b
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem }

theorem wstate_rtpre (a b : Nat) : RTPre64 softEnv 2 (wstate a b) := by
  have hw : wmem.accessible (wsp - softDepth) (softDepth + 8 + 8 * 2) true = true := by decide
  have h4 : (wstate a b).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (wstate a b).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (wstate a b).mem = wmem := rfl
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, softEnv]; decide
  · simp only [h4]; decide
  · simp only [h4, softEnv]; decide
  · simp only [h4]; decide
  · simp only [h4, hm, softEnv, BitVec.toNat_ofNat]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp, softDepth]) (by simp [wsp, softDepth])
  · simp only [h4, hm]; decide
  · simp [softEnv]

theorem wstate_pre (a b : Nat) : SoftPre64 (wstate a b) := ⟨wstate_rtpre a b, rfl⟩

/-- `1.0`. -/
def one : Nat := 0x3ff0000000000000

/-! ## The four operations -/

theorem softFadd64_impl : SoftFaddContract64 (toy.link (at0 addCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hmx⟩, hnt⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run [GoMXCSR.ctl hmx, GoMXCSR.unmasked hmx, GoMXCSR.mod hmx]
  have ha := (s.regs 0).isLt
  have hb := (s.regs 3).isLt
  have h := FP.binop_add_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    (s.regs 0).toNat (s.regs 3).toNat ha hb
  obtain ⟨hlt, h⟩ := h
  refine SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
    (by simp [setXmmF_apply]) rfl hdf.symm ?_ (MemFrame.refl _ _) ?_
  · exact mxcsr_ctl _ _ s.mxcsr.isLt
  · simp only [setRegF_apply]
    simp only [Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt (show (s.regs 3).toNat < 2 ^ 128 by omega)]
    have hlt' : (FP.binop FP.BinOp.add binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res < 2 ^ 64 := hlt
    generalize (FP.binop FP.BinOp.add binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res = x at *
    have e0 : (s.regs 0).toNat / 18446744073709551616 = 0 := by omega
    simp only [e0, Nat.zero_mul, Nat.zero_add, show (0 : Nat) = 4 ↔ False by decide, ite_false, ite_true,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show x % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 = x by omega]
    exact h

/-- `SoftFaddContract64` is satisfiable: `1.0 + 1.0`. -/
theorem softFadd64_satisfiable : ∃ impl : List Janus.Amd64.Segment, SoftFaddContract64 (toy.link impl) A0 ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ SoftPre64 s ∧ ¬ AddTiny (s.regs 0).toNat (s.regs 3).toNat :=
  ⟨_, softFadd64_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFsub64_impl : SoftFsubContract64 (toy.link (at0 subCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hmx⟩, hnt⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run [GoMXCSR.ctl hmx, GoMXCSR.unmasked hmx, GoMXCSR.mod hmx]
  have ha := (s.regs 0).isLt
  have hb := (s.regs 3).isLt
  have h := FP.binop_sub_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    (s.regs 0).toNat (s.regs 3).toNat ha hb
  obtain ⟨hlt, h⟩ := h
  refine SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
    (by simp [setXmmF_apply]) rfl hdf.symm ?_ (MemFrame.refl _ _) ?_
  · exact mxcsr_ctl _ _ s.mxcsr.isLt
  · simp only [setRegF_apply]
    simp only [Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt (show (s.regs 3).toNat < 2 ^ 128 by omega)]
    have hlt' : (FP.binop FP.BinOp.sub binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res < 2 ^ 64 := hlt
    generalize (FP.binop FP.BinOp.sub binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res = x at *
    have e0 : (s.regs 0).toNat / 18446744073709551616 = 0 := by omega
    simp only [e0, Nat.zero_mul, Nat.zero_add, show (0 : Nat) = 4 ↔ False by decide, ite_false, ite_true,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show x % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 = x by omega]
    exact h

/-- `SoftFsubContract64` is satisfiable: `1.0 - 1.0`. -/
theorem softFsub64_satisfiable : ∃ impl : List Janus.Amd64.Segment, SoftFsubContract64 (toy.link impl) A0 ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ SoftPre64 s ∧ ¬ SubTiny (s.regs 0).toNat (s.regs 3).toNat :=
  ⟨_, softFsub64_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFmul64_impl : SoftFmulContract64 (toy.link (at0 mulCode)) A0 := by
  rw [link_at0]
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

/-- `SoftFmulContract64` is satisfiable: `1.0 * 1.0`. -/
theorem softFmul64_satisfiable : ∃ impl : List Janus.Amd64.Segment, SoftFmulContract64 (toy.link impl) A0 ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ SoftPre64 s ∧ ¬ MulTiny (s.regs 0).toNat (s.regs 3).toNat :=
  ⟨_, softFmul64_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

theorem softFdiv64_impl : SoftFdivContract64 (toy.link (at0 divCode)) A0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hpre, hmx⟩, hnt⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run [GoMXCSR.ctl hmx, GoMXCSR.unmasked hmx, GoMXCSR.mod hmx]
  have ha := (s.regs 0).isLt
  have hb := (s.regs 3).isLt
  have h := FP.binop_div_ieee (c := ⟨.rne, false, false⟩) ⟨rfl, rfl⟩ binary64 (Or.inr rfl)
    (s.regs 0).toNat (s.regs 3).toNat ha hb
  obtain ⟨hlt, h⟩ := h
  refine SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
    (by simp [setXmmF_apply]) rfl hdf.symm ?_ (MemFrame.refl _ _) ?_
  · exact mxcsr_ctl _ _ s.mxcsr.isLt
  · simp only [setRegF_apply]
    simp only [Nat.mod_eq_of_lt (show (s.regs 0).toNat < 2 ^ 128 by omega),
      Nat.mod_eq_of_lt (show (s.regs 3).toNat < 2 ^ 128 by omega)]
    have hlt' : (FP.binop FP.BinOp.div binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res < 2 ^ 64 := hlt
    generalize (FP.binop FP.BinOp.div binary64 ⟨.rne, false, false⟩ (s.regs 0).toNat (s.regs 3).toNat).res = x at *
    have e0 : (s.regs 0).toNat / 18446744073709551616 = 0 := by omega
    simp only [e0, Nat.zero_mul, Nat.zero_add, show (0 : Nat) = 4 ↔ False by decide, ite_false, ite_true,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show x % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 = x by omega]
    exact h

/-- `SoftFdivContract64` is satisfiable: `1.0 / 1.0`. -/
theorem softFdiv64_satisfiable : ∃ impl : List Janus.Amd64.Segment, SoftFdivContract64 (toy.link impl) A0 ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ SoftPre64 s ∧ ¬ DivTiny (s.regs 0).toNat (s.regs 3).toNat :=
  ⟨_, softFdiv64_impl, wstate one one, rfl, wstate_pre _ _, by decide⟩

/-! ## `KeepAlive` -/

theorem keepAlive64_impl : KeepAliveContract64 (toy.link (at0 [0xc3])) A0 wcgo := by
  rw [link_at0]
  intro s hpc ⟨hpre, _, _⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run
  exact SoftRet64.intro 2 s _ _ rfl (by simp [setRegF_apply]) rfl rfl rfl rfl hdf.symm rfl (MemFrame.refl _ _) trivial

/-- `KeepAliveContract64` is satisfiable. -/
theorem keepAlive64_satisfiable : ∃ impl : List Janus.Amd64.Segment, KeepAliveContract64 (toy.link impl) A0 wcgo ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ RTPre64 softEnv 2 s ∧ Misc.CgoAlwaysFalse s.mem wcgo ∧
      Spec.Disjoint wcgo 1 ((s.regs 4).toNat - softDepth) (softDepth + 8 + 8 * 2) :=
  ⟨_, keepAlive64_impl, wstate 0 0, rfl, wstate_rtpre _ _, ⟨by decide, by decide, by decide⟩, by unfold Spec.Disjoint; decide⟩

end Janus.Contracts.SoftFloatSatAmd64
