import Janus.Contracts.InstrumentCallsAmd64
import Janus.Contracts.InstrumentSat
import Janus.Contracts.IfaceSatAmd64

/-!
# The `-d=checkptr` contracts are satisfiable (amd64)

As `Janus.Contracts.InstrumentSat`: the model `C0`, the code `RET` (`c3`), and the call state
`IfaceSatAmd64.wstate`.
-/

namespace Janus.Contracts.InstrumentSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64
  Janus.Contracts.InstrumentSat

/-- `ret`. -/
def retCode : List Nat := [0xc3]

theorem ret_rtReturn (n : Nat) (s : State) (hpc : s.rip = BitVec.ofNat 64 A0) (hpre : RTPre64 C0.toRtEnv n s) :
    ReachesRet (withCode retCode) (retAddrOf s) s fun s' => RTReturn64 C0.toRtEnv n s s' fun _ _ => True := by
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx, hdf, hra, hout⟩ := hpre
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hal hd1 hd2 hst hra
  janus64_run
  exact RTReturn64.intro C0.toRtEnv n s _ _ rfl rfl rfl rfl rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _)
    ⟨he1, he2, hd⟩ trivial

theorem checkptrAlignment64_impl : CheckptrAlignment64 (toy.link (at0 retCode)) A0 C0 := by
  rw [link_at0]; intro s hpc ⟨hpre, _⟩; exact ret_rtReturn 3 s hpc hpre

theorem checkptrArithmetic64_impl : CheckptrArithmetic64 (toy.link (at0 retCode)) A0 C0 := by
  rw [link_at0]; intro s hpc ⟨hpre, _⟩; exact ret_rtReturn 4 s hpc hpre

theorem wstate_rtpre64 (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : RTPre64 C0.toRtEnv n (wstate r) := by
  have hw : wmem.accessible (wsp - 64) (64 + 8 + 8 * 4) true = true := by decide
  have h4 : (wstate r).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (wstate r).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (wstate r).mem = wmem := rfl
  refine ⟨wmem_env ((wstate r).regs 14), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, C0_depth]; decide
  · simp only [h4]; decide
  · simp only [h4, C0_depth]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, C0_depth, BitVec.toNat_ofNat]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [h4, hm]; decide
  · simp only [h4, C0_depth, C0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- `CheckptrAlignment64` is satisfiable: `(*T)(nil)` passes. -/
theorem checkptrAlignment64_satisfiable : ∃ (C : CheckptrModel) (impl : List Janus.Amd64.Segment), C.Laws ∧
    CheckptrAlignment64 (toy.link impl) A0 C ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      RTPre64 C.toRtEnv 3 s ∧ AlignOK C s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat :=
  ⟨C0, _, C0_laws, checkptrAlignment64_impl, wstate fun _ => 0, rfl, wstate_rtpre64 _ 3 (by decide),
    Or.inl (by simp [wstate])⟩

/-- `CheckptrArithmetic64` is satisfiable: a nil result passes. -/
theorem checkptrArithmetic64_satisfiable : ∃ (C : CheckptrModel) (impl : List Janus.Amd64.Segment), C.Laws ∧
    CheckptrArithmetic64 (toy.link impl) A0 C ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      RTPre64 C.toRtEnv 4 s ∧ ArithOK C s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat :=
  ⟨C0, _, C0_laws, checkptrArithmetic64_impl, wstate fun _ => 0, rfl, wstate_rtpre64 _ 4 (by decide),
    by simp [minLegalPointer, wstate], Or.inl rfl⟩

end Janus.Contracts.InstrumentSatAmd64
