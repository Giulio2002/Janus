import Janus.Contracts.InstrumentCalls
import Janus.Contracts.IfaceSat

/-!
# The `-d=checkptr` contracts are satisfiable (arm64)

For `CheckptrAlignment` and `CheckptrArithmetic`: a model `C0` whose laws hold (`C0_laws`: the
environment of `Janus.Contracts.IfaceModel`, and `checkptrBase` constantly `0`, i.e. no address
is in a Go object), machine code that meets the contract for it (`RET`: the checks pass and
change nothing), proved by symbolic execution, and a call state that satisfies the contract's
precondition (`IfaceSat.wstate`).
-/

namespace Janus.Contracts.InstrumentCallsSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Instrument Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- The model: `IfaceModel.R0`'s environment and memory, no Go objects. -/
def C0 : CheckptrModel :=
  { Env := Env0, priv := [(0x10000, 0x11000)], depth := 64, base := fun _ _ _ => 0 }

@[simp] theorem C0_priv : C0.priv = [(0x10000, 0x11000)] := rfl
@[simp] theorem C0_depth : C0.depth = 64 := rfl

theorem C0_laws : C0.Laws :=
  ⟨⟨fun m m' g h ha => R0_laws.env_frame m m' g h ha⟩, fun _ _ _ _ => rfl⟩

/-- `ret`. -/
def retCode : List Nat := [0xd65f03c0]

theorem ret_rtReturn (n : Nat) (s : State) (hpc : s.pc = BitVec.ofNat 64 A0) (hpre : RTPre C0.toRtEnv n s) :
    ReachesRet (withCode retCode) (s.regs GoABI.regLR) s fun s' => RTReturn C0.toRtEnv n s s' fun _ _ => True := by
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hpre
  janus_run
  exact RTReturn.intro C0.toRtEnv n s _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _)
    ⟨he1, he2, hd⟩ trivial

theorem checkptrAlignment_impl : CheckptrAlignment (toy.link (at0 retCode)) A0 C0 := by
  rw [link_at0]; intro s hpc ⟨hpre, _⟩; exact ret_rtReturn 3 s hpc hpre

theorem checkptrArithmetic_impl : CheckptrArithmetic (toy.link (at0 retCode)) A0 C0 := by
  rw [link_at0]; intro s hpc ⟨hpre, _⟩; exact ret_rtReturn 4 s hpc hpre

theorem wstate_rtpre' (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : RTPre C0.toRtEnv n (wstate r) := by
  have hw : wmem.accessible (wsp - 64) (64 + 8 + 8 * 4) true = true := by decide
  have h28 : (wstate r).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (wstate r).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (wstate r).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate r).mem = wmem := rfl
  refine ⟨wmem_env ((wstate r).regs 28), ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, C0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, C0_depth]; decide
  · simp only [hsp]; simp [wsp]; omega
  · simp only [hsp, hm, C0_depth, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [hsp, C0_depth, C0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- `CheckptrAlignment` is satisfiable: `(*T)(nil)` passes. -/
theorem checkptrAlignment_satisfiable : ∃ (C : CheckptrModel) (impl : List Segment), C.Laws ∧
    CheckptrAlignment (toy.link impl) A0 C ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      RTPre C.toRtEnv 3 s ∧ AlignOK C s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat :=
  ⟨C0, _, C0_laws, checkptrAlignment_impl, wstate fun _ => 0, rfl, wstate_rtpre' _ 3 (by decide),
    Or.inl rfl⟩

/-- `CheckptrArithmetic` is satisfiable: a nil result passes (`checkptrBase(nil) = 0`). -/
theorem checkptrArithmetic_satisfiable : ∃ (C : CheckptrModel) (impl : List Segment), C.Laws ∧
    CheckptrArithmetic (toy.link impl) A0 C ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      RTPre C.toRtEnv 4 s ∧ ArithOK C s.mem (s.regs 28) (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat :=
  ⟨C0, _, C0_laws, checkptrArithmetic_impl, wstate fun _ => 0, rfl, wstate_rtpre' _ 4 (by decide),
    by simp [ArithOK, minLegalPointer, wstate], Or.inl rfl⟩

end Janus.Contracts.InstrumentCallsSat
