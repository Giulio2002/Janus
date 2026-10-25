import JanusASL.Proofs.LdStUImm
import JanusASL.Proofs.MemWrite

/-! # A non-trivial instance of the load/store hypotheses

`witnessState` is an explicit Sail state and `witnessJs` a Janus state with one writable 16-byte
region at `0x10_0004_0000` (the check's data buffer address): `Rel`, `MemRel` and
`LinuxEL0Config` hold for them (kernel-checked), and `ldstUImm_agree` instantiated at `LDR X0,
[X1]` and `STR X0, [X1]` (with `X1` the region's base) gives the ASL step's agreement for these
real accesses. `UserMapped` stays a hypothesis of the instances: it is a statement about the
translation tables, evaluated (not proved) by `janus-asl-check` on its base state (docs/ASL.md). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The region's base (the check's `dataBase`). -/
def wBase : Nat := 0x10_0004_0000

def wPState : ProcState :=
  { N := 0, Z := 0, C := 0, V := 0, D := 0, A := 0, I := 0, F := 0, EXLOCK := 0, PAN := 0, UAO := 0, DIT := 0,
    TCO := 0, PM := 0, PPEND := 0, BTYPE := 0, ZA := 0, SM := 0, ALLINT := 0, SS := 0, IL := 0, EL := 0, nRW := 0,
    SP := 0, Q := 0, GE := 0, SSBS := 0, IT := 0, J := 0, T := 0, E := 0, M := 0 }

def wFeat : Vector Bool 259 := Vector.ofFn fun i => !(cfgFeaturesOff.contains i.val)

def wTM : TMState := default

/-- The registers: GPRs zero except X1 = the region base, and the configuration of `LinuxEL0Config`. -/
def wRegs : Std.ExtDHashMap Register RegisterType :=
  ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((∅ : Std.ExtDHashMap Register RegisterType).insert .R0 0#64).insert .R1 (BitVec.ofNat 64 wBase)).insert .R2 0#64).insert .R3 0#64).insert .R4 0#64).insert .R5 0#64).insert .R6 0#64).insert .R7 0#64).insert .R8 0#64).insert .R9 0#64).insert .R10 0#64).insert .R11 0#64).insert .R12 0#64).insert .R13 0#64).insert .R14 0#64).insert .R15 0#64).insert .R16 0#64).insert .R17 0#64).insert .R18 0#64).insert .R19 0#64).insert .R20 0#64).insert .R21 0#64).insert .R22 0#64).insert .R23 0#64).insert .R24 0#64).insert .R25 0#64).insert .R26 0#64).insert .R27 0#64).insert .R28 0#64).insert .R29 0#64).insert .R30 0#64).insert .SP_EL0 0#64).insert ._PC 0x1000000800#64).insert .PSTATE wPState).insert .FeatureImpl wFeat).insert .SCR_EL3 0x24006030401#64).insert .SCR 0#32).insert .HCR_EL2 0x30080000000#64).insert .HCRX_EL2 0x800#64).insert .TCR_EL1 0x25b5903510#64).insert .MDCR_EL3 0x10000000#64).insert .MDCR_EL2 0#64).insert .BRBFCR_EL1 0#64).insert .BRBCR_EL1 0#64).insert .BRBCR_EL2 0#64).insert .PMSIDR_EL1 0x103604f#64).insert .PMSCR_EL1 0#64).insert .PMSCR_EL2 0#64).insert .PMBLIMITR_EL1 0#64).insert .PMBSR_EL1 0#64).insert .GCSCRE0_EL1 0#64).insert .SPESampleInFlight false).insert .InGuardedPage false).insert .SCTLR_EL1 0x2000422fcf4f91d#64).insert ._MPAM3_EL3 0x4000000000000000#64).insert .MPAM2_EL2 0#64).insert .TSTATE wTM)

/-- Memory: the 16 region bytes, all zero. -/
def wMem : Std.ExtHashMap Nat (BitVec 8) :=
  memIns ∅ (List.ofFn fun i : Fin 16 => (wBase + i.val, (fun _ => 0#8) i.val))

def witnessState : SState :=
  { regs := wRegs, choiceState := (), mem := wMem, tags := (), cycleCount := 0, sailOutput := #[] }

def witnessJs : Janus.Arm64.State :=
  { regs := fun i => if i = 1 then BitVec.ofNat 64 wBase else 0, sp := 0, pc := 0x1000000800,
    flags := ⟨false, false, false, false⟩,
    mem := { bytes := fun _ => 0, regions := [{ base := wBase, size := 16, writable := true }] } }

theorem witness_rel : Rel witnessJs witnessState where
  gpr i hi := by
    match i, hi with
    | 0, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 1, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 2, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 3, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 4, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 5, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 6, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 7, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 8, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 9, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 10, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 11, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 12, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 13, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 14, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 15, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 16, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 17, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 18, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 19, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 20, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 21, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 22, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 23, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 24, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 25, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 26, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 27, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 28, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 29, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | 30, _ => simp [gprVal, witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
    | _ + 31, h => exact absurd h (by omega)
  sp := by simp [witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
  pc := by simp [witnessState, wRegs, witnessJs, Std.ExtDHashMap.get?_insert]
  pstate := ⟨wPState, by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert],
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem witness_memRel : MemRel witnessJs.mem witnessState := by
  intro a ha
  obtain ⟨r, hr, h1, h2, _, _⟩ := ha
  simp [witnessJs] at hr
  subst hr
  have := memIns_get (∅ : Std.ExtHashMap Nat (BitVec 8)) wBase 16 (fun _ => 0#8) a
  rw [if_pos (by simp at h1 h2; omega)] at this
  exact this

set_option maxRecDepth 100000 in
theorem witness_cfg : LinuxEL0Config witnessState where
  fi := ⟨wFeat, by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert], fun f => by
    obtain ⟨h0, hlt⟩ := num_of_Feature_range f
    show wFeat[(num_of_Feature f).toNat]! = cfgFeat f
    simp [wFeat, cfgFeat, hlt]⟩
  scr3 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  scr := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  hcr2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  hcrx2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  tcr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  mdcr3 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  mdcr2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  brbfcr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  brbcr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  brbcr2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  pmsidr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  pmscr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  pmscr2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  pmblimitr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  pmbsr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  gcscre0 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  speInFlight := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  inGuarded := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  sctlr1 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  mpam3 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  mpam2 := by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert]
  tstate := ⟨wTM, by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert], rfl⟩
  pstate := ⟨wPState, by simp [witnessState, wRegs, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩

/-- **The hypotheses hold together, with a non-empty writable region**: `Rel`, `MemRel` and
`LinuxEL0Config` (kernel-checked). -/
theorem witness_hyps : Rel witnessJs witnessState ∧ MemRel witnessJs.mem witnessState ∧
    LinuxEL0Config witnessState ∧ witnessJs.mem.regions ≠ [] :=
  ⟨witness_rel, witness_memRel, witness_cfg, by simp [witnessJs]⟩

theorem witness_ldr_step : ∃ js', Janus.Arm64.step 0xF9400020 witnessJs = .ok js' := ⟨_, rfl⟩
theorem witness_str_step : ∃ js', Janus.Arm64.step 0xF9000020 witnessJs = .ok js' := ⟨_, rfl⟩

/-- **`LDR X0, [X1]` on the witness**: Janus steps it, and (given `UserMapped`) the ASL step agrees. -/
theorem witness_ldr_asl (hU : UserMapped witnessJs.mem witnessState) :
    ∃ js' s', Janus.Arm64.step 0xF9400020 witnessJs = .ok js' ∧
      (janus_step (BitVec.ofNat 32 0xF9400020)).run witnessState = .ok .Janus_OK s' ∧ Rel js' s' ∧
      MemRel js'.mem s' ∧ LinuxEL0Config s' := by
  obtain ⟨js', hj⟩ := witness_ldr_step
  obtain ⟨s', h1, h2, h3, h4⟩ := ldstUImm_agree (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    witness_rel witness_memRel witness_cfg hU hj
  exact ⟨js', s', hj, h1, h2, h3, h4⟩

/-- **`STR X0, [X1]` on the witness**: Janus steps it, and (given `UserMapped`) the ASL step agrees. -/
theorem witness_str_asl (hU : UserMapped witnessJs.mem witnessState) :
    ∃ js' s', Janus.Arm64.step 0xF9000020 witnessJs = .ok js' ∧
      (janus_step (BitVec.ofNat 32 0xF9000020)).run witnessState = .ok .Janus_OK s' ∧ Rel js' s' ∧
      MemRel js'.mem s' ∧ LinuxEL0Config s' := by
  obtain ⟨js', hj⟩ := witness_str_step
  obtain ⟨s', h1, h2, h3, h4⟩ := ldstUImm_agree (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    witness_rel witness_memRel witness_cfg hU hj
  exact ⟨js', s', hj, h1, h2, h3, h4⟩

end JanusASL.Proofs
