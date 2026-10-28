import JanusASL.Proofs
import JanusASL.Verify
import Lean

/-! # Red-team round ASL (docs/AUDIT-ASL.md): what `Rel`, `LinuxEL0Config` and the example
transfers mean

Checked by `audit/rt-asl/run.sh` (`lake env lean` in JanusASL/, then an axiom audit).

* A1 `Rel` is a function from Sail states to the Janus state's X0-X30, SP, PC and NZCV
  (`Rel.unique`): no Sail state relates two Janus states that differ in one of them
  (`Rel.no_two_regs`, `Rel.no_two_flags`, ...). It says nothing about memory, V registers,
  TPIDR_EL0, DCZID or `regs i` for `i ≥ 31` (`Rel.ignores_mem`).
* A2 `Rel` and `LinuxEL0Config` are jointly satisfiable for EVERY Janus state (`wit`,
  `wit_rel`, `wit_cfg`): the hypotheses of every `*_agree`, `run_agree` and `correctness_asl`
  are never contradictory.
* A3 The example transfer, restated purely about the ASL (no Janus state in the statement):
  from every Sail state with `LinuxEL0Config` that holds the Go call of `Add` (X0 = x, X1 = y,
  X30 = ret, PC = entry, all GPRs and SP present, EL0t), the ASL run returns to `ret` with
  X0 = x + y (`Add_pure_asl`). -/

namespace JanusASL.RedTeam
open ArmASL ArmASL.Functions JanusASL.Proofs Janus Janus.Arm64 Janus.GoABI

/-! ## A1: `Rel` is functional on X0-X30, SP, PC, NZCV -/

theorem Rel.unique {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (h' : Rel js' s) :
    (∀ i < 31, js.regs i = js'.regs i) ∧ js.sp = js'.sp ∧ js.pc = js'.pc ∧ js.flags = js'.flags := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
  · have a := h.gpr i hi; rw [h'.gpr i hi] at a; exact (Option.some.inj a).symm
  · have a := h.sp; rw [h'.sp] at a; exact (Option.some.inj a).symm
  · have a := h.pc; rw [h'.pc] at a; exact (Option.some.inj a).symm
  · obtain ⟨p, hp, hps⟩ := h.pstate
    obtain ⟨p', hp', hps'⟩ := h'.pstate
    rw [hp] at hp'; cases hp'
    have bv : ∀ a b : Bool, BitVec.ofBool a = BitVec.ofBool b → a = b := by decide
    cases hf : js.flags; cases hf' : js'.flags
    rw [hf] at hps; rw [hf'] at hps'
    simp only [Flags.mk.injEq]
    exact ⟨bv _ _ (hps.n.symm.trans hps'.n), bv _ _ (hps.z.symm.trans hps'.z),
      bv _ _ (hps.c.symm.trans hps'.c), bv _ _ (hps.v.symm.trans hps'.v)⟩

/-- No Sail state relates two Janus states that differ in a general-purpose register. -/
theorem Rel.no_two_regs {js js' : Janus.Arm64.State} {i : Nat} (hi : i < 31) (hd : js.regs i ≠ js'.regs i)
    (s : SState) : ¬ (Rel js s ∧ Rel js' s) := fun ⟨h, h'⟩ => hd ((Rel.unique h h').1 i hi)

theorem Rel.no_two_sp {js js' : Janus.Arm64.State} (hd : js.sp ≠ js'.sp) (s : SState) :
    ¬ (Rel js s ∧ Rel js' s) := fun ⟨h, h'⟩ => hd (Rel.unique h h').2.1

theorem Rel.no_two_pc {js js' : Janus.Arm64.State} (hd : js.pc ≠ js'.pc) (s : SState) :
    ¬ (Rel js s ∧ Rel js' s) := fun ⟨h, h'⟩ => hd (Rel.unique h h').2.2.1

theorem Rel.no_two_flags {js js' : Janus.Arm64.State} (hd : js.flags ≠ js'.flags) (s : SState) :
    ¬ (Rel js s ∧ Rel js' s) := fun ⟨h, h'⟩ => hd (Rel.unique h h').2.2.2

/-- What `Rel` does not see: any Janus memory (and V registers, TPIDR, DCZID) relates to the
same Sail state. A postcondition about those is NOT transferred by `Ensures.toASL` (finding A4). -/
theorem Rel.ignores_mem {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (m : Memory)
    (vr : Nat → BitVec 128) (tp : BitVec 64) (dz : BitVec 5) :
    Rel { js with mem := m, vregs := vr, tpidr := tp, dczid := dz } s :=
  ⟨h.gpr, h.sp, h.pc, h.pstate⟩

/-! ## A2: a witness of `Rel js s ∧ LinuxEL0Config s` for every `js` -/

/-- The feature vector of `LinuxEL0Config`. -/
def witFeatures : Vector Bool 259 := Vector.ofFn fun i => !(cfgFeaturesOff.contains i.val)

/-- `janus_init`'s PSTATE at EL0t, with Janus' flags. -/
def witPState (f : Flags) : ProcState :=
  let p : ProcState := default
  { p with EL := (0 : BitVec 2), nRW := (0 : BitVec 1), SP := (0 : BitVec 1),
           N := BitVec.ofBool f.n, Z := BitVec.ofBool f.z, C := BitVec.ofBool f.c, V := BitVec.ofBool f.v }

/-- The configuration registers at `janus_init`'s values (the values `LinuxEL0Config` pins). -/
def witCfg (s : SState) : SState :=
  ((((((((((((((((((((((s.set .FeatureImpl witFeatures).set .SCR_EL3 0x24006030401#64).set .SCR 0#32).set
    .HCR_EL2 0x30080000000#64).set .HCRX_EL2 0x800#64).set .TCR_EL1 0x25b5903510#64).set .MDCR_EL3 0x10000000#64).set
    .MDCR_EL2 0#64).set .BRBFCR_EL1 0#64).set .BRBCR_EL1 0#64).set .BRBCR_EL2 0#64).set .PMSIDR_EL1 0x103604f#64).set
    .PMSCR_EL1 0#64).set .PMSCR_EL2 0#64).set .PMBLIMITR_EL1 0#64).set .PMBSR_EL1 0#64).set .GCSCRE0_EL1 0#64).set
    .SPESampleInFlight false).set .InGuardedPage false).set .SCTLR_EL1 0x2000422fcf4f91d#64).set
    ._MPAM3_EL3 0x4000000000000000#64).set .MPAM2_EL2 0#64).set .TSTATE { (default : TMState) with depth := 0 }

/-- X0..X(n-1) set from `r`. -/
def witGprs (r : Nat → BitVec 64) : Nat → SState → SState
  | 0, s => s
  | n + 1, s => setGpr (witGprs r n s) (r n) n

/-- The witness: the empty Sail state with the configuration, Janus' GPRs, SP, PC and PSTATE. -/
def wit (js : Janus.Arm64.State) : SState :=
  ((witGprs js.regs 31 (witCfg default)).set .SP_EL0 js.sp |>.set ._PC js.pc).set .PSTATE (witPState js.flags)

theorem witGprs_other (r : Nat → BitVec 64) : ∀ (n : Nat), n ≤ 31 → ∀ (s : SState) (x : Register),
    isGprReg x = false → (witGprs r n s).regs.get? x = s.regs.get? x
  | 0, _, _, _, _ => rfl
  | n + 1, hn, s, x, hx => by
    simp only [witGprs]
    rw [get?_setGpr _ _ (by omega) x hx]
    exact witGprs_other r n (by omega) s x hx

theorem witGprs_gpr (r : Nat → BitVec 64) : ∀ (n : Nat), n ≤ 31 → ∀ (s : SState) (i : Nat), i < n →
    gprVal (witGprs r n s) i = some (r i)
  | 0, _, _, _, hi => absurd hi (by omega)
  | n + 1, hn, s, i, hi => by
    simp only [witGprs]
    rw [gprVal_setGpr _ _ (by omega) (by omega)]
    by_cases e : i = n
    · subst e; simp
    · rw [if_neg e]; exact witGprs_gpr r n (by omega) s i (by omega)

theorem wit_rel (js : Janus.Arm64.State) : Rel js (wit js) where
  gpr i hi := by
    simp only [wit]
    rw [gprVal_set _ _ _ rfl hi, gprVal_set _ _ _ rfl hi, gprVal_set _ _ _ rfl hi]
    exact witGprs_gpr js.regs 31 (Nat.le_refl _) _ i hi
  sp := by
    simp only [wit]
    rw [get?_set_ne _ _ (by decide), get?_set_ne _ _ (by decide)]; simp
  pc := by
    simp only [wit]
    rw [get?_set_ne _ _ (by decide)]; simp
  pstate := ⟨witPState js.flags, by simp [wit], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

set_option maxRecDepth 100000 in
theorem witFeatures_spec (f : Feature) : witFeatures[num_of_Feature f]! = cfgFeat f := by
  cases f <;> rfl

theorem wit_get (js : Janus.Arm64.State) (r : Register) (hg : isGprReg r = false) (h1 : r ≠ .SP_EL0)
    (h2 : r ≠ ._PC) (h3 : r ≠ .PSTATE) : (wit js).regs.get? r = (witCfg default).regs.get? r := by
  simp only [wit]
  rw [get?_set_ne _ _ (Ne.symm h3), get?_set_ne _ _ (Ne.symm h2), get?_set_ne _ _ (Ne.symm h1)]
  exact witGprs_other js.regs 31 (Nat.le_refl _) _ r hg

theorem cfg_get {js : Janus.Arm64.State} {r : Register} (hg : isGprReg r = false) (h1 : r ≠ .SP_EL0)
    (h2 : r ≠ ._PC) (h3 : r ≠ .PSTATE) {v : RegisterType r} (hv : (witCfg default).regs.get? r = some v) :
    (wit js).regs.get? r = some v := by rw [wit_get js r hg h1 h2 h3]; exact hv

theorem wit_cfg (js : Janus.Arm64.State) : LinuxEL0Config (wit js) where
  fi := ⟨witFeatures, cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self]), witFeatures_spec⟩
  scr3 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  scr := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  hcr2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  hcrx2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  tcr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  mdcr3 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  mdcr2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  brbfcr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  brbcr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  brbcr2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  pmsidr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  pmscr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  pmscr2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  pmblimitr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  pmbsr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  gcscre0 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  speInFlight := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  inGuarded := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  sctlr1 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  mpam3 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  mpam2 := cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self])
  tstate := ⟨{ (default : TMState) with depth := 0 }, cfg_get rfl (by decide) (by decide) (by decide) (by simp +decide only [witCfg, get?_set_ne, get?_set_self]), rfl⟩
  pstate := ⟨witPState js.flags, by simp [wit], rfl, rfl, rfl⟩

/-- **A2.** The hypotheses `Rel js s ∧ LinuxEL0Config s` are satisfiable for every Janus state. -/
theorem rel_cfg_satisfiable (js : Janus.Arm64.State) : ∃ s, Rel js s ∧ LinuxEL0Config s :=
  ⟨wit js, wit_rel js, wit_cfg js⟩

/-! ## A3: the `Add` transfer as a statement about the ASL alone

The shipped `Add` program (the words `janus extract` copies for `example.com/basic.Add`), its
shipped Janus proof, and its ASL transfer the way `janus verify --asl` derives it (`Ensures.toASL`
with the facts of `JanusASL.Verify.covered_*` from a kernel-evaluated `covered`). The four
hand-copied example programs are no longer in `JanusASL.Proofs.Examples`; this audit keeps its own
copy of `Add`, since its point is the statement's meaning, not the binary. -/

namespace AddProg
open Janus.Tactic

def program : Program :=
  { segments := [{ name := "example.com/basic.Add", base := 0x930c0, words := [0x8b010000, 0xd65f03c0] }],
    stubs := [], exitAddr := 0 }
def entry : Nat := 0x930c0

theorem correctness (x y : BitVec 64) :
    Ensures program entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

theorem covered : JanusASL.Classify.covered program = true := by decide +kernel

theorem correctness_asl (x y : BitVec 64) {ret : Nat} (hret : RetAddr program ret) {js : State}
    (hs : CallSetup (program.withExit ret) entry [x, y] js) {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (program.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ (js'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  Ensures.toASL (correctness x y) (JanusASL.Verify.covered_words _ covered) (JanusASL.Verify.covered_code _ covered)
    (JanusASL.Verify.covered_stubs _ covered) hret hs trivial h hc

end AddProg

/-- The Janus state a Sail state holds (X0-X30, SP_EL0, PC, NZCV; empty memory). -/
def ofSail (s : SState) : Janus.Arm64.State where
  regs i := (gprVal s i).getD 0
  sp := (s.regs.get? .SP_EL0).getD 0
  pc := (s.regs.get? ._PC).getD 0
  flags := match s.regs.get? .PSTATE with
    | some p => ⟨p.N == 1#1, p.Z == 1#1, p.C == 1#1, p.V == 1#1⟩
    | none => ⟨false, false, false, false⟩
  mem := default

theorem bit_ofBool (b : BitVec 1) : b = BitVec.ofBool (b == 1#1) := by revert b; decide

theorem ofSail_rel {s : SState} (hg : ∀ i < 31, ∃ v, gprVal s i = some v) {sp pc : BitVec 64}
    (hsp : s.regs.get? .SP_EL0 = some sp) (hpc : s.regs.get? ._PC = some pc)
    {p : ProcState} (hp : s.regs.get? .PSTATE = some p) (he : p.EL = 0#2) (hn : p.nRW = 0#1) (hs : p.SP = 0#1) (hsm : p.SM = 0#1) :
    Rel (ofSail s) s where
  gpr i hi := by obtain ⟨v, hv⟩ := hg i hi; simp [ofSail, hv]
  sp := by simp [ofSail, hsp]
  pc := by simp [ofSail, hpc]
  pstate := ⟨p, hp, by
    simp only [ofSail, hp]
    exact ⟨hs, he, hn, bit_ofBool _, bit_ofBool _, bit_ofBool _, bit_ofBool _, hsm⟩⟩

/-- **A3.** `Add` under the ASL with no Janus state in the statement: from every Sail state in
`LinuxEL0Config` holding a Go call of `Add` (X0 = x, X1 = y, X30 = ret, PC = entry; every GPR,
SP_EL0 present), the ASL run returns to `ret` with `x + y` in X0. -/
theorem Add_pure_asl (x y : BitVec 64) {ret : Nat} (hret : RetAddr AddProg.program ret)
    (s : SState) (hc : LinuxEL0Config s) (hg : ∀ i < 31, ∃ v, gprVal s i = some v) {sp : BitVec 64}
    (hsp : s.regs.get? .SP_EL0 = some sp) (h0 : gprVal s 0 = some x) (h1 : gprVal s 1 = some y)
    (h30 : gprVal s 30 = some (BitVec.ofNat 64 ret))
    (hpc : s.regs.get? ._PC = some (BitVec.ofNat 64 AddProg.entry))
    (hsm : ∀ p : ProcState, s.regs.get? .PSTATE = some p → p.SM = 0#1) :
    ∃ fuel s', aslRun (AddProg.program.withExit ret) fuel s = .returned s' ∧
      ∃ r, gprVal s' 0 = some r ∧ r.toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  obtain ⟨p, hp, he, hn, hs⟩ := hc.pstate
  have hr := ofSail_rel hg hsp hpc hp he hn hs (hsm p hp)
  have hcs : CallSetup (AddProg.program.withExit ret) AddProg.entry [x, y] (ofSail s) :=
    { pc := by simp [ofSail, hpc]
      lr := by simp [ofSail, regLR, h30, Program.withExit]
      args := by
        intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        match i, hi with
        | 0, _ => simp [ofSail, h0]
        | 1, _ => simp [ofSail, h1] }
  obtain ⟨fuel, s', js', hrun, hrel, _, _, hx⟩ :=
    AddProg.correctness_asl x y hret hcs hr hc
  exact ⟨fuel, s', hrun, js'.regs 0, hrel.gpr 0 (by omega), hx⟩

end JanusASL.RedTeam

/-! Axiom check of this file's theorems (run.sh fails on any line not "ok"). -/
open Lean Elab Command in
elab "#rt_asl_axioms" : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``JanusASL.RedTeam.Rel.unique, ``JanusASL.RedTeam.Rel.no_two_regs, ``JanusASL.RedTeam.Rel.no_two_sp,
      ``JanusASL.RedTeam.Rel.no_two_pc, ``JanusASL.RedTeam.Rel.no_two_flags, ``JanusASL.RedTeam.Rel.ignores_mem,
      ``JanusASL.RedTeam.rel_cfg_satisfiable, ``JanusASL.RedTeam.Add_pure_asl] do
    let axs ← liftCoreM <| Lean.collectAxioms n
    let bad := axs.filter (fun a => !allowed.contains a)
    if bad.isEmpty then logInfo m!"rt-asl ok {n}" else logError m!"rt-asl BAD {n} uses {bad}"

#rt_asl_axioms
