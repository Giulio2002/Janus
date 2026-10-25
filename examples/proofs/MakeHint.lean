import Extracted

/-!
# `MakeHint(n int) map[uint64]uint64` returns `make(map[uint64]uint64, n)` (arm64)

**Guarantee.** For every model `M`, readiness predicate `H` and `makemap` satisfying
`MapVar.MakeMap`, and every call state in which the runtime is ready for the allocation (`H`,
which sees the type descriptor and the hint): the call returns a non-nil map pointer that
represents the empty map, distinct from every map that existed before, with the runtime
environment intact. The hint only sizes the tables; it does not change the abstract map.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.MakeHint" 8)
    (segWord Extracted.program "example.com/basic.MakeHint" 9) 0

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (n : BitVec 64) (s : State) : Prop :=
  CallerOK M s 48 0 ∧ M.Typ mapType ∧
    H [mapType, n.toNat, 0] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem)

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hmk : MakeMap (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap") M H) (n : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [n] (pre M H n)
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        (∀ mp f, M.Rep s.mem mp f → mp ≠ (s'.regs 0).toNat) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.makemap"]
  have hfw : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29)))
      [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 0)] := by janus_frame
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, by simp [setReg], ?_⟩ ?_
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    rw [show (s.sp - 48#64).toNat = s.sp.toNat - 48 by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl]
    simpa using hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    janus_run
    simp only [setReg_apply, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' hfresh ⊢
    refine ⟨hnz, hrep, fun mp f h => hfresh mp f (hl.rep_frame _ _ _ _ h
      (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))), henv'⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `MapModel0.MC ck64`, the readiness `MapModel0.HMake` (no map is alive yet, the header
is writable), code meeting `MakeMap` for them (`MapSat.makeCode`, reached by a branch), and a
call `MakeHint(100)` with no map alive. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.MapVarSat

def cAddr : Nat := Extracted.program.contractAddr "runtime.makemap"

def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := makeCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : MakeMap (Extracted.program.link implAt) cAddr (MC ck64) HMake := by
  have hA : MakeMap (Extracted.program.link implAt) A0 (MC ck64) HMake := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) makeMap_impl
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def n : BitVec 64 := 100#64

/-- The witness call state: `MakeHint(100)`, no map alive. -/
def s0 : State :=
  { regs := fun i => if i = 0 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmemDead }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0) with rfl; rfl⟩

theorem pre0 : pre (MC ck64) HMake n s0 := by
  refine ⟨⟨show ZEnv mmemDead from mmem_zenv.writeLE _ (by decide), ⟨by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩, trivial, hMake_dead _ _ _⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady)
    (ret : Nat) (s : State) (n : BitVec 64),
    M.Laws ∧ MakeMap (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makemap") M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [n] s ∧ pre M H n s :=
  ⟨implAt, MC _, HMake, ret, s0, n, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: a new, empty map. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat ≠ 0 ∧ (MC ck64).Rep s'.mem (s'.regs 0).toNat AMap.empty :=
  correctness implAt (MC _) (MC_laws _) HMake model n ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end Witness

end Proof
