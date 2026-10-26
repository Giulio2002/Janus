import Extracted

/-!
# `InsertPtr(m map[*PNode]uint64, p *PNode, v uint64)` sets `m[p] = v` (arm64)

**Guarantee.** For every model `M`, readiness predicate `H` and `mapassign_fast64ptr`
satisfying `MapVar.Assign64Ptr` (8-byte values), every non-nil map `m` holding `f` (keyed by the
pointer's value) and every call state in which the runtime is ready (`H`): the call returns and
memory represents `f` with `p ↦ v`, the runtime environment intact. Lookups of a pointer-keyed
map go through `mapaccess1_fast64` (`LookupPtr`) on the same model.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.InsertPtr" 9)
    (segWord Extracted.program "example.com/basic.InsertPtr" 10) 0

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (m k : BitVec 64)
    (f : AMap (BitVec 64) (BitVec 64)) (s : State) : Prop :=
  CallerOK M s 48 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    H [mapType, m.toNat, k.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem)

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hasn : MapVar.Assign64Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64ptr") 8 M H)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (pre M H m k f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set k v) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_fast64ptr"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, by simpa [setReg] using hm0, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48))
      (hi := s.sp.toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    rw [show (s.sp - 48#64).toNat = s.sp.toNat - 48 by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl]
    simpa using hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 32) (by omega) (by omega))
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hset
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `MapModel0.MC ck64`, the readiness `MapModel0.HAssign` (the map is empty), code
meeting `Assign64Ptr` for them (`MapSat.assignCode`, reached by a branch), and a call state
inserting the pointer `VAL` with value `42` into the empty non-nil map `MP`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.MapVarSat

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_fast64ptr"

def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := assignCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : MapVar.Assign64Ptr (Extracted.program.link implAt) cAddr 8 (MC ck64) HAssign := by
  have hA : MapVar.Assign64Ptr (Extracted.program.link implAt) A0 8 (MC ck64) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (assign64Ptr_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kv : BitVec 64 := BitVec.ofNat 64 VAL
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertPtr(MP, VAL, 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kv else if i = 2 then v
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv, v] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem pre0 : pre (MC ck64) HAssign mv kv AMap.empty s0 := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, by decide, mmem_repC _, hAssign_mmem _ _ _⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady)
    (ret : Nat) (s : State) (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
    M.Laws ∧ MapVar.Assign64Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64ptr") 8 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, k, v] s ∧
    pre M H m k f s :=
  ⟨implAt, MC _, HAssign, ret, s0, mv, kv, v, AMap.empty, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: the map now holds `VAL ↦ 42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MC ck64).Rep s'.mem MP (AMap.empty.set kv 42#64) :=
  correctness implAt (MC _) (MC_laws _) HAssign model mv kv v AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
