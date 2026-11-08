import Extracted

/-!
# `Insert(m, k, v)` sets `m[k] = v` (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, for a non-nil map holding `f`, the call returns and afterwards memory represents the map `f` with `k ↦ v` (the runtime environment intact). A nil map is not covered: `mapassign` panics there, and the contract requires a non-nil map.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.Map` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted `ADRP`+`ADD` words. The runtime must be ready for the allocating call (`H : RtReady`, assumed at entry for that call; without it the contract was unsatisfiable, finding R3-C1, `audit/maps/model/Unsat.lean`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.Insert" 9)
    (segWord Extracted.program "example.com/basic.Insert" 10) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M H)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 48 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
        H [mapType, m.toNat, k.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem))
      (fun s s' => M.Rep s'.mem m.toNat (f.set k v) ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_fast64"]
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

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMap.lean` sits at `runtime.mapassign_fast64`'s address in this program;
`janus_map_assign` proves `Assign` for it (the model `MC`: one map of at most one entry) by running the stub code. Below, a
concrete call state of `Insert(map, 5, 7)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.LiveStubMap
open Janus.Contracts.IfaceModel (wsp wg)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapassign_fast64"))
theorem addr : Extracted.program.contractAddr "runtime.mapassign_fast64" = cA := by decide
def implAt : List Segment := [assignSeg cA]
/-- The precondition of `Assign`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def AssignSite (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (f : AMap (BitVec 64) (BitVec 64)) (s_c : State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ (s_c.regs 1).toNat ≠ 0 ∧ M.Rep s_c.mem (s_c.regs 1).toNat f ∧
    Ready H M.priv [(s_c.regs 0).toNat, (s_c.regs 1).toNat, (s_c.regs 2).toNat] s_c

def linked : Program := Extracted.program.link implAt

theorem h0 : Assign linked cA (MC ck64) HAssign := by janus_map_assign

theorem hcon : Assign (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapassign_fast64") (MC ck64) HAssign := by
  rw [addr]; exact h0

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Memory := withData mmem dat

def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 1 then 5 else if i = 2 then 7 else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5, 7] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (MC ck64) s0 48 32 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Disjoint, MC_depth]; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (MC ck64) s0 48 32 ∧ (MC ck64).Typ mapType ∧ (BitVec.ofNat 64 MP).toNat ≠ 0 ∧ (MC ck64).Rep s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    HAssign [mapType, (BitVec.ofNat 64 MP).toNat, (5 : BitVec 64).toNat] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView (MC ck64).priv s0.mem) :=
  ⟨callerOK, trivial, by decide, ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, by unfold HAssign; decide⟩

/-- The call state of the `mapassign_fast64` contract (U-WITNESS-CALLSITE): at the callee's entry, the map call's frame
set up (`SP` lowered by the caller's frame), with the contract's precondition. -/
def wsCall : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 mapType else if i = 1 then BitVec.ofNat 64 MP else if i = 2 then 7
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (wsp - 48), pc := BitVec.ofNat 64 cA,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

set_option maxRecDepth 100000 in
theorem wsCall_pre : AssignSite (MC ck64) HAssign AMap.empty wsCall := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, trivial, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, by unfold Ready HAssign; decide⟩
  simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapassign_fast64`
meeting `Assign` for it, and a call state of `Insert(map, 5, 7)` that satisfies the precondition; the call state of the
`mapassign_fast64` contract; and the returning run. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (ret : Nat)
    (s : State), M.Laws ∧
    Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5, 7] s ∧
    (CallerOK M s 48 32 ∧ M.Typ mapType ∧ (BitVec.ofNat 64 MP).toNat ≠ 0 ∧ M.Rep s.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    H [mapType, (BitVec.ofNat 64 MP).toNat, (5 : BitVec 64).toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView M.priv s.mem)) ∧
    (∃ (f : AMap (BitVec 64) (BitVec 64)) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapassign_fast64") ∧
      AssignSite M H f s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
      (M.Rep s'.mem (BitVec.ofNat 64 MP).toNat (AMap.empty.set 5 7) ∧ M.Env s'.mem (s.regs 28)) :=
  ⟨implAt, (MC ck64), HAssign, ret, s0, (MC_laws _), hcon, hret, setup, pre,
    ⟨AMap.empty, wsCall, by simp only [wsCall]; exact addr.symm ▸ rfl, wsCall_pre⟩,
    correctness implAt (MC ck64) (MC_laws _) HAssign hcon (BitVec.ofNat 64 MP) 5 7 AMap.empty ret hret s0 setup pre⟩

/-- The theorem fires: `Insert(map, 5, 7)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ((MC ck64).Rep s'.mem (BitVec.ofNat 64 MP).toNat (emp.set 5 7) ∧ (MC ck64).Env s'.mem (s0.regs 28)) :=
  correctness implAt (MC ck64) (MC_laws _) HAssign hcon (BitVec.ofNat 64 MP) 5 7 AMap.empty ret hret s0 setup pre

end Witness

end Proof
