import Extracted

/-!
# `NewMap()` returns a new, empty, non-nil map (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns a non-nil header pointer that represents the empty map (through `makemap_small`).

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

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hmk : MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H) :
    Ensures (Extracted.program.link impl) Extracted.entry []
      (fun s => CallerOK M s 16 0 ∧ H [] (s.regs 28).toNat (s.sp.toNat - 16) (rtView M.priv s.mem))
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.makemap_small"]
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), ?_⟩ ?_
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega)),
      rtView_writeLE (Outside.of_sub hout (by omega) (by omega)),
      show (s.sp - 16#64).toNat = s.sp.toNat - 16 by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl]
    exact hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    janus_run
    simp only [setReg_apply, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' ⊢
    exact ⟨hnz, hrep, henv'⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMap.lean` sits at `runtime.makemap_small`'s address in this program;
`janus_map_makesmall` proves `MakeSmall` for it (the model `MC`: one map of at most one entry) by running the stub code. Below, a
concrete call state of `NewMap()` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.LiveStubMap
open Janus.Contracts.IfaceModel (wsp wg)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.makemap_small"))
theorem addr : Extracted.program.contractAddr "runtime.makemap_small" = cA := by decide
def implAt : List Segment := [makeSmallSeg cA]
def linked : Program := Extracted.program.link implAt

theorem h0 : MakeSmall linked cA (MC ck64) HMake := by janus_map_makesmall

theorem hcon : MakeSmall (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.makemap_small") (MC ck64) HMake := by
  rw [addr]; exact h0

def mem0 : Memory := mmemDead

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (MC ck64) s0 16 0 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Disjoint, MC_depth]; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (MC ck64) s0 16 0 ∧ HMake [] (s0.regs 28).toNat (s0.sp.toNat - 16) (rtView (MC ck64).priv s0.mem)  ∧
    IsMap (MC ck64) s0.mem 0 emp :=
  ⟨callerOK, by unfold HMake; decide, by simp [IsMap, emp]⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.makemap_small`
meeting `MakeSmall` for it, and a call state of `NewMap()` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : RtReady) (ret : Nat)
    (s : State), M.Laws ∧
    MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    (CallerOK M s 16 0 ∧ H [] (s.regs 28).toNat (s.sp.toNat - 16) (rtView M.priv s.mem) ∧ IsMap M s.mem 0 emp) :=
  ⟨implAt, (MC ck64), HMake, ret, s0, (MC_laws _), hcon, hret, setup, pre⟩

/-- The theorem fires: `NewMap()` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ((s'.regs 0).toNat ≠ 0 ∧ (MC ck64).Rep s'.mem (s'.regs 0).toNat AMap.empty ∧ (MC ck64).Env s'.mem (s0.regs 28)) :=
  correctness implAt (MC ck64) (MC_laws _) HMake hcon  ret hret s0 setup pre

end Witness

end Proof
