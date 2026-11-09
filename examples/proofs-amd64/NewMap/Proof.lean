import Janus
import Extracted

/-!
# `NewMap()` returns a new, empty, non-nil map (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns a non-nil header pointer that represents the empty map (through `makemap_small`).

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.MapAmd64` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted RIP-relative `LEA`.

The runtime must be ready for the allocating call (`H : RtReady`, assumed at entry for that call; without it the contract was unsatisfiable, finding R3-C1, `test/redteam/maps/model/Unsat.lean`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (H : Contracts.RtReady)
    (hmk : MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H) :
    Ensures (Extracted.program.link impl) Extracted.entry []
      (fun s => CallerOK M s 16 8 ∧
        H [] (s.regs 14).toNat ((s.regs 4).toNat - 16) (Contracts.rtView M.priv s.mem))
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp16 : (s.regs 4 - 16#64).toNat = (s.regs 4).toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.makemap_small"]
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp16]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by simp [setRegF, keepABI, hsp16, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), ?_⟩ ?_
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp16]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    exact hH
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp16] at hfr
    janus64_run
    simp only [setRegF, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' ⊢
    exact ⟨hnz, hrep, henv'⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMapAmd64.lean` sits at `runtime.makemap_small`'s address in this program;
`janus64_map_makesmall` proves `MakeSmall` for it (the model `MC`: one map of at most one entry) by running the stub code. Below, a
concrete call state of `NewMap()` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.LiveStubMapAmd64
open Janus.Contracts.IfaceModel (wsp wg wret)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.makemap_small"))
theorem addr : Extracted.program.contractAddr "runtime.makemap_small" = cA := by decide
def implAt : List Janus.Amd64.Segment := [makeSmallSeg cA]
def linked : Janus.Amd64.Program := Extracted.program.link implAt

theorem h0 : MakeSmall linked cA (MC ck64) HMake := by janus64_map_makesmall

theorem hcon : MakeSmall (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.makemap_small") (MC ck64) HMake := by
  rw [addr]; exact h0

def mem0 : Janus.Arm64.Memory := mmem64Dead

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def ret : Nat := wret

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (MC ck64) s0 16 8 := by
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Janus.Spec.Disjoint, MC_depth]; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (MC ck64) s0 16 8 ∧ HMake [] (s0.regs 14).toNat ((s0.regs 4).toNat - 16) (Contracts.rtView (MC ck64).priv s0.mem)  ∧
    IsMap (MC ck64) s0.mem 0 emp :=
  ⟨callerOK, by unfold HMake; decide, by simp [IsMap, emp]⟩

theorem rtpre_pc {K V : Type} {M : MapModel K V} {n : Nat} {s : Janus.Amd64.State} (a : BitVec 64) (h : RTPre M n s) :
    RTPre M n { s with rip := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩

/-- The precondition of `MakeSmall`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def MakeSmallSite (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 0 s_c ∧ Contracts.Ready64 H M.priv [] s_c

/-- The call state of the `makemap_small` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSatAmd64`, at the contract address. -/
def wsCall : Janus.Amd64.State := { mstate64 mmem64Dead (args 0 0) with rip := BitVec.ofNat 64 cA }

theorem wsCall_pre : MakeSmallSite (MC ck64) HMake wsCall :=
  ⟨rtpre_pc _ (mstate64_rtpre _ rfl rfl mmem64Dead rfl _ 0 (by decide)
      (show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide)) mmem64Dead_guard mmem64Dead_ret),
    hMake_dead64 _ _ _⟩

/-- The theorem fires: `NewMap()` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ((s'.regs 0).toNat ≠ 0 ∧ (MC ck64).Rep s'.mem (s'.regs 0).toNat AMap.empty ∧ (MC ck64).Env s'.mem (s0.regs 14)) :=
  correctness implAt (MC ck64) (MC_laws _) HMake hcon ret hret s0 setup ⟨pre.1, pre.2.1⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.makemap_small`
meeting `MakeSmall` for it, and a call state of `NewMap()` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (ret : Nat)
    (s : Janus.Amd64.State), M.Laws ∧
    MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [] s ∧
    (CallerOK M s 16 8 ∧ H [] (s.regs 14).toNat ((s.regs 4).toNat - 16) (Contracts.rtView M.priv s.mem) ∧ IsMap M s.mem 0 emp) ∧
    (∃ (s_c : Janus.Amd64.State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makemap_small") ∧ MakeSmallSite M H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    ((s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧ M.Env s'.mem (s.regs 14)) :=
  ⟨implAt, (MC ck64), HMake, ret, s0, (MC_laws _), hcon, hret, setup, pre, ⟨wsCall, by show BitVec.ofNat 64 cA = _; rw [addr], wsCall_pre⟩, returns⟩

end Witness

end Proof
