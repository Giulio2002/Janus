import Extracted

/-!
# `ClearMap(m)` empties `m` (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns and memory represents the empty map at `m` (a nil map stays nil).

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.Map` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted `ADRP`+`ADD` words.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/basic.ClearMap" 7)
    (segWord Extracted.program "example.com/basic.ClearMap" 8) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hclr : Contracts.Map.Clear (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapclear") M)
    (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m]
      (fun s => CallerOK M s 32 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun s s' => IsMap M s'.mem m.toNat AMap.empty ∧ M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapclear"]
  refine Reaches.call (Summary.withExit (hclr f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 32))
      (hi := s.sp.toNat + 0) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hmap'⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hmap' henv'
    exact ⟨hmap', henv'⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMap.lean` sits at `runtime.mapclear`'s address in this program;
`janus_map_clear` proves `Contracts.Map.Clear` for it (the model `ME`: one empty non-nil map) by running the stub code. Below, a
concrete call state of `ClearMap(map)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.LiveStubMap
open Janus.Contracts.IfaceModel (wsp wg)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapclear"))
theorem addr : Extracted.program.contractAddr "runtime.mapclear" = cA := by decide
def implAt : List Segment := [retSeg cA]
def linked : Program := Extracted.program.link implAt

theorem h0 : Contracts.Map.Clear linked cA (ME (BitVec 64)) := by janus_map_clear

theorem hcon : Contracts.Map.Clear (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapclear") (ME (BitVec 64)) := by
  rw [addr]; exact h0

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Memory := withData mmem dat

def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (ME (BitVec 64)) s0 32 0 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Disjoint, ME_depth]; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (ME (BitVec 64)) s0 32 0 ∧ (ME (BitVec 64)).Typ mapType ∧ IsMap (ME (BitVec 64)) s0.mem (BitVec.ofNat 64 MP).toNat emp :=
  ⟨callerOK, trivial, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, by decide, by decide⟩⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapclear`
meeting `Contracts.Map.Clear` for it, and a call state of `ClearMap(map)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (ret : Nat)
    (s : State), M.Laws ∧
    Contracts.Map.Clear (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapclear") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP] s ∧
    (CallerOK M s 32 0 ∧ M.Typ mapType ∧ IsMap M s.mem (BitVec.ofNat 64 MP).toNat emp) :=
  ⟨implAt, (ME (BitVec 64)), ret, s0, (ME_laws _), hcon, hret, setup, pre⟩

/-- The theorem fires: `ClearMap(map)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (IsMap (ME (BitVec 64)) s'.mem (BitVec.ofNat 64 MP).toNat emp ∧ (ME (BitVec 64)).Env s'.mem (s0.regs 28)) :=
  correctness implAt (ME (BitVec 64)) (ME_laws _) hcon (BitVec.ofNat 64 MP) emp ret hret s0 setup pre

end Witness

end Proof
