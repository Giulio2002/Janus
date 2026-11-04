import Janus
import Extracted

/-!
# `Lookup(m, k)` returns `m[k]` and whether `k` is present (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns (never faulting or panicking), obeys the ABI, and returns the value stored under `k` (`0` if absent, also for a nil map) and, in the low byte of the second result register, `1` iff `k` is present.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.MapAmd64` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted RIP-relative `LEA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x14)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_fast64") M)
    (m k : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k]
      (fun s => CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => s'.regs 0 = (f k).getD 0 ∧ (s'.regs 3).toNat % 256 = (f k).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess2_fast64"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, keepABI, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus64_run
    all_goals simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hs3 hok
    all_goals first | exact hok | exact ⟨by rw [hs3]; simp, hok⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMapAmd64.lean` sits at `runtime.mapaccess2_fast64`'s address in this program;
`janus64_map_access2` proves `Access2` for it (the model `ME`: one empty non-nil map) by running the stub code. Below, a
concrete call state of `Lookup(map, 5)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.LiveStubMapAmd64
open Janus.Contracts.IfaceModel (wsp wg wret)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapaccess2_fast64"))
theorem addr : Extracted.program.contractAddr "runtime.mapaccess2_fast64" = cA := by decide
def implAt : List Janus.Amd64.Segment := [accessSeg cA]
def linked : Janus.Amd64.Program := Extracted.program.link implAt

theorem h0 : Access2 linked cA (ME (BitVec 64)) := by janus64_map_access2

theorem hcon : Access2 (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapaccess2_fast64") (ME (BitVec 64)) := by
  rw [addr]; exact h0

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Janus.Arm64.Memory := Janus.Contracts.LiveStubMap.withData mmem64 dat

def ret : Nat := wret

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 3 then 5 else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (ME (BitVec 64)) s0 40 8 := by
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Janus.Spec.Disjoint, ME_depth]; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (ME (BitVec 64)) s0 40 8 ∧ (ME (BitVec 64)).Typ mapType ∧ IsMap (ME (BitVec 64)) s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty :=
  ⟨callerOK, trivial, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, by decide, by decide⟩⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapaccess2_fast64`
meeting `Access2` for it, and a call state of `Lookup(map, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64)) (ret : Nat)
    (s : Janus.Amd64.State), M.Laws ∧
    Access2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_fast64") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5] s ∧
    (CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem (BitVec.ofNat 64 MP).toNat AMap.empty) :=
  ⟨implAt, (ME (BitVec 64)), ret, s0, (ME_laws _), hcon, hret, setup, pre⟩

/-- The theorem fires: `Lookup(map, 5)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 0 = (emp 5).getD 0 ∧ (s'.regs 3).toNat % 256 = (emp 5).isSome.toNat) :=
  correctness implAt (ME (BitVec 64)) (ME_laws _) hcon (BitVec.ofNat 64 MP) 5 emp ret hret s0 setup pre

end Witness

end Proof
