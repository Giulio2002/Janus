import Extracted

/-!
# `MakeAdder(a uint64) func(uint64) uint64`: creating an escaping closure

**Guarantee.** For every `a`, every list `rt` of runtime-owned memory ranges and **every**
implementation of `runtime.newobject` that satisfies the allocation contract
`NewobjectContract` (`Janus/Contracts/Alloc.lean`), and every Go call state of
`example.com/basic.MakeAdder` in which the stack-growth prologue falls through, the stack window
`[SP-4144, SP+24)` (the 48-byte frame, 4096 bytes for the runtime, the spill slot) is writable
and outside `rt`, and memory holds the program's read-only data (the type descriptor of the
closure's struct): the call returns, obeys the ABI, and `fv = X0` is a **fresh** funcval:

* `[fv, fv+16)` lies inside the runtime-owned ranges (disjoint from everything the caller holds
  outside them), writable, 16-byte aligned;
* its code word is the closure body `MakeAdder.func1` (`FuncvalIs`) and the captured variable
  after it is `a` (`ClosureCtx`): exactly the hypotheses under which a caller's theorem about
  calling `fv` (as `MapSum.lean` does) applies;
* memory is unchanged outside `rt` and the stack window.

The closure outlives the call, so the compiler allocates its funcval with `runtime.newobject`
(compare `Compose.lean`, where it stays in the frame) and fills in the code address and `a`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The address of the closure's type descriptor, the argument MakeAdder passes to
`runtime.newobject` (the `ADRP` + `ADD` pair at `MakeAdder+0x1c`), recomputed from the extracted
words. -/
def fvType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "example.com/basic.MakeAdder" 7)
    (segWord Extracted.program "example.com/basic.MakeAdder" 8) 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧
        H [fvType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
        s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
        FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
        ClosureCtx s'.mem (s'.regs 0) [a] ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hH⟩
  janus_intro hs
  janus_eval_nat h_ft : fvType
  rw [h_ft] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus_run
  have hf : segAddr Extracted.program "example.com/basic.MakeAdder.func1" = janus_eval% segAddr Extracted.program "example.com/basic.MakeAdder.func1" := by decide
  refine ⟨‹_›, ‹_›, ‹_›, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · janus_simp
    exact accessible_sub ‹s.mem.accessible _ 16 true = true› (by simp) (by omega) (by omega)
  · rw [hf]; janus_simp
  · janus_simp
    simp only [List.length_cons, List.length_nil]
    exact accessible_sub ‹s.mem.accessible _ 16 true = true› (by simp) (by omega) (by omega)
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    janus_simp
    rfl
  · janus_frame

/-! ## Non-vacuity witness

`janus_alloc_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete allocator at
`runtime.newobject`'s address, the runtime-owned ranges `rt` (the heap and the closure's type
descriptor) and the readiness predicate `H`, and proves the contract `hnew` for them. Below, a
concrete call state of `MakeAdder(7)` satisfies the whole precondition, `H` included, and the call
returns the closure the theorem describes. -/

namespace Witness

janus_alloc_witness types := [fvType]

open AllocW (impl rt H linked hnew)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% fvType
def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length
def dbase : Nat := janus_eval% dat.base

def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then 7 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [7] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [fvType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : fvType = tyA := by unfold tyA; decide
  rw [hpt]
  refine Janus.Contracts.AllocWitness.allocH_intro
    (Janus.Contracts.AllocWitness.inRanges_ty (tys := AllocW.tys) (a := tyA) (by decide)) ?_ ?_ ?_
  · decide
  · decide
  · refine Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_
    have h1 : ¬(dbase ≤ heap + i ∧ heap + i < dbase + dlen) := by
      simp only [dbase, heap, dlen]; omega
    show bytes (heap + i) = 0
    simp only [bytes]; rw [if_neg h1]

theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧
    H [fvType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, AllocW.rt, Janus.Contracts.AllocWitness.allocRt, AllocW.tys, outside_cons, outside_nil, List.map]; decide, hH⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- The call state at `runtime.newobject`'s entry (argument `fvType`, callee `SP` 48 below). -/
def wsCall : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 cAddr,
    flags := ⟨false, false, false, false⟩, mem := s0.mem }

@[reducible] def nwSite (rt : List (Nat × Nat)) (H : RtReady) (s_c : State) : Prop :=
  NewobjectPre 4096 s_c ∧ Ready H rt [(s_c.regs 0).toNat] s_c

set_option maxRecDepth 100000 in
theorem wsCall_pre : nwSite rt H wsCall := by
  have h := hH
  have hpt : fvType = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  exact h

/-- The theorem fires: for this call and this allocator, `MakeAdder(7)` returns a fresh closure
in `rt`. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
    s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
    FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
    ClosureCtx s'.mem (s'.regs 0) [(7 : BitVec 64)] ∧
    MemFrame s0.mem s'.mem (rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 24)]) :=
  correctness impl rt H 7 hnew ret hret s0 setup pre

/-- The hypotheses are satisfiable: an allocator meeting the contract (`hnew`), runtime ranges,
a readiness predicate, and a call state of `MakeAdder(7)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [7] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt ∧
      H [fvType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      nwSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    InRanges (s'.regs 0).toNat 16 rt ∧ (s'.regs 0).toNat % 16 = 0 ∧
    s'.mem.accessible (s'.regs 0).toNat 16 true = true ∧
    FuncvalIs s'.mem (s'.regs 0) (segAddr Extracted.program "example.com/basic.MakeAdder.func1") ∧
    ClosureCtx s'.mem (s'.regs 0) [(7 : BitVec 64)] ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, ret, s0, hnew, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness

end Proof
