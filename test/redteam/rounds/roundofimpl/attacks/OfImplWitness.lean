import Extracted

/-!
# `NewPair(a, b uint64) *Pair` returns a fresh heap object holding `a` and `b`

**Guarantee.** For all `a`, `b`, every list `rt` of runtime-owned memory ranges and **every**
implementation of `runtime.newobject` that satisfies the allocation contract
`NewobjectContract` (`Janus/Contracts/Alloc.lean`: it returns a fresh, zeroed, aligned object of
`typ.Size_` bytes inside `rt` and changes nothing outside `rt` and its own stack), and every Go call
state of `example.com/basic.NewPair` in which the stack-growth prologue falls through, the stack
window `[SP-4144, SP+24)` (NewPair's 48-byte frame, 4096 bytes for the runtime, the two spill
slots) is writable and outside `rt`, and memory holds the program's read-only data (the type
descriptor of `Pair`): the call returns, obeys the ABI, and `X0` is a pointer `ptr` with

* `[ptr, ptr+16)` inside the runtime-owned ranges, so it is disjoint from every object the
  caller holds outside them (a *fresh* object), writable and 16-byte aligned;
* the word at `ptr` is `a` and the word at `ptr+8` is `b`;
* memory unchanged outside `rt` and the stack window.

**What is assumed.** The statement quantifies over the code at `runtime.newobject`
(`Extracted.program.link impl`) and assumes the contract for it (the hypothesis `hnew`). The
allocator itself is not executed: `janus extract --contract runtime.newobject` leaves it out
(`Extracted.program.contracts`), and the theorem holds for the real binary exactly when the real
runtime meets the contract (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The address of `Pair`'s type descriptor, the argument NewPair passes to `runtime.newobject`
(the `ADRP` + `ADD` pair at `NewPair+0x20`), recomputed from the extracted words. -/
def pairType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.NewPair" 8)
    (segWord Extracted.program "example.com/basic.NewPair" 9) 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧
        H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  have hnew := NewobjectContract.of_codeIn (codeIn_ofImpl_of_apart hap) hnew
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : pairType
  rw [h_pt] at hH
  janus_data hd [hw]
  -- run to the instruction after `bl runtime.newobject`, using the contract at the call
  janus_run until [Extracted.entry + 0x34] calls [hnew.pos]
  -- the object is inside `rt`, the stack window outside it
  have hdj := InRanges.disjoint ‹InRanges _ 16 rt› hout
  janus_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_, ?_⟩
  · janus_simp
  · janus_simp
  · janus_frame

/-! ## Non-vacuity witness

`janus_alloc_witness` (`Janus/Contracts/AllocWitness.lean`) builds a concrete allocator at
`runtime.newobject`'s address, the runtime-owned ranges `rt` (the heap and `Pair`'s type descriptor),
the readiness predicate `H`, and proves the contract `hnewO` for them (about `Extracted.program.ofImpl impl`, with `hap`). Below, a concrete call
state of `NewPair(3, 5)` satisfies the whole precondition, `H` included, and the call returns
the object the theorem describes. -/

namespace Witness

janus_alloc_witness_ofimpl types := [pairType]

open AllocW (impl rt H linked hnewO hap)
open Janus.Contracts.AllocWitness (heap)

def tyA : Nat := janus_eval% pairType
def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length

def bytes (a : Nat) : Byte :=
  if tyA ≤ a ∧ a < tyA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0) else 0

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 5 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [pairType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : pairType = tyA := by unfold tyA; decide
  rw [hpt]
  refine Janus.Contracts.AllocWitness.allocH_intro
    (Janus.Contracts.AllocWitness.inRanges_ty (tys := AllocW.tys) (a := tyA) (by decide)) ?_ ?_ ?_
  · decide
  · decide
  · refine Janus.Contracts.AllocWitness.heapZero_of_bytes _ _ fun i hi => ?_
    have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + dlen) := by
      simp only [tyA, heap, dlen]; omega
    show bytes (heap + i) = 0
    simp only [bytes]; rw [if_neg h1]

theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧
    H [pairType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, AllocW.rt, Janus.Contracts.AllocWitness.allocRt, AllocW.tys, outside_cons, outside_nil, List.map]; decide, hH⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

/-- The call state at `runtime.newobject`'s entry (argument `pairType`, callee `SP` 48 below). -/
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
  have hpt : pairType = tyA := by unfold tyA; decide
  rw [hpt] at h
  refine ⟨⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, (by simp only [calleeStack, outside_cons, outside_nil]; decide)⟩, ?_⟩
  exact h


/-- The theorem fires: for this call and this allocator, `NewPair(3, 5)` returns a fresh object in
`rt` holding 3 and 5. -/
theorem returns : Returns ((Extracted.program.link AllocW.impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 16 true = true ∧
      s'.mem.readLE ptr 8 = (3 : BitVec 64).toNat ∧ s'.mem.readLE (ptr + 8) 8 = (5 : BitVec 64).toNat ∧
      MemFrame s0.mem s'.mem (rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 24)]) :=
  correctness impl rt H 3 5 hap hnewO ret hret s0 setup pre

/-- The hypotheses are satisfiable: an allocator meeting the contract (`hnew`), runtime ranges,
a readiness predicate, and a call state of `NewPair(3, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State),
    ImplApart Extracted.program impl ∧
    NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt ∧
      H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      nwSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 16 true = true ∧
      s'.mem.readLE ptr 8 = (3 : BitVec 64).toNat ∧ s'.mem.readLE (ptr + 8) 8 = (5 : BitVec 64).toNat ∧
      MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨AllocW.impl, AllocW.rt, AllocW.H, ret, s0, AllocW.hap, AllocW.hnewO, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness



/-! ## Witness attack (test/redteam/rounds/roundofimpl/run-roundofimpl.sh): the witness omits the placement premise

`ImplApart Extracted.program impl` is a hypothesis of `correctness`, so a witness that exhibits the
rest but not the premise does not show the theorem non-vacuous (the runtime might have to overlap
the extracted code). It must be rejected, like the control `Proof.Witness.nonvacuous`. -/

namespace NoApart

namespace Witness

theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State),
    NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt ∧
      H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      Proof.Witness.nwSite rt H s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 16 true = true ∧
      s'.mem.readLE ptr 8 = (3 : BitVec 64).toNat ∧ s'.mem.readLE (ptr + 8) 8 = (5 : BitVec 64).toNat ∧
      MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨Proof.Witness.AllocW.impl, Proof.Witness.AllocW.rt, Proof.Witness.AllocW.H, Proof.Witness.ret,
    Proof.Witness.s0, Proof.Witness.AllocW.hnewO, Proof.Witness.hret, Proof.Witness.setup,
    Proof.Witness.pre, ⟨Proof.Witness.wsCall, rfl, Proof.Witness.wsCall_pre⟩, Proof.Witness.returns⟩

end Witness

end NoApart
