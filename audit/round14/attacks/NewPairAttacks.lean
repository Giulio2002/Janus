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
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧
        H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
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
the readiness predicate `H`, and proves the contract `hnew` for them. Below, a concrete call
state of `NewPair(3, 5)` satisfies the whole precondition, `H` included, and the call returns
the object the theorem describes. -/

namespace Witness

janus_alloc_witness types := [pairType]

open AllocW (impl rt H linked hnew)
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
    ⟨by decide, by decide⟩, by decide⟩, ?_⟩
  exact h

/-- The theorem fires: for this call and this allocator, `NewPair(3, 5)` returns a fresh object in
`rt` holding 3 and 5. -/
theorem returns : Returns ((Extracted.program.link impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 16 true = true ∧
      s'.mem.readLE ptr 8 = (3 : BitVec 64).toNat ∧ s'.mem.readLE (ptr + 8) 8 = (5 : BitVec 64).toNat ∧
      MemFrame s0.mem s'.mem (rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 24)]) :=
  correctness impl rt H 3 5 hnew ret hret s0 setup pre

/-- The hypotheses are satisfiable: an allocator meeting the contract (`hnew`), runtime ranges,
a readiness predicate, and a call state of `NewPair(3, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat)
    (s : State),
    NewobjectContract (Extracted.program.link impl)
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
  ⟨impl, rt, H, ret, s0, hnew, hret, setup, pre, ⟨wsCall, rfl, wsCall_pre⟩, returns⟩

end Witness


/-! ## Round 14 attacks (audit/round14/run-round14.sh): each theorem below is verified by name and must be
rejected, except the controls (`Proof.correctness`, `Proof.Witness.nonvacuous`, `Proof.Witness.returns`). -/

def NPre (rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4144) 4168 rt ∧ H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)

/-- BAD1 (the red-team finding): the main guarantee for the consumer's own toy allocator, no hypothesis
on the runtime. Used to verify and report "Runtime contracts assumed: runtime.newobject (pinned)". -/
theorem bad1 (a b : BitVec 64) :
    Ensures (Extracted.program.link Witness.AllocW.impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 Witness.AllocW.rt ∧
        Witness.AllocW.H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView Witness.AllocW.rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 Witness.AllocW.rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (Witness.AllocW.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) :=
  correctness Witness.AllocW.impl Witness.AllocW.rt Witness.AllocW.H a b Witness.AllocW.hnew

/-- BAD2: the contract for the consumer's allocator, offered as a theorem about the program. -/
theorem bad2 : NewobjectContract (Extracted.program.link Witness.AllocW.impl)
      (Extracted.program.contractAddr "runtime.newobject") Witness.AllocW.rt 4096 Witness.AllocW.H :=
  Witness.AllocW.hnew

/-- BAD3: the implementation is existentially quantified INSIDE the statement. -/
theorem bad3 (a b : BitVec 64) :
    ∃ impl : List Segment, Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD4: no contract, but the implementation is constrained (here: it has three segments). -/
theorem bad4 (impl : List Segment) (h : impl.length = 3) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD5: the empty implementation, a closed choice. -/
theorem bad5 (a b : BitVec 64) :
    Ensures (Extracted.program.link []) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD6: a program built by hand from `Extracted.program` with other segments. -/
theorem bad6 (impl : List Segment) (a b : BitVec 64) :
    Ensures { Extracted.program with segments := impl } Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD7: the implementation is a lambda-bound variable of a nested binder, not of the statement. -/
theorem bad7 (a b : BitVec 64) :
    (fun impl : List Segment => Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0)) Witness.AllocW.impl := sorry

/-- BAD8: the contract hypothesis names the toy allocator, the program a variable. -/
theorem bad8 (impl : List Segment) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link Witness.AllocW.impl)
      (Extracted.program.contractAddr "runtime.newobject") Witness.AllocW.rt 4096 Witness.AllocW.H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD9: a premise about the implementation headed by a Janus predicate that is not a runtime contract
(`RetAddr (link impl) ret`): it pins `impl` (here: to code that has a valid return address) and is not a pinned contract. -/
theorem bad9 (impl : List Segment) (ret : Nat) (h : RetAddr (Extracted.program.link impl) ret) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD10: a premise equating a Janus function of the linked program with a number. -/
theorem bad10 (impl : List Segment) (h : (Extracted.program.link impl).exitAddr = 0) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-- BAD11: the linked program equated with the one linked to the toy allocator. -/
theorem bad11 (impl : List Segment) (h : Extracted.program.link impl = Extracted.program.link Witness.AllocW.impl)
    (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun _ s' => (s'.regs 0).toNat = 0) := sorry

/-! ### weak witnesses -/

namespace WeakA.Witness
/-- mentions Extracted.program, proves nothing about a state. -/
theorem nonvacuous : ∃ n : Nat, Extracted.program = Extracted.program ∧ n = n := ⟨0, rfl, rfl⟩
end WeakA.Witness

namespace WeakB.Witness
open Proof.Witness
/-- the right shape, but the readiness predicate `H` is not required of the state. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt) :=
  ⟨AllocW.impl, AllocW.rt, AllocW.H, ret, s0, AllocW.hnew, hret, setup, pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1⟩
end WeakB.Witness

namespace WeakC.Witness
open Proof.Witness
/-- the right shape, but no allocator contract: the hypothesis `hnew` is not exhibited. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    H = H ∧ RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt ∧
      H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) :=
  ⟨AllocW.impl, AllocW.rt, AllocW.H, ret, s0, rfl, hret, setup, pre⟩
end WeakC.Witness

namespace WeakD.Witness
open Proof.Witness
/-- the right shape, but the state is not required to be a call state of the entry. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    (GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4144) 4168 rt ∧
      H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) :=
  ⟨AllocW.impl, AllocW.rt, AllocW.H, ret, s0, AllocW.hnew, hret, pre⟩
end WeakD.Witness

namespace WeakE.Witness
/-- not an existential at all: the concrete-implementation statement under a witness name. -/
theorem nonvacuous (a b : BitVec 64) :
    Ensures (Extracted.program.link Proof.Witness.AllocW.impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 Proof.Witness.AllocW.rt ∧
        Proof.Witness.AllocW.H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView Proof.Witness.AllocW.rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 16 Proof.Witness.AllocW.rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 16 true = true ∧
        s'.mem.readLE ptr 8 = a.toNat ∧ s'.mem.readLE (ptr + 8) 8 = b.toNat ∧
        MemFrame s.mem s'.mem (Proof.Witness.AllocW.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) :=
  correctness Proof.Witness.AllocW.impl Proof.Witness.AllocW.rt Proof.Witness.AllocW.H a b Proof.Witness.AllocW.hnew
end WeakE.Witness

namespace WeakF.Witness
open Proof.Witness
/-- `returns` with a trivial postcondition. -/
theorem returns : Returns ((Extracted.program.link AllocW.impl).withExit ret) s0 fun _ => True :=
  Returns.mono Proof.Witness.returns fun _ _ => trivial
end WeakF.Witness

namespace WeakG.Witness
open Proof.Witness
/-- `returns` that only says the ABI is obeyed, not the main theorem's guarantee. -/
theorem returns : Returns ((Extracted.program.link AllocW.impl).withExit ret) s0 fun s' => ABIReturn s0 s' :=
  Returns.mono Proof.Witness.returns fun _ h => h.1
end WeakG.Witness

namespace WeakI.Witness
open Proof.Witness
/-- `returns` padded with `True`. -/
theorem returns : Returns ((Extracted.program.link AllocW.impl).withExit ret) s0 fun s' => ABIReturn s0 s' ∧ True :=
  Returns.mono Proof.Witness.returns fun _ h => ⟨h.1, trivial⟩
end WeakI.Witness

namespace HideA.Witness
/-- a MAIN guarantee (quantified runtime, honest contract hypothesis) hidden in a `Witness` namespace under another
name: a lemma of a witness namespace is not a verifiable result, so it cannot be the theorem reported as Verified. -/
theorem guarantee (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (NPre rt H) (fun _ _ => True) := sorry
end HideA.Witness

namespace HideB.Witness
/-- the same guarantee under the exact name `Witness.returns`: not a `Returns` statement about a start state. -/
theorem returns (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (NPre rt H) (fun _ _ => True) := sorry
end HideB.Witness

namespace WeakH.Witness
/-- `returns` that is not a Returns statement. -/
theorem returns : Extracted.program = Extracted.program := rfl
end WeakH.Witness

end Proof
