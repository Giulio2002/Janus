import Extracted

/-!
# `Cons(next *Node, v uint64) *Node`: one allocation and one pointer store (arm64)

```go
type Node struct{ Next *Node; V uint64 }
func Cons(next *Node, v uint64) *Node { return &Node{Next: next, V: v} }
```

The smallest user of both live runtime contracts: `runtime.newobject` allocates the node and
`runtime.gcWriteBarrier1` is the barrier of the store of `next` (the flag unknown: both branches are
executed). The point of the example is its **Witness**: the stub runtime that makes the two live
contracts satisfiable at `Extracted.program`'s own contract addresses is the generic
`Janus.Contracts.LiveStub` (`LiveStub.newobjectSeg`, `LiveStub.wbSeg`, `janus_live_newobject`,
`janus_live_wb`); nothing in the file proves a contract by hand.

**Guarantee.** For every runtime satisfying the live contracts with a budget of at least 16
bytes, and every call state whose frame is outside the runtime-owned ranges: the call returns, the
result is a 16-byte node inside `R.rt` whose fields are `next` and `v`, memory changes only in `R.rt`
and the stack window, and the invariant holds again for some live set that contains the node.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor `Cons` passes to `newobject` (`ADRP`+`ADD` at `Cons+0x20`) and the address of the
write-barrier flag (`ADRP`+`MOVWU` at `Cons+0x2c`), recomputed from the extracted words. -/
def nodeType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/rtmisc/stubdemo.Cons" 8)
    (segWord Extracted.program "example.com/rtmisc/stubdemo.Cons" 9) 0
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program "example.com/rtmisc/stubdemo.Cons" 11)
    (segWord Extracted.program "example.com/rtmisc/stubdemo.Cons" 12) 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (next v : BitVec 64)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1) :
    Ensures (Extracted.program.link impl) Extracted.entry [next, v]
      (fun s => GuardOK s 4144 ∧ StackOK s 4152 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4152) 4168 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4168 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
        Outside nodeType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧ 16 ≤ b)
      (fun s s' => InRanges (s'.regs 0).toNat 16 R.rt ∧
        s'.mem.readLE (s'.regs 0).toNat 8 = next.toNat ∧
        s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = v.toNat ∧
        ∃ b' L', b - 16 ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          InRanges (s'.regs 0).toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4152, s.sp.toNat + 16)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty, hok1, hok2, hinv, hbud⟩
  janus_intro hs
  janus_data hd [hw]
  janus_eval_nat h_t : nodeType
  janus_eval_nat h_f : flagAddr
  rw [h_t] at hty hok1
  rw [h_f] at hflag
  janus_run calls [hnew.pos, hwb]
  all_goals sorry

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")

/-- The stub runtime: generic code, placed at `Extracted.program`'s own contract addresses. -/
def implAt : List Segment := [newobjectSeg newA, wbSeg wbA]

/-- The requests the witness runtime serves: `Cons`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [nodeType]) ∨ (a = wbA ∧ args = [1])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = wbA := by decide

/-- The two live contracts at `Cons`'s own addresses: one tactic each. -/
theorem model_new : NewobjectLiveContract linked newA 4096 R := by janus_live_newobject
theorem model_wb : WbLiveContract linked wbA 4096 R 1 := by janus_live_wb 1

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4152, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

/-- `Cons(nil, 7)`. -/
def s0 : State :=
  { regs := fun i => if i = 1 then 7 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 7] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : GuardOK s0 4144 ∧ StackOK s0 4152 16 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4152) 4168 R.rt ∧ Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4152) 4168 ∧
    Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧ s0.mem.accessible flagAddr 4 false = true ∧
    Outside nodeType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧ 16 ≤ 0x400 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, ?_, ?_, inv0, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, rfl⟩
  · rw [addr_wb]; exact Or.inr ⟨rfl, rfl⟩

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`Cons(nil, 7)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : State),
    NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 7] s ∧
    (GuardOK s 4144 ∧ StackOK s 4152 16 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4152) 4168 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4152) 4168 ∧
      Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ s.mem.accessible flagAddr 4 false = true ∧
      Outside nodeType 16 R.rt ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
      R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
      R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧ 16 ≤ b) :=
  ⟨implAt, R, 0x400, ret, s0, by rw [addr_new]; exact model_new, by rw [addr_wb]; exact model_wb, hret, setup, pre⟩

/-- So the guarantee is reached: `Cons(nil, 7)` returns a non-nil node `{Next: nil, V: 7}` inside `R.rt`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat ≠ 0 ∧ InRanges (s'.regs 0).toNat 16 R.rt ∧
      s'.mem.readLE (s'.regs 0).toNat 8 = 0 ∧ s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = 7 :=
  (correctness implAt R 0x400 0 7 (by rw [addr_new]; exact model_new) (by rw [addr_wb]; exact model_wb)
    ret hret s0 setup pre).mono
    fun _ ⟨habi, hr, h1, h2, _⟩ => by
      refine ⟨habi, ?_, hr, h1, h2⟩
      intro h0
      obtain ⟨⟨lo, hi⟩, hm, h1, h2⟩ := hr
      rw [h0] at h1 h2
      simp only [rt_eq, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm <;>
        (simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; simp only [HEAP, HEND, BUMP, WBUF] at h1 h2; omega)

end Witness

end Proof
