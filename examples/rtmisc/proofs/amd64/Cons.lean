import Extracted

/-!
# `Cons(next *Node, v uint64) *Node`: one allocation and one pointer store (amd64)

```go
type Node struct{ Next *Node; V uint64 }
func Cons(next *Node, v uint64) *Node { return &Node{Next: next, V: v} }
```

The amd64 twin of `arm64/Cons.lean`: `runtime.newobject` allocates the node, `runtime.gcWriteBarrier1`
is the barrier of the store of `next`. The **Witness** uses the generic stub runtime of
`Janus.Contracts.LiveStubAmd64` (`newobjectSeg`, `wbSeg`, `janus64_live_newobject`,
`janus64_live_wb`), placed at `Extracted.program`'s own contract addresses.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor `Cons` passes to `newobject` (the RIP-relative `LEAQ` at `Cons+0x18`) and the
address of the write-barrier flag (the `CMPL` at `Cons+0x25`), recomputed from the extracted code. -/
def nodeType : Nat := ripTarget Extracted.program (Extracted.entry + 0x18)
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x25)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (next v : BitVec 64)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1) :
    Ensures (Extracted.program.link impl) Extracted.entry [next, v]
      (fun s => StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4152 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧ 16 ≤ b)
      (fun s s' => InRanges (s'.regs 0).toNat 16 R.rt ∧
        s'.mem.readLE (s'.regs 0).toNat 8 = next.toNat ∧
        s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = v.toNat ∧
        ∃ b' L', b - 16 ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          InRanges (s'.regs 0).toNat 16 L' ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty, hok1, hok2, hinv, hbud⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  janus64_data hd [hw]
  janus_eval_nat h_t : nodeType
  janus_eval_nat h_f : flagAddr
  rw [h_t] at hty hok1
  rw [h_f] at hflag
  janus64_run calls [hnew.pos, hwb]
  all_goals janus_split_and
  all_goals first
    | janus_frame
    | (janus_clear_irrel; omega; done)
    | skip
  all_goals (try janus64_simp)
  all_goals refine ⟨by assumption, b - 16, ?_, by omega, ?_, ?_, ?_⟩
  any_goals (first | exact InRanges.cons_head [] (Nat.le_refl _) (Nat.le_refl _) | skip)
  all_goals first | janus_live | janus_frame

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")

def implAt : List Amd64.Segment := [newobjectSeg newA, wbSeg wbA]

/-- The requests the witness runtime serves: `Cons`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [nodeType]) ∨ (a = wbA ∧ args = [1])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = wbA := by decide

theorem model_new : NewobjectLiveContract64 linked newA 4096 R := by janus64_live_newobject
theorem model_wb : WbLiveContract64 linked wbA 4096 R 1 := by janus64_live_wb 1

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The bump cell holds `HEAP`; the return address `ret = 0x1000` is at `[RSP]`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4128, 4152, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 3 then 7 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 7] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
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

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : StackGuardOK s0 4128 ∧ StackWritable s0 4128 24 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4128) 4152 R.rt ∧
    Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4128) 4152 ∧ Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
    s0.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧ 16 ≤ 0x400 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, ?_, ?_, inv0, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, rfl⟩
  · rw [addr_wb]; exact Or.inr ⟨rfl, rfl⟩

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`Cons(nil, 7)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : Amd64.State),
    NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 7] s ∧
    (StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
      Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 4).toNat - 4128) 4152 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4152 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      s.mem.accessible flagAddr 4 false = true ∧ Outside nodeType 16 R.rt ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [nodeType] ∧
      R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
      R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧ 16 ≤ b) :=
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
