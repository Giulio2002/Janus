import ThreeArm.Main

/-!
# `Three` (arm64): non-vacuity witness

A concrete runtime (the bump-allocator toy of `Janus.Contracts.LiveToy`, with code for `makeslice`,
`newobject` and `gcWriteBarrier2`) and a call state of `Three(2, 7)` that satisfy every hypothesis of
`ThreeArm.correctness`; `returns` instantiates the theorem.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open ThreeArm

namespace ThreeArm.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat

def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

def implAt : List Segment :=
  [{ name := "witness.makeslice", base := mkA, words := makesliceCodeD },
   { name := "witness.newobject", base := newA, words := newobjectCodeD },
   { name := "witness.gcWriteBarrier2", base := wbA, words := wbCode }]

/-- The requests the witness runtime serves: `Three(2, 7)`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = mkA ∧ args = [u64Type, 2, 2]) ∨ (a = newA ∧ args = [cellType]) ∨ (a = wbA ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbA := by decide


set_option maxRecDepth 20000 in
theorem model_mk : MakesliceLiveContract linked mkA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet linked _ s _
  janus_run
  exact finish_makesliceD (tys := []) (by intro t ht; simp at ht) pre

set_option maxRecDepth 20000 in
theorem model_new : NewobjectLiveContract linked newA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet linked _ s _
  janus_run
  exact finish_newobjectD (tys := []) (by intro t ht; simp at ht) pre

set_option maxRecDepth 20000 in
theorem model_wb : WbLiveContract linked wbA 4096 R 2 := by
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  change ReachesRet linked _ s _
  janus_run
  have h := wb_post (tys := []) (ok := ok) (by intro t ht; simp at ht) (n := 2) (b := b) (L := L) (s := s) (by omega) pre.2.2.1 pre.2.2.2.2
  simp only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true, show 8 * 2 = 16 from rfl] at h
  exact h


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
  | none => if a = BUMP + 2 then 0x50 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4168, 4192, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 2 else if i = 1 then 7 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [2, 7] s0 :=
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

theorem pre : Pre R 0x400 2 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, ?_, by decide, by decide, ?_, ?_, ?_, inv0, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_mk]; exact Or.inl ⟨rfl, by decide⟩
  · rw [addr_new]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [addr_wb]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)


/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`Three(2, 7)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : State),
    MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [2, 7] s ∧
    Pre R b 2 s :=
  ⟨implAt, R, 0x400, ret, s0, by rw [addr_mk]; exact model_mk, by rw [addr_new]; exact model_new,
    by rw [addr_wb]; exact model_wb, hret, setup, pre⟩

/-- So the guarantee is reached: `Three(2, 7)` returns three disjoint objects, `A[0] = 7`, `C.P = &B[0]`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 3).toNat = pb ∧ (s'.regs 6).toNat = pc ∧
      s'.mem.readLE pa 8 = 7 ∧ s'.mem.readLE pc 8 = pb ∧
      Apart pa 16 pb 16 ∧ Apart pa 16 pc 16 ∧ Apart pb 16 pc 16 :=
  (correctness implAt R 0x400 2 7 (by rw [addr_mk]; exact model_mk) (by rw [addr_new]; exact model_new)
    (by rw [addr_wb]; exact model_wb) ret hret s0 setup pre).mono
    fun _ ⟨habi, pa, pb, pc, h0, h3, h6, _, _, _, _, _, _, _, hab, hac, hbc, hA, hC, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at hab hac hbc
      exact ⟨habi, pa, pb, pc, h0, h3, h6, hA, hC, hab, hac, hbc⟩

end ThreeArm.Witness
