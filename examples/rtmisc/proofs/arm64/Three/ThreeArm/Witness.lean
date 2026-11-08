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
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4168, 4192, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

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


/-! ### The call-site states of the three runtime contracts -/

/-- A call state at the runtime entry `addr` (words `x, y, z` in `X0, X1, X2`), in the witness's world:
the heap and the invariant are those of `s0`; the callee's frame lies just below the caller's. -/
def callS (addr x y z : Nat) : State :=
  { s0 with
    pc := BitVec.ofNat 64 addr
    sp := BitVec.ofNat 64 (sp0 - 16)
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 1 then BitVec.ofNat 64 y
      else if i = 2 then BitVec.ofNat 64 z else s0.regs i }

theorem cs_sp (a x y z : Nat) : (callS a x y z).sp.toNat = sp0 - 16 := by rfl
theorem cs_g (a x y z : Nat) : ((callS a x y z).regs 28).toNat = g0 := by rfl
theorem cs_x30 (a x y z : Nat) : ((callS a x y z).regs 30).toNat = ret := by rfl
theorem cs_mem (a x y z : Nat) : (callS a x y z).mem = mem0 := rfl

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 3) : CallOK (callS a x y z) 4096 n := by
  have hw : mem0.accessible (sp0 - 16 - 4096) (4096 + 8 + 8 * 3) true = true := by decide
  simp only [CallOK, cs_x30, cs_sp, cs_mem]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by first | decide | (unfold sp0; omega), ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_room (a x y z n : Nat) (hn : n ≤ 3) : StackRoom (callS a x y z) 4096 n := by
  simp only [StackRoom, GuardOK, cs_g, cs_sp, cs_mem, calleeStack]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, sp0, g0]
  omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 3) : LiveSep (calleeStack (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [calleeStack, cs_sp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega

def sMk : State := callS mkA u64Type 2 2
def sNew : State := callS newA cellType 0 0
def sWb : State := callS wbA 0 0 0

@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
      (s.regs 28).toNat s.mem (calleeStack s 4096 3)

theorem site_mk : mkSite R mkA [] 0x400 sMk := by
  refine ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide⟩,
    cs_room _ _ _ _ 3 (by omega), ?_, inv0, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 3 (by omega)⟩
  exact Or.inl ⟨rfl, by decide⟩

@[reducible] def newSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1)

theorem site_new : newSite R newA [] 0x400 sNew := by
  refine ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ⟨by decide, by decide⟩, by decide⟩,
    cs_room _ _ _ _ 1 (by omega), ?_, inv0, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

@[reducible] def wbSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 0 ∧ R.ok addr [2] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] R.rt

theorem site_wb : wbSite R wbA [] 0x400 sWb := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, fun r hr => absurd hr (by simp), ?_⟩
  intro x hx
  simp only [sWb, cs_sp, List.mem_singleton] at hx
  subst hx
  rw [rt_eq]
  simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF]
  omega

/-- The returning run, exactly as `correctness` states it at the witness. -/
theorem returnsF : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R 2 7 s0 s' :=
  correctness implAt R 0x400 2 7 (by rw [addr_mk]; exact model_mk) (by rw [addr_new]; exact model_new)
    (by rw [addr_wb]; exact model_wb) ret hret s0 setup pre

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of
`Three(2, 7)` satisfying the precondition; a call-site state for each of the three contracts; and the
returning run. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : State),
    MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [2, 7] s ∧
    Pre R b 2 s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      newSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R 2 7 s s' :=
  ⟨implAt, R, 0x400, ret, s0, by rw [addr_mk]; exact model_mk, by rw [addr_new]; exact model_new,
    by rw [addr_wb]; exact model_wb, hret, setup, pre,
    ⟨[], 0x400, sMk, by rw [addr_mk]; rfl, by rw [addr_mk]; exact site_mk⟩,
    ⟨[], 0x400, sNew, by rw [addr_new]; rfl, by rw [addr_new]; exact site_new⟩,
    ⟨[], 0x400, sWb, by rw [addr_wb]; rfl, by rw [addr_wb]; exact site_wb⟩, returnsF⟩

/-- So the guarantee is reached: `Three(2, 7)` returns three disjoint objects, `A[0] = 7`, `C.P = &B[0]`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 3).toNat = pb ∧ (s'.regs 6).toNat = pc ∧
      s'.mem.readLE pa 8 = 7 ∧ s'.mem.readLE pc 8 = pb ∧
      Apart pa 16 pb 16 ∧ Apart pa 16 pc 16 ∧ Apart pb 16 pc 16 :=
  returnsF.mono
    fun _ ⟨habi, pa, pb, pc, h0, h3, h6, _, _, _, _, _, _, _, hab, hac, hbc, hA, hC, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at hab hac hbc
      exact ⟨habi, pa, pb, pc, h0, h3, h6, hA, hC, hab, hac, hbc⟩

end ThreeArm.Witness
