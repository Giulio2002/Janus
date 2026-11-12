import ThreeAmd.Main

/-!
# `Three` (amd64): non-vacuity witness

A concrete runtime (the bump-allocator toy of `Janus.Contracts.LiveToy`, with x86-64 code for
`makeslice`, `newobject` and `gcWriteBarrier2`) and a call state of `Three(2, 7)` that satisfy every
hypothesis of `ThreeAmd.correctness`; `returns` instantiates the theorem.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open ThreeAmd

namespace ThreeAmd.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64
open Janus.Contracts.LiveSat (bump_acc)

def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

def implAt : List Amd64.Segment :=
  [{ name := "witness.makeslice", base := mkA, bytes := makesliceCodeD },
   { name := "witness.newobject", base := newA, bytes := newobjectCodeD },
   { name := "witness.gcWriteBarrier2", base := wbA, bytes := wbCode }]

/-- The requests the witness runtime serves: `Three(2, 7)`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = mkA ∧ args = [u64Type, 2, 2]) ∨ (a = newA ∧ args = [cellType]) ∨ (a = wbA ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbA := by decide

set_option maxRecDepth 20000 in
theorem model_mk : MakesliceLiveContract64 linked mkA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hap := bump_apart64 pre.2.2.2.2.2.2
  change ReachesRet linked _ s _
  janus64_run
  exact finish_makesliceD (tys := []) (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
    (by simp [setRegF, BUMP]) (by simp [BUMP]) pre

set_option maxRecDepth 20000 in
theorem model_new : NewobjectLiveContract64 linked newA 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hWs := pre.2.2.2.2.2.2
  have hret : Outside (s.regs 4).toNat 8 (toyRt []) := by
    have h := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
    simp only [Nat.add_sub_cancel_left] at h
    exact h
  have hap : Apart 4194304 8 (s.regs 4).toNat 8 := ((inRanges_bump []).apart hret).symm
  change ReachesRet linked _ s _
  janus64_run
  exact finish_newobjectD (tys := []) (by intro t ht; simp at ht) _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
    (by simp [setRegF, BUMP]) (by simp [BUMP]) pre

set_option maxRecDepth 20000 in
theorem model_wb : WbLiveContract64 linked wbA 4096 R 2 := by
  intro L b s hpc pre
  have ⟨hra, hal, h3, h4, h5⟩ := pre.1
  change ReachesRet linked _ s _
  janus64_run
  exact wb_post64 (tys := []) (ok := ok) (by intro t ht; simp at ht) (by omega) pre.2.2.1 pre.2.2.2.2
    (by simp [retAddrOf])
    (by intro i; simp only [setRegF]; by_cases h4 : i = 4 <;> by_cases h11 : i = 11 <;> simp [h4, h11])
    (by simp) rfl rfl (by simp) rfl rfl rfl

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
  ⟨bytes0, [⟨sp0 - 4152, 4176, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then 2 else if i = 3 then 7 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [2, 7] s0 :=
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

theorem pre : Pre R 0x400 2 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
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

/-- A call state at the runtime entry `addr` (words `x, y, z` in `RAX, RBX, RCX`), in the witness's world:
the heap and the invariant are those of `s0`; the callee's frame lies just below the caller's. -/
def callS (addr x y z : Nat) : Amd64.State :=
  { s0 with
    rip := BitVec.ofNat 64 addr
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 3 then BitVec.ofNat 64 y
      else if i = 1 then BitVec.ofNat 64 z else if i = 4 then BitVec.ofNat 64 (sp0 - 16) else s0.regs i }

theorem cs_rsp (a x y z : Nat) : ((callS a x y z).regs 4).toNat = sp0 - 16 := by rfl
theorem cs_g (a x y z : Nat) : ((callS a x y z).regs 14).toNat = g0 := by rfl
theorem cs_mem (a x y z : Nat) : (callS a x y z).mem = mem0 := rfl

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 3) : CallOK64 (callS a x y z) 4096 n := by
  have hw : mem0.accessible (sp0 - 16 - 4096) (4096 + 8 + 8 * 3) true = true := by decide
  have h1 : mem0.readLE (sp0 - 16) 8 < 2 ^ 47 := by decide
  simp only [CallOK64, cs_rsp, cs_mem]
  refine ⟨h1, by first | decide | (unfold sp0; omega), by first | decide | (unfold sp0; omega),
    by first | decide | (unfold sp0; omega), ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_room (a x y z n : Nat) (hn : n ≤ 3) : StackRoom64 (callS a x y z) 4096 n := by
  simp only [StackRoom64, GuardOK64, cs_g, cs_rsp, cs_mem, calleeStack64]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, sp0, g0]
  omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 3) : LiveSep (liveWin64 (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [liveWin64, calleeStack64, cs_rsp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with (rfl | rfl) | rfl <;>
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega

def sMk : Amd64.State := callS mkA u64Type 2 2
def sNew : Amd64.State := callS newA cellType 0 0
def sWb : Amd64.State := callS wbA 0 0 0

@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
      (s.regs 14).toNat s.mem (liveWin64 s 4096 3)

theorem site_mk : mkSite R mkA [] 0x400 sMk := by
  refine ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, (by simp only [calleeStack64, outside_cons, outside_nil]; decide)⟩,
    cs_room _ _ _ _ 3 (by omega), ?_, inv0, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 3 (by omega)⟩
  exact Or.inl ⟨rfl, by decide⟩

@[reducible] def newSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  NewobjectPre64 4096 s ∧ StackRoom64 s 4096 1 ∧
    LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 1)

theorem site_new : newSite R newA [] 0x400 sNew := by
  refine ⟨⟨cs_callOK _ _ _ _ 1 (by omega), ⟨by decide, by decide⟩, (by simp only [calleeStack64, outside_cons, outside_nil]; decide)⟩,
    cs_room _ _ _ _ 1 (by omega), ?_, inv0, by decide, fun r hr => absurd hr (by simp), cs_winR _ _ _ _ 1 (by omega)⟩
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

@[reducible] def wbSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  CallOK64 s 4096 0 ∧ R.ok addr [2] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] ∧
    LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] R.rt

theorem site_wb : wbSite R wbA [] 0x400 sWb := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, fun r hr => absurd hr (by simp), ?_⟩
  intro x hx
  simp only [sWb, cs_rsp, List.mem_singleton] at hx
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
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (ret : Nat) (s : Amd64.State),
    MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [2, 7] s ∧
    Pre R b 2 s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      newSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R 2 7 s s' :=
  ⟨implAt, R, 0x400, ret, s0, by rw [addr_mk]; exact model_mk, by rw [addr_new]; exact model_new,
    by rw [addr_wb]; exact model_wb, hret, setup, pre,
    ⟨[], 0x400, sMk, by rw [addr_mk]; rfl, by rw [addr_mk]; exact site_mk⟩,
    ⟨[], 0x400, sNew, by rw [addr_new]; rfl, by rw [addr_new]; exact site_new⟩,
    ⟨[], 0x400, sWb, by rw [addr_wb]; rfl, by rw [addr_wb]; exact site_wb⟩, returnsF⟩

/-- So the guarantee is reached: `Three(2, 7)` returns three disjoint objects, `A[0] = 7`, `C.P = &B[0]`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ pa pb pc : Nat, (s'.regs 0).toNat = pa ∧ (s'.regs 7).toNat = pb ∧ (s'.regs 9).toNat = pc ∧
      s'.mem.readLE pa 8 = 7 ∧ s'.mem.readLE pc 8 = pb ∧
      Apart pa 16 pb 16 ∧ Apart pa 16 pc 16 ∧ Apart pb 16 pc 16 :=
  returnsF.mono
    fun _ ⟨habi, pa, pb, pc, h0, h3, h6, _, _, _, _, _, _, _, hab, hac, hbc, hA, hC, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at hab hac hbc
      exact ⟨habi, pa, pb, pc, h0, h3, h6, hA, hC, hab, hac, hbc⟩

end ThreeAmd.Witness
