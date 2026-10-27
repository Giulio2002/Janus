import ChainArm.Main

/-!
# `Chain` (arm64): non-vacuity witness

A concrete runtime (the bump-allocator toy of `Janus.Contracts.LiveToy`, with RISC code for
`memmove` (8 bytes), `makeslice` and `gcWriteBarrier2`) and a call state of `Chain(dst, src, bx, 2)`
with one-word slices that satisfy every hypothesis of `ChainArm.correctness`; `returns` instantiates
the theorem.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open ChainArm

namespace ChainArm.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

def implAt : List Segment :=
  [{ name := "witness.memmove", base := mvA, words := memmoveCode },
   { name := "witness.makeslice", base := mkA, words := makesliceCodeD },
   { name := "witness.gcWriteBarrier2", base := wbA, words := wbCode }]

/-- The caller's objects: `dst` (8 bytes), `src` (8 bytes), `bx` (16 bytes), in the heap. -/
def dstP : Nat := HEAP
def srcP : Nat := HEAP + 0x10
def bxP : Nat := HEAP + 0x20
def liveL : List (Nat × Nat) := [(dstP, dstP + 8), (srcP, srcP + 8), (bxP, bxP + 16)]

/-- The requests the witness runtime serves: `Chain(dst, src, bx, 2)` with one-word slices. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = mvA ∧ ∃ d sr, args = [d, sr, 8]) ∨ (a = mkA ∧ args = [u64Type, 2, 2]) ∨ (a = wbA ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbA := by decide

set_option maxRecDepth 20000 in
theorem model_mv : MemmoveLive linked mvA 4096 R := by
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  have h8 : (s.regs 2).toNat = 8 := by
    rcases hLm.1 with ⟨_, d, sr, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · simp only [List.cons.injEq, and_true] at h; exact h.2.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  rw [h8] at hs2 hd2 hd4
  change ReachesRet linked _ s _
  janus_run
  rw [h8]
  refine liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

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

/-- The bump cell holds `HEAP + 0x30` (past the three caller objects); `src[0] = 0x55`. -/
def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP then 0x30 else if a = BUMP + 2 then 0x50 else if a = srcP then 0x55 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4152, 4224, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 dstP else if i = 1 then 1 else if i = 2 then 1
      else if i = 3 then BitVec.ofNat 64 srcP else if i = 4 then 1 else if i = 5 then 1
      else if i = 6 then BitVec.ofNat 64 bxP else if i = 7 then 2 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1, BitVec.ofNat 64 srcP, 1, 1,
    BitVec.ofNat 64 bxP, 2] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

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

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP + 0x30 := by decide

theorem inv0 : R.inv 0x100 liveL (s0.regs 28).toNat (view R.rt liveL s0.mem) := by
  refine toyInv_init_live (m := mem0) (g := (s0.regs 28).toNat) (p0 := HEAP + 0x30) (by decide) (by decide) (by decide)
    (by intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega)
    bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [BUMP, HEAP] at *; omega),
    if_neg (by simp only [srcP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : Pre R 0x100 liveL (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, inv0, ?_,
    ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_mk]; exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  · rw [addr_wb]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [addr_mv]; exact Or.inl ⟨rfl, dstP, srcP, by decide⟩
  · intro t; rw [addr_mv]; exact Or.inl ⟨rfl, t, srcP, rfl⟩
  · intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Outside, outside_cons, outside_nil, and_true] <;> decide
  · exact ⟨(dstP, dstP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(srcP, srcP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(bxP, bxP + 16), by simp [liveL], by decide, by decide⟩
  all_goals (simp only [Apart]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a live set, a budget and a
call of `Chain(dst, src, bx, 2)` (one-word slices) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State),
    MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1,
      BitVec.ofNat 64 srcP, 1, 1, BitVec.ofNat 64 bxP, 2] s ∧
    Pre R b L (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s :=
  ⟨implAt, R, 0x100, liveL, ret, s0, by rw [addr_mv]; exact model_mv, by rw [addr_mk]; exact model_mk,
    by rw [addr_wb]; exact model_wb, hret, setup, pre⟩

/-- So the guarantee is reached: `Chain(dst, src, bx, 2)` stores a fresh array `t` (apart from the three
caller objects) in `bx.P` and `2` in `bx.N`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ t : Nat, s'.mem.readLE bxP 8 = t ∧ s'.mem.readLE (bxP + 8) 8 = 2 ∧
      Apart t 16 dstP 8 ∧ Apart t 16 srcP 8 ∧ Apart t 16 bxP 16 :=
  (correctness implAt R 0x100 liveL (BitVec.ofNat 64 dstP) 1 1 (BitVec.ofNat 64 srcP) 1 1 (BitVec.ofNat 64 bxP) 2
    (by rw [addr_mv]; exact model_mv) (by rw [addr_mk]; exact model_mk)
    (by rw [addr_wb]; exact model_wb) ret hret s0 setup pre).mono
    fun _ ⟨habi, t, h1, h2, h3, h4, h5, h6, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at h3 h4 h5 h6
      exact ⟨habi, t, h1, h2, h4, h5, h6⟩

end ChainArm.Witness
