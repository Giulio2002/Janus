import ChainAmd.Main

/-!
# `Chain` (amd64): non-vacuity witness

A concrete runtime (the bump-allocator toy of `Janus.Contracts.LiveToy`, with x86-64 code for
`memmove` (8 bytes), `makeslice` and `gcWriteBarrier2`) and a call state of `Chain(dst, src, bx, 2)`
with one-word slices that satisfy every hypothesis of `ChainAmd.correctness`; `returns` instantiates
the theorem.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open ChainAmd

namespace ChainAmd.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64
open Janus.Contracts.LiveSat (bump_acc)

def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def mkA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.makeslice")
def wbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

def implAt : List Amd64.Segment :=
  [{ name := "witness.memmove", base := mvA, bytes := memmoveCode },
   { name := "witness.makeslice", base := mkA, bytes := makesliceCodeD },
   { name := "witness.gcWriteBarrier2", base := wbA, bytes := wbCode }]

/-- The caller's objects: `dst` (8 bytes), `src` (8 bytes), `bx` (16 bytes), in the heap. -/
def dstP : Nat := HEAP
def srcP : Nat := HEAP + 0x10
def bxP : Nat := HEAP + 0x20
def liveL : List (Nat × Nat) := [(dstP, dstP + 8), (srcP, srcP + 8), (bxP, bxP + 16)]

/-- The requests the witness runtime serves: `Chain(dst, src, bx, 2)` with one-word slices. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = mvA ∧ ∃ d sr, args = [d, sr, 8]) ∨ (a = mkA ∧ args = [u64Type, 2, 2]) ∨ (a = wbA ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_mk : Extracted.program.contractAddr "runtime.makeslice" = mkA := by decide
theorem addr_wb : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbA := by decide

set_option maxRecDepth 20000 in
theorem model_mv : MemmoveLive64 linked mvA 4096 R := by
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  have h8 : (s.regs 1).toNat = 8 := by
    rcases hLm.1 with ⟨_, d, sr, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · simp only [List.cons.injEq, and_true] at h; exact h.2.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  rw [h8] at hs2 hd2
  rw [h8] at hd4 hd5
  have hap : Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  change ReachesRet linked _ s _
  janus64_run
  rw [h8]
  refine liveMemRet_store64 (v := s.mem.readLE (s.regs 3).toNat 8) (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

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

/-- The bump cell holds `HEAP + 0x30` (past the three caller objects); `src[0] = 0x55`; the return
address `ret = 0x1000` is at `[RSP]`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP then 0x30 else if a = BUMP + 2 then 0x50 else if a = srcP then 0x55
    else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4144, 4216, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, 0x10000, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 dstP else if i = 3 then 1 else if i = 1 then 1
      else if i = 7 then BitVec.ofNat 64 srcP else if i = 6 then 1 else if i = 8 then 1
      else if i = 9 then BitVec.ofNat 64 bxP else if i = 10 then 2 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1, BitVec.ofNat 64 srcP, 1, 1,
    BitVec.ofNat 64 bxP, 2] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    match i, h with
    | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl,
    rfl⟩

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

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP + 0x30 := by decide

theorem inv0 : R.inv 0x100 liveL (s0.regs 14).toNat (view R.rt liveL s0.mem) := by
  refine toyInv_init_live (m := mem0) (g := (s0.regs 14).toNat) (p0 := HEAP + 0x30) (by decide) (by decide) (by decide)
    (by intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega)
    bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [BUMP, HEAP] at *; omega),
    if_neg (by simp only [srcP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : Pre R 0x100 liveL (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s0 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, inv0, ?_,
    ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_mk]; exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  · rw [addr_wb]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [addr_mv]; exact Or.inl ⟨rfl, dstP, srcP, rfl⟩
  · intro t; rw [addr_mv]; exact Or.inl ⟨rfl, t, srcP, rfl⟩
  · intro r hr; simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [Outside, outside_cons, outside_nil, and_true] <;> decide
  · exact ⟨(dstP, dstP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(srcP, srcP + 8), by simp [liveL], by decide, by decide⟩
  · exact ⟨(bxP, bxP + 16), by simp [liveL], by decide, by decide⟩
  all_goals (simp only [Apart]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a live set, a budget and a
call of `Chain(dst, src, bx, 2)` (one-word slices) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : Amd64.State),
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
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

end ChainAmd.Witness
