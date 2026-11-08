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
  | none => if a = BUMP then 0x30 else if a = BUMP + 3 then 0x10 else if a = srcP then 0x55 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4152, 4224, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

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

/-! ### The call-site states of the three runtime contracts -/

/-- A call state at the runtime entry `addr` (words `x, y, z` in `X0, X1, X2`), in the witness's world:
the stack, the heap and the invariant are those of `s0`. -/
def callS (addr x y z : Nat) : State :=
  { s0 with
    pc := BitVec.ofNat 64 addr
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 1 then BitVec.ofNat 64 y
      else if i = 2 then BitVec.ofNat 64 z else s0.regs i }

theorem cs_sp (a x y z : Nat) : (callS a x y z).sp.toNat = sp0 := by rfl
theorem cs_g (a x y z : Nat) : ((callS a x y z).regs 28).toNat = g0 := by rfl
theorem cs_x30 (a x y z : Nat) : ((callS a x y z).regs 30).toNat = ret := by rfl
theorem cs_mem (a x y z : Nat) : (callS a x y z).mem = mem0 := rfl

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 5) : CallOK (callS a x y z) 4096 n := by
  have hw : mem0.accessible (sp0 - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  simp only [CallOK, cs_x30, cs_sp, cs_mem]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by first | decide | (unfold sp0; omega), ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_room (a x y z n : Nat) (hn : n ≤ 5) : StackRoom (callS a x y z) 4096 n := by
  simp only [StackRoom, GuardOK, cs_g, cs_sp, cs_mem, calleeStack]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, sp0, g0]
  omega

theorem cs_eqpre (a x y z n : Nat) (hn : n ≤ 5) : Mem.EqPre 4096 n (callS a x y z) :=
  ⟨(guardOK_iff _ _).1 (cs_room a x y z n hn).1, cs_callOK a x y z n hn, (cs_room a x y z n hn).2⟩

theorem cs_winL (a x y z n : Nat) (hn : n ≤ 5) : LiveSep liveL (calleeStack (callS a x y z) 4096 n) := by
  intro r hr
  simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [calleeStack, cs_sp, outside_cons, outside_nil, and_true, sp0]
  rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 5) : LiveSep (calleeStack (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [calleeStack, cs_sp, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with rfl | rfl <;>
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega

def sMv : State := callS mvA dstP srcP 8
def sMk : State := callS mkA u64Type 2 2
def sWb : State := callS wbA 0 0 0

@[reducible] def mvSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  Mem.EqPre 4096 3 s ∧
  LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
  Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
  LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat

theorem site_mv : mvSite R mvA liveL 0x100 sMv := by
  refine ⟨cs_eqpre _ _ _ _ 3 (by omega), ⟨?_, ?_, cs_winL _ _ _ _ 3 (by omega), cs_winR _ _ _ _ 3 (by omega)⟩,
    ⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_, ?_⟩⟩
  · exact Or.inl ⟨rfl, dstP, srcP, rfl⟩
  · exact inv0
  · show Outside srcP 8 (calleeStack sMv 4096 3)
    simp only [calleeStack, sMv, cs_sp, outside_cons, outside_nil, and_true, srcP, HEAP, sp0]; omega
  · show Outside dstP 8 (calleeStack sMv 4096 3)
    simp only [calleeStack, sMv, cs_sp, outside_cons, outside_nil, and_true, dstP, HEAP, sp0]; omega
  · exact Or.inl ⟨(dstP, dstP + 8), by simp [liveL], by decide, by decide⟩

@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
      (s.regs 28).toNat s.mem (calleeStack s 4096 3)

theorem site_mk : mkSite R mkA liveL 0x100 sMk := by
  refine ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide⟩,
    cs_room _ _ _ _ 3 (by omega), ?_, inv0, by decide, cs_winL _ _ _ _ 3 (by omega), cs_winR _ _ _ _ 3 (by omega)⟩
  exact Or.inr (Or.inl ⟨rfl, by decide⟩)

@[reducible] def wbSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK s 4096 0 ∧ R.ok addr [2] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    LiveSep L [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] R.rt

theorem site_wb : wbSite R wbA liveL 0x100 sWb := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, ?_, ?_⟩
  · intro r hr
    simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [sWb, cs_sp, outside_cons, outside_nil, and_true, sp0]
    rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega
  · intro x hx
    simp only [sWb, cs_sp, List.mem_singleton] at hx
    subst hx
    rw [rt_eq]
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF]
    omega

/-- The returning run, exactly as `correctness` states it at the witness. -/
theorem returnsF : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Post R 0x100 (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s0 s' :=
  correctness implAt R 0x100 liveL (BitVec.ofNat 64 dstP) 1 1 (BitVec.ofNat 64 srcP) 1 1 (BitVec.ofNat 64 bxP) 2
    (by rw [addr_mv]; exact model_mv) (by rw [addr_mk]; exact model_mk)
    (by rw [addr_wb]; exact model_wb) ret hret s0 setup pre

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a live set, a budget and a
call of `Chain(dst, src, bx, 2)` (one-word slices) satisfying the precondition; a call-site state for each
of the three contracts; and the returning run. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State),
    MemmoveLive (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1,
      BitVec.ofNat 64 srcP, 1, 1, BitVec.ofNat 64 bxP, 2] s ∧
    Pre R b L (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Post R b (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s s' :=
  ⟨implAt, R, 0x100, liveL, ret, s0, by rw [addr_mv]; exact model_mv, by rw [addr_mk]; exact model_mk,
    by rw [addr_wb]; exact model_wb, hret, setup, pre,
    ⟨liveL, 0x100, sMv, by rw [addr_mv]; rfl, by rw [addr_mv]; exact site_mv⟩,
    ⟨liveL, 0x100, sMk, by rw [addr_mk]; rfl, by rw [addr_mk]; exact site_mk⟩,
    ⟨liveL, 0x100, sWb, by rw [addr_wb]; rfl, by rw [addr_wb]; exact site_wb⟩, returnsF⟩

/-- So the guarantee is reached: `Chain(dst, src, bx, 2)` stores a fresh array `t` (apart from the three
caller objects) in `bx.P` and `2` in `bx.N`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ ∃ t : Nat, s'.mem.readLE bxP 8 = t ∧ s'.mem.readLE (bxP + 8) 8 = 2 ∧
      Apart t 16 dstP 8 ∧ Apart t 16 srcP 8 ∧ Apart t 16 bxP 16 :=
  returnsF.mono
    fun _ ⟨habi, t, h1, h2, h3, h4, h5, h6, _⟩ => by
      have hbs : blockSize (8 * (2 : BitVec 64).toNat) true = 16 := by decide
      rw [hbs] at h3 h4 h5 h6
      exact ⟨habi, t, h1, h2, h4, h5, h6⟩

end ChainArm.Witness
