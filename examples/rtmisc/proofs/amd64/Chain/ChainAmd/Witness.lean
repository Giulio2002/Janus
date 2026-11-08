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
  | none => if a = BUMP then 0x30 else if a = BUMP + 3 then 0x10 else if a = srcP then 0x55
    else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4144, 4216, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

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

/-! ### The call-site states of the three runtime contracts -/

/-- A call state at the runtime entry `a` (words `x, y, z` in `RAX, RBX, RCX`), in the witness's world:
the stack, the heap and the invariant are those of `s0`. -/
def callS (addr x y z : Nat) : Amd64.State :=
  { s0 with
    rip := BitVec.ofNat 64 addr
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 3 then BitVec.ofNat 64 y
      else if i = 1 then BitVec.ofNat 64 z else s0.regs i }

theorem cs_rsp (a x y z : Nat) : ((callS a x y z).regs 4).toNat = sp0 := by rfl
theorem cs_g (a x y z : Nat) : ((callS a x y z).regs 14).toNat = g0 := by rfl
theorem cs_mem (a x y z : Nat) : (callS a x y z).mem = mem0 := rfl

theorem cs_callOK (a x y z n : Nat) (hn : n ≤ 5) : CallOK64 (callS a x y z) 4096 n := by
  have hw : mem0.accessible (sp0 - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  have h1 : mem0.readLE sp0 8 < 2 ^ 47 := by decide
  simp only [CallOK64, cs_rsp, cs_mem]
  refine ⟨h1, by first | decide | (unfold sp0; omega), by first | decide | (unfold sp0; omega),
    by first | decide | (unfold sp0; omega), ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem cs_room (a x y z n : Nat) (hn : n ≤ 5) : StackRoom64 (callS a x y z) 4096 n := by
  simp only [StackRoom64, GuardOK64, cs_g, cs_rsp, cs_mem, calleeStack64]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, sp0, g0]
  omega

theorem cs_eqpre (a x y z n : Nat) (hn : n ≤ 5) : MemPre64 4096 n (callS a x y z) := by
  have hw : mem0.accessible (sp0 - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, cs_g, cs_mem]; decide
  · simp only [regG, stackguard0Offset, cs_g, cs_mem]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, cs_g, cs_rsp, cs_mem]; decide
  · simp only [cs_rsp, cs_mem]; decide
  · simp only [cs_rsp]; decide
  · simp only [cs_rsp]; simp [sp0]; omega
  · simp only [cs_rsp, cs_mem]
    exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)
  · rfl
  · rfl
  · simp only [cs_rsp, cs_mem]; decide
  · simp only [cs_g, cs_rsp, MemAmd64.calleeStack, MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    simp only [sp0, g0]
    omega

theorem cs_winL (a x y z n : Nat) (hn : n ≤ 5) : LiveSep liveL (liveWin64 (callS a x y z) 4096 n) := by
  intro r hr
  simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [liveWin64, calleeStack64, cs_rsp, List.cons_append, List.nil_append, outside_cons, outside_nil,
    and_true, sp0]
  rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega

theorem cs_winR (a x y z n : Nat) (hn : n ≤ 5) : LiveSep (liveWin64 (callS a x y z) 4096 n) R.rt := by
  intro x' hx
  simp only [liveWin64, calleeStack64, cs_rsp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rw [rt_eq]
  rcases hx with (rfl | rfl) | rfl <;>
    simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega

def sMv : Amd64.State := callS mvA dstP srcP 8
def sMk : Amd64.State := callS mkA u64Type 2 2
def sWb : Amd64.State := callS wbA 0 0 0

@[reducible] def mvSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  MemPre64 4096 3 s ∧
  LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3) ∧
  MemAmd64.Input s 4096 3 (s.regs 3).toNat (s.regs 1).toNat ∧
  LiveDest64 R L s 4096 3 (s.regs 0).toNat (s.regs 1).toNat

theorem site_mv : mvSite R mvA liveL 0x100 sMv := by
  refine ⟨cs_eqpre _ _ _ _ 3 (by omega), ⟨?_, ?_, cs_winL _ _ _ _ 3 (by omega), cs_winR _ _ _ _ 3 (by omega)⟩,
    ⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_, ?_, ?_⟩⟩
  · exact Or.inl ⟨rfl, dstP, srcP, rfl⟩
  · exact inv0
  · simp only [sMv, MemAmd64.calleeStack, MapAmd64.calleeStack, cs_rsp, outside_cons, outside_nil, and_true]
    show (srcP + 8 ≤ sp0 - 4096 ∨ sp0 ≤ srcP) ∧ (srcP + 8 ≤ sp0 + 8 ∨ sp0 + 8 + 8 * 3 ≤ srcP)
    simp only [srcP, HEAP, sp0]; omega
  · show Outside dstP 8 (calleeStack64 sMv 4096 3)
    simp only [calleeStack64, sMv, cs_rsp, outside_cons, outside_nil, and_true, dstP, HEAP, sp0]; omega
  · exact Or.inl ⟨(dstP, dstP + 8), by simp [liveL], by decide, by decide⟩
  · show Outside dstP 8 [(((sMv).regs 4).toNat, ((sMv).regs 4).toNat + 8)]
    simp only [sMv, cs_rsp, outside_cons, outside_nil, and_true, dstP, HEAP, sp0]; omega

@[reducible] def mkSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
    LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
      (s.regs 14).toNat s.mem (liveWin64 s 4096 3)

theorem site_mk : mkSite R mkA liveL 0x100 sMk := by
  refine ⟨⟨cs_callOK _ _ _ _ 3 (by omega), ?_, by decide, by decide, by decide⟩, cs_room _ _ _ _ 3 (by omega),
    ?_, ?_, by decide, cs_winL _ _ _ _ 3 (by omega), cs_winR _ _ _ _ 3 (by omega)⟩
  · exact ⟨by decide, by decide⟩
  · exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  · exact inv0

@[reducible] def wbSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  CallOK64 s 4096 0 ∧ R.ok addr [2] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    LiveSep L [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] ∧
    LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] R.rt

theorem site_wb : wbSite R wbA liveL 0x100 sWb := by
  refine ⟨cs_callOK _ _ _ _ 0 (by omega), Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, ?_, ?_⟩
  · intro r hr
    simp only [liveL, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [sWb, cs_rsp, outside_cons, outside_nil, and_true, sp0]
    rcases hr with rfl | rfl | rfl <;> simp only [dstP, srcP, bxP, HEAP] <;> omega
  · intro x hx
    simp only [sWb, cs_rsp, List.mem_singleton] at hx
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
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : Amd64.State),
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MakesliceLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 dstP, 1, 1,
      BitVec.ofNat 64 srcP, 1, 1, BitVec.ofNat 64 bxP, 2] s ∧
    Pre R b L (BitVec.ofNat 64 dstP) 1 (BitVec.ofNat 64 srcP) 1 (BitVec.ofNat 64 bxP) 2 s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
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

end ChainAmd.Witness
