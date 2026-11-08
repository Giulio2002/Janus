import Extracted

/-!
# `Zero(s []byte)` is `clear(s)` (amd64)

The amd64 twin of `arm64/Zero.lean`: `runtime.memclrNoHeapPointers` is `MemclrNoHeapPointersLive64`;
the **Witness** uses the generic stub runtime `Janus.Contracts.LiveStubAmd64.memclrSeg` and the tactic
`janus64_live_memclr` at `Extracted.program`'s own contract address.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (ptr len cap : BitVec 64)
    (hz : MemclrNoHeapPointersLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap]
      (fun s => StackGuardOK s 4128 ∧ StackWritable s 4128 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Outside ((s.regs 4).toNat - 4128) 4144 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4144 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 16)]) ∧
        (0 < len.toNat →
          R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [ptr.toNat, len.toNat] ∧
          ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat len.toNat true = true ∧
          Apart ptr.toNat len.toNat ((s.regs 4).toNat - 4128) 4144 ∧
          (InRanges ptr.toNat len.toNat L ∨ Outside ptr.toNat len.toNat R.rt)))
      (fun s s' => Mem.Zeroed s'.mem ptr.toNat len.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 16),
          (ptr.toNat, ptr.toNat + len.toNat)])) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hinv, hLs, hdest⟩
  have harg1 : s.regs 3 = len := by
    have := hs.args 1 (by simp)
    simpa [GoABI.argReg, GoABI.intArgRegs] using this
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  by_cases h0 : len.toNat = 0
  · have hl0 : s.regs 3 = 0#64 := by
      rw [harg1]; apply BitVec.eq_of_toNat_eq; simpa using h0
    janus64_run
    · exact ⟨fun i hi => by omega, RtInv.inv_frame (ws := [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 16)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have e : (s.regs 4).toNat + 16 - ((s.regs 4).toNat - 4128) = 4144 := by omega
          simp only [e]; exact hout) hinv, by janus_frame⟩
  · obtain ⟨hok, hb48, hacc, hap, hd2⟩ := hdest (by omega)
    janus64_run calls [hz]
    exact ⟨by assumption, by assumption, by janus_frame⟩

namespace Witness

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.LiveSat (bump_acc)

def clA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
def ptr0 : Nat := 0x250000

/-- The stub runtime: generic code, placed at `Extracted.program`'s own contract address. -/
def implAt : List Amd64.Segment := [memclrSeg clA 12]

def ok : Nat → List Nat → Prop := fun a args => a = clA ∧ args = [ptr0, 12]

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_cl : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = clA := by decide

theorem hok_cl : ∀ args, ok clA args → ∃ d, args = [d, 12] := fun _ h => ⟨ptr0, h.2⟩

theorem model_cl : MemclrNoHeapPointersLive64 linked clA 4096 R := by janus64_live_memclr 12 hok_cl

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

/-- The bump cell holds `HEAP`; the return address `ret = 0x1000` is at `[RSP]`; `ptr0` holds `0xff`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else if ptr0 ≤ a ∧ a < ptr0 + 16 then 0xff else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4128, 4176, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨ptr0, 0x100, true⟩]⟩

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 ptr0 else if i = 3 then 12 else if i = 1 then 12
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 ptr0, 12, 12] s0 :=
  ⟨rfl, by decide, rfl, by decide,
    by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl, rfl⟩

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega),
    if_neg (by simp only [ptr0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : StackGuardOK s0 4128 ∧ StackWritable s0 4128 16 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Outside ((s0.regs 4).toNat - 4128) 4144 R.rt ∧
    Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4128) 4144 ∧
    Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
    R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧
    (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s0.regs 4).toNat - 4128, (s0.regs 4).toNat + 16)]) ∧
    (0 < (12 : BitVec 64).toNat →
      R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
        [(BitVec.ofNat 64 ptr0).toNat, (12 : BitVec 64).toNat] ∧
      (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
      s0.mem.accessible (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat true = true ∧
      Apart (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat ((s0.regs 4).toNat - 4128) 4144 ∧
      (InRanges (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat [] ∨
        Outside (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat R.rt)) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, ?_, by decide, ?_,
    inv0, fun r hr => absurd hr (by simp), fun _ => ⟨?_, by decide, by decide, by decide, Or.inr ?_⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_cl]; exact ⟨rfl, rfl⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

/-! ### The call-site state of the `memclrNoHeapPointers` contract -/

def callS (addr x y : Nat) : Amd64.State :=
  { s0 with
    rip := BitVec.ofNat 64 addr
    regs := fun i => if i = 0 then BitVec.ofNat 64 x else if i = 3 then BitVec.ofNat 64 y else s0.regs i }

theorem cs_rsp (a x y : Nat) : ((callS a x y).regs 4).toNat = sp0 := by rfl
theorem cs_g (a x y : Nat) : ((callS a x y).regs 14).toNat = g0 := by rfl
theorem cs_mem (a x y : Nat) : (callS a x y).mem = mem0 := rfl

theorem cs_eqpre (a x y : Nat) : MemPre64 4096 2 (callS a x y) := by
  have hw : mem0.accessible (sp0 - 4096) (4096 + 8 + 8 * 2) true = true := by decide
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, cs_g, cs_mem]; decide
  · simp only [regG, stackguard0Offset, cs_g, cs_mem]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, cs_g, cs_rsp, cs_mem]; decide
  · simp only [cs_rsp, cs_mem]; decide
  · simp only [cs_rsp]; decide
  · simp only [cs_rsp]; simp [sp0]
  · simp only [cs_rsp, cs_mem]
    exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)
  · rfl
  · rfl
  · simp only [cs_rsp, cs_mem]; decide
  · simp only [cs_g, cs_rsp, MemAmd64.calleeStack, MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    simp only [sp0, g0]
    omega

def sCl : Amd64.State := callS clA ptr0 12

@[reducible] def clSite (R : RtInv) (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : Amd64.State) : Prop :=
  MemPre64 4096 2 s ∧
  LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat] L b s (liveWin64 s 4096 2) ∧
  LiveDest64 R L s 4096 2 (s.regs 0).toNat (s.regs 3).toNat

theorem site_cl : clSite R clA [] 0x400 sCl := by
  refine ⟨cs_eqpre _ _ _, ⟨⟨rfl, rfl⟩, inv0, fun r hr => absurd hr (by simp), ?_⟩, ?_⟩
  · intro x hx
    simp only [sCl, liveWin64, calleeStack64, cs_rsp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [rt_eq]
    rcases hx with (rfl | rfl) | rfl <;>
      simp only [outside_cons, outside_nil, and_true, sp0, HEAP, HEND, BUMP, WBUF] <;> omega
  · have h0 : (sCl.regs 0).toNat = ptr0 := by decide
    have h3 : (sCl.regs 3).toNat = 12 := by decide
    simp only [h0, h3]
    refine ⟨by decide, by decide, ?_, Or.inr ?_, ?_⟩
    · simp only [sCl, calleeStack64, cs_rsp, outside_cons, outside_nil, and_true, ptr0, sp0]; omega
    · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
    · simp only [sCl, cs_rsp, outside_cons, outside_nil, and_true, ptr0, sp0]; omega

theorem returnsF : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (Mem.Zeroed s'.mem (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat ∧
      R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s'.mem) ∧
      MemFrame s0.mem s'.mem (R.rt ++ [((s0.regs 4).toNat - 4128, (s0.regs 4).toNat + 16),
        ((BitVec.ofNat 64 ptr0).toNat, (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat)])) :=
  correctness implAt R 0x400 [] (BitVec.ofNat 64 ptr0) 12 12 (by rw [addr_cl]; exact model_cl)
    ret hret s0 setup pre

theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (s : Amd64.State),
    MemclrNoHeapPointersLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 ptr0, 12, 12] s ∧
    (StackGuardOK s 4128 ∧ StackWritable s 4128 16 ∧ (s.regs 4).toNat % 8 = 0 ∧
      Outside ((s.regs 4).toNat - 4128) 4144 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4144 ∧
      Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
      (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 16)]) ∧
      (0 < (12 : BitVec 64).toNat →
        R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
          [(BitVec.ofNat 64 ptr0).toNat, (12 : BitVec 64).toNat] ∧
        (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat true = true ∧
        Apart (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat ((s.regs 4).toNat - 4128) 4144 ∧
        (InRanges (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat L ∨
          Outside (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat R.rt))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ (Mem.Zeroed s'.mem (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 16),
          ((BitVec.ofNat 64 ptr0).toNat, (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat)])) :=
  ⟨implAt, R, 0x400, [], ret, s0, by rw [addr_cl]; exact model_cl, hret, setup, pre,
    ⟨[], 0x400, sCl, by rw [addr_cl]; rfl, by rw [addr_cl]; exact site_cl⟩, returnsF⟩

theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Mem.Zeroed s'.mem ptr0 12 :=
  returnsF.mono fun _ ⟨habi, hz, _⟩ => ⟨habi, by simpa [ptr0] using hz⟩

end Witness

end Proof
