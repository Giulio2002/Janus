import Extracted

/-!
# `Zero(s []byte)` is `clear(s)` (arm64)

```go
func Zero(s []byte) { clear(s) }
```

`runtime.memclrNoHeapPointers` is the **live** contract `MemclrNoHeapPointersLive` of
`Janus/Contracts/Live.lean`, with the runtime hypothesis `R`. The point of the example is its
**Witness**: the stub runtime that makes the contract satisfiable at `Extracted.program`'s own
contract address is the generic `Janus.Contracts.LiveStub` (`LiveStub.memclrSeg`,
`janus_live_memclr`); nothing in the file proves the contract by hand.

**Guarantee.** For every runtime `R` satisfying the contract, every live set `L` and call state whose
frame is outside the runtime-owned ranges and whose slice is either inside a live object or outside
the runtime's ranges, writable and apart from the frame: the call returns, the `len` bytes at `ptr`
are zero, the runtime's invariant holds again for the same `L`, and memory changed only in the
frame and the slice.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (ptr len cap : BitVec 64)
    (hz : MemclrNoHeapPointersLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap]
      (fun s => GuardOK s 4128 ∧ StackOK s 4136 16 ∧ Outside (s.sp.toNat - 4136) 4152 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4136) 4152 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4136, s.sp.toNat + 16)]) ∧
        (0 < len.toNat →
          R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [ptr.toNat, len.toNat] ∧
          ptr.toNat + len.toNat ≤ 2 ^ 48 ∧ s.mem.accessible ptr.toNat len.toNat true = true ∧
          Apart ptr.toNat len.toNat (s.sp.toNat - 4136) 4152 ∧
          (InRanges ptr.toNat len.toNat L ∨ Outside ptr.toNat len.toNat R.rt)))
      (fun s s' => Mem.Zeroed s'.mem ptr.toNat len.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4136, s.sp.toNat + 16),
          (ptr.toNat, ptr.toNat + len.toNat)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hinv, hLs, hdest⟩
  have harg1 : s.regs 1 = len := by simpa using hs.args 1 (by simp)
  janus_intro hs
  by_cases h0 : len.toNat = 0
  · have hl0 : s.regs 1 = 0#64 := by
      rw [harg1]; apply BitVec.eq_of_toNat_eq; simpa using h0
    janus_run
    · exact ⟨fun i hi => by omega, RtInv.inv_frame (ws := [(s.sp.toNat - 4136, s.sp.toNat + 16)]) (by janus_frame)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have e : s.sp.toNat + 16 - (s.sp.toNat - 4136) = 4152 := by omega
          simp only [e]; exact hout) hinv, by janus_frame⟩
  · obtain ⟨hok, hb48, hacc, hap, hd2⟩ := hdest (by omega)
    janus_run calls [hz]
    exact ⟨by assumption, by assumption, by janus_frame⟩

namespace Witness

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def clA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
def ptr0 : Nat := 0x250000

/-- The stub runtime: generic code, placed at `Extracted.program`'s own contract address. -/
def implAt : List Segment := [memclrSeg clA 12]

/-- The requests the witness runtime serves: `Zero`'s (12 bytes at `ptr0`). -/
def ok : Nat → List Nat → Prop := fun a args => a = clA ∧ args = [ptr0, 12]

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_cl : Extracted.program.contractAddr "runtime.memclrNoHeapPointers" = clA := by decide

theorem hok_cl : ∀ args, ok clA args → ∃ d, args = [d, 12] := fun _ h => ⟨ptr0, h.2⟩

/-- The contract at `Zero`'s own address: one tactic. -/
theorem model_cl : MemclrNoHeapPointersLive linked clA 4096 R := by janus_live_memclr 12 hok_cl

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def bytes0 (a : Nat) : Byte :=
  if a = BUMP + 3 then 0x10 else if ptr0 ≤ a ∧ a < ptr0 + 16 then 0xff else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4136, 4152, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨ptr0, 0x100, true⟩]⟩

/-- `Zero(s)` for the 12-byte slice at `ptr0`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 ptr0 else if i = 1 then 12 else if i = 2 then 12
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 ptr0, 12, 12] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [ptr0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : GuardOK s0 4128 ∧ StackOK s0 4136 16 ∧ Outside (s0.sp.toNat - 4136) 4152 R.rt ∧
    Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4136) 4152 ∧
    Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧
    (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [(s0.sp.toNat - 4136, s0.sp.toNat + 16)]) ∧
    (0 < (12 : BitVec 64).toNat →
      R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
        [(BitVec.ofNat 64 ptr0).toNat, (12 : BitVec 64).toNat] ∧
      (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
      s0.mem.accessible (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat true = true ∧
      Apart (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat (s0.sp.toNat - 4136) 4152 ∧
      (InRanges (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat [] ∨
        Outside (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat R.rt)) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ?_, by decide, ?_,
    inv0, fun r hr => absurd hr (by simp), fun _ => ⟨?_, by decide, by decide, by decide, Or.inr ?_⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_cl]; exact ⟨rfl, rfl⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget, a live set and a
call of `Zero` on 12 bytes satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (s : State),
    MemclrNoHeapPointersLive (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 ptr0, 12, 12] s ∧
    (GuardOK s 4128 ∧ StackOK s 4136 16 ∧ Outside (s.sp.toNat - 4136) 4152 R.rt ∧
      Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4136) 4152 ∧
      Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
      R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
      (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4136, s.sp.toNat + 16)]) ∧
      (0 < (12 : BitVec 64).toNat →
        R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers")
          [(BitVec.ofNat 64 ptr0).toNat, (12 : BitVec 64).toNat] ∧
        (BitVec.ofNat 64 ptr0).toNat + (12 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat true = true ∧
        Apart (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat (s.sp.toNat - 4136) 4152 ∧
        (InRanges (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat L ∨
          Outside (BitVec.ofNat 64 ptr0).toNat (12 : BitVec 64).toNat R.rt))) :=
  ⟨implAt, R, 0x400, [], ret, s0, by rw [addr_cl]; exact model_cl, hret, setup, pre⟩

/-- So the guarantee is reached: `Zero` zeroes the 12 bytes at `ptr0`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ Mem.Zeroed s'.mem ptr0 12 :=
  (correctness implAt R 0x400 [] (BitVec.ofNat 64 ptr0) 12 12 (by rw [addr_cl]; exact model_cl)
    ret hret s0 setup pre).mono fun _ ⟨habi, hz, _⟩ => ⟨habi, by simpa [ptr0] using hz⟩

end Witness

end Proof
