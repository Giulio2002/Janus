import Extracted

/-!
# `Push(s []byte, b byte) []byte` is `append(s, b)` (amd64)

```go
func Push(s []byte, b byte) []byte { return append(s, b) }
```

`runtime.growslice` is the **live** contract `RtLiveContract64 … growsliceSpec growsliceLive` of
`Janus/Contracts/Live.lean` (any element type; here `uint8`: size 1, no pointers), with the runtime
hypothesis `R`; it is called only when the slice is full. The point of the example is its
**Witness**: the stub runtime that makes the contract satisfiable at `Extracted.program`'s own
contract address is the generic `Janus.Contracts.LiveStubAmd64` (`LiveStubAmd64.growsliceSeg`,
`janus64_live_growslice`); nothing in the file proves the contract by hand.

**Guarantee.** For every runtime `R` satisfying the contract, every live set `L`, every slice
`(ptr, len, cap)` with `len ≤ cap < 2^40` and every call state whose frame is outside the
runtime-owned ranges:

* **room left** (`len < cap`, the array writable and inside a live object or outside the runtime's
  ranges): the result is `(ptr, len + 1, cap)`, the byte at `ptr + len` is `b`, the runtime's invariant
  holds again for the same `L`, and memory changed only there and in the frame;
* **full** (`len = cap`, the runtime ready for `growslice(ptr, len+1, cap, 1, uint8)` within the budget):
  the capacity is `growCap 1 true (len+1) cap`, the new array is inside `R.rt`, starts with the old `len`
  bytes, then `b`, the runtime's invariant holds again for a live set that contains the new array, and
  memory changed only in `R.rt` and the frame.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The type descriptor of `uint8`, the last argument of `growslice` (the RIP-relative `LEAQ` at
`Push+0x25`), recomputed from the extracted code. -/
def u8Type : Nat := ripTarget Extracted.program (Extracted.entry + 0x25)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (ptr len cap x : BitVec 64)
    (hgs : RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x]
      (fun s => StackGuardOK s 4176 ∧ StackWritable s 4176 40 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4176) 4216 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4176) 4216 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ ptr.toNat + cap.toNat ≤ 2 ^ 48 ∧
        Apart ptr.toNat cap.toNat ((s.regs 4).toNat - 4176) 4216 ∧
        Apart u8Type 16 ((s.regs 4).toNat - 4176) 4216 ∧
        (len.toNat < cap.toNat → s.mem.accessible ptr.toNat cap.toNat true = true ∧
          (InRanges ptr.toNat cap.toNat L ∨ Outside ptr.toNat cap.toNat R.rt)) ∧
        (cap.toNat ≤ len.toNat →
          R.ok (Extracted.program.contractAddr "runtime.growslice")
            [ptr.toNat, len.toNat + 1, cap.toNat, 1, u8Type] ∧
          roundupsize (nextslicecap (len.toNat + 1) cap.toNat) true ≤ b ∧
          (0 < len.toNat → s.mem.accessible ptr.toNat len.toNat false = true)))
      (fun s s' => (s'.regs 3).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 1 = cap ∧
          s'.mem.readLE (ptr.toNat + len.toNat) 1 = x.toNat % 256 ∧
          R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
          MemFrame s.mem s'.mem [(ptr.toNat + len.toNat, ptr.toNat + len.toNat + 1),
            ((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 1).toNat = growCap 1 true (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (s'.regs 1).toNat R.rt ∧
          (∀ i, i < len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (ptr.toNat + i)) ∧
          s'.mem.readLE ((s'.regs 0).toNat + len.toNat) 1 = x.toNat % 256 ∧
          (∃ b' L', R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
            InRanges (s'.regs 0).toNat (s'.regs 1).toNat L') ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]))) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hinv, hLs, hlc, hc, hpb,
    hdj, hdt, hroom, hgrow⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr ⊢
  janus_eval_nat h_ut : u8Type
  unfold Apart at hdj
  janus64_data hd [hw]
  by_cases hl : len.toNat < cap.toNat
  · obtain ⟨hacc, hdest⟩ := hroom hl
    janus64_run
    refine ⟨fun _ => ⟨?_, by janus_frame⟩, fun h => absurd h (by omega)⟩
    refine RtInv.inv_frame' (ws := [(ptr.toNat + len.toNat, ptr.toNat + len.toNat + 1),
      ((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) (by janus_frame) ?_ hinv
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rcases hdest with h | h
      · right; exact InRanges.sub h (by first | (dsimp only; omega) | omega) (by first | (dsimp only; omega) | omega)
      · left; exact Outside.of_sub h (by first | (dsimp only; omega) | omega) (by first | (dsimp only; omega) | omega)
    · left
      have e : (s.regs 4).toNat + 40 - ((s.regs 4).toNat - 4176) = 4216 := by omega
      simp only [e]; exact hout
  · obtain ⟨hok, hcost, hrd⟩ := hgrow (by omega)
    rw [h_ut] at hok hdt
    janus64_run until [Extracted.entry + 0x31] calls [hgs]
    rename_i r0 r1 r2 jk fl vx vy M ym ep hfr hpost hlf hfresh hapart hinv2
    obtain ⟨hr1, hr2, hin, hb48, hacc, hcp, hz, -⟩ := hpost
    have hle := le_growCap 1 true (len.toNat + 1) cap.toNat (by decide)
    have hr2ne : r2.toNat ≠ 0 := by omega
    rw [if_neg hr2ne] at hinv2
    have hacc' : M.accessible r0.toNat r2.toNat true = true := by simpa using hacc
    have hacc2 : M.accessible (r0.toNat + len.toNat) 1 true = true :=
      Memory.accessible_mono _ hacc' (by omega) (by omega)
    janus64_run

namespace Witness

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def u8A : Nat := janus_eval% u8Type
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]

/-- The stub runtime: generic code, placed at `Extracted.program`'s own contract address. -/
def implAt : List Amd64.Segment := [growsliceSeg grA 0 16 8]

/-- The requests the witness runtime serves: `Push`'s (`growslice(nil, 1, 0, 1, uint8)`). -/
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ args = [0, 1, 0, 1, u8A]

def R : RtInv := toyR tys ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem ut_eq : u8Type = u8A := by decide

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 1, 0, 1, (u8A, 1, 0).1] := fun _ h => ⟨0, h.2⟩

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract64 linked grA 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (u8A, 1, 0) 1 0 1 16 8 hok_gr

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The return address `ret = 0x1000` is at `[RSP]`; the bump cell holds `HEAP`. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4176, 4216, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩] ++
    Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

/-- `Push(nil, 7)`. -/
def s0 : Amd64.State :=
  { regs := fun i => if i = 7 then 7 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, 7] s0 :=
  ⟨rfl, by decide, rfl, by decide,
    by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

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

theorem tysOK : TysOK tys := by decide

open Janus.Contracts.PoolSat (toyInv_init_tys)

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump
    (fun i hi hi' => ?_) (by decide) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] ++ [(u8A, u8A + 16)] := rfl

theorem pre : StackGuardOK s0 4176 ∧ StackWritable s0 4176 40 ∧ (s0.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s0.mem ∧
        Outside ((s0.regs 4).toNat - 4176) 4216 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4176) 4216 ∧
        Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
        R.inv 0x400 ([] : List (Nat × Nat)) (s0.regs 14).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s0.regs 4).toNat - 4176, (s0.regs 4).toNat + 40)]) ∧
        (0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 40 ∧ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart (0 : BitVec 64).toNat (0 : BitVec 64).toNat ((s0.regs 4).toNat - 4176) 4216 ∧
        Apart u8Type 16 ((s0.regs 4).toNat - 4176) 4216 ∧
        ((0 : BitVec 64).toNat < (0 : BitVec 64).toNat → s0.mem.accessible (0 : BitVec 64).toNat (0 : BitVec 64).toNat true = true ∧
          (InRanges (0 : BitVec 64).toNat (0 : BitVec 64).toNat ([] : List (Nat × Nat)) ∨ Outside (0 : BitVec 64).toNat (0 : BitVec 64).toNat R.rt)) ∧
        ((0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat →
          R.ok (Extracted.program.contractAddr "runtime.growslice")
            [(0 : BitVec 64).toNat, (0 : BitVec 64).toNat + 1, (0 : BitVec 64).toNat, 1, u8Type] ∧
          roundupsize (nextslicecap ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) true ≤ 0x400 ∧
          (0 < (0 : BitVec 64).toNat → s0.mem.accessible (0 : BitVec 64).toNat (0 : BitVec 64).toNat false = true)) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    inv0, fun r hr => absurd hr (by simp), by decide, by decide, by decide, by decide, by decide,
    fun h => absurd h (by decide), fun _ => ⟨?_, by decide, fun h => absurd h (by decide)⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [addr_gr, ut_eq]; exact ⟨rfl, rfl⟩

theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (s : Amd64.State),
    RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [0, 0, 0, 7] s ∧
    StackGuardOK s 4176 ∧ StackWritable s 4176 40 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4176) 4216 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4176) 4216 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        (0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 40 ∧ (0 : BitVec 64).toNat + (0 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart (0 : BitVec 64).toNat (0 : BitVec 64).toNat ((s.regs 4).toNat - 4176) 4216 ∧
        Apart u8Type 16 ((s.regs 4).toNat - 4176) 4216 ∧
        ((0 : BitVec 64).toNat < (0 : BitVec 64).toNat → s.mem.accessible (0 : BitVec 64).toNat (0 : BitVec 64).toNat true = true ∧
          (InRanges (0 : BitVec 64).toNat (0 : BitVec 64).toNat L ∨ Outside (0 : BitVec 64).toNat (0 : BitVec 64).toNat R.rt)) ∧
        ((0 : BitVec 64).toNat ≤ (0 : BitVec 64).toNat →
          R.ok (Extracted.program.contractAddr "runtime.growslice")
            [(0 : BitVec 64).toNat, (0 : BitVec 64).toNat + 1, (0 : BitVec 64).toNat, 1, u8Type] ∧
          roundupsize (nextslicecap ((0 : BitVec 64).toNat + 1) (0 : BitVec 64).toNat) true ≤ b ∧
          (0 < (0 : BitVec 64).toNat → s.mem.accessible (0 : BitVec 64).toNat (0 : BitVec 64).toNat false = true)) :=
  ⟨implAt, R, 0x400, [], ret, s0, by rw [addr_gr]; exact model_gr, hret, setup, pre⟩

theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 3).toNat = 1 ∧ (s'.regs 1).toNat = 8 ∧
      InRanges (s'.regs 0).toNat 8 R.rt ∧ s'.mem.readLE (s'.regs 0).toNat 1 = 7 :=
  (correctness implAt R 0x400 [] 0 0 0 7 (by rw [addr_gr]; exact model_gr)
    ret hret s0 setup pre).mono
    fun s' ⟨habi, h1, _, hg⟩ => by
      obtain ⟨h2, h3, -, h4, -⟩ := hg (by decide)
      have e2 : (s'.regs 1).toNat = 8 := by rw [h2]; decide
      exact ⟨habi, by simpa using h1, e2, by rw [← e2]; exact h3, by simpa using h4⟩

end Witness

end Proof
