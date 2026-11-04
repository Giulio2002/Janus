import Janus.Contracts.AllocSat
import Janus.Contracts.LiveStub

/-!
# The (non-live) allocation contracts at a program's own addresses (arm64)

`NewobjectContract p addr rt stack H`, `MallocgcContract`, `MakesliceContract` are single-call
contracts parametrised by the runtime-owned ranges `rt` and a readiness predicate `H` (what the
runtime sees at the call). `AllocSat` proves them for its own `rt` (a 64 KiB heap and one type
descriptor). This file generalises that proof over `rt`: the consumer chooses the ranges (it can add
its own type descriptors) and the heap address, and the stub (`MOVZ X0, #heap>>16, LSL #16; RET`
at the contract address) returns the heap.

```lean
def heap : Nat := 0x10000
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (nodeType, nodeType + 16)]
def H : RtReady := NewReadyAt rt heap                 -- heap writable and zero; typ in rt, size ≤ 32 KiB
def linked : Program := Extracted.program.link [StubAlloc.heapSeg newA heap]
theorem hnew : NewobjectContract linked newA rt 4096 H := by janus_newobject heap (by simp [rt])
```
The last argument proves `(heap, heap + 0x10000) ∈ rt`. The proof is by running the stub, as for the live
stubs: no new trusted statement.
-/

namespace Janus.Contracts.StubAlloc

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.AllocSat (le_blockSize)

/-- The heap `[heap, heap + 64 KiB)` is writable and zero, as the runtime sees it. -/
def HeapReadyAt (heap : Nat) (v : Memory) : Prop :=
  v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

/-- `newobject`'s readiness: the heap, and a type descriptor inside `rt` of at most 32 KiB. -/
def NewReadyAt (rt : List (Nat × Nat)) (heap : Nat) : RtReady := fun args _ _ v =>
  HeapReadyAt heap v ∧ ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

/-- `mallocgc`'s readiness: the heap, and a request of at most 32 KiB. -/
def MallocReadyAt (heap : Nat) : RtReady := fun args _ _ v =>
  HeapReadyAt heap v ∧ ∃ sz typ nz, args = [sz, typ, nz] ∧ sz ≤ 32768

/-- `makeslice`'s readiness: the heap, and an element type inside `rt` with `size · cap ≤ 32 KiB`. -/
def MakeReadyAt (rt : List (Nat × Nat)) (heap : Nat) : RtReady := fun args _ _ v =>
  HeapReadyAt heap v ∧ ∃ et l c, args = [et, l, c] ∧ InRanges et 16 rt ∧ typSize v et * c ≤ 32768

/-- The stub: `MOVZ X0, #(heap >> 16), LSL #16; RET` (`heap` a multiple of 64 KiB below 4 GiB). -/
def heapSeg (addr heap : Nat) : Segment :=
  ⟨"stub.heap", addr, [0xd2a00000 + heap / 65536 * 32, 0xd65f03c0]⟩

/-- The object every implementation returns is `Fresh` for a request of at most 32 KiB. -/
theorem fresh_heap_at {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {m : Memory} {size round : Nat}
    (zero hdr : Bool) (hr : HeapReadyAt heap (rtView rt m)) (hsz : size ≤ round)
    (hround : round ≤ 32768) : Fresh rt m heap size round zero hdr := by
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), hrt, Nat.le_refl _, Nat.le_refl _⟩
  exact ⟨⟨(heap, heap + 0x10000), hrt, Nat.le_refl _, by omega⟩, by omega,
    Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), fun _ => by omega, fun _ _ => by omega,
    fun _ => fun i hi => hz' i (by omega), hsz⟩

theorem callRegs_one (r : Nat → W64) (x : W64) : callRegs r r [x] = setReg r 0 x := by
  funext i
  rcases i with _ | i
  · rfl
  · simp only [callRegs, setReg, List.getD_cons_succ, List.getD_nil]
    split <;> (try split) <;> first | rfl | (exfalso; omega)

theorem toNat_heap {heap : Nat} (h : heap < 2 ^ 64) : (BitVec.ofNat 64 heap).toNat = heap := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `newobject`'s object is the heap. -/
theorem newobject_obj {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hin : InRanges (s.regs 0).toNat 16 rt)
    (hsz : typSize (rtView rt s.mem) (s.regs 0).toNat ≤ 32768) : newobjectObj rt s s.mem heap := by
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem mallocgc_obj {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hsz : (s.regs 0).toNat ≤ 32768) :
    mallocgcObj rt s s.mem heap := by
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem makeslice_obj {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hin : InRanges (s.regs 0).toNat 16 rt)
    (hsz : typSize (rtView rt s.mem) (s.regs 0).toNat * (s.regs 2).toNat ≤ 32768) :
    makesliceObj rt s s.mem heap := by
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ 32768 at hsz
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

end Janus.Contracts.StubAlloc

/-- `NewobjectContract linked a rt 4096 (NewReadyAt rt heap)` for the stub `StubAlloc.heapSeg a heap`;
`hrt : (heap, heap + 0x10000) ∈ rt`. -/
syntax "janus_newobject " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_newobject $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      subst hargs
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 $heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      · simp only [retStateX]; rw [Janus.Contracts.StubAlloc.callRegs_one]; try rfl
      · rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
        exact Janus.Contracts.StubAlloc.newobject_obj $hrt (by decide) (by decide) hr hin hsz))

/-- `MallocgcContract linked a rt 4096 (MallocReadyAt heap)` for `StubAlloc.heapSeg a heap`. -/
syntax "janus_mallocgc " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_mallocgc $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, sz, typ, nz, hargs, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 $heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      · simp only [retStateX]; rw [Janus.Contracts.StubAlloc.callRegs_one]; try rfl
      · rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
        exact Janus.Contracts.StubAlloc.mallocgc_obj $hrt (by decide) (by decide) hr hsz))

/-- `MakesliceContract linked a rt 4096 (MakeReadyAt rt heap)` for `StubAlloc.heapSeg a heap`. -/
syntax "janus_makeslice " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_makeslice $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, rfl⟩ := hargs
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      refine ⟨BitVec.ofNat 64 $heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_,
        ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      · simp only [retStateX]; rw [Janus.Contracts.StubAlloc.callRegs_one]; try rfl
      · rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
        exact Janus.Contracts.StubAlloc.makeslice_obj $hrt (by decide) (by decide) hr hin hsz))
