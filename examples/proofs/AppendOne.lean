import Extracted

/-!
# `AppendOne(s []uint64, x uint64) []uint64` is `append(s, x)`

**Guarantee.** For every slice `(ptr, len, cap)` with `len ≤ cap < 2^39` and every `x`, every list
`rt` of runtime-owned ranges and **every** implementation of `runtime.growslice` satisfying
`GrowsliceContract` (8-byte pointer-free elements, `Janus/Contracts/Alloc.lean`), and every Go call
state of `example.com/basic.AppendOne` in which the stack-growth prologue falls through, the stack
window `[SP-4192, SP+40)` is writable, outside `rt` and disjoint from the array `[ptr, ptr+8cap)`,
the array is writable when `len < cap` and its `len` words readable when `len > 0`: the call
returns, obeys the ABI, the result has length `len + 1`, and

* **room left** (`len < cap`): the result is `(ptr, len+1, cap)`, word `len` is `x`, and only that
  word (and the stack window) changed;
* **growth** (`len = cap`, through `runtime.growslice`): the capacity is
  `growCap8 (len+1) cap` (Go's `nextslicecap` rounded up to the allocator's size class), the new
  array lies inside `rt` (fresh), is writable and 8-byte aligned, its first `len` words are the old
  elements, word `len` is `x`, the words after it are `0`, and memory outside `rt` and the stack
  window is unchanged. This holds for a nil slice too (`len = cap = 0`).

**What is assumed.** The contract for `runtime.growslice` (hypothesis `hg`); growslice itself
(the allocation, `memmove` and `memclrNoHeapPointers` of the new array) is not executed.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- The precondition. -/
def Pre (rt : List (Nat × Nat)) (ptr len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4192 40 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4192) 4232 rt ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 39 ∧
    ptr.toNat + 8 * cap.toNat ≤ 2 ^ 48 ∧ Disjoint ptr.toNat (8 * cap.toNat) (s.sp.toNat - 4192) 4232 ∧
    (len.toNat < cap.toNat → s.mem.accessible ptr.toNat (8 * cap.toNat) true = true) ∧
    (0 < len.toNat → s.mem.accessible ptr.toNat (8 * len.toNat) false = true)

/-- Word `i` past the appended one is still zero after the store of word `L`. -/
theorem zero_after_store {m : Memory} {P L C x i : Nat}
    (hz : ZeroBytes m (P + 8 * (L + 1)) (8 * C - 8 * (L + 1))) (h1 : L < i) (h2 : i < C) :
    (m.writeLE (P + 8 * L) 8 x).readLE (P + 8 * i) 8 = 0 := by
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    show P + 8 * i = P + 8 * (L + 1) + 8 * (i - (L + 1)) by omega]
  exact hz.readLE (by omega)

/-- Word `i < L` of the copy is the old word, after the store of word `L`. -/
theorem copy_after_store {m m₀ : Memory} {P Q L x i : Nat}
    (hcp : ∀ j, j < 8 * L → m.bytes (P + j) = m₀.bytes (Q + j)) (hi : i < L) :
    (m.writeLE (P + 8 * L) 8 x).readLE (P + 8 * i) 8 = m₀.readLE (Q + 8 * i) 8 := by
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  exact readLE_of_copy hcp (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (ptr len cap x : BitVec 64)
    (hg : GrowsliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x]
      (Pre rt ptr len cap)
      (fun s s' => (s'.regs 1).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 2 = cap ∧
          s'.mem.readLE (ptr.toNat + 8 * len.toNat) 8 = x.toNat ∧
          MemFrame s.mem s'.mem [(ptr.toNat + 8 * len.toNat, ptr.toNat + 8 * len.toNat + 8),
            (s.sp.toNat - 4192, s.sp.toNat + 40)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 2).toNat = growCap8 (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) rt ∧
          (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) true = true ∧
          (∀ i, i < len.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = s.mem.readLE (ptr.toNat + 8 * i) 8) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8 * len.toNat) 8 = x.toNat ∧
          (∀ i, len.toNat < i → i < growCap8 (len.toNat + 1) cap.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4192, s.sp.toNat + 40)]))) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hlc, hc, hpb, hdj, hwr, hrd⟩
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hdj
  by_cases hl : len.toNat < cap.toNat
  · have hw' := hwr hl
    janus_run
    exact ⟨fun _ => by janus_frame, fun h => absurd h (by omega)⟩
  · have hle := le_growCap8 (len.toNat + 1) cap.toNat
    by_cases h0 : len.toNat = 0
    · janus_run until [Extracted.entry + 0x3c] calls [hg.empty]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => absurd hi (by omega), fun i h1 h2 => ?_, by janus_frame⟩⟩
      exact zero_after_store hz h1 h2
    · have hr := hrd (by omega)
      janus_run until [Extracted.entry + 0x3c] calls [hg.withOld]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      have hcp := ‹∀ i, i < 8 * _ → _›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => ?_, fun i h1 h2 => ?_, by janus_frame⟩⟩
      · rw [copy_after_store hcp hi]
        janus_simp
      · exact zero_after_store hz h1 h2

end Proof
