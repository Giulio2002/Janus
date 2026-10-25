import Janus
import Extracted

/-!
# `AppendOne(s []uint64, x uint64) []uint64` on amd64: `append(s, x)`

**Guarantee.** As for arm64 (`examples/proofs/AppendOne.lean`), with the slice in `RAX, RBX, RCX`,
`x` in `RDI`, the stack window `[RSP-4176, RSP+40)`, and `runtime.growslice` given by
`GrowsliceContract64`: with room left, word `len` becomes `x` and nothing else changes; when full
(also for a nil slice), the result is a fresh array of capacity `growCap8 (len+1) cap` inside `rt`
holding the old elements, then `x`, then zeros.

**What is assumed.** Only the contract hypothesis `hg` (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- The address of `uint64`'s type descriptor, the element type AppendOne passes to
`runtime.growslice` (the `LEA` before the call loads it): the extraction's only data object. -/
def u64Type : Nat := dataBase Extracted.program 0

/-- The precondition. When the slice is full, the runtime is ready (`H`) for the call
`growslice(ptr, len+1, cap, 1, uint64)` from AppendOne's frame (`RSP - 80` at the callee). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (ptr len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4176 40 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4176) 4216 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
    len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 39 ∧
    ptr.toNat + 8 * cap.toNat ≤ 2 ^ 48 ∧
    Spec.Disjoint ptr.toNat (8 * cap.toNat) ((s.regs 4).toNat - 4176) 4216 ∧
    (len.toNat < cap.toNat → s.mem.accessible ptr.toNat (8 * cap.toNat) true = true) ∧
    (0 < len.toNat → s.mem.accessible ptr.toNat (8 * len.toNat) false = true) ∧
    (cap.toNat ≤ len.toNat →
      H [ptr.toNat, len.toNat + 1, cap.toNat, 1, u64Type] (s.regs 14).toNat ((s.regs 4).toNat - 80)
        (rtView rt s.mem))

/-- Word `i` past the appended one is still zero after the store of word `L`. -/
theorem zero_after_store {m : Arm64.Memory} {P L C x i A : Nat}
    (hz : ZeroBytes m (P + 8 * (L + 1)) (8 * C - 8 * (L + 1))) (hA : A = P + 8 * L) (h1 : L < i)
    (h2 : i < C) : (m.writeLE A 8 x).readLE (P + 8 * i) 8 = 0 := by
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    show P + 8 * i = P + 8 * (L + 1) + 8 * (i - (L + 1)) by omega]
  exact hz.readLE (by omega)

/-- Word `i < L` of the copy is the old word, after the store of word `L`. -/
theorem copy_after_store {m m₀ : Arm64.Memory} {P Q L x i A : Nat}
    (hcp : ∀ j, j < 8 * L → m.bytes (P + j) = m₀.bytes (Q + j)) (hA : A = P + 8 * L) (hi : i < L) :
    (m.writeLE A 8 x).readLE (P + 8 * i) 8 = m₀.readLE (Q + 8 * i) 8 := by
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  exact readLE_of_copy hcp (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (ptr len cap x : BitVec 64)
    (hg : GrowsliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [ptr, len, cap, x]
      (Pre rt H ptr len cap)
      (fun s s' => (s'.regs 3).toNat = len.toNat + 1 ∧
        (len.toNat < cap.toNat → s'.regs 0 = ptr ∧ s'.regs 1 = cap ∧
          s'.mem.readLE (ptr.toNat + 8 * len.toNat) 8 = x.toNat ∧
          MemFrame s.mem s'.mem [(ptr.toNat + 8 * len.toNat, ptr.toNat + 8 * len.toNat + 8),
            ((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]) ∧
        (cap.toNat ≤ len.toNat →
          (s'.regs 1).toNat = growCap8 (len.toNat + 1) cap.toNat ∧
          InRanges (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) rt ∧
          (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * growCap8 (len.toNat + 1) cap.toNat) true = true ∧
          (∀ i, i < len.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = s.mem.readLE (ptr.toNat + 8 * i) 8) ∧
          s'.mem.readLE ((s'.regs 0).toNat + 8 * len.toNat) 8 = x.toNat ∧
          (∀ i, len.toNat < i → i < growCap8 (len.toNat + 1) cap.toNat →
            s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4176, (s.regs 4).toNat + 40)]))) := by
  intro ret hret s hs ⟨hsg, ⟨hb, ha, hw⟩, hd, hout, hal, hlc, hc, hpb, hdj, hwr, hrd, hHf⟩
  janus64_intro hs
  janus_eval_nat h_ut : u64Type
  have hgl := hsg.load
  have hgb := hsg.below
  have hnw2 := hsg.noWrap
  have hgr := hsg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hb ha hw hout hal hdj ⊢
  janus64_data hd [hw]
  by_cases hl : len.toNat < cap.toNat
  · have hw' := hwr hl
    janus64_run
    exact ⟨fun _ => by janus_frame, fun h => absurd h (by omega)⟩
  · have hle := le_growCap8 (len.toNat + 1) cap.toNat
    have hH := hHf (by omega)
    rw [h_ut] at hH
    clear hHf
    by_cases h0 : len.toNat = 0
    · janus64_run until [Extracted.entry + 0x31] calls [hg.empty]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus64_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => absurd hi (by omega), fun i h1 h2 => ?_, by janus_frame⟩⟩
      exact zero_after_store hz (by omega) h1 h2
    · have hr := hrd (by omega)
      janus64_run until [Extracted.entry + 0x31] calls [hg.withOld]
      have hdj2 := InRanges.disjoint ‹InRanges _ _ rt› hout
      janus64_run
      have hin := ‹InRanges _ (8 * growCap8 _ _) rt›
      have hacc := ‹s.mem.accessible _ (8 * growCap8 _ _) true = true›
      have h8 := ‹16 ≤ 8 * growCap8 _ _ ∨ _ → _›
      have hz := ‹ZeroBytes _ _ (8 * growCap8 _ _ - _)›
      have hcp := ‹∀ i, i < 8 * _ → _›
      refine ⟨fun h => absurd h hl, fun _ => ⟨hin, h8 (Or.inr (by omega)), hacc,
        fun i hi => ?_, fun i h1 h2 => ?_, by janus_frame⟩⟩
      · rw [copy_after_store hcp (by omega) hi]
        janus64_simp
      · exact zero_after_store hz (by omega) h1 h2

end Proof
