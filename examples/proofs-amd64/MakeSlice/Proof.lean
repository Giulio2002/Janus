import Janus
import Extracted

/-!
# `MakeSlice(n int) []uint64` on amd64: a fresh zeroed slice of `n` words

**Guarantee.** For every `n ≤ 2^45`, every `rt` and **every** implementation of
`runtime.makeslice` satisfying `MakesliceContract64`, and every Go call state in which the
prologue falls through, `RSP` is 8-aligned, `[RSP-4136, RSP+16)` is writable and outside `rt`, and
the read-only data is loaded: the call returns, obeys the ABI, `RBX = RCX = n` (length and
capacity), and for `n > 0` the array `[RAX, RAX+8n)` lies inside `rt` (fresh), is writable,
8-byte aligned and all zero. Memory outside `rt` and the stack window is unchanged.

**What is assumed.** Only the contract hypothesis `hmk` (docs/RUNTIME-CONTRACTS.md).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Proof

/-- The address of `uint64`'s type descriptor, the element type MakeSlice passes to
`runtime.makeslice` (the `LEA` before the call loads it): the extraction's only data object. -/
def u64Type : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (n : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧ n.toNat ≤ 2 ^ 45 ∧
        H [u64Type, n.toNat, n.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => s'.regs 3 = n ∧ s'.regs 1 = n ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat (8 * n.toNat) rt ∧ (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * n.toNat) true = true ∧
          ∀ i, i < n.toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 16)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hn, hH⟩
  janus64_intro hs
  janus_eval_nat h_ut : u64Type
  rw [h_ut] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  by_cases h0 : n.toNat = 0
  · janus64_run calls [hmk]
    exact ⟨fun h => absurd h (by omega), by janus_frame⟩
  · janus64_run calls [hmk.pos]
    have hin := ‹InRanges _ (blockSize _ _) rt›
    have hacc := ‹Arm64.Memory.accessible s.mem _ (blockSize _ _) true = true›
    have h8 := ‹16 ≤ _ ∨ _ → _›
    have hz := ‹ZeroBytes _ _ (8 * n.toNat)›
    have hge := ‹8 * n.toNat ≤ blockSize _ _›
    refine ⟨fun _ => ⟨hin.sub (Nat.le_refl _) (by omega), h8 (Or.inr (by omega)),
      Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), fun i hi => ?_⟩, by janus_frame⟩
    simpa using hz.readLE (k := 8 * i) (j := 8) (by omega)

end Proof
