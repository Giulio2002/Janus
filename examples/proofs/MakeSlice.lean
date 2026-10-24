import Extracted

/-!
# `MakeSlice(n int) []uint64` returns a fresh zeroed slice of `n` words

**Guarantee.** For every `n ≤ 2^45`, every list `rt` of runtime-owned memory ranges and
**every** implementation of `runtime.makeslice` satisfying `MakesliceContract`
(`Janus/Contracts/Alloc.lean`), and every Go call state of `example.com/basic.MakeSlice` in which
the stack-growth prologue falls through, the stack window `[SP-4144, SP+16)` is writable and
outside `rt`, and memory holds the program's read-only data (the `uint64` type descriptor): the
call returns, obeys the ABI, and the result slice `(X0, X1, X2)` has length and capacity `n`
(`X1 = X2 = n`); for `n > 0` its array `[X0, X0 + 8n)` lies inside the runtime-owned ranges (so it
is fresh: disjoint from all caller data outside them), is writable and 8-byte aligned, and every
word of it is `0`. Memory outside `rt` and the stack window is unchanged. For `n = 0` the pointer
is not specified (Go returns `&runtime.zerobase`).

**What is assumed.** The contract for `runtime.makeslice` (hypothesis `hmk`), stated for the code
linked at its address; the allocator is not executed (docs/RUNTIME-CONTRACTS.md). `n ≤ 2^45` keeps
`8n` within `maxAlloc`, so no panic path of `makeslice` is taken.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (n : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [n]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 16 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4160 rt ∧ n.toNat ≤ 2 ^ 45)
      (fun s s' => s'.regs 1 = n ∧ s'.regs 2 = n ∧
        (0 < n.toNat → InRanges (s'.regs 0).toNat (8 * n.toNat) rt ∧ (s'.regs 0).toNat % 8 = 0 ∧
          s'.mem.accessible (s'.regs 0).toNat (8 * n.toNat) true = true ∧
          ∀ i, i < n.toNat → s'.mem.readLE ((s'.regs 0).toNat + 8 * i) 8 = 0) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 16)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hn⟩
  janus_intro hs
  janus_data hd [hw]
  by_cases h0 : n.toNat = 0
  · janus_run calls [hmk]
    exact ⟨fun h => absurd h (by omega), by janus_frame⟩
  · janus_run calls [hmk.pos]
    rename_i hin _ hacc h8 _ hz hge
    refine ⟨fun _ => ⟨hin.sub (Nat.le_refl _) (by omega), h8 (Or.inr (by omega)),
      Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), fun i hi => ?_⟩, by janus_frame⟩
    simpa using hz.readLE (k := 8 * i) (j := 8) (by omega)

end Proof
