import Extracted

/-!
# `AddAsm(x, y uint64) uint64` (Go assembly, ABI0, arm64), through its callee summary

```
TEXT ·AddAsm(SB), NOSPLIT, $0-24       // examples/asm/asm_arm64.s
	MOVD x+0(FP), R0 ; MOVD y+8(FP), R1 ; ADD R1, R0, R0 ; MOVD R0, ret+16(FP) ; RET
```

**Guarantee.** For all `x`, `y` and every ABI0 call state of `example.com/asm.AddAsm.abi0` with
`x`, `y` in frame words 0 and 1 (`CallSetup0`: `8(RSP)`, `16(RSP)`; the result word 2 at
`24(RSP)` writable; `RSP` aligned), the call returns (never faulting), restores `RSP`, `g`, `FP`
and `R18`, and its result word is `x + y` (mod `2^64`).

**How.** The function is proved once as a callee `Summary0` (from any state at its entry: it
writes the sum of frame words 0 and 1 into word 2, nothing else, and returns to `X30` with only
the reserved registers kept), and the standalone contract follows from it by
`Ensures0.of_summary0` — the summary is what a caller (a direct ABI0 call, or the wrapper) uses.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec

namespace Proof

/-- `AddAsm.abi0` as a callee, from any state at its entry: it writes `x + y` (the frame words 0
and 1) into the result word 2 and nothing else, and returns to `X30`. -/
theorem add_summary :
    Summary0 Extracted.program Extracted.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.sp.toNat % 16 = 0 ∧
        s.sp.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat + 8) 24 true = true)
      (fun s m => MemFrame (s.mem.writeLE (s.sp.toNat + 24) 8
          ((s.mem.readLE (s.sp.toNat + 8) 8 + s.mem.readLE (s.sp.toNat + 16) 8) % 2 ^ 64)) m
        [(s.sp.toNat, s.sp.toNat)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5⟩
  janus_run
  exact MemFrame.refl _ _

theorem correctness (x y : BitVec 64) :
    EnsuresResults0 Extracted.program Extracted.entry [x, y] 1 (fun _ => True)
      (fun r => r = [x + y]) := by
  refine Ensures0.of_summary0 add_summary ?_ ?_
  · intro ret s hret hs _
    have := hret.aligned
    have := hret.user
    refine ⟨?_, ?_, hs.spAligned, ?_, ?_⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · exact hs.frame_bound
    · exact hs.frame_accessible
  · intro ret s s' _ hs _ hf
    have h0 := hs.arg (i := 0) (by simp)
    have h1 := hs.arg (i := 1) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at h0 h1
    simp only [results0, wordsAt_succ, wordsAt_zero, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [hf.readLE (s.sp.toNat + 24) 8 (by simp), Memory.readLE_writeLE_self _ _ _ _, h0, h1]
    simp only [List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]

end Proof
