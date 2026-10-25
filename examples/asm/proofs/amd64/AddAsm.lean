import Janus
import Extracted

/-!
# `AddAsm(x, y uint64) uint64` (Go assembly, ABI0, amd64), through its callee summary

```
TEXT ·AddAsm(SB), NOSPLIT, $0-24       // examples/asm/asm_amd64.s
	MOVQ x+0(FP), AX ; MOVQ y+8(FP), BX ; ADDQ BX, AX ; MOVQ AX, ret+16(FP) ; RET
```

**Guarantee.** For all `x`, `y` and every ABI0 call state of `example.com/asm.AddAsm.abi0`
(`CallSetup0`: return address at `[RSP]`, `x`, `y` at `8(RSP)`, `16(RSP)`, the result word at
`24(RSP)`, the return slot and frame writable, `DF` clear), the call returns (never faulting),
pops the return address, keeps `RBP`, the `FS` base and `DF` (`ABIReturn0`; `R14` and `X15` are
not ABI0 obligations), and its result word is `x + y` (mod `2^64`).

**How.** A callee `Summary0` (from any state at the entry), then `Ensures0.of_summary0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

namespace Proof

theorem add_summary :
    Summary0 Extracted.program Extracted.entry
      (fun s => (s.regs 4).toNat + 32 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 4).toNat 32 true = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s m => MemFrame (s.mem.writeLE ((s.regs 4).toNat + 24) 8
          ((s.mem.readLE ((s.regs 4).toNat + 8) 8 + s.mem.readLE ((s.regs 4).toNat + 16) 8) % 2 ^ 64)) m
        [((s.regs 4).toNat, (s.regs 4).toNat)]) := by
  intro s hpc ⟨h1, h2, h3⟩
  janus64_run
  exact MemFrame.refl _ _

theorem correctness (x y : BitVec 64) :
    EnsuresResults0 Extracted.program Extracted.entry [x, y] 1 (fun _ => True)
      (fun r => r = [x + y]) := by
  refine Ensures0.of_summary0 add_summary ?_ ?_
  · intro ret s hret hs _
    have := hret.user
    refine ⟨hs.frame_bound, hs.frame_accessible, ?_⟩
    rw [hs.ret]; exact this
  · intro ret s s' _ hs _ hf
    have h0 := hs.arg (i := 0) (by simp)
    have h1 := hs.arg (i := 1) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at h0 h1
    simp only [results0, wordsAt_succ, wordsAt_zero, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, regSP]
    rw [hf.readLE ((s.regs 4).toNat + 24) 8 (by simp),
      Janus.Arm64.Memory.readLE_writeLE_self _ _ _ _, h0, h1]
    simp only [List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]

end Proof
