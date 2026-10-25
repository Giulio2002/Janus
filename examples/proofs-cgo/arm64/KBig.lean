import Extracted

/-!
# `struct k_big k_big(int64_t x, int64_t y)` (C, arm64): a 32-byte result through `X8`

```c
struct k_big { int64_t a, b, c, d; };
struct k_big k_big(int64_t x, int64_t y) { struct k_big r = { x + y, x - y, x * y, x ^ y }; return r; }
```

**Guarantee.** For all 64-bit `x`, `y`, every AAPCS64 call of the gcc-compiled `k_big` whose
arguments are where the classification puts them (`x`, `y` in `X0`, `X1`) and whose caller
passes, as the classification of the 32-byte non-HFA result requires (§6.9), the address of a
writable 32-byte result buffer in `X8` (`CCallA.retBuf`), returns, restores what AAPCS64
requires (`CReturn`), leaves in the buffer the struct `{x + y, x - y, x * y, x ^ y}` (mod 2^64)
and writes no other memory.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.C

namespace Proof

def big : CType := .struct [.int 8 true, .int 8 true, .int 8 true, .int 8 true]
def sig : AAPCS64.Sig := ⟨some big, [.int 8 true, .int 8 true], none⟩

theorem passing : sig.passing = [.direct [⟨0, 8, .gpr 0⟩], .direct [⟨0, 8, .gpr 1⟩]] := by decide
theorem result : AAPCS64.result big = .indirect (.gpr 8) := by decide
theorem size_big : CType.size big = 32 := by decide

/-- The bytes of a `struct k_big`. -/
def quad (a b c d : BitVec 64) : Nat :=
  a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat

theorem correctness (x y : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig [x.toNat, y.toNat] (fun _ => True)
      (fun s s' v => v = quad (x + y) (x - y) (x * y) (x ^^^ y) ∧
        MemFrame s.mem s'.mem [((s.regs 8).toNat, (s.regs 8).toNat + 32)]) := by
  intro ret hret s hs _
  have hpc := hs.pc
  have hlr := hs.lr
  have ha := hs.args
  rw [passing] at ha
  simp only [sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word] at ha
  obtain ⟨h0, h1⟩ := ha
  obtain ⟨hb, hacc⟩ : Buffer s (s.regs 8) 32 true := by
    have := hs.retBuf big rfl result; rwa [size_big] at this
  simp only [Program.withExit] at hlr
  janus_run
  refine ⟨_, ⟨?_, rfl, ?_⟩⟩
  · simp only [Returned, sig, result, ResultAt, size_big, readLE_32]
    simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
    simp only [quad, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_xor,
      Nat.reducePow]
    have := (x ^^^ y).isLt
    rw [BitVec.toNat_xor] at this
    omega
  · janus_frame

end Proof
