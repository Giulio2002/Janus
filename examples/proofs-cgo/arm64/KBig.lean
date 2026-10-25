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

/-- The memory after `k_big` wrote the struct at `a` (the four stores of its two `STP`s). -/
def bigMem (m : Memory) (a : Nat) (x y : BitVec 64) : Memory :=
  (((m.writeLE a 8 (x.toNat + y.toNat)).writeLE (a + 8) 8 (18446744073709551616 - y.toNat + x.toNat)).writeLE
    (a + 16) 8 (x.toNat * y.toNat)).writeLE (a + 24) 8 (x.toNat ^^^ y.toNat)

/-- The 32 bytes of the result in `bigMem`. -/
theorem bigMem_read (m : Memory) (a : Nat) (x y : BitVec 64) :
    (bigMem m a x y).readLE a 32 = quad (x + y) (x - y) (x * y) (x ^^^ y) := by
  simp only [bigMem, readLE_32]
  simp (disch := omega) only [Memory.readLE_writeLE_self, Memory.readLE_writeLE_of_disjoint]
  simp only [quad, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_xor,
    Nat.reducePow]
  have := (x ^^^ y).isLt
  rw [BitVec.toNat_xor] at this
  omega

/-- The argument values of `k_big(x, y)`. -/
def vals (x y : BitVec 64) : List Nat := [x.toNat, y.toNat]

/-- What `k_big` needs: its arguments where the classification puts them, the result buffer
(`X8`) and a return address. -/
def SPre (vs : List Nat) (s : State) : Prop :=
  ArgsAt s sig.args vs sig.passing ∧ RetBuf s sig ∧ (s.regs 30).toNat % 4 = 0 ∧
    (s.regs 30).toNat < 2 ^ 56

theorem spre_iff (x y : BitVec 64) (s : State) :
    SPre (vals x y) s ↔ s.regs 0 = x ∧ s.regs 1 = y ∧ (s.regs 8).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 8).toNat 32 true = true ∧ (s.regs 30).toNat % 4 = 0 ∧
      (s.regs 30).toNat < 2 ^ 56 := by
  unfold SPre
  have hrb : RetBuf s sig ↔ (s.regs 8).toNat + 32 ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 8).toNat 32 true = true := by
    constructor
    · intro h; have := h big rfl result; rwa [size_big] at this
    · intro h t ht _; cases ht; rw [size_big]; exact h
  rw [passing, hrb]
  simp only [vals, sig, ArgsAt, ArgAt, PiecesAt, and_true, pieceAt_gpr_word, and_assoc]

/-- What it guarantees: the callee-saved state, the struct written at `X8` and nothing else. -/
abbrev SPost (x y : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 19 = s.regs 19 ∧ s'.regs 20 = s.regs 20 ∧ s'.regs 21 = s.regs 21 ∧
    s'.regs 22 = s.regs 22 ∧ s'.regs 23 = s.regs 23 ∧ s'.regs 24 = s.regs 24 ∧
    s'.regs 25 = s.regs 25 ∧ s'.regs 26 = s.regs 26 ∧ s'.regs 27 = s.regs 27 ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.fpcr = s.fpcr ∧ s'.vregs = s.vregs ∧
    s'.mem = bigMem s.mem (s.regs 8).toNat x y

theorem summary (x y : BitVec 64) :
    Summary Extracted.program Extracted.entry (SPre (vals x y)) (SPost x y) := by
  intro s hpc hpre
  obtain ⟨h0, h1, hb, hacc, hlra, hlrb⟩ := (spre_iff x y s).1 hpre
  janus_run
  simp only [SPost, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, true_and]
  rfl

/-- **`k_big` under the C calling convention**: the struct is written through `X8`. -/
theorem correctness (x y : BitVec 64) :
    CEnsuresR Extracted.program Extracted.entry sig (vals x y) (fun _ => True)
      (fun s s' v => v = quad (x + y) (x - y) (x * y) (x ^^^ y) ∧
        MemFrame s.mem s'.mem [((s.regs 8).toNat, (s.regs 8).toNat + 32)]) :=
  CEnsuresA.of_summary (summary x y)
    (fun _ _ hret hs _ => ⟨hs.args, hs.retBuf, hs.lr_ok hret⟩)
    (fun s _ _ ⟨hsp, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hfc, hv, hm⟩ =>
      ⟨CReturn.of_eqs hsp h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 hfc hv, _,
        by simp only [Returned, sig, result, ResultAt, size_big, hm, bigMem_read], rfl,
        by rw [hm]; unfold bigMem; janus_frame⟩)

end Proof
