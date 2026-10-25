import Janus.Amd64.TacticAVX
import Janus.Tactic.Vector
import Janus.Spec.CRC32C

/-!
# Proof support for the SSE packed instructions (WP-D)

Extends the `janus64_exec` / `janus64_post` simp sets so that `janus64_run` steps the
instructions of `Janus.Amd64.ExecSSE`, and adds the element lemmas the proofs about vector code
need. Everything is proved from the model.

* `ExecSSE.exec` is unfolded per constructor (definitional `rfl` equations, as `exec`), and so
  is its operand plumbing (`readN`, `readG`, `doneX`, `doneFP`). The state updates are rewritten
  to the normal form of the scalar instructions (`setXmmF`, `setRegF`).
* The packed operations themselves (`pintOp`, `pshiftOp`, `pimmOp`, ...) are **not** unfolded
  (as on arm64): a symbolic `XMM` register holds a term like `pintOp (.add 32) x y`, and the
  element lemmas (`elem_pintOp_add`, ...) evaluate what the code reads back from it;
  `elem_readLE` reads an element of loaded data.
* `elem_pshufd`, `elem_setWidth_32`: the shuffles and moves of the integer code.
* `sum32`: the wrapping sum of 32-bit words in memory, the specification of a vectorised
  reduction; `paddd_lanes` is its lane-wise step.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64 Janus.Arm64 Janus.Tactic

janus_rfl_eqns ExecSSE.exec [janus64_exec]

/- The bit-serial CRC of `CRC32` doubles its term at every step under `whnf` (the next register
is an `if` on the current one); proofs reason about it with `Janus.Spec.CRC32C`, never by
unfolding it, so the elaborator must not unfold it either. -/
/-- `CRC32` results are 32-bit values (zero-extended into the 64-bit register). -/
@[janus64_exec, janus64_post] theorem toNat_ofNat_crc32c (n x d : Nat) :
    (BitVec.ofNat 64 (ExecSSE.crc32c n (x % 4294967296) d)).toNat = ExecSSE.crc32c n (x % 4294967296) d := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Janus.Spec.CRC32C.crc32c_lt n _ d (Nat.mod_lt _ (by decide))) (by decide))

@[janus64_exec, janus64_post] theorem crc32c_mod_32 (n x d : Nat) :
    ExecSSE.crc32c n (x % 4294967296) d % 4294967296 = ExecSSE.crc32c n (x % 4294967296) d :=
  Nat.mod_eq_of_lt (Janus.Spec.CRC32C.crc32c_lt n _ d (Nat.mod_lt _ (by decide)))

set_option allowUnsafeReducibility true in
attribute [irreducible] ExecSSE.crc32c

attribute [janus64_exec] ExecSSE.readN ExecSSE.readG ExecSSE.doneX ExecSSE.doneFP ExecSSE.raiseMx

@[janus64_exec] theorem ExecSSE.setXmm_eq (s : State) (r : Nat) (v : W128) :
    ExecSSE.setXmm s r v = { s with xmm := setXmmF s.xmm r v } := rfl
@[janus64_exec] theorem ExecSSE.setReg_eq (s : State) (r : Nat) (v : W64) :
    ExecSSE.setReg s r v = { s with regs := setRegF s.regs r v } := rfl

attribute [janus64_exec, janus64_post] elem_ofElems elem_mod_two_pow elem_readLE_64 elem_readLE_8
  elem_mod_2_128 elem_mod_2_64 elem_64_mod elem_8_mod

/-- An element of a 128-bit register value (`BitVec.toNat` is below `2^128`). -/
theorem elem_lt' (x e i : Nat) : elem x e i < 2 ^ e := elem_lt x e i

@[janus64_exec, janus64_post] theorem elem_32_mod (x i : Nat) : elem x 32 i % 4294967296 = elem x 32 i :=
  Nat.mod_eq_of_lt (elem_lt x 32 i)

/-- A 32-bit element of loaded data. -/
@[janus64_exec, janus64_post] theorem elem_readLE_32 (m : Janus.Amd64.Memory) {a n i : Nat} (h : 4 * (i + 1) ≤ n) :
    elem (m.readLE a n) 32 i = m.readLE (a + 4 * i) 4 := elem_readLE m (k := 4) h

/-- `PSHUFD` as element selection. -/
theorem pshufd_ofElems (a imm : Nat) :
    pshufdNat a imm = ofElems 32 4 fun i => elem a 32 (imm / 4 ^ i % 4) := by
  simp only [pshufdNat, ofElems, elem, Nat.mod_mod]
  simp

/-- `PSHUFD`: dword `i` of the result is dword `imm[2i+1:2i]` of the source. -/
theorem elem_pshufd (a imm : Nat) {i : Nat} (hi : i < 4) :
    elem (pshufdNat a imm) 32 i = elem a 32 (imm / 4 ^ i % 4) := by
  rw [pshufd_ofElems, elem_ofElems _ hi, Nat.mod_eq_of_lt (elem_lt _ _ _)]

@[janus64_exec, janus64_post] theorem elem_pshufd_0 (a imm : Nat) :
    elem (pshufdNat a imm) 32 0 = elem a 32 (imm % 4) := by
  rw [elem_pshufd a imm (by decide)]; try simp
@[janus64_exec, janus64_post] theorem elem_pshufd_1 (a imm : Nat) :
    elem (pshufdNat a imm) 32 1 = elem a 32 (imm / 4 % 4) := by
  rw [elem_pshufd a imm (by decide)]; try simp
@[janus64_exec, janus64_post] theorem elem_pshufd_2 (a imm : Nat) :
    elem (pshufdNat a imm) 32 2 = elem a 32 (imm / 16 % 4) := by
  rw [elem_pshufd a imm (by decide)]; try simp
@[janus64_exec, janus64_post] theorem elem_pshufd_3 (a imm : Nat) :
    elem (pshufdNat a imm) 32 3 = elem a 32 (imm / 64 % 4) := by
  rw [elem_pshufd a imm (by decide)]; try simp

/-- `PADDB/W/D/Q`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_add {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.add e) a b) e i = (elem a e i + elem b e i) % 2 ^ e := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]

/-- `PSUBB/W/D/Q`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_sub {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.sub e) a b) e i = (elem a e i + 2 ^ e - elem b e i) % 2 ^ e := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]

/-- `PCMPEQB/W/D/Q`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_cmpeq {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.cmpeq e) a b) e i = if elem a e i = elem b e i then 2 ^ e - 1 else 0 := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]
  split
  · exact Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos e) (by decide))
  · exact Nat.zero_mod _

/-- `PADD*` results are 128-bit values. -/
@[janus64_exec, janus64_post] theorem pintOp_add_mod (e a b : Nat) :
    ExecSSE.pintOp (.add e) a b % 340282366920938463463374607431768211456 = ExecSSE.pintOp (.add e) a b := by
  apply Nat.mod_eq_of_lt
  simp only [ExecSSE.pintOp, ExecSSE.lanes]
  have h : e * (128 / e) ≤ 128 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self 128 e
  exact Nat.lt_of_lt_of_le (ofElems_lt _ _ _) (Nat.pow_le_pow_right (by decide) h)

/-- `PSHUFD` results are 128-bit values. -/
@[janus64_exec, janus64_post] theorem pshufdNat_mod (a imm : Nat) :
    pshufdNat a imm % 340282366920938463463374607431768211456 = pshufdNat a imm := by
  apply Nat.mod_eq_of_lt
  rw [pshufd_ofElems]
  exact ofElems_lt 32 4 _

/-- `MOVD r32, xmm` of a value: its element 0. -/
@[janus64_exec, janus64_post] theorem toNat_setWidth_32_ofNat (v : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 128 v))).toNat = elem v 32 0 := by
  simp [elem, BitVec.toNat_setWidth]
  omega

/-- An element of a value below `2^128` read as a 32-bit element: element 0 is the low bits. -/
theorem elem_32_zero (x : Nat) : elem x 32 0 = x % 4294967296 := by
  simp [elem]

/-- The low 32 bits of a register value are its element 0. -/
theorem toNat_setWidth_32 (x : W128) : (x.setWidth 32).toNat = elem x.toNat 32 0 := by
  simp [elem, BitVec.toNat_setWidth]

/-! ## Wrapping sums of 32-bit words -/

/-- `Σ_{i < n} M[a + 4 (s·i + j)]` (the 32-bit words at stride `s` from word `j`), as a natural. -/
def sumStride (m : Janus.Amd64.Memory) (a s j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumStride m a s j n + m.readLE (a + 4 * (s * n + j)) 4

/-- `Σ_{i < n} M[a + 4 i]`: the plain sum of `n` 32-bit words. -/
def sum32 (m : Janus.Amd64.Memory) (a n : Nat) : Nat := sumStride m a 1 0 n

theorem sum32_zero (m : Janus.Amd64.Memory) (a : Nat) : sum32 m a 0 = 0 := rfl

theorem sum32_succ (m : Janus.Amd64.Memory) (a n : Nat) :
    sum32 m a (n + 1) = sum32 m a n + m.readLE (a + 4 * n) 4 := by
  simp [sum32, sumStride]

/-- Eight more words. -/
theorem sum32_add8 (m : Janus.Amd64.Memory) (a k : Nat) : sum32 m a (8 * k + 8) = sum32 m a (8 * k) +
    (m.readLE (a + 4 * (8 * k + 0)) 4 + m.readLE (a + 4 * (8 * k + 1)) 4 +
      m.readLE (a + 4 * (8 * k + 2)) 4 + m.readLE (a + 4 * (8 * k + 3)) 4 +
      m.readLE (a + 4 * (8 * k + 4)) 4 + m.readLE (a + 4 * (8 * k + 5)) 4 +
      m.readLE (a + 4 * (8 * k + 6)) 4 + m.readLE (a + 4 * (8 * k + 7)) 4) := by
  simp only [sum32, sumStride, Nat.add_zero, Nat.one_mul]
  omega

/-- Splitting the first `8k` words into the eight word classes mod 8. -/
theorem sum32_eight (m : Janus.Amd64.Memory) (a : Nat) : ∀ k,
    sum32 m a (8 * k) = sumStride m a 8 0 k + sumStride m a 8 1 k + sumStride m a 8 2 k +
      sumStride m a 8 3 k + sumStride m a 8 4 k + sumStride m a 8 5 k + sumStride m a 8 6 k +
      sumStride m a 8 7 k
  | 0 => rfl
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, sum32_add8, sum32_eight m a k]
    simp only [sumStride]
    omega

end Janus.Amd64.Tactic
