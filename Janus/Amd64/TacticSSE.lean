import Janus.Amd64.TacticAVX
import Janus.Tactic.Vector

/-!
# Proof support for the SSE packed instructions (WP-D)

Extends the `janus64_exec` / `janus64_post` simp sets so that `janus64_run` steps the
instructions of `Janus.Amd64.ExecSSE`, and adds the element lemmas the proofs about vector code
need. Everything is proved from the model.

* `ExecSSE.exec` is unfolded per constructor (definitional `rfl` equations, as `exec`), and so
  are its operand plumbing (`readN`, `readG`, `doneX`, `doneFP`) and the packed operations
  (`pintOp`, `pshiftOp`, `pimmOp`) on a literal operation. The state updates are rewritten to
  the normal form of the scalar instructions (`setXmmF`, `setRegF`).
* A vector value is then an `ofElems` term (`lanes`); `elem_ofElems` (shared with arm64,
  `Janus.Tactic.Vector`) reads an element back, `elem_readLE` reads an element of loaded data.
* `elem_pshufd`, `elem_setWidth_32`: the shuffles and moves of the integer code.
* `sum32`: the wrapping sum of 32-bit words in memory, the specification of a vectorised
  reduction; `paddd_lanes` is its lane-wise step.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64 Janus.Arm64 Janus.Tactic

janus_rfl_eqns ExecSSE.exec [janus64_exec]
janus_rfl_eqns ExecSSE.pintOp [janus64_exec]
janus_rfl_eqns ExecSSE.pshiftOp [janus64_exec]
janus_rfl_eqns ExecSSE.pimmOp [janus64_exec]

attribute [janus64_exec] ExecSSE.readN ExecSSE.readG ExecSSE.doneX ExecSSE.doneFP ExecSSE.raiseMx
  ExecSSE.lanes ExecSSE.sel

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
