import Janus.Tactic.Vector
import Janus.Tactic.Float
import Janus.Arm64.ExecNeon

/-!
# Symbolic execution of the Advanced SIMD classes of `NeonInstr`

* `exec_neon` (`exec (.neon i) s = execNeon i s`, by `rfl`) and the unfoldings of the executor
  plumbing (`execNeon`, the per-class `NeonExec.*` functions, `vpart`, `setVpart`, `qcCommit`,
  ...), registered in `janus_exec`. As in `Janus.Tactic.Vector`, the lane operations
  themselves (`Neon.threeSameInt`, `Neon.permOp`, `NeonFP.threeSameFP`, ...) are **not**
  unfolded: a symbolic register holds a term like `permOp 8 128 3 x y`, and element lemmas
  evaluate what later instructions read back.
* The copies of `baseAddr`/`memIndexed`/`memVPair` in `ExecNeon` are the originals of `Exec`
  (`NeonExec.baseAddr_eq`, ...), so the trusted base has one definition of each in effect.
* Element lemmas for the lane operations, and `laneSum` (the sum of the lanes of a vector), the
  quantity the across-lanes reductions compute.

Nothing here is trusted: every lemma is proved from the model.
-/

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.Arm64.Neon Janus.Arm64.NeonFP Janus.Arm64.NeonExec

/-! ## The copies in `ExecNeon` are `Exec`'s definitions -/

theorem NeonExec.baseAddr_eq : NeonExec.baseAddr = Janus.Arm64.baseAddr := rfl
theorem NeonExec.memIndexed_eq : NeonExec.memIndexed = Janus.Arm64.memIndexed := rfl
theorem NeonExec.memVPair_eq : NeonExec.memVPair = Janus.Arm64.memVPair := rfl

/-! ## `exec` of `Instr.neon` -/

@[janus_exec] theorem exec_neon (i : NeonInstr) (s : State) : exec (.neon i) s = execNeon i s := rfl

attribute [janus_exec] execNeon NeonExec.dsize NeonExec.vpart NeonExec.setVpart NeonExec.qcCommit
  NeonExec.intCommit NeonExec.rpresUnknown NeonExec.threeSame NeonExec.sThreeSame
  NeonExec.threeDiff NeonExec.sThreeDiff NeonExec.twoMisc NeonExec.sTwoMisc NeonExec.across
  NeonExec.sPairwise NeonExec.perm NeonExec.fixedLanes NeonExec.shiftImm NeonExec.sShiftImm
  NeonExec.intIdx NeonExec.fpIdx NeonExec.byElem NeonExec.sByElem NeonExec.sDup
  NeonExec.fpCvtFixed NeonExec.baseAddr NeonExec.memIndexed NeonExec.memVPair NeonExec.selemOf
  NeonExec.ldStructRegs NeonExec.ldstStruct NeonExec.ldstNP Neon.esizeOf neonHsb4

/-! ## Elements of the lane operations -/

/-- ZIP1/ZIP2 (`opcode = 011` / `111`): element `i` of the result. -/
theorem elem_zip {esize ds opcode i : Nat} (x y : Nat) (hop : opcode % 4 = 3) (hi : i < ds / esize) :
    elem (permOp esize ds opcode x y) esize i =
      if i % 2 = 0 then elem x esize (opcode / 4 * (ds / esize / 2) + i / 2)
      else elem y esize (opcode / 4 * (ds / esize / 2) + i / 2) := by
  have h1 : opcode % 4 ≠ 1 := by omega
  have h2 : opcode % 4 ≠ 2 := by omega
  unfold permOp
  simp only [h1, h2, ite_false]
  rw [elem_ofElems _ hi]
  split <;> exact Nat.mod_eq_of_lt (elem_lt _ _ _)

/-- `Σ_{j < n} Elem[x, j, e]`: the sum of the lanes of a vector. -/
def laneSum (e x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => laneSum e x k + elem x e k

end Janus.Tactic

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.Arm64.Neon

/-! ## Element arithmetic -/

/-- An element of twice the size is two adjacent elements. -/
theorem elem_two (v e j : Nat) : elem v (2 * e) j = elem v e (2 * j) + 2 ^ e * elem v e (2 * j + 1) := by
  unfold elem
  have h1 : 2 ^ (e * (2 * j + 1)) = 2 ^ (2 * e * j) * 2 ^ e := by
    rw [← Nat.pow_add]; congr 1; rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_assoc]
  have h2 : e * (2 * j) = 2 * e * j := by rw [Nat.mul_left_comm, Nat.mul_assoc]
  have h3 : 2 ^ (2 * e) = 2 ^ e * 2 ^ e := by rw [← Nat.pow_add, Nat.two_mul]
  rw [h1, h2, ← Nat.div_div_eq_div_mul, h3, Nat.mod_mul]

/-- `elem` of a value shifted down by whole elements. -/
theorem elem_div_pow (v e k i : Nat) : elem (v / 2 ^ (e * k)) e i = elem v e (i + k) := by
  unfold elem
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add, Nat.add_comm (e * i)]

@[janus_exec, janus_post] theorem elem_zero (e i : Nat) : elem 0 e i = 0 := by simp [elem]

/-- ZIP1/ZIP2 with a zero second operand, read with elements of twice the size: the
zero-extended elements of the selected half of `x`. -/
theorem elem_zip_zero (e ds opcode j : Nat) (x : Nat) (hop : opcode % 4 = 3) (hj : 2 * j + 1 < ds / e) :
    elem (permOp e ds opcode x 0) (2 * e) j = elem x e (opcode / 4 * (ds / e / 2) + j) := by
  rw [elem_two, elem_zip _ _ hop (by omega), elem_zip _ _ hop hj]
  have : (2 * j + 1) % 2 = 1 := by omega
  simp [this, elem_zero]

@[janus_exec, janus_post] theorem elem_zip_zero_16 {ds opcode j : Nat} (x : Nat) (hop : opcode % 4 = 3)
    (hj : 2 * j + 1 < ds / 8) : elem (permOp 8 ds opcode x 0) 16 j = elem x 8 (opcode / 4 * (ds / 8 / 2) + j) :=
  elem_zip_zero 8 ds opcode j x hop hj
@[janus_exec, janus_post] theorem elem_zip_zero_32 {ds opcode j : Nat} (x : Nat) (hop : opcode % 4 = 3)
    (hj : 2 * j + 1 < ds / 16) : elem (permOp 16 ds opcode x 0) 32 j = elem x 16 (opcode / 4 * (ds / 16 / 2) + j) :=
  elem_zip_zero 16 ds opcode j x hop hj
@[janus_exec, janus_post] theorem elem_zip_zero_64 {ds opcode j : Nat} (x : Nat) (hop : opcode % 4 = 3)
    (hj : 2 * j + 1 < ds / 32) : elem (permOp 32 ds opcode x 0) 64 j = elem x 32 (opcode / 4 * (ds / 32 / 2) + j) :=
  elem_zip_zero 32 ds opcode j x hop hj

/-- `truncInt` of a natural number. -/
theorem truncInt_nat (k a : Nat) : truncInt k (a : Int) = a % 2 ^ k := by
  unfold truncInt
  rw [show ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) by push_cast; rfl, ← Int.natCast_emod, Int.toNat_natCast]

/-- UADDW/UADDW2 (three different, `U = 1`, `opcode = 0001`): element `i` of the result. -/
theorem elem_uaddw {e n part i : Nat} (x y d : Nat) (hi : i < n) :
    elem (threeDiffOp true e n 1 part x y d).1 (2 * e) i =
      (elem x (2 * e) i + elem (if part = 1 then y / 2 ^ 64 else y % 2 ^ 64) e i) % 2 ^ (2 * e) := by
  unfold threeDiffOp
  simp only [show (1 : Nat) ≠ 0 by decide, ite_true, ite_false]
  rw [elem_ofElems _ hi]
  simp only [intOf, ite_true]
  rw [show ((elem x (2 * e) i : Int) + (elem (if part = 1 then y / 2 ^ 64 else y % 2 ^ 64) e i : Int)) =
      ((elem x (2 * e) i + elem (if part = 1 then y / 2 ^ 64 else y % 2 ^ 64) e i : Nat) : Int) by push_cast; rfl,
    truncInt_nat, Nat.mod_mod]

@[janus_exec, janus_post] theorem elem_uaddw_64 {n part i : Nat} (x y d : Nat) (hi : i < n) :
    elem (threeDiffOp true 32 n 1 part x y d).1 64 i =
      (elem x 64 i + elem (if part = 1 then y / 2 ^ 64 else y % 2 ^ 64) 32 i) % 2 ^ 64 :=
  elem_uaddw (e := 32) x y d hi

@[janus_exec, janus_post] theorem elem_hi64_32 (y i : Nat) : elem (y / 2 ^ 64) 32 i = elem y 32 (i + 2) :=
  elem_div_pow y 32 2 i
@[janus_exec, janus_post] theorem elem_hi64_32' (y i : Nat) :
    elem (y / 18446744073709551616) 32 i = elem y 32 (i + 2) := elem_div_pow y 32 2 i

/-- ADD (vector, `U = 0`, `opcode = 10000`): element `i` of the result. -/
@[janus_exec, janus_post] theorem elem_add {size ds e i : Nat} (x y d : Nat) (he : 8 * 2 ^ size = e)
    (hi : i < ds / e) :
    elem (threeSameOp false size 16 ds x y d) e i = (elem x e i + elem y e i) % 2 ^ e := by
  subst he
  have : threeSameOp false size 16 ds x y d = ofElems (8 * 2 ^ size) (ds / (8 * 2 ^ size)) fun i =>
      elem x (8 * 2 ^ size) i + elem y (8 * 2 ^ size) i := rfl
  rw [this, elem_ofElems _ hi]

/-- ADDP (scalar): the sum of the two 64-bit elements. -/
@[janus_exec, janus_post] theorem reduceAdd_2 (x : Nat) :
    reduceAdd 64 x 2 = (elem x 64 0 + elem x 64 1) % 2 ^ 64 := by
  simp only [reduceAdd, sumElems, intOf, ite_true, Int.zero_add]
  rw [show ((elem x 64 0 : Int) + (elem x 64 1 : Int)) = ((elem x 64 0 + elem x 64 1 : Nat) : Int) by push_cast; rfl,
    truncInt_nat]

end Janus.Tactic

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.Arm64.Neon

/-! ## Non-saturating operations do not set `FPSR.QC`

For the opcodes that cannot saturate, the saturation flag of the result is `false`, so
`qcCommit` leaves `FPSR` alone (the side conditions are literal comparisons). -/

@[janus_exec, janus_post] theorem threeDiffOp_snd {U : Bool} {e n opcode part x y d : Nat}
    (h : opcode ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12]) : (threeDiffOp U e n opcode part x y d).2 = false := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

@[janus_exec, janus_post] theorem threeSameInt_snd {U : Bool} {size opcode ds x y d : Nat}
    (h : opcode ∈ [0, 2, 3, 4, 6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23]) : (threeSameInt U size opcode ds x y d).2 = false := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

@[janus_exec, janus_post] theorem twoMiscInt_snd {U : Bool} {size opcode ds x d : Nat}
    (h : opcode ∈ [0, 1, 2, 4, 5, 6, 8, 9, 10, 11]) : (twoMiscInt U size opcode ds x d).2 = false := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

@[janus_exec, janus_post] theorem shiftImmInt_snd {U : Bool} {esize opcode ds immhb x d : Nat}
    (h : opcode ∈ [0, 2, 4, 6, 8, 10]) : (shiftImmInt U esize opcode ds immhb x d).2 = false := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

@[janus_exec, janus_post] theorem byElemInt_snd {U : Bool} {e n opcode part x d el : Nat}
    (h : opcode ∈ [0, 2, 4, 6, 8, 10]) : (byElemInt U e n opcode part x d el).2 = false := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

@[janus_exec, janus_post] theorem xtn_snd {e n x : Nat} : (narrowOp false e n 0b10010 x).2 = false := rfl

@[janus_exec, janus_post] theorem shrn_snd {esize n opcode shift x : Nat} (h : opcode / 2 = 8) :
    (shiftNarrowOp false esize n opcode shift x).2 = false := by
  unfold shiftNarrowOp; simp [h]

end Janus.Tactic
