import Janus.Amd64.TacticSSE

/-!
# Proof support for the AVX / AVX2 / FMA3 instructions (WP-F)

Extends the `janus64_exec` / `janus64_post` simp sets so that `janus64_run` steps the
instructions of `Janus.Amd64.ExecAVX`, proves the compatibility of the width-generic semantics
with WP-D's at 128 bits, the **VEX.128 zero-upper rule** and its legacy-SSE counterpart, and adds
the element lemmas for 256-bit vector code. Everything is proved from the model.

* `ExecAVX.exec` is unfolded per constructor (definitional `rfl` equations, as `exec`), and so
  is its operand plumbing (`rd`, `getV`, `doneV`, `doneFPV`, `doneS`); `ExecAVX.setV` gets the
  `setXmmF` normal form of both halves (`ExecAVX.setV_eq`).
* At `l = 128` the lane-generic operations are WP-D's (`pintV_128`, `pimmV_128`, `pshiftV_128`,
  `shufV_pshufd_128`, `cvtV_128`, `vcmp_legacy`), so the WP-D element lemmas apply unchanged to
  VEX.128 code. At `l = 256` an element of a per-lane result is an element of the lane operation
  (`elem_perLane_256`); `elem_pintV_256_add32`, `elem_pintV_256_mull32` are the instances the
  vectorised loops use.
* `setV_128_upper`, `vex128_zero_upper` (every register an `AvxI` instruction writes at 128 bits
  has bits 255:128 zero afterwards), `sse_preserves_upper` (no legacy-SSE `SseI` instruction
  changes any upper half).
* `dot32`/`dotStride`: the wrapping dot product of 32-bit words in memory, the specification of
  the vectorised dot-product example, with its lane decomposition `dot32_split`.
-/

namespace Janus.Amd64

/-- The vector registers an `AvxI` instruction writes, with the width it writes them at. -/
def AvxI.vdsts : AvxI XLoc Loc Addr → List (Nat × Nat)
  | .pint _ l d _ _ | .pshift _ _ l d _ _ | .pimm _ l d _ _ _ | .shuf _ l d _ _ | .blendv _ l d _ _ _
  | .pmovx _ _ _ l d _ | .movdup _ l d _ | .fpArith _ _ l d _ _ | .fpCmp _ l d _ _ _
  | .fpRound _ l d _ _ | .fpHorz _ _ l d _ _ | .fpAddsub _ l d _ _ | .fma _ _ _ _ _ l d _ _
  | .permilv _ l d _ _ | .bcast _ l d _ | .shiftv _ _ l d _ _ | .cvtph2ps l d _ => [(d, l)]
  | .insertpsM d _ _ _ | .pinsr _ d _ _ _ | .movHalfL _ d _ _ | .phminposuw d _ | .sArith _ _ d _ _
  | .sCmp _ d _ _ _ | .cvtsi2f _ _ d _ _ | .cvtff _ d _ _ | .sRound _ d _ _ _ | .movsRR _ d _ _
  | .vload _ d _ | .movdG _ d _ | .cvtps2ph _ (.xmm d) _ _ => [(d, 128)]
  | .pcmpstrm _ _ _ _ _ => [(0, 128)]
  | .cvt op l d _ => [(d, if ExecAVX.cvtHalf op then 128 else l)]
  | .perm2 d _ _ _ | .permd d _ _ | .permq d _ _ | .insert128 d _ _ _ => [(d, 256)]
  | .extract128 (.xmm d) _ _ => [(d, 128)]
  | .maskmov _ l true x _ _ => [(x, l)]
  | .gather e ie l d m _ => [(d, if l / max e ie * e = 256 then 256 else 128), (m, 256)]
  | _ => []

end Janus.Amd64

namespace Janus.Amd64.Tactic

open Janus.Amd64 Janus.Arm64 Janus.Tactic

/-! ## Simp set: the executor -/

janus_rfl_eqns ExecAVX.exec [janus64_exec]

attribute [janus64_exec] ExecAVX.rd ExecAVX.getV ExecAVX.doneV ExecAVX.doneFPV ExecAVX.doneS
  ExecAVX.countOp

/-- The VEX register write in the normal form of the scalar instructions. -/
@[janus64_exec] theorem ExecAVX.setV_eq (s : State) (l n v : Nat) :
    ExecAVX.setV s l n v = { s with xmm := setXmmF s.xmm n (BitVec.ofNat 128 v), ymmHi := setXmmF s.ymmHi n (if l = 256 then BitVec.ofNat 128 (v / 2 ^ 128) else 0) } := rfl

/-- `ExecAVX.setV` is `State.setV`, the VEX write of `Instr.vmov`/`Instr.vop`. -/
theorem ExecAVX.setV_eq_state (s : State) (l n v : Nat) : ExecAVX.setV s l n v = s.setV l n v := rfl

/-- `ExecAVX.getV` is `State.getV`. -/
theorem ExecAVX.getV_eq_state (s : State) (l n : Nat) : ExecAVX.getV s l n = s.getV l n := rfl

/-! ## Compatibility with WP-D at 128 bits -/

@[janus64_exec, janus64_post] theorem pintV_128 (op : PIntOp) (a b : Nat) :
    ExecAVX.pintV op 128 a b = ExecSSE.pintOp op a b := by
  unfold ExecAVX.pintV ExecAVX.perLane; split <;> rfl

@[janus64_exec, janus64_post] theorem pimmV_128 (op : PImmOp) (a b imm : Nat) :
    ExecAVX.pimmV op 128 a b imm = ExecSSE.pimmOp op a b imm := rfl

@[janus64_exec, janus64_post] theorem pshiftV_128 (op : PShiftOp) (e a imm : Nat) :
    ExecAVX.pshiftV op e 128 a imm = ExecSSE.pshiftOp op e a imm := rfl

@[janus64_exec, janus64_post] theorem shufV_128 (op : VShufOp) (b imm : Nat) :
    ExecAVX.shufV op 128 b imm = ExecAVX.shufLane op 0 b imm := rfl

/-- `VPSHUFD xmm` is `PSHUFD`. -/
@[janus64_exec, janus64_post] theorem shufLane_pshufd (b imm : Nat) :
    ExecAVX.shufLane .pshufd 0 b imm = pshufdNat b imm := (pshufd_ofElems b imm).symm

/-- The conversions at 128 bits are WP-D's. -/
theorem cvtV_128 (op : CvtOp) (c : FP.Ctl) (b : Nat) : ExecAVX.cvtV op 128 c b = ExecSSE.cvtOp op c b := by
  cases op <;> rfl

/-- The eight legacy predicates of `VCMPPS`... are `CMPPS`'s. -/
theorem vcmp_legacy (f : Janus.Float.Fmt) (c : FP.Ctl) (p a b : Nat) (hp : p < 8) :
    ExecAVX.vcmp f c p a b = FP.cmp f c p a b := by
  have : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [ExecAVX.vcmp, FP.cmp]; split <;> simp_all)

/-! ## The VEX.128 zero-upper rule -/

/-- A 128-bit VEX write zeroes bits 255:128 of its destination. -/
theorem setV_128_upper (s : State) (n v : Nat) : (ExecAVX.setV s 128 n v).ymmHi n = 0 := by
  simp [ExecAVX.setV]

/-- A VEX write leaves the other registers' upper halves alone. -/
theorem setV_upper_other (s : State) (l n v i : Nat) (h : i ≠ n) :
    (ExecAVX.setV s l n v).ymmHi i = s.ymmHi i := by
  simp [ExecAVX.setV, h]

set_option maxHeartbeats 4000000 in
/-- **The VEX.128 zero-upper rule.** If an AVX instruction completes, every vector register it
writes at 128 bits has bits 255:128 zero afterwards. -/
theorem vex128_zero_upper (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : AvxI XLoc Loc Addr) (s' : State) (h : ExecAVX.exec s next pc ea i = .ok s') :
    ∀ d, (d, 128) ∈ i.vdsts → s'.ymmHi d = 0 := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS,
    ExecAVX.maskmovExec, ExecAVX.gatherExec] at h <;>
    (repeat' split at h) <;> (try cases h) <;> intro d hd <;>
    simp only [AvxI.vdsts, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd <;>
    (try obtain ⟨rfl, hl⟩ := hd) <;> (try subst hl) <;> simp_all [ExecAVX.setV, ExecSSE.raiseMx] <;> omega

set_option maxHeartbeats 4000000 in
/-- The upper halves of the registers an AVX instruction does not write are unchanged
(`VZEROALL` aside, which zeroes them all). -/
theorem vex_upper_other (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : AvxI XLoc Loc Addr) (s' : State) (h : ExecAVX.exec s next pc ea i = .ok s') (hz : i ≠ .vzeroall) :
    ∀ j, j ∉ i.vdsts.map Prod.fst → s'.ymmHi j = s.ymmHi j := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS,
    ExecAVX.maskmovExec, ExecAVX.gatherExec] at h <;>
    (repeat' split at h) <;> (try cases h) <;> intro j hj <;>
    simp only [AvxI.vdsts, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hj <;>
    simp_all [ExecAVX.setV, ExecSSE.raiseMx, ExecSSE.setReg]

/-- **Legacy SSE preserves the upper halves.** No WP-D instruction changes bits 255:128 of any
register. -/
theorem sse_preserves_upper (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : SseI XLoc Loc Addr) (s' : State) (h : ExecSSE.exec s next pc ea i = .ok s') :
    s'.ymmHi = s.ymmHi := by
  cases i <;> simp only [ExecSSE.exec, ExecSSE.doneX, ExecSSE.doneFP] at h <;>
    (repeat' split at h) <;> (try cases h) <;> rfl

/-- `exec` of an AVX instruction is `ExecAVX.exec`. -/
theorem exec_avx (i : AvxI XLoc Loc Addr) (len : Nat) (s : State) :
    exec (.avx i) len s = ExecAVX.exec s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) s.rip.toNat
      (fun a => (ea s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) a).toNat) i := rfl

/-- `exec` of a WP-D instruction is `ExecSSE.exec`. -/
theorem exec_sse (i : SseI XLoc Loc Addr) (len : Nat) (s : State) :
    exec (.sse i) len s = ExecSSE.exec s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) s.rip.toNat
      (fun a => (ea s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) a).toNat) i := rfl

/-- **The VEX.128 zero-upper rule**, for a decoded AVX instruction: every vector register it
writes at 128 bits has bits 255:128 zero afterwards. -/
theorem exec_vex128_zero_upper (i : AvxI XLoc Loc Addr) (len : Nat) (s s' : State)
    (h : exec (.avx i) len s = .ok s') : ∀ d, (d, 128) ∈ i.vdsts → s'.ymmHi d = 0 :=
  vex128_zero_upper s _ _ _ i s' (by rw [exec_avx] at h; exact h)

/-- **Legacy SSE preserves the upper halves**, for a decoded WP-D instruction. -/
theorem exec_sse_preserves_upper (i : SseI XLoc Loc Addr) (len : Nat) (s s' : State)
    (h : exec (.sse i) len s = .ok s') : s'.ymmHi = s.ymmHi :=
  sse_preserves_upper s _ _ _ i s' (by rw [exec_sse] at h; exact h)

/-! ## Elements of 256-bit results -/

/-- Element `i` of the `j`-th `e·k`-bit element is element `k·j + i`. -/
theorem elem_lane {x e k j i : Nat} (h : i < k) : elem (elem x (e * k) j) e i = elem x e (k * j + i) := by
  unfold elem
  apply Nat.eq_of_testBit_eq; intro t
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < e
  · have h1 : t + e * i < e * k := by
      have : e * (i + 1) ≤ e * k := Nat.mul_le_mul_left e h
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    have h2 : t + e * i + e * k * j = t + e * (k * j + i) := by
      rw [Nat.mul_add, ← Nat.mul_assoc]; omega
    simp [ht, h1, h2]
  · simp [ht]

/-- Element `i` of a value below `2^128` as 32-bit elements of its 128-bit lanes. -/
@[janus64_exec, janus64_post] theorem elem_elem128_32 {x j i : Nat} (h : i < 4) :
    elem (elem x 128 j) 32 i = elem x 32 (4 * j + i) := elem_lane (e := 32) (k := 4) h

@[janus64_exec, janus64_post] theorem elem_128_mod (x j : Nat) :
    elem x 128 j % 340282366920938463463374607431768211456 = elem x 128 j :=
  Nat.mod_eq_of_lt (elem_lt x 128 j)

/-- An element of a per-lane 256-bit result. -/
theorem elem_perLane_256 {e k i : Nat} (f : Nat → Nat → Nat → Nat) (a b : Nat) (hk : e * k = 128)
    (hi : i < 2 * k) :
    elem (ExecAVX.perLane 256 f a b) e i = elem (f (i / k) (elem a 128 (i / k)) (elem b 128 (i / k))) e (i % k) := by
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hd : i = k * (i / k) + i % k := (Nat.div_add_mod i k).symm
  have hq : i / k < 2 := by
    rw [Nat.div_lt_iff_lt_mul hk0]; omega
  rw [ExecAVX.perLane, if_pos rfl]
  conv => lhs; rw [hd]
  rw [← elem_lane (Nat.mod_lt i hk0), hk, elem_ofElems _ hq,
    elem_mod_two_pow (by
      have : e * (i % k + 1) ≤ e * k := Nat.mul_le_mul_left e (Nat.mod_lt i hk0)
      omega)]

/-- Per-lane 256-bit results are 256-bit values. -/
theorem perLane_256_lt (f : Nat → Nat → Nat → Nat) (a b : Nat) : ExecAVX.perLane 256 f a b < 2 ^ 256 := by
  rw [ExecAVX.perLane, if_pos rfl]; exact ofElems_lt 128 2 _

@[janus64_exec, janus64_post] theorem pintV_256_mod (op : PIntOp) (a b : Nat) :
    ExecAVX.pintV op 256 a b %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      ExecAVX.pintV op 256 a b := by
  apply Nat.mod_eq_of_lt
  have : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  rw [← this]; unfold ExecAVX.pintV; split <;> exact perLane_256_lt _ _ _

/-- `PMULLW`/`PMULLD`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_mull {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.mull e) a b) e i = elem a e i * elem b e i % 2 ^ e := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]

/-- A WP-D lane vector is a 128-bit value. -/
theorem lanes_lt (e : Nat) (f : Nat → Nat) : ExecSSE.lanes e f < 2 ^ 128 := by
  unfold ExecSSE.lanes
  have h : e * (128 / e) ≤ 128 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self 128 e
  exact Nat.lt_of_lt_of_le (ofElems_lt _ _ _) (Nat.pow_le_pow_right (by decide) h)

/-- The packed integer operations whose result is a lane vector (all but `andn`, `movhl`). -/
def pintLanes : PIntOp → Bool
  | .andn | .movhl => false
  | _ => true

/-- Their results are 128-bit values. -/
@[janus64_exec, janus64_post] theorem pintOp_lanes_mod (op : PIntOp) (a b : Nat) (h : pintLanes op = true) :
    ExecSSE.pintOp op a b % 340282366920938463463374607431768211456 = ExecSSE.pintOp op a b := by
  apply Nat.mod_eq_of_lt
  rw [show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 by decide]
  cases op <;> simp only [pintLanes, reduceCtorEq] at h <;> exact lanes_lt _ _

/-- `PMAXUB/W/D`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_maxu {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.maxu e) a b) e i = max (elem a e i) (elem b e i) := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]
  exact Nat.mod_eq_of_lt (by have := elem_lt a e i; have := elem_lt b e i; omega)

/-- `PMINUB/W/D`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintOp_minu {e i : Nat} (a b : Nat) (h : i < 128 / e) :
    elem (ExecSSE.pintOp (.minu e) a b) e i = min (elem a e i) (elem b e i) := by
  simp only [ExecSSE.pintOp, ExecSSE.lanes]; rw [elem_ofElems _ h]
  exact Nat.mod_eq_of_lt (by have := elem_lt a e i; have := elem_lt b e i; omega)

/-- `VPADDD ymm`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintV_256_add32 {i : Nat} (a b : Nat) (h : i < 8) :
    elem (ExecAVX.pintV (.add 32) 256 a b) 32 i = (elem a 32 i + elem b 32 i) % 4294967296 := by
  unfold ExecAVX.pintV
  simp only [ExecAVX.countOp, Bool.false_eq_true, if_false]
  rw [elem_perLane_256 _ _ _ (k := 4) (by decide) (by omega),
    elem_pintOp_add _ _ (by simp; omega), elem_elem128_32 (Nat.mod_lt _ (by decide)),
    elem_elem128_32 (Nat.mod_lt _ (by decide)), Nat.div_add_mod]

/-- `VPMULLD ymm`, element-wise. -/
@[janus64_exec, janus64_post] theorem elem_pintV_256_mull32 {i : Nat} (a b : Nat) (h : i < 8) :
    elem (ExecAVX.pintV (.mull 32) 256 a b) 32 i = elem a 32 i * elem b 32 i % 4294967296 := by
  unfold ExecAVX.pintV
  simp only [ExecAVX.countOp, Bool.false_eq_true, if_false]
  rw [elem_perLane_256 _ _ _ (k := 4) (by decide) (by omega),
    elem_pintOp_mull _ _ (by simp; omega), elem_elem128_32 (Nat.mod_lt _ (by decide)),
    elem_elem128_32 (Nat.mod_lt _ (by decide)), Nat.div_add_mod]

/-- `PMULLD` results are 128-bit values. -/
@[janus64_exec, janus64_post] theorem pintOp_mull_mod (e a b : Nat) :
    ExecSSE.pintOp (.mull e) a b % 340282366920938463463374607431768211456 = ExecSSE.pintOp (.mull e) a b := by
  apply Nat.mod_eq_of_lt
  simp only [ExecSSE.pintOp, ExecSSE.lanes]
  have h : e * (128 / e) ≤ 128 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self 128 e
  exact Nat.lt_of_lt_of_le (ofElems_lt _ _ _) (Nat.pow_le_pow_right (by decide) h)

/-! ## Wrapping dot products of 32-bit words -/

/-- `Σ_{i < n} A[s·i + j] · B[s·i + j]` over the 32-bit words of `A` at `a` and `B` at `b`
(stride `s`, from word `j`), as a natural number. -/
def dotStride (m : Memory) (a b s j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => dotStride m a b s j n + m.readLE (a + 4 * (s * n + j)) 4 * m.readLE (b + 4 * (s * n + j)) 4

/-- `Σ_{i < n} A[i] · B[i]`: the dot product of `n` 32-bit words. -/
def dot32 (m : Memory) (a b n : Nat) : Nat := dotStride m a b 1 0 n

theorem dot32_zero (m : Memory) (a b : Nat) : dot32 m a b 0 = 0 := rfl

theorem dot32_succ (m : Memory) (a b n : Nat) :
    dot32 m a b (n + 1) = dot32 m a b n + m.readLE (a + 4 * n) 4 * m.readLE (b + 4 * n) 4 := by
  simp [dot32, dotStride]

/-- `k` more words. -/
theorem dot32_add (m : Memory) (a b n : Nat) : ∀ k,
    dot32 m a b (n + k) = dot32 m a b n +
      ExecSSE.sumN k fun j => m.readLE (a + 4 * (n + j)) 4 * m.readLE (b + 4 * (n + j)) 4
  | 0 => rfl
  | k + 1 => by
    rw [← Nat.add_assoc, dot32_succ, dot32_add m a b n k, ExecSSE.sumN, Nat.add_assoc]

theorem sumN_add (k : Nat) (f g : Nat → Nat) :
    ExecSSE.sumN k (fun j => f j + g j) = ExecSSE.sumN k f + ExecSSE.sumN k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ExecSSE.sumN, ih]; omega

theorem sumN_congr (k : Nat) (f g : Nat → Nat) (h : ∀ j, j < k → f j = g j) :
    ExecSSE.sumN k f = ExecSSE.sumN k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ExecSSE.sumN]; rw [ih fun j hj => h j (by omega), h k (by omega)]

/-- Splitting the first `s·k` words into the `s` word classes modulo `s`. -/
theorem dot32_split (m : Memory) (a b s : Nat) : ∀ k,
    dot32 m a b (s * k) = ExecSSE.sumN s fun j => dotStride m a b s j k
  | 0 => by
    rw [Nat.mul_zero, dot32_zero]
    induction s with
    | zero => rfl
    | succ s ih => simp only [ExecSSE.sumN, dotStride]; exact ih
  | k + 1 => by
    rw [Nat.mul_succ, dot32_add, dot32_split m a b s k, ← sumN_add]
    apply sumN_congr; intro j _
    simp only [dotStride]

end Janus.Amd64.Tactic
