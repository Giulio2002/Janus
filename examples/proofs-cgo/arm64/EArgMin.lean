import Extracted

/-!
# `size_t e_argmin(const int64_t *a, size_t n, e_cmp_fn cmp)` (C, arm64): a call through a
# function pointer, and `e_argmin_i64`, which passes it `e_cmp_i64`

```c
size_t e_argmin(const int64_t *a, size_t n, e_cmp_fn cmp) {
	size_t best = 0;
	for (size_t i = 1; i < n; i++)
		if (cmp(&a[i], &a[best]) < 0)
			best = i;
	return best;
}
int e_cmp_i64(const void *x, const void *y) { ... (a > b) - (a < b) ... }
size_t e_argmin_i64(const int64_t *a, size_t n) { return e_argmin(a, n, e_cmp_i64); }
```

**Guarantees.**

* `argmin_summary`: for **every** comparator — code anywhere (`Extracted.program.link impl`,
  for every `impl`) satisfying the function-pointer hypothesis `CFuncIs` with the qsort-style
  comparator contract `CmpPre`/`CmpPost` for some strict order `lt` (the sign of the `int` it
  returns is that of `lt` on the two `int64_t`s its arguments point to; it may use `K` bytes of
  stack) — `e_argmin` returns the index of the first `lt`-minimum of `a[0..n)` (`best`), restores
  the callee-saved state and changes no memory above the stack.
* `cmp_fn`: the compiled `e_cmp_i64` satisfies that hypothesis for the signed order (`K = 0`):
  the hypothesis is satisfiable, by real code.
* `correctness`: so `e_argmin_i64(a, n)` returns the first signed minimum of `a[0..n)`, with no
  hypothesis about the comparator left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI
open Janus.Contracts.Libc (memFrame_trans)

namespace Proof

abbrev cmpE : Nat := segAddr Extracted.program "e_cmp_i64"
abbrev argminE : Nat := segAddr Extracted.program "e_argmin"

/-- The `i`-th `int64_t` at `a`. -/
def word (m : Memory) (a i : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * i) 8)

/-- A comparator call: two readable `int64_t` pointers, a return address, `K` bytes of stack. -/
def CmpPre (K : Nat) (s : State) : Prop :=
  (s.regs 0).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 8 false = true ∧
    (s.regs 1).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 8 false = true ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ CStack s K 0

/-- What it returns: an `int` whose sign bit is `lt *x *y`; memory changed only below `SP`. -/
def CmpPost (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (s s' : State) : Prop :=
  ((s'.regs 0).setWidth 32).msb = lt (word s.mem (s.regs 0).toNat 0) (word s.mem (s.regs 1).toNat 0) ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - K, s.sp.toNat)]

/-! ## The comparator `e_cmp_i64` -/

theorem cmp_fn : CFuncIs Extracted.program (BitVec.ofNat 64 cmpE) (CmpPre 0) (CmpPost BitVec.slt 0) := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hpc ⟨h0b, h0a, h1b, h1a, hal, hlt, hcs⟩
  have hpc' : s.pc = BitVec.ofNat 64 (janus_eval% cmpE) := by rw [hpc]; rfl
  clear hpc
  obtain ⟨-, -, -, -⟩ := hcs
  janus_run
  refine ⟨?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, word, Nat.mul_zero, Nat.add_zero, BitVec.slt_eq_decide]
  generalize BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 0)) 8) = X
  generalize BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 1)) 8) = Y
  by_cases h1 : X.toInt ≤ Y.toInt <;> by_cases h2 : Y.toInt ≤ X.toInt <;>
    simp only [h1, h2, if_true, if_false] <;>
    first | decide | (simp only [show ¬ X.toInt < Y.toInt by omega]; decide) |
      (simp only [show X.toInt < Y.toInt by omega]; decide)

/-! ## `e_argmin`, for every comparator -/

/-- The index of the first `lt`-minimum of `x 0, …, x i`. -/
def best (lt : BitVec 64 → BitVec 64 → Bool) (x : Nat → BitVec 64) : Nat → Nat
  | 0 => 0
  | i + 1 => if lt (x (i + 1)) (x (best lt x i)) then i + 1 else best lt x i

theorem best_le (lt : BitVec 64 → BitVec 64 → Bool) (x : Nat → BitVec 64) : ∀ i, best lt x i ≤ i
  | 0 => Nat.le_refl _
  | i + 1 => by
    simp only [best]; split
    · exact Nat.le_refl _
    · have := best_le lt x i; omega

/-- The loop head `add x1, x23, x20, lsl #3` and the indirect call `blr x24`. -/
abbrev head : Nat := argminE + 0x40
abbrev blrPC : Nat := argminE + 0x48

/-- What `e_argmin` needs. -/
def APre (impl : List Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64)
    (s : State) : Prop :=
  s.regs 0 = a ∧ s.regs 1 = n ∧
    CFuncIs (Extracted.program.link impl) (s.regs 2) (CmpPre K) (CmpPost lt K) ∧
    a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible a.toNat (8 * n.toNat) false = true ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ CStack s (64 + K) 0 ∧
    Outside a.toNat (8 * n.toNat) [(s.sp.toNat - (64 + K), s.sp.toNat)]

/-- What it guarantees. -/
def APost (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64) (s s' : State) : Prop :=
  CReturn s s' ∧ (s'.regs 0).toNat = best lt (word s.mem a.toNat) (n.toNat - 1) ∧
    MemFrame s.mem s'.mem [(s.sp.toNat - (64 + K), s.sp.toNat)]


theorem nv_sub_zero32 (x : BitVec 32) :
    ((addSub x 0#32 true).snd.n == (addSub x 0#32 true).snd.v) = !x.msb := by
  have h1 : BitVec.ofNat 32 (x.toNat + 4294967295 + 1) = x := by
    apply BitVec.eq_of_toNat_eq; have := x.isLt
    simp only [BitVec.toNat_ofNat]; omega
  have h2 : (~~~(0#32)).toInt = -1 := by decide
  simp only [addSub, addWithCarry, ite_true, h2, Bool.toNat_true]
  simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow, Nat.reduceSub, h1]
  have h3 : decide (x.toInt ≠ x.toInt + -1 + ((1 : Nat) : Int)) = false := by simp; omega
  rw [h3]; cases x.msb <;> rfl

/-- A frame with more excluded bytes. -/
theorem memFrame_widen {m m' : Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (hw : ∀ a n, Outside a n rs' → Outside a n rs) : MemFrame m m' rs' :=
  ⟨fun a n ho => h.readLE a n (hw a n ho), h.accessible⟩

theorem best_succ (lt : BitVec 64 → BitVec 64 → Bool) (x : Nat → BitVec 64) (i : Nat) (hi : 1 ≤ i) :
    best lt x i = if lt (x i) (x (best lt x (i - 1))) then i else best lt x (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [best]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem argmin_loop (impl : List Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64)
    (s : State) (hpre : APre impl lt K a n s) :
    ∀ k (S : State) (i : Nat), i + k + 1 = n.toNat → 1 ≤ i →
      S.pc = BitVec.ofNat 64 (janus_eval% head) → S.regs 19 = BitVec.ofNat 64 i →
      S.regs 20 = BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1)) →
      S.regs 21 = BitVec.ofNat 64 (a.toNat + 8 * i) → S.regs 22 = n → S.regs 23 = a →
      S.regs 24 = s.regs 2 → S.sp = s.sp - 64#64 → S.regs 29 = s.sp - 64#64 →
      S.regs 25 = s.regs 25 → S.regs 26 = s.regs 26 → S.regs 27 = s.regs 27 → S.regs 28 = s.regs 28 →
      S.fpcr = s.fpcr → VLow s S → MemFrame s.mem S.mem [(s.sp.toNat - (64 + K), s.sp.toNat)] →
      S.mem.readLE (s.sp.toNat - 64) 8 = (s.regs 29).toNat → S.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 30).toNat →
      S.mem.readLE (s.sp.toNat - 48) 8 = (s.regs 19).toNat → S.mem.readLE (s.sp.toNat - 40) 8 = (s.regs 20).toNat →
      S.mem.readLE (s.sp.toNat - 32) 8 = (s.regs 21).toNat → S.mem.readLE (s.sp.toNat - 24) 8 = (s.regs 22).toNat →
      S.mem.readLE (s.sp.toNat - 16) 8 = (s.regs 23).toNat → S.mem.readLE (s.sp.toNat - 8) 8 = (s.regs 24).toNat →
      ReachesRet (Extracted.program.link impl) (s.regs 30) S (APost lt K a n s) := by
  obtain ⟨h0, h1, hf, hab, hac, hal, hlt, ⟨hsa, hsb, hsc, hsw⟩, hout⟩ := hpre
  intro k
  induction k with
  | zero =>
    intro S i hk hi1 hpc h19 h20 h21 h22 h23 h24 hsp h29 h25 h26 h27 h28 hfc hv hm m1 m2 m3 m4 m5 m6 m7 m8
    have hbi := best_le lt (word s.mem a.toNat) (i - 1)
    janus_run until [janus_eval% blrPC]
    refine ReachesRet.blr_call (rn := 24) (c := janus_eval% blrPC) (w := 0xd63f0300) rfl
      (stepOK_link impl (by decide)) (by decide) (by simpa [setReg_apply, h24] using hf) ?_ ?_
    · have hx1 : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1) * 8)).toNat =
          a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [CmpPre, blrState, State.writeZR, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hx1]
      have hai : (BitVec.ofNat 64 (a.toNat + 8 * i)).toNat = a.toNat + 8 * i := by
        rw [BitVec.toNat_ofNat]; omega
      rw [hai, hm.accessible, hm.accessible]
      refine ⟨by omega, Memory.accessible_mono _ hac (by omega) (by omega), by omega,
        Memory.accessible_mono _ hac (by omega) (by omega), by decide, by decide, ?_⟩
      have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      refine ⟨by simp only [h64]; omega, by simp only [h64]; omega, by simp only [h64]; omega, ?_⟩
      simp only [h64, hm.accessible]
      exact Memory.accessible_mono _ hsw (by omega) (by omega)
    · intro s1 hpc1 hcr1 hpost1
      have V1 := hcr1.vlow
      have C1 := hcr1
      obtain ⟨hpo, hmf1⟩ := hpost1
      simp only [cReturn_iff, blrState, State.writeZR, setReg_apply, ↓reduceIte, Nat.reduceEqDiff,
        Nat.reducePow] at hcr1 hpc1 hpo hmf1
      obtain_cret hcr1
      janus_run [m1, m2, m3, m4, m5, m6, m7, m8]
      have hw0 : ∀ j, j < n.toNat → S.mem.readLE (a.toNat + 8 * j) 8 = s.mem.readLE (a.toNat + 8 * j) 8 :=
        fun j hj => hm.readLE _ _ (by simp at hout ⊢; omega)
      have hb1 : best lt (word s.mem a.toNat) (i - 1) < n.toNat := by omega
      have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      have hai : (BitVec.ofNat 64 (a.toNat + 8 * i)).toNat = a.toNat + 8 * i := by
        rw [BitVec.toNat_ofNat]; omega
      have hx1 : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1) * 8)).toNat =
          a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [hai, hx1, word, Nat.mul_zero, Nat.add_zero, hw0 i (by omega), hw0 _ hb1] at hpo
      simp only [h64] at hmf1
      have VL := hv.trans V1 rfl
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, VL 8 (by omega) (by omega),
        VL 9 (by omega) (by omega), VL 10 (by omega) (by omega), VL 11 (by omega) (by omega),
        VL 12 (by omega) (by omega), VL 13 (by omega) (by omega), VL 14 (by omega) (by omega),
        VL 15 (by omega) (by omega)⟩, ?_, ?_⟩
      all_goals try (simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]; done)
      · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]; exact C1.x25.trans h25
      · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]; exact C1.x26.trans h26
      · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]; exact C1.x27.trans h27
      · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]; exact C1.x28.trans h28
      · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, nv_sub_zero32, hpo]
        rw [show n.toNat - 1 = i by omega, best_succ _ _ _ hi1]
        simp only [word]
        by_cases hL : lt (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * i) 8))
          (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1)) 8)) = true
        · simp only [hL, Bool.not_true, Bool.false_eq_true, if_false, if_true, BitVec.toNat_ofNat]; omega
        · have hL' : lt (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * i) 8))
              (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1)) 8)) = false := by
            simpa using hL
          simp only [hL', Bool.not_false, if_true, Bool.false_eq_true, if_false, BitVec.toNat_ofNat]
          omega
      · exact memFrame_widen (memFrame_trans hm hmf1) (by intro x y; simp; omega)
  | succ k ih =>
    intro S i hk hi1 hpc h19 h20 h21 h22 h23 h24 hsp h29 h25 h26 h27 h28 hfc hv hm m1 m2 m3 m4 m5 m6 m7 m8
    have hbi := best_le lt (word s.mem a.toNat) (i - 1)
    janus_run until [janus_eval% blrPC]
    refine ReachesRet.blr_call (rn := 24) (c := janus_eval% blrPC) (w := 0xd63f0300) rfl
      (stepOK_link impl (by decide)) (by decide) (by simpa [setReg_apply, h24] using hf) ?_ ?_
    · have hx1 : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1) * 8)).toNat =
          a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [CmpPre, blrState, State.writeZR, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, hx1]
      have hai : (BitVec.ofNat 64 (a.toNat + 8 * i)).toNat = a.toNat + 8 * i := by
        rw [BitVec.toNat_ofNat]; omega
      rw [hai, hm.accessible, hm.accessible]
      refine ⟨by omega, Memory.accessible_mono _ hac (by omega) (by omega), by omega,
        Memory.accessible_mono _ hac (by omega) (by omega), by decide, by decide, ?_⟩
      have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      refine ⟨by simp only [h64]; omega, by simp only [h64]; omega, by simp only [h64]; omega, ?_⟩
      simp only [h64, hm.accessible]
      exact Memory.accessible_mono _ hsw (by omega) (by omega)
    · intro s1 hpc1 hcr1 hpost1
      have V1 := hcr1.vlow
      have C1 := hcr1
      obtain ⟨hpo, hmf1⟩ := hpost1
      simp only [cReturn_iff, blrState, State.writeZR, setReg_apply, ↓reduceIte, Nat.reduceEqDiff,
        Nat.reducePow] at hcr1 hpc1 hpo hmf1
      obtain_cret hcr1
      janus_run [m1, m2, m3, m4, m5, m6, m7, m8] until [janus_eval% head]
      have hw0 : ∀ j, j < n.toNat → S.mem.readLE (a.toNat + 8 * j) 8 = s.mem.readLE (a.toNat + 8 * j) 8 :=
        fun j hj => hm.readLE _ _ (by simp at hout ⊢; omega)
      have hb1 : best lt (word s.mem a.toNat) (i - 1) < n.toNat := by omega
      have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
        rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      have hai : (BitVec.ofNat 64 (a.toNat + 8 * i)).toNat = a.toNat + 8 * i := by
        rw [BitVec.toNat_ofNat]; omega
      have hx1 : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1) * 8)).toNat =
          a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      simp only [hai, hx1, word, Nat.mul_zero, Nat.add_zero, hw0 i (by omega), hw0 _ hb1] at hpo
      simp only [h64] at hmf1
      have VL := hv.trans V1 rfl
      have hF := memFrame_widen (rs' := [(s.sp.toNat - (64 + K), s.sp.toNat)]) (memFrame_trans hm hmf1)
        (by intro x y; simp; omega)
      have hs1 : ∀ x, s.sp.toNat - 64 ≤ x → x + 8 ≤ s.sp.toNat → s1.mem.readLE x 8 = S.mem.readLE x 8 :=
        fun x h1 h2 => hmf1.readLE _ _ (by simp; omega)
      have hbest : best lt (word s.mem a.toNat) (i + 1 - 1) = best lt (word s.mem a.toNat) i := by simp
      refine ih _ (i + 1) (by omega) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ rfl VL hF ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · rw [hbest, best_succ _ _ _ hi1, nv_sub_zero32, hpo]
        simp only [word]
        by_cases hL : lt (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * i) 8))
          (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1)) 8)) = true
        · simp only [hL, Bool.not_true, Bool.false_eq_true, if_false, if_true]
        · have hL' : lt (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * i) 8))
              (BitVec.ofNat 64 (s.mem.readLE (a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1)) 8)) = false := by
            simpa using hL
          simp only [hL', Bool.not_false, if_true, Bool.false_eq_true, if_false]
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · exact C1.x22.trans h22
      · exact C1.x23.trans h23
      · exact C1.x24.trans h24
      · exact C1.fp.trans h29
      · exact C1.x25.trans h25
      · exact C1.x26.trans h26
      · exact C1.x27.trans h27
      · exact C1.x28.trans h28
      · rw [hs1 _ (by omega) (by omega)]; exact m1
      · rw [hs1 _ (by omega) (by omega)]; exact m2
      · rw [hs1 _ (by omega) (by omega)]; exact m3
      · rw [hs1 _ (by omega) (by omega)]; exact m4
      · rw [hs1 _ (by omega) (by omega)]; exact m5
      · rw [hs1 _ (by omega) (by omega)]; exact m6
      · rw [hs1 _ (by omega) (by omega)]; exact m7
      · rw [hs1 _ (by omega) (by omega)]; exact m8


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem argmin_entry (impl : List Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64) :
    Summary (Extracted.program.link impl) argminE (APre impl lt K a n) (APost lt K a n) := by
  intro s hpc ⟨h0, h1, hf, hab, hac, hal, hlt, ⟨hsa, hsb, hsc, hsw⟩, hout⟩
  have hpc' : s.pc = BitVec.ofNat 64 (janus_eval% argminE) := hpc
  clear hpc
  have hpre : APre impl lt K a n s := ⟨h0, h1, hf, hab, hac, hal, hlt, ⟨hsa, hsb, hsc, hsw⟩, hout⟩
  have h64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run until [janus_eval% head]
  · refine ⟨CReturn.of_eqs rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl, ?_, by janus_frame⟩
    all_goals simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff]
    rw [show n.toNat - 1 = 0 by omega]; rfl
  · refine argmin_loop impl lt K a n s hpre (n.toNat - 2) _ 1 (by omega) (Nat.le_refl _) rfl
      ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ rfl (VLow.of_eq rfl) (by janus_frame) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff])
    all_goals (try (janus_simp; done))
    · rfl
    · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]


/-! ## `e_argmin_i64`: the comparator discharged -/

theorem link_nil : Extracted.program.link [] = Extracted.program := by
  simp [Program.link]

/-- `e_argmin` with `e_cmp_i64` (the hypothesis `CFuncIs` replaced by the comparator's address). -/
theorem argmin_cmp (a n : BitVec 64) :
    Summary Extracted.program argminE
      (fun s => s.regs 0 = a ∧ s.regs 1 = n ∧ s.regs 2 = BitVec.ofNat 64 cmpE ∧
        a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible a.toNat (8 * n.toNat) false = true ∧
        (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ CStack s (64 + 0) 0 ∧
        Outside a.toNat (8 * n.toNat) [(s.sp.toNat - (64 + 0), s.sp.toNat)])
      (APost BitVec.slt 0 a n) := by
  have h := argmin_entry [] BitVec.slt 0 a n
  rw [link_nil] at h
  exact h.mono (fun s ⟨h0, h1, h2, r⟩ => ⟨h0, h1, by rw [h2]; exact cmp_fn, r⟩) (fun _ _ _ h => h)

theorem correctness (a n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, n]
      (fun s => Extracted.program.DataLoaded s.mem ∧ a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible a.toNat (8 * n.toNat) false = true ∧ CStack s 64 0 ∧
        Outside a.toNat (8 * n.toNat) [(s.sp.toNat - 64, s.sp.toNat)])
      (fun s s' => (s'.regs 0).toNat = best BitVec.slt (word s.mem a.toNat) (n.toNat - 1) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 64, s.sp.toNat)]) := by
  intro ret hret s hs ⟨hd, hab, hac, ⟨hsa, hsb, hsc, hsw⟩, hout⟩
  janus_intro hs.call
  janus_data hd []
  have hr48 : ret < 2 ^ 48 := hret.user
  janus_run [GoABI.regLR] calls [argmin_cmp a n]
  rename_i hpost
  obtain ⟨hc, hx, hmf⟩ := hpost
  exact ⟨by simpa [setReg] using (cReturn_iff _ _).1 hc, hx, hmf⟩

end Proof
