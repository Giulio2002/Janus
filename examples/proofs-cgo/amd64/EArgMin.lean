import Extracted

/-!
# `size_t e_argmin(const int64_t *a, size_t n, e_cmp_fn cmp)` (C, amd64): a call through a
# function pointer, and `e_argmin_i64`, which passes it `e_cmp_i64`

The x86-64 counterpart of the arm64 proof (same C source).

**Guarantees.**

* `argmin_entry`: for **every** comparator, code anywhere (`Extracted.program.link impl`, for
  every `impl`) satisfying the function-pointer hypothesis `CFuncIs` with the qsort-style
  comparator contract `CmpPre`/`CmpPost` for some strict order `lt` (the sign of the `int` it
  returns is that of `lt` on the two `int64_t`s `RDI`, `RSI` point to; it may use `K` bytes of
  stack), `e_argmin` returns the index of the first `lt`-minimum of `a[0..n)` (`best`), restores
  the callee-saved state and changes no memory above the stack. The loop reaches the comparator
  by `call *%r14` (`ReachesRet.callInd_call`).
* `cmp_fn`: the compiled `e_cmp_i64` satisfies that hypothesis for the signed order (`K = 0`).
* `correctness`: so `e_argmin_i64(a, n)` (`mov $e_cmp_i64, %rdx; jmp e_argmin`) returns the first
  signed minimum of `a[0..n)`, with no hypothesis about the comparator left. The extractor finds
  `e_cmp_i64` through the immediate operand (`cImmediateRoots`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI
open Janus.Contracts.Libc (memFrame_trans)

namespace Proof

abbrev cmpE : Nat := segAddr Extracted.program "e_cmp_i64"
abbrev argminE : Nat := segAddr Extracted.program "e_argmin"

/-- The `i`-th `int64_t` at `a`. -/
def word (m : Janus.Arm64.Memory) (a i : Nat) : BitVec 64 := BitVec.ofNat 64 (m.readLE (a + 8 * i) 8)

/-- A comparator call: two readable `int64_t` pointers (`RDI`, `RSI`), `K` bytes of stack below
the return address, the direction flag clear. -/
def CmpPre (K : Nat) (s : State) : Prop :=
  (s.regs 7).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 7).toNat 8 false = true ∧
    (s.regs 6).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat 8 false = true ∧
    CStack s K 8 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false

/-- What it returns: an `int` whose sign bit is `lt *x *y`; memory changed only below `RSP`. -/
def CmpPost (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (s s' : State) : Prop :=
  ((s'.regs 0).setWidth 32).msb = lt (word s.mem (s.regs 7).toNat 0) (word s.mem (s.regs 6).toNat 0) ∧
    MemFrame s.mem s'.mem [((s.regs 4).toNat - K, (s.regs 4).toNat)]

theorem cmp_fn : CFuncIs Extracted.program (BitVec.ofNat 64 cmpE) (CmpPre 0) (CmpPost BitVec.slt 0) := by
  refine ⟨by decide, ?_⟩
  intro s hpc ⟨h0b, h0a, h1b, h1a, ⟨_, hsb, hnw, hacc⟩, hra, hdf⟩
  have hpc' : s.rip = BitVec.ofNat 64 (janus_eval% cmpE) := by rw [hpc]; rfl
  clear hpc
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hsb
  janus64_run
  refine ⟨?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, word, Nat.mul_zero, Nat.add_zero, BitVec.slt_eq_decide]
  generalize BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 7)) 8) = X
  generalize BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 6)) 8) = Y
  by_cases h1 : X.toInt < Y.toInt <;> by_cases h2 : Y.toInt < X.toInt <;>
    simp only [h1, h2, if_true, if_false, decide_true, decide_false] <;>
    first | decide | omega

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

theorem best_succ (lt : BitVec 64 → BitVec 64 → Bool) (x : Nat → BitVec 64) (i : Nat) (hi : 1 ≤ i) :
    best lt x i = if lt (x i) (x (best lt x (i - 1))) then i else best lt x (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp [best]

/-- The loop head `lea (%r12,%rbp,8), %rsi` and the indirect call `call *%r14`. -/
abbrev head : Nat := argminE + 0x30
abbrev callPC : Nat := argminE + 0x38

/-- What `e_argmin` needs. -/
def APre (impl : List Amd64.Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64)
    (s : State) : Prop :=
  s.regs 7 = a ∧ s.regs 6 = n ∧
    CFuncIs (Extracted.program.link impl) (s.regs 2) (CmpPre K) (CmpPost lt K) ∧
    a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible a.toNat (8 * n.toNat) false = true ∧
    CStack s (48 + K) 8 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false ∧
    Outside a.toNat (8 * n.toNat) [((s.regs 4).toNat - (48 + K), (s.regs 4).toNat + 8)]

/-- What it guarantees. -/
def APost (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64) (s s' : State) : Prop :=
  CReturn s s' ∧ (s'.regs 0).toNat = best lt (word s.mem a.toNat) (n.toNat - 1) ∧
    MemFrame s.mem s'.mem [((s.regs 4).toNat - (48 + K), (s.regs 4).toNat)]

/-- A frame with more excluded bytes. -/
theorem memFrame_widen {m m' : Janus.Arm64.Memory} {rs rs' : List (Nat × Nat)} (h : MemFrame m m' rs)
    (hw : ∀ a n, Outside a n rs' → Outside a n rs) : MemFrame m m' rs' :=
  ⟨fun a n ho => h.readLE a n (hw a n ho), h.accessible⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem argmin_loop (impl : List Amd64.Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64)
    (s : State) (hpre : APre impl lt K a n s) :
    ∀ k (S : State) (i : Nat), i + k + 1 = n.toNat → 1 ≤ i →
      S.rip = BitVec.ofNat 64 (janus_eval% head) → S.regs 3 = BitVec.ofNat 64 i →
      S.regs 5 = BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1)) →
      S.regs 12 = a → S.regs 13 = n → S.regs 14 = s.regs 2 → S.regs 4 = s.regs 4 - 40#64 →
      S.regs 15 = s.regs 15 → S.df = false → S.mxcsr.toNat / 64 = s.mxcsr.toNat / 64 →
      S.fpucw = s.fpucw → MemFrame s.mem S.mem [((s.regs 4).toNat - (48 + K), (s.regs 4).toNat)] →
      S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 14).toNat →
      S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 13).toNat →
      S.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 12).toNat →
      S.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 5).toNat →
      S.mem.readLE ((s.regs 4).toNat - 40) 8 = (s.regs 3).toNat →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S (APost lt K a n s) := by
  obtain ⟨h0, h1, hf, hab, hac, ⟨hsa, hsb, hsc, hsw⟩, hra, hdf0, hout⟩ := hpre
  simp only [CABI.regSP] at hsa hsb hsc hsw
  simp only [outside_cons, outside_nil, and_true] at hout
  have h40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  intro k
  induction k with
  | zero =>
    intro S i hk hi1 hpc h3 h5 h12 h13 h14 h4 h15 hdf hmx hcw hm m1 m2 m3 m4 m5
    have hbi := best_le lt (word s.mem a.toNat) (i - 1)
    janus64_run until [janus_eval% callPC]
    have h48 : (s.regs 4 - 40#64 - 8).toNat = (s.regs 4).toNat - 48 := by
      show (s.regs 4 - 40#64 - 8#64).toNat = _
      rw [BitVec.toNat_sub, h40]; simp only [BitVec.toNat_ofNat]; omega
    have hai : (a + BitVec.ofNat 64 i <<< 3).toNat = a.toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; simp only [Nat.shiftLeft_eq]
      have := best_le lt (word s.mem a.toNat) (i - 1)
      rw [Nat.mod_eq_of_lt (a := i) (by omega)]; omega
    have hab' : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1)) <<< 3).toNat =
        a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; simp only [Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (a := best lt (word s.mem a.toNat) (i - 1)) (by omega)]; omega
    refine ReachesRet.callInd_call (r := 14) (c := janus_eval% callPC) (len := 3) (bs := [0x41, 0xff, 0xd6, 0x85, 0xc0, 0x48, 0x0f, 0x48, 0xeb, 0x48, 0x83, 0xc3, 0x01, 0x49, 0x39])
      rfl (stepOK_link impl (by decide)) (by simpa [setRegF_apply, h14] using hf) ?_ ?_ ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h4, h48, hm.accessible]
      exact Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)
    · simp only [CmpPre, callState, State.setReg, State.setRip, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff,
        CStack, CABI.regSP, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.readLE_writeLE_self, h4, h48,
        hai, hab', hm.accessible]
      refine ⟨by omega, Janus.Arm64.Memory.accessible_mono _ hac (by omega) (by omega), by omega,
        Janus.Arm64.Memory.accessible_mono _ hac (by omega) (by omega),
        ⟨by omega, by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)⟩,
        by decide, trivial⟩
    · intro s1 hpc1 hcr1 hpost1
      obtain ⟨hpo, hmf1⟩ := hpost1
      simp only [cReturn_iff, callState, State.setReg, State.setRip, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff,
        retAddrOf_eq, Janus.Arm64.Memory.readLE_writeLE_self, h4, h48, hai, hab', CmpPost, word,
        BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow, Nat.mul_zero, Nat.add_zero]
        at hcr1 hpc1 hpo hmf1
      obtain ⟨c1sp, c1bx, c1bp, c112, c113, c114, c115, c1df, c1mx, c1cw⟩ := hcr1
      have hb1 : best lt (word s.mem a.toNat) (i - 1) < n.toNat := by omega
      have hw0 : ∀ j, j < n.toNat → (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 48) 8 (janus_eval% (argminE + 0x3b))).readLE
          (a.toNat + 8 * j) 8 = s.mem.readLE (a.toNat + 8 * j) 8 := fun j hj => by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hm.readLE _ _ (by simp; omega)]
        omega
      rw [hw0 i (by omega), hw0 _ hb1] at hpo
      janus64_run [m1, m2, m3, m4, m5]
      have hwf : MemFrame S.mem (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 48) 8 (janus_eval% (argminE + 0x3b)))
          [((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)] :=
        Janus.Contracts.Libc.memFrame_of_bytes rfl fun _ h => Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)
      refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals dsimp only
      all_goals first
        | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; done)
        | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, c115, h15]; done)
        | exact c1df
        | (rw [c1mx, hmx])
        | (rw [c1cw, hcw])
        | exact memFrame_widen (memFrame_trans hm (memFrame_trans hwf hmf1)) (by intro x y; simp; omega)
        | skip
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hpo]
      rw [show n.toNat - 1 = i by omega, best_succ _ _ _ hi1]
      simp only [word, Nat.mul_zero, Nat.add_zero]
      have hbi' := best_le lt (word s.mem a.toNat) (i - 1)
      have hnl := n.isLt
      split <;> rename_i hL <;> simp only [BitVec.toNat_ofNat, hL, if_true, if_false, Bool.false_eq_true] <;> omega
  | succ k ih =>
    intro S i hk hi1 hpc h3 h5 h12 h13 h14 h4 h15 hdf hmx hcw hm m1 m2 m3 m4 m5
    have hbi := best_le lt (word s.mem a.toNat) (i - 1)
    janus64_run until [janus_eval% callPC]
    have h48 : (s.regs 4 - 40#64 - 8).toNat = (s.regs 4).toNat - 48 := by
      show (s.regs 4 - 40#64 - 8#64).toNat = _
      rw [BitVec.toNat_sub, h40]; simp only [BitVec.toNat_ofNat]; omega
    have hai : (a + BitVec.ofNat 64 i <<< 3).toNat = a.toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; simp only [Nat.shiftLeft_eq]
      have := best_le lt (word s.mem a.toNat) (i - 1)
      rw [Nat.mod_eq_of_lt (a := i) (by omega)]; omega
    have hab' : (a + BitVec.ofNat 64 (best lt (word s.mem a.toNat) (i - 1)) <<< 3).toNat =
        a.toNat + 8 * best lt (word s.mem a.toNat) (i - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]; simp only [Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (a := best lt (word s.mem a.toNat) (i - 1)) (by omega)]; omega
    refine ReachesRet.callInd_call (r := 14) (c := janus_eval% callPC) (len := 3) (bs := [0x41, 0xff, 0xd6, 0x85, 0xc0, 0x48, 0x0f, 0x48, 0xeb, 0x48, 0x83, 0xc3, 0x01, 0x49, 0x39])
      rfl (stepOK_link impl (by decide)) (by simpa [setRegF_apply, h14] using hf) ?_ ?_ ?_
    · simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h4, h48, hm.accessible]
      exact Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)
    · simp only [CmpPre, callState, State.setReg, State.setRip, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff,
        CStack, CABI.regSP, Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.readLE_writeLE_self, h4, h48,
        hai, hab', hm.accessible]
      refine ⟨by omega, Janus.Arm64.Memory.accessible_mono _ hac (by omega) (by omega), by omega,
        Janus.Arm64.Memory.accessible_mono _ hac (by omega) (by omega),
        ⟨by omega, by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)⟩,
        by decide, trivial⟩
    · intro s1 hpc1 hcr1 hpost1
      obtain ⟨hpo, hmf1⟩ := hpost1
      simp only [cReturn_iff, callState, State.setReg, State.setRip, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff,
        retAddrOf_eq, Janus.Arm64.Memory.readLE_writeLE_self, h4, h48, hai, hab', CmpPost, word,
        BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceAdd, Nat.reducePow, Nat.mul_zero, Nat.add_zero]
        at hcr1 hpc1 hpo hmf1
      obtain ⟨c1sp, c1bx, c1bp, c112, c113, c114, c115, c1df, c1mx, c1cw⟩ := hcr1
      have hb1 : best lt (word s.mem a.toNat) (i - 1) < n.toNat := by omega
      have hw0 : ∀ j, j < n.toNat → (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 48) 8 (janus_eval% (argminE + 0x3b))).readLE
          (a.toNat + 8 * j) 8 = s.mem.readLE (a.toNat + 8 * j) 8 := fun j hj => by
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hm.readLE _ _ (by simp; omega)]
        omega
      rw [hw0 i (by omega), hw0 _ hb1] at hpo
      janus64_run [m1, m2, m3, m4, m5] until [janus_eval% head]
      have hwf : MemFrame S.mem (Janus.Arm64.Memory.writeLE S.mem ((s.regs 4).toNat - 48) 8 (janus_eval% (argminE + 0x3b)))
          [((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)] :=
        Janus.Contracts.Libc.memFrame_of_bytes rfl fun _ h => Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)
      have hF := memFrame_widen (rs' := [((s.regs 4).toNat - (48 + K), (s.regs 4).toNat)])
        (memFrame_trans hm (memFrame_trans hwf hmf1)) (by intro x y; simp; omega)
      have hs1 : ∀ x, (s.regs 4).toNat - 40 ≤ x → x + 8 ≤ (s.regs 4).toNat → s1.mem.readLE x 8 = S.mem.readLE x 8 :=
        fun x h1 h2 => by
          rw [hmf1.readLE _ _ (by simp; omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; omega
      have hbest : best lt (word s.mem a.toNat) (i + 1 - 1) = best lt (word s.mem a.toNat) i := by simp
      have hnl := n.isLt
      have hbi' := best_le lt (word s.mem a.toNat) (i - 1)
      refine ih _ (i + 1) (by omega) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hF ?_ ?_ ?_ ?_ ?_
      all_goals dsimp only
      all_goals first
        | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, c112, c113, c114, c115, h12, h13, h14, h15]; done)
        | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, c1sp, h4, BitVec.sub_add_cancel]; done)
        | (rw [c1mx, hmx])
        | (rw [c1cw, hcw])
        | (rw [hs1 _ (by omega) (by omega)]; first | with_reducible exact m1 | with_reducible exact m2 | with_reducible exact m3 | with_reducible exact m4 | with_reducible exact m5 | exact m1 | exact m2 | exact m3 | exact m4 | exact m5)
        | skip
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, hpo]
      rw [hbest, best_succ _ _ _ hi1]
      simp only [word, Nat.mul_zero, Nat.add_zero]
      split <;> rename_i hL <;> simp only [hL, if_true, if_false, Bool.false_eq_true]



set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem argmin_entry (impl : List Amd64.Segment) (lt : BitVec 64 → BitVec 64 → Bool) (K : Nat) (a n : BitVec 64) :
    Summary (Extracted.program.link impl) argminE (APre impl lt K a n) (APost lt K a n) := by
  intro s hpc hpre
  have hpre' := hpre
  obtain ⟨h0, h1, hf, hab, hac, ⟨hsa, hsb, hsc, hsw⟩, hra, hdf0, hout⟩ := hpre
  have hpc' : s.rip = BitVec.ofNat 64 (janus_eval% argminE) := hpc
  clear hpc
  simp only [CABI.regSP] at hsa hsb hsc hsw
  janus64_run until [janus_eval% head]
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by janus_frame⟩
    all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; done)
    · simp only [CABI.regSP, setRegF_apply, ↓reduceIte]; rfl
    · rw [show n.toNat - 1 = 0 by omega]; simp [best, setRegF_apply]
  · refine argmin_loop impl lt K a n s hpre' (n.toNat - 2) _ 1 (by omega) (Nat.le_refl _) rfl
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by janus_frame) ?_ ?_ ?_ ?_ ?_
    all_goals try (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; done)
    all_goals try (janus64_simp; done)
    simp [best, setRegF_apply]

/-! ## `e_argmin_i64`: the comparator discharged -/

theorem link_nil : Extracted.program.link [] = Extracted.program := by
  simp [Amd64.Program.link]

/-- `e_argmin` with `e_cmp_i64` (the hypothesis `CFuncIs` replaced by the comparator's address). -/
theorem argmin_cmp (a n : BitVec 64) :
    Summary Extracted.program argminE
      (fun s => s.regs 7 = a ∧ s.regs 6 = n ∧ s.regs 2 = BitVec.ofNat 64 cmpE ∧
        a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧ s.mem.accessible a.toNat (8 * n.toNat) false = true ∧
        ((s.regs 4).toNat % 16 = 8 ∧ 48 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧
          s.mem.accessible ((s.regs 4).toNat - 48) 56 true = true) ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.df = false ∧
        Outside a.toNat (8 * n.toNat) [((s.regs 4).toNat - (48 + 0), (s.regs 4).toNat + 8)])
      (APost BitVec.slt 0 a n) := by
  have h := argmin_entry [] BitVec.slt 0 a n
  rw [link_nil] at h
  exact h.mono (fun s ⟨h0, h1, h2, h3, h4, ⟨c1, c2, c3, c4⟩, r⟩ => ⟨h0, h1, by rw [h2]; exact cmp_fn, h3, h4,
    ⟨c1, c2, c3, c4⟩, r⟩) (fun _ _ _ h => h)

set_option maxRecDepth 100000 in
theorem correctness (a n : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, n]
      (fun s => a.toNat + 8 * n.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible a.toNat (8 * n.toNat) false = true ∧ CStack s 48 8 ∧
        Outside a.toNat (8 * n.toNat) [((s.regs 4).toNat - 48, (s.regs 4).toNat + 8)])
      (fun s s' => (s'.regs 0).toNat = best BitVec.slt (word s.mem a.toNat) (n.toNat - 1) ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 48, (s.regs 4).toNat)]) := by
  intro ret hret s hs ⟨hab, hac, ⟨hsa, hsb, hsc, hsw⟩, hout⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = a := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = n := hs.reg (i := 1) (by simp)
  have hr47 : ret < 2 ^ 47 := hret.user
  simp only [CABI.regSP, Amd64.Program.withExit] at hsa hsb hsc hsw h_ret
  -- the summary's `Outside` premise, unfolded as the integrated stepping simp set leaves it
  have hout' := hout
  simp only [outside_cons, outside_nil, and_true] at hout'
  janus64_run calls [argmin_cmp a n]
  rename_i hpost
  obtain ⟨hc, hx, hmf⟩ := hpost
  have := (cReturn_iff _ _).1 hc
  simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, CABI.regSP] at this
  exact ⟨this, hx, hmf⟩
end Proof
