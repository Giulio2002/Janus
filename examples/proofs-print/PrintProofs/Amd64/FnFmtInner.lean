import PrintProofs.Amd64.FnFmtArith

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print

namespace PrintFn

/-! ## The inner loop of `formatBase10`'s nine-digit chunks

`formatBase10` writes a chunk of nine digits (`y < 10^9`) from the right, two digits per iteration
of a loop that runs four times (`+0x60`), then the last digit. The loop is proved once, as an
induction on the iteration count, against the bytes it wrote (`readBytes`), so that the chunk loop
around it does not unroll it. -/

/-- The two-digit pairs `y / 100^t % 100` for `t < k`, most significant pair first, as the digits
`formatBase10` writes. -/
def pairsOf (y k : Nat) : List (BitVec 8) :=
  (List.range k).reverse.flatMap fun t =>
    [Janus.Spec.Print.digit (y / 100 ^ t % 100 / 10), Janus.Spec.Print.digit (y / 100 ^ t % 100 % 10)]

theorem pairsOf_succ (y k : Nat) :
    pairsOf y (k + 1) = [Janus.Spec.Print.digit (y / 100 ^ k % 100 / 10),
      Janus.Spec.Print.digit (y / 100 ^ k % 100 % 10)] ++ pairsOf y k := by
  simp [pairsOf, List.range_succ, List.reverse_append]

theorem pairsOf_zero (y : Nat) : pairsOf y 0 = [] := rfl

theorem digits9_eq (y : Nat) :
    digits9 y = Janus.Spec.Print.digit (y / 100000000 % 10) :: pairsOf y 4 := by
  simp only [digits9, pairsOf, List.range_succ, List.range_zero, List.map, List.reverse_nil,
    List.reverse_cons, List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.reducePow, Nat.pow_zero, Nat.div_one, List.cons.injEq, and_true]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact congrArg _ (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 40000000 in
theorem fb_inner (impl : List Amd64.Segment) (ret : W64) (SMv a i Y D : Nat) (M0 : Memory)
    (hi9 : 9 ≤ i) (hi20 : i ≤ 20) (hY : Y < 1000000000) (hD : D < 2 ^ 64)
    (hlit : (4927680#64 : BitVec 64) = BitVec.ofNat 64 SMv)
    (hSMb : 4927680 ≤ SMv ∧ SMv ≤ 4927680) (hab : a + 20 ≤ 2 ^ 48)
    (hap : a + 20 ≤ SMv ∨ SMv + 200 ≤ a)
    (hacc : M0.accessible a 20 true = true) (hsma : M0.accessible SMv 200 false = true)
    (h_sm : ∀ j, j < 200 → M0.readLE (SMv + j) 1 = smallsByte j) :
    ∀ m k, k + m = 4 → ∀ (S : State) (x : Nat), x = Y / 100 ^ k →
      S.rip = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0x60) →
      S.regs 0 = BitVec.ofNat 64 k → S.regs 3 = BitVec.ofNat 64 (i - 2 * k) →
      S.regs 7 = BitVec.ofNat 64 a → S.regs 6 = BitVec.ofNat 64 x → S.regs 2 = BitVec.ofNat 64 D →
      S.regs 1 = 20#64 →
      MemFrame M0 S.mem [(a, a + 20)] →
      readBytes S.mem (a + (i - 2 * k)) (2 * k + (20 - i)) = pairsOf Y k ++ readBytes M0 (a + i) (20 - i) →
      ∀ Q : State → Prop,
        (∀ S' : State, S'.rip = BitVec.ofNat 64 (segAddr P "internal/strconv.formatBase10" + 0xbe) →
          S'.regs 0 = BitVec.ofNat 64 4 → S'.regs 3 = BitVec.ofNat 64 (i - 8) →
          S'.regs 7 = BitVec.ofNat 64 a → S'.regs 6 = BitVec.ofNat 64 (Y / 100 ^ 4) →
          S'.regs 2 = BitVec.ofNat 64 D → S'.regs 1 = 20#64 →
          (∀ r, r = 4 ∨ r = 5 ∨ r = 14 → S'.regs r = S.regs r) → S'.xmm 15 = S.xmm 15 →
          S'.fsBase = S.fsBase → S'.df = S.df → S'.mxcsr = S.mxcsr → S'.x87 = S.x87 → S'.fpucw = S.fpucw →
          MemFrame M0 S'.mem [(a, a + 20)] →
          readBytes S'.mem (a + (i - 8)) (8 + (20 - i)) = pairsOf Y 4 ++ readBytes M0 (a + i) (20 - i) →
          ReachesRet (P.link impl) ret S' Q) →
        ReachesRet (P.link impl) ret S Q := by
  intro m
  induction m with
  | zero =>
    intro k hk S x hx hpc h0 h3 h7 h6 h2 h1 hf hrb Q hQ
    have hk4 : k = 4 := by omega
    subst hk4
    janus64_run until [segAddr P "internal/strconv.formatBase10" + 0xbe]
    refine hQ _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hrb
    all_goals first
      | exact h0
      | (dsimp only; first | rfl | assumption | (rw [hx]; rfl) | (simp [h3]; done) | (simp [h7]; done) | (simp [h6, hx]; done) | (simp [h2]; done) | (simp [h1]; done))
      | skip
    all_goals try (intro r hr; rfl)
    all_goals rfl
  | succ m ih =>
    intro k hk S x hx hpc h0 h3 h7 h6 h2 h1 hf hrb Q hQ
    have hxl : x < 1000000000 := by rw [hx]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hY
    have hk3 : k < 4 := by omega
    have e2 : (i - 2 * k + (18446744073709551614 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 2 * k - 2) := by omega
    have e1 : (i - 2 * k + (18446744073709551615 + a) % 18446744073709551616) % 18446744073709551616 = a + (i - 2 * k - 1) := by omega
    janus64_run [hlit, div100_magic64 x (by omega), mul100_32 (x / 100) (by omega), mod100_32 x (by omega), e1, e2]
      until [segAddr P "internal/strconv.formatBase10" + 0x60]
    have hr100 : x % 100 < 100 := Nat.mod_lt _ (by decide)
    have hx100 : x / 100 = Y / 100 ^ (k + 1) := by rw [hx, Nat.pow_succ, Nat.div_div_eq_div_mul]
    refine ih (k + 1) (by omega) _ (x / 100) hx100 rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Q ?_
    · simp [setRegF_apply]
    · simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    · simp [setRegF_apply, h7]
    · simp [setRegF_apply]
    · simp [setRegF_apply, h2]
    · simp [setRegF_apply, h1]
    · janus_frame
    · dsimp only
      have hp1 : a + (i - 2 * k - 2) + 1 = a + (i - 2 * k - 1) := by omega
      have hi2 : a + (i - 2 * (k + 1)) = a + (i - 2 * k - 2) := by omega
      have hn2 : 2 * (k + 1) + (20 - i) = (2 * k + (20 - i)) + 2 := by omega
      rw [hi2, hn2, ← hp1, readBytes_two_writes, show a + (i - 2 * k - 2) + 1 + 1 = a + (i - 2 * k) by omega,
        hrb, pairsOf_succ, ← hx, List.append_assoc]
      congr 1
      rw [two_mul32 (x % 100) (by omega), smallsByte_mod256 (x % 100 * 2) (by omega),
        show (x % 100 * 2 + 1) % 4294967296 + SMv = SMv + (x % 100 * 2 + 1) by omega, h_sm _ (by omega)]
      simp only [List.cons.injEq, and_true]
      exact ⟨smalls_hi _ hr100, smalls_lo _ hr100⟩
    · intro S' h1' h2' h3' h4' h5' h6' h7' hr hx15 hfs hdf hmx hx87 hfw hf' hrb'
      refine hQ S' h1' h2' h3' h4' h5' h6' h7' (fun r hr' => ?_) ?_ ?_ ?_ ?_ ?_ ?_ hf' hrb'
      · rw [hr r hr']; rcases hr' with rfl | rfl | rfl <;> simp [setRegF_apply]
      · rw [hx15]
      · rw [hfs]
      · rw [hdf]
      · rw [hmx]
      · rw [hx87]
      · rw [hfw]
end PrintFn
