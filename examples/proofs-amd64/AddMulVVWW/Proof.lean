import Janus
import Extracted

/-! `math/big.addMulVVWW(z, x, y []Word, m, a Word) (c Word)` on amd64 (Go assembly, ABI0), the
ADX/BMI2 path (`hasADX`): `z = x + y·m + a` over `n = len(z)` words, with two interleaved carry
chains (`MULXQ`, `ADCXQ` carrying through `CF`, `ADOXQ` through `OF`), unrolled eight times
(`alt8`) after `n mod 8` single steps (`alt1`).

**Guarantee** (`correctness`). For every length `n` and every `z`, `x`, `y` of `n` words (`z`
writable, `x` and `y` readable, `z` either equal to `x` or disjoint from it, disjoint from `y`
and from the 104-byte frame), on a CPU where `math/big.hasADX` is set, the call returns, its
result word `c` and the new `z` satisfy `z + 2^(64n)·c = x + y·m + a` (little-endian `n`-word
numbers), and it writes nothing but `z` and the result slot (`Post`).

**How.** One invariant at the three loop points, `z[0..i) + 2^(64i)·BX = x[0..i) + m·y[0..i) + a`
with `x[i..n)` and `y` unchanged (`OnlyWrites` on `z[0..i)`): `atHead1`, `loop1` (induction on the
single steps left), `atHead8`, `loop8` (induction on the 8-word blocks left). Each step's carry
arithmetic is closed by `janus64_arith` (the reflective carry procedure) on the step's words, and
`step_combine` lifts it to the whole prefix. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false

/-- The `alt8` loop head (`TESTQ SI, SI`). -/
abbrev head8 : Nat := Extracted.entry + 0x16d
/-- The `alt8cont` loop body (the back edge `JNZ` goes there). -/
abbrev body8 : Nat := Extracted.entry + 0x176

/-- What the call leaves: `z` and the carry word (result slot at `96(RSP)`) are `x + y·m + a`,
and nothing outside `z` and the result slot is written. -/
def Post (z x y n m a : Nat) (s s' : State) : Prop :=
  s'.mem.readLE z (8 * n) + 2 ^ (64 * n) * s'.mem.readLE ((s.regs 4).toNat + 96) 8 =
      s.mem.readLE x (8 * n) + m * s.mem.readLE y (8 * n) + a ∧
    s'.mem.regions = s.mem.regions ∧
    ∀ b, (b < z ∨ z + 8 * n ≤ b) → (b < (s.regs 4).toNat + 96 ∨ (s.regs 4).toNat + 104 ≤ b) →
      s'.mem.bytes b = s.mem.bytes b

theorem step_combine (Zp B c Zw w c' X Xw m Y Yw a : Nat) (hP : Zp + B * c = X + m * Y + a)
    (hw : Zw + w * c' = Xw + m * Yw + c) :
    (Zp + B * Zw) + (B * w) * c' = (X + B * Xw) + m * (Y + B * Yw) + a := by
  have h := congrArg (B * ·) hw
  simp only [Nat.mul_add, ← Nat.mul_assoc] at h
  rw [Nat.mul_add m Y, ← Nat.mul_assoc m B Yw, Nat.mul_comm m B]
  omega

/-- 64 bytes as 8 little-endian limbs. -/
theorem readLE_64 (m : Memory) (a : Nat) :
    m.readLE a 64 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 +
      2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 +
      2 ^ 320 * m.readLE (a + 40) 8 + 2 ^ 384 * m.readLE (a + 48) 8 +
      2 ^ 448 * m.readLE (a + 56) 8 := by
  have h := fun b k l => Janus.Arm64.Memory.readLE_add m b k l
  rw [show 64 = 8 + 56 from rfl, h, show 56 = 8 + 48 from rfl, h, show 48 = 8 + 40 from rfl, h,
    show 40 = 8 + 32 from rfl, h, show 32 = 8 + 24 from rfl, h, show 24 = 8 + 16 from rfl, h,
    show 16 = 8 + 8 from rfl, h]
  simp only [Nat.add_assoc, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]

/-- `k` more words after `i`. -/
theorem readLE_words (m : Memory) (a i k : Nat) :
    m.readLE a (8 * (i + k)) = m.readLE a (8 * i) + 2 ^ (64 * i) * m.readLE (a + 8 * i) (8 * k) := by
  rw [Nat.mul_add, Janus.Arm64.Memory.readLE_add, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul,
    show 8 * (8 * i) = 64 * i by omega]

/-- The result word of the 11-word frame. -/
theorem results0_one (s s' : State) :
    results0 s s' 11 1 = [BitVec.ofNat 64 (s'.mem.readLE ((s.regs 4).toNat + 96) 8)] := by
  simp only [results0, wordsAt, regSP, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]

theorem onlyWrites_mono {m m' : Memory} {p n n' : Nat} (h : Janus.Spec.OnlyWrites m m' p n)
    (hn : n ≤ n') : Janus.Spec.OnlyWrites m m' p n' :=
  ⟨h.1, fun b hb => h.2 b (by omega)⟩

theorem accessible_of_onlyWrites {m m' : Memory} {p n : Nat} (h : Janus.Spec.OnlyWrites m m' p n)
    {a k : Nat} {w : Bool} (ha : m.accessible a k w = true) : m'.accessible a k w = true := by
  simp only [Janus.Arm64.Memory.accessible, h.1] at ha ⊢; exact ha

theorem readLE_of_onlyWrites {m m' : Memory} {p n : Nat} (h : Janus.Spec.OnlyWrites m m' p n)
    {a k : Nat} (ha : a + k ≤ p ∨ p + n ≤ a) : m'.readLE a k = m.readLE a k :=
  Janus.Arm64.Memory.readLE_congr fun i hi => h.2 _ (by omega)

set_option maxHeartbeats 8000000 in
theorem loop8 (s0 : State) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (z x y n m a : Nat) (hm : m < 2 ^ 64) (hzb : z + 8 * n ≤ 2 ^ 48)
    (hxb : x + 8 * n ≤ 2 ^ 48) (hyb : y + 8 * n ≤ 2 ^ 48)
    (hz : s0.mem.accessible z (8 * n) true = true) (hx : s0.mem.accessible x (8 * n) false = true)
    (hy : s0.mem.accessible y (8 * n) false = true)
    (hzx : z = x ∨ z + 8 * n ≤ x ∨ x + 8 * n ≤ z) (hzy : z + 8 * n ≤ y ∨ y + 8 * n ≤ z)
    (hzf : z + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 104 ≤ z)
    (hfb : (s0.regs 4).toNat + 104 ≤ 2 ^ 48)
    (hfacc : s0.mem.accessible (s0.regs 4).toNat 104 true = true)
    (hra : s0.mem.readLE (s0.regs 4).toNat 8 = ret) :
    ∀ k (S : State) (i : Nat), i + 8 * (k + 1) = n →
      S.rip = BitVec.ofNat 64 body8 → S.regs 8 = BitVec.ofNat 64 (x + 8 * i) →
      S.regs 9 = BitVec.ofNat 64 (y + 8 * i) → S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      S.regs 6 = BitVec.ofNat 64 (k + 1) → S.regs 2 = BitVec.ofNat 64 m → S.regs 7 = 0 →
      S.regs 4 = s0.regs 4 → S.regs 5 = s0.regs 5 → S.fsBase = s0.fsBase → S.df = s0.df →
      Janus.Spec.OnlyWrites s0.mem S.mem z (8 * i) →
      S.mem.readLE z (8 * i) + 2 ^ (64 * i) * (S.regs 3).toNat =
        s0.mem.readLE x (8 * i) + m * s0.mem.readLE y (8 * i) + a →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s0 s' ∧ Post z x y n m a s0 s') := by
  intro k
  induction k with
  | zero =>
    intro S i hn hpc h8 h9 h10 h6 h2 h7 h4 h5 hfs hdf how hinv
    have hzS := accessible_of_onlyWrites how hz
    have hxS := accessible_of_onlyWrites how hx
    have hyS := accessible_of_onlyWrites how hy
    have hfaccS := accessible_of_onlyWrites how hfacc
    have hraS : S.mem.readLE (s0.regs 4).toNat 8 = ret := by
      rw [readLE_of_onlyWrites how (by omega), hra]
    have hru := hret.user
    janus64_run
    obtain rfl : n = i + 8 := by omega
    refine ⟨hfs, ?_, ?_, fun b hb hb' => ?_⟩
    · simp only
      rw [readLE_words, readLE_words, readLE_words, show 64 * (i + 8) = 64 * i + 512 by omega,
        Nat.pow_add, show 8 * 8 = 64 from rfl,
        ← readLE_of_onlyWrites how (a := x + 8 * i) (k := 64) (by omega),
        ← readLE_of_onlyWrites how (a := y + 8 * i) (k := 64) (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      refine step_combine _ _ _ _ _ _ _ _ _ _ _ _ hinv ?_
      simp only [readLE_64]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      janus64_arith
    · simp only [Janus.Arm64.Memory.regions_writeLE]; exact how.1
    · simp only
      simp (disch := omega) only [Janus.Arm64.Memory.bytes_writeLE_outside]
      exact how.2 b (by omega)
  | succ k ih =>
    intro S i hn hpc h8 h9 h10 h6 h2 h7 h4 h5 hfs hdf how hinv
    have hzS := accessible_of_onlyWrites how hz
    have hxS := accessible_of_onlyWrites how hx
    have hyS := accessible_of_onlyWrites how hy
    have hfaccS := accessible_of_onlyWrites how hfacc
    janus64_run until [body8]
    refine ih _ (i + 8) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10]; omega) | (simp [setRegF_apply, h2, h4, h5, h7, hfs, hdf]; done)
    · simp only
      repeat (refine Janus.Spec.onlyWrites_writeLE _ ?_ (by omega) (by omega))
      exact onlyWrites_mono how (by omega)
    · simp only
      rw [readLE_words, readLE_words, readLE_words, show 64 * (i + 8) = 64 * i + 512 by omega,
        Nat.pow_add, show 8 * 8 = 64 from rfl,
        ← readLE_of_onlyWrites how (a := x + 8 * i) (k := 64) (by omega),
        ← readLE_of_onlyWrites how (a := y + 8 * i) (k := 64) (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      refine step_combine _ _ _ _ _ _ _ _ _ _ _ _ hinv ?_
      simp only [readLE_64]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow]
      janus64_arith


/-- The `alt1cont` loop body and the `alt1` loop head (`TESTQ R11, R11`). -/
abbrev body1 : Nat := Extracted.entry + 0x132
abbrev head1 : Nat := Extracted.entry + 0x12d

set_option maxHeartbeats 8000000 in
theorem atHead8 (s0 : State) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (z x y n m a : Nat) (hm : m < 2 ^ 64) (hzb : z + 8 * n ≤ 2 ^ 48)
    (hxb : x + 8 * n ≤ 2 ^ 48) (hyb : y + 8 * n ≤ 2 ^ 48)
    (hz : s0.mem.accessible z (8 * n) true = true) (hx : s0.mem.accessible x (8 * n) false = true)
    (hy : s0.mem.accessible y (8 * n) false = true)
    (hzx : z = x ∨ z + 8 * n ≤ x ∨ x + 8 * n ≤ z) (hzy : z + 8 * n ≤ y ∨ y + 8 * n ≤ z)
    (hzf : z + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 104 ≤ z)
    (hfb : (s0.regs 4).toNat + 104 ≤ 2 ^ 48)
    (hfacc : s0.mem.accessible (s0.regs 4).toNat 104 true = true)
    (hra : s0.mem.readLE (s0.regs 4).toNat 8 = ret) :
    ∀ k (S : State) (i : Nat), i + 8 * k = n →
      S.rip = BitVec.ofNat 64 head8 → S.regs 8 = BitVec.ofNat 64 (x + 8 * i) →
      S.regs 9 = BitVec.ofNat 64 (y + 8 * i) → S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      S.regs 6 = BitVec.ofNat 64 k → S.regs 2 = BitVec.ofNat 64 m → S.regs 7 = 0 →
      S.regs 4 = s0.regs 4 → S.regs 5 = s0.regs 5 → S.fsBase = s0.fsBase → S.df = s0.df →
      Janus.Spec.OnlyWrites s0.mem S.mem z (8 * i) →
      S.mem.readLE z (8 * i) + 2 ^ (64 * i) * (S.regs 3).toNat =
        s0.mem.readLE x (8 * i) + m * s0.mem.readLE y (8 * i) + a →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s0 s' ∧ Post z x y n m a s0 s') := by
  intro k S i hn hpc h8 h9 h10 h6 h2 h7 h4 h5 hfs hdf how hinv
  have hzS := accessible_of_onlyWrites how hz
  have hxS := accessible_of_onlyWrites how hx
  have hyS := accessible_of_onlyWrites how hy
  have hfaccS := accessible_of_onlyWrites how hfacc
  have hraS : S.mem.readLE (s0.regs 4).toNat 8 = ret := by
    rw [readLE_of_onlyWrites how (by omega), hra]
  have hru := hret.user
  cases k with
  | zero =>
    janus64_run
    obtain rfl : i = n := by omega
    refine ⟨hfs, ?_, ?_, fun b hb hb' => ?_⟩
    · simp only
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (S.regs 3).isLt]
      exact hinv
    · simp only [Janus.Arm64.Memory.regions_writeLE]; exact how.1
    · simp only
      rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
      exact how.2 b hb
  | succ k =>
    have hk : k + 1 < 2 ^ 64 := by omega
    janus64_run until [body8]
    have h11 : True := trivial
    refine loop8 s0 ret hret z x y n m a hm hzb hxb hyb hz hx hy hzx hzy hzf hfb hfacc hra k _ i (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · exact how
    · simpa [setRegF_apply] using hinv

set_option maxHeartbeats 8000000 in
theorem loop1 (s0 : State) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (z x y n m a : Nat) (hm : m < 2 ^ 64) (hzb : z + 8 * n ≤ 2 ^ 48)
    (hxb : x + 8 * n ≤ 2 ^ 48) (hyb : y + 8 * n ≤ 2 ^ 48)
    (hz : s0.mem.accessible z (8 * n) true = true) (hx : s0.mem.accessible x (8 * n) false = true)
    (hy : s0.mem.accessible y (8 * n) false = true)
    (hzx : z = x ∨ z + 8 * n ≤ x ∨ x + 8 * n ≤ z) (hzy : z + 8 * n ≤ y ∨ y + 8 * n ≤ z)
    (hzf : z + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 104 ≤ z)
    (hfb : (s0.regs 4).toNat + 104 ≤ 2 ^ 48)
    (hfacc : s0.mem.accessible (s0.regs 4).toNat 104 true = true)
    (hra : s0.mem.readLE (s0.regs 4).toNat 8 = ret) :
    ∀ k (S : State) (i k8 : Nat), i + (k + 1) + 8 * k8 = n →
      S.rip = BitVec.ofNat 64 body1 → S.regs 8 = BitVec.ofNat 64 (x + 8 * i) →
      S.regs 9 = BitVec.ofNat 64 (y + 8 * i) → S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      S.regs 11 = BitVec.ofNat 64 (k + 1) → S.regs 6 = BitVec.ofNat 64 k8 →
      S.regs 2 = BitVec.ofNat 64 m → S.regs 7 = 0 →
      S.regs 4 = s0.regs 4 → S.regs 5 = s0.regs 5 → S.fsBase = s0.fsBase → S.df = s0.df →
      Janus.Spec.OnlyWrites s0.mem S.mem z (8 * i) →
      S.mem.readLE z (8 * i) + 2 ^ (64 * i) * (S.regs 3).toNat =
        s0.mem.readLE x (8 * i) + m * s0.mem.readLE y (8 * i) + a →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s0 s' ∧ Post z x y n m a s0 s') := by
  intro k
  induction k with
  | zero =>
    intro S i k8 hn hpc h8 h9 h10 h11 h6 h2 h7 h4 h5 hfs hdf how hinv
    have hzS := accessible_of_onlyWrites how hz
    have hxS := accessible_of_onlyWrites how hx
    have hyS := accessible_of_onlyWrites how hy
    have hfaccS := accessible_of_onlyWrites how hfacc
    have hraS : S.mem.readLE (s0.regs 4).toNat 8 = ret := by
      rw [readLE_of_onlyWrites how (by omega), hra]
    have hru := hret.user
    janus64_run until [head8]
    refine atHead8 s0 ret hret z x y n m a hm hzb hxb hyb hz hx hy hzx hzy hzf hfb hfacc hra k8 _ (i + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · simp only
      repeat (refine Janus.Spec.onlyWrites_writeLE _ ?_ (by omega) (by omega))
      exact onlyWrites_mono how (by omega)
    · simp only
      rw [readLE_words, readLE_words, readLE_words, show 64 * (i + 1) = 64 * i + 64 by omega,
        Nat.pow_add, show 8 * 1 = 8 from rfl,
        ← readLE_of_onlyWrites how (a := x + 8 * i) (k := 8) (by omega),
        ← readLE_of_onlyWrites how (a := y + 8 * i) (k := 8) (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      refine step_combine _ _ _ _ _ _ _ _ _ _ _ _ hinv ?_
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow]
      janus64_arith
  | succ k ih =>
    intro S i k8 hn hpc h8 h9 h10 h11 h6 h2 h7 h4 h5 hfs hdf how hinv
    have hzS := accessible_of_onlyWrites how hz
    have hxS := accessible_of_onlyWrites how hx
    have hyS := accessible_of_onlyWrites how hy
    have hfaccS := accessible_of_onlyWrites how hfacc
    have hraS : S.mem.readLE (s0.regs 4).toNat 8 = ret := by
      rw [readLE_of_onlyWrites how (by omega), hra]
    have hru := hret.user
    janus64_run until [body1]
    refine ih _ (i + 1) k8 (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · simp only
      repeat (refine Janus.Spec.onlyWrites_writeLE _ ?_ (by omega) (by omega))
      exact onlyWrites_mono how (by omega)
    · simp only
      rw [readLE_words, readLE_words, readLE_words, show 64 * (i + 1) = 64 * i + 64 by omega,
        Nat.pow_add, show 8 * 1 = 8 from rfl,
        ← readLE_of_onlyWrites how (a := x + 8 * i) (k := 8) (by omega),
        ← readLE_of_onlyWrites how (a := y + 8 * i) (k := 8) (by omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      refine step_combine _ _ _ _ _ _ _ _ _ _ _ _ hinv ?_
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow]
      janus64_arith

set_option maxHeartbeats 8000000 in
theorem atHead1 (s0 : State) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (z x y n m a : Nat) (hm : m < 2 ^ 64) (hzb : z + 8 * n ≤ 2 ^ 48)
    (hxb : x + 8 * n ≤ 2 ^ 48) (hyb : y + 8 * n ≤ 2 ^ 48)
    (hz : s0.mem.accessible z (8 * n) true = true) (hx : s0.mem.accessible x (8 * n) false = true)
    (hy : s0.mem.accessible y (8 * n) false = true)
    (hzx : z = x ∨ z + 8 * n ≤ x ∨ x + 8 * n ≤ z) (hzy : z + 8 * n ≤ y ∨ y + 8 * n ≤ z)
    (hzf : z + 8 * n ≤ (s0.regs 4).toNat ∨ (s0.regs 4).toNat + 104 ≤ z)
    (hfb : (s0.regs 4).toNat + 104 ≤ 2 ^ 48)
    (hfacc : s0.mem.accessible (s0.regs 4).toNat 104 true = true)
    (hra : s0.mem.readLE (s0.regs 4).toNat 8 = ret) :
    ∀ k (S : State) (i k8 : Nat), i + k + 8 * k8 = n →
      S.rip = BitVec.ofNat 64 head1 → S.regs 8 = BitVec.ofNat 64 (x + 8 * i) →
      S.regs 9 = BitVec.ofNat 64 (y + 8 * i) → S.regs 10 = BitVec.ofNat 64 (z + 8 * i) →
      S.regs 11 = BitVec.ofNat 64 k → S.regs 6 = BitVec.ofNat 64 k8 →
      S.regs 2 = BitVec.ofNat 64 m → S.regs 7 = 0 →
      S.regs 4 = s0.regs 4 → S.regs 5 = s0.regs 5 → S.fsBase = s0.fsBase → S.df = s0.df →
      Janus.Spec.OnlyWrites s0.mem S.mem z (8 * i) →
      S.mem.readLE z (8 * i) + 2 ^ (64 * i) * (S.regs 3).toNat =
        s0.mem.readLE x (8 * i) + m * s0.mem.readLE y (8 * i) + a →
      Reaches (Extracted.program.withExit ret) S
        (IsReturn fun s' => ABIReturn0 s0 s' ∧ Post z x y n m a s0 s') := by
  intro k S i k8 hn hpc h8 h9 h10 h11 h6 h2 h7 h4 h5 hfs hdf how hinv
  have hzS := accessible_of_onlyWrites how hz
  have hxS := accessible_of_onlyWrites how hx
  have hyS := accessible_of_onlyWrites how hy
  have hfaccS := accessible_of_onlyWrites how hfacc
  have hraS : S.mem.readLE (s0.regs 4).toNat 8 = ret := by
    rw [readLE_of_onlyWrites how (by omega), hra]
  have hru := hret.user
  cases k with
  | zero =>
    janus64_run until [head8]
    refine atHead8 s0 ret hret z x y n m a hm hzb hxb hyb hz hx hy hzx hzy hzf hfb hfacc hra k8 _ i (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · exact how
    · simpa [setRegF_apply] using hinv
  | succ k =>
    have hk : k + 1 < 2 ^ 64 := by omega
    janus64_run until [body1]
    refine loop1 s0 ret hret z x y n m a hm hzb hxb hyb hz hx hy hzx hzy hzf hfb hfacc hra k _ i k8 (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · first | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, h2, h6, h8, h9, h10, h11]; omega) | (simp [setRegF_apply, h2, h4, h5, h6, h7, h8, h9, h10, h11, hfs, hdf]; done)
    · exact how
    · simpa [setRegF_apply] using hinv

/-- `runtime`'s `math/big.hasADX` (the `CMPB` at the entry). -/
def hasADX : Nat := ripTarget Extracted.program Extracted.entry

/-- **`math/big.addMulVVWW(z, x, y []Word, m, a Word) (c Word)`, the ADX/BMI2 path**: for
every length `n = len(z)`, on a CPU where `math/big.hasADX` is set, the call writes
`z = x + y·m + a` over `n` words with the carry word `c` as its result (`z + 2^(64n)·c =
x + y·m + a`, all little-endian bignums of `n` words), and writes nothing but `z` and the result
slot. `z` may be `x` itself (`math/big` calls it in place) but must not overlap `y` or the frame. -/
theorem correctness (z zl zc x xl xc y yl yc mw aw : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [z, zl, zc, x, xl, xc, y, yl, yc, mw, aw] 1
      (fun s => s.mem.accessible hasADX 1 false = true ∧ s.mem.readLE hasADX 1 ≠ 0 ∧
        Buffer s z (8 * zl.toNat) true ∧ Buffer s x (8 * zl.toNat) false ∧
        Buffer s y (8 * zl.toNat) false ∧
        (z = x ∨ Disjoint z (8 * zl.toNat) x (8 * zl.toNat)) ∧ Disjoint z (8 * zl.toNat) y (8 * zl.toNat) ∧
        Disjoint z (8 * zl.toNat) (s.regs 4) 104)
      (fun s s' => Post z.toNat x.toNat y.toNat zl.toNat mw.toNat aw.toNat s s') := by
  intro ret hret s hs ⟨hua, hu, ⟨hzb, hz⟩, ⟨hxb, hx⟩, ⟨hyb, hy⟩, hzx, hzy, hzf⟩
  have hbv : ¬ BitVec.ofNat 8 (s.mem.readLE hasADX 1) = 0#8 := fun h =>
    hu (Janus.Spec.MemHash.readLE1_eq_zero h)
  simp only [hasADX] at hua hu hbv
  janus64_addrs
  janus64_intro0 hs
  simp only [Disjoint] at hzx hzy hzf
  have hzx' : z.toNat = x.toNat ∨ z.toNat + 8 * zl.toNat ≤ x.toNat ∨ x.toNat + 8 * zl.toNat ≤ z.toNat := by
    rcases hzx with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  have hm := mw.isLt
  have hand7 : ∀ t : Nat, t &&& 7 = t % 8 := fun t => Nat.and_two_pow_sub_one_eq_mod t 3
  janus64_run until [head1, Extracted.entry + 0xd]
  · exact absurd hbr hbv
  refine atHead1 s ret hret z.toNat x.toNat y.toNat zl.toNat mw.toNat aw.toNat hm hzb hxb hyb hz hx hy
    hzx' hzy hzf h_fb h_facc h_ret (zl.toNat % 8) _ 0 (zl.toNat / 8) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · first | (simp [setRegF_apply, h_df]; done) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h_rd_arg0, h_rd_arg1, h_rd_arg3, h_rd_arg6, h_rd_arg9, h_rd_arg10, hand7]; omega)
  · simp only; exact Janus.Spec.onlyWrites_refl _ _ _
  · simp [setRegF_apply]

end Proof
