import Janus.Contracts.MemSat

/-!
# The hashing contracts are satisfiable (arm64)

For every contract of `Janus.Contracts.Hash`: machine code (A64 assembly, its words below) at the
address `A0` of a program with no other code, a proof by symbolic execution that it satisfies
the contract for the model `EqHashModel.H0` (whose laws hold, `EqHashModel.H0_laws`) and every
stack bound `d` (no implementation uses its stack), and a call state over the witness memory
`EqHashModel.wmem` that satisfies the contract's precondition (`<contract>_satisfiable`).

In `H0` every byte hash and every `typehash` is its seed, so the byte hashes are `mov x0, x1`.
The float hashes compute Go's special cases: `c1 · (c0 ^ h)` for `±0` (the bits other than the
sign are zero) and the seed otherwise; for a NaN the seed is a possible result, because `c1` is
invertible modulo `2^64` (`c1_inv`), so `h = c1 · (c0 ^ h ^ rnd)` for the random word
`rnd = (c1⁻¹ · h) ^ c0 ^ h`. The interface hashes return `c1 · (h ^ c0)` for a non-nil type
(`typehash` of `H0` returns the seed `h ^ c0`) and `h` for nil.
-/

namespace Janus.Contracts.HashSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Mem Janus.Contracts.Hash Janus.Contracts.IfaceSat
  Janus.Contracts.EqHashModel Janus.Contracts.MemSat Janus.Float

/-! ## The witness and the return -/

/-- The witness state satisfies `HPre` for `H0` and the stack bound 64. -/
theorem wstate_hPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : HPre H0 64 n (MemSat.wstate r) :=
  ⟨wmem_henv _, (wstate_eqPre r n hn).1, (wstate_eqPre r n hn).2.1, wstate_outside r n,
    (wstate_eqPre r n hn).2.2, by simp [MemSat.wstate, IfaceModel.wg]⟩

/-- `HRet` from `Keeps`. -/
theorem hRet_of {H : HashModel} {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hk : Keeps s s') (hf : MemFrame s.mem s'.mem (H.priv ++ calleeStack s d nargs))
    (he : H.Env s'.mem (s.regs 28)) (hp : P s'.regs) : HRet H d nargs s s' P :=
  ⟨_, _, _, _, _, hk.ret_eq, hf, he, hp⟩

/-! ## Byte hashes, `typehash`, `rand` -/

/-- `mov x0, x1; ret`: the seed. -/
def seedCode : List Nat := [0xaa0103e0, 0xd65f03c0]

/-- Running `seedCode`: `X0` is the seed, nothing else changes. -/
theorem seed_run {s : State} {Q : State → Prop} (hpc : s.pc = BitVec.ofNat 64 A0)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (h : Q { s with regs := setReg s.regs 0 (s.regs 1), pc := s.regs 30 }) :
    ReachesRet (withCode seedCode) (s.regs regLR) s Q := by
  janus_run
  exact h

/-- The seed returned: a `HRet` for `H0`. -/
theorem seed_hRet {d nargs : Nat} {s : State} {P : (Nat → W64) → Prop} (he : H0.Env s.mem (s.regs 28))
    (hp : P (setReg s.regs 0 (s.regs 1))) :
    HRet H0 d nargs s { s with regs := setReg s.regs 0 (s.regs 1), pc := s.regs 30 } P :=
  hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
    (MemFrame.refl _ _) he hp

/-- A seed `h < 2^64` is its own `H0` hash. -/
theorem seed_mod (x : W64) : x.toNat % 18446744073709551616 = x.toNat := Nat.mod_eq_of_lt x.isLt

theorem memhash_impl (d : Nat) : Memhash (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

theorem memhash0_impl (d : Nat) : Memhash0 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨he, _, ⟨hl1, hl2, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg]))

theorem memhashN_impl (d n : Nat) : MemhashN (toy.link (at0 seedCode)) A0 H0 d n := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

theorem memhash32_impl (d : Nat) : Memhash32 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

theorem memhash64_impl (d : Nat) : Memhash64 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

theorem memhashVarlen_impl (d : Nat) : MemhashVarlen (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

theorem strhash_impl (d : Nat) : Strhash (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  exact seed_run hpc hl1 hl2 (seed_hRet he (by simp [setReg, seed_mod]))

/-- `mov x0, x2; ret`: `typehash` of `H0` is its seed. -/
def typehashCode : List Nat := [0xaa0203e0, 0xd65f03c0]

theorem typehash_impl (d : Nat) : Typehash (toy.link (at0 typehashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_run
  exact hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
    (MemFrame.refl _ _) he (by simp [setReg, seed_mod])

/-- `ret`: some word. -/
def randCode : List Nat := [0xd65f03c0]

theorem rand_impl (d : Nat) : Rand (toy.link (at0 randCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨he, _, ⟨hl1, hl2, _⟩, _⟩
  janus_run
  exact hRet_of ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he trivial

/-! ## Float hashes -/

/-- `c1` is invertible modulo `2^64`. -/
theorem c1_inv : c1 * 7906388553261026367 % 2 ^ 64 = 1 := by decide

/-- A seed `h` is a possible `H0` hash of a non-zero float: the byte hash for a number, and for
a NaN the result of the random word `(c1⁻¹ · h) ^ c0 ^ h`. -/
theorem fhashIs_seed (f : Fmt) (k x h : Nat) (hz : classify f x ≠ .zero) (hh : h < 2 ^ 64) :
    FHashIs H0 f k x h h := by
  unfold FHashIs
  rw [ite_eq_right_iff.mpr (fun h => absurd h hz)]
  split
  · have hy : 7906388553261026367 * h % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have hc0 : c0 < 2 ^ 64 := by decide
    refine ⟨7906388553261026367 * h % 2 ^ 64 ^^^ c0 ^^^ h,
      Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hy hc0) hh, ?_⟩
    have hx : c0 ^^^ h ^^^ (7906388553261026367 * h % 2 ^ 64 ^^^ c0 ^^^ h) =
        7906388553261026367 * h % 2 ^ 64 := by
      rw [Nat.xor_comm (7906388553261026367 * h % 2 ^ 64 ^^^ c0) h, ← Nat.xor_assoc,
        Nat.xor_assoc c0 h h, Nat.xor_self, Nat.xor_zero, Nat.xor_comm, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]
    rw [hx, Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod, c1_inv, Nat.one_mul, Nat.mod_mod,
      Nat.mod_eq_of_lt hh]
  · simp [Nat.mod_eq_of_lt hh]

/-- The zero class: exponent and fraction fields zero. -/
theorem classify_zero (f : Fmt) (x : Nat) :
    classify f x = .zero ↔ (expOf f x = 0 ∧ fracOf f x = 0) := by
  unfold classify
  by_cases h1 : expOf f x = 0
  · by_cases h2 : fracOf f x = 0 <;> simp [h1, h2]
  · simp only [h1, ite_false, false_and, iff_false]
    repeat' split
    all_goals simp

/-- `±0` (the bits below the sign are zero) is the zero class of binary64. -/
theorem classify64_zero (x : Nat) : classify binary64 x = .zero ↔ x % 9223372036854775808 = 0 := by
  rw [classify_zero]; simp only [expOf, fracOf, binary64]; omega

/-- `±0` is the zero class of binary32. -/
theorem classify32_zero (x : Nat) : classify binary32 x = .zero ↔ x % 2147483648 = 0 := by
  rw [classify_zero]; simp only [expOf, fracOf, binary32]; omega

/-- `ldr x2, [x0]; tst x2, #0x7fffffffffffffff; b.ne 1f; mov x4, #c0; mov x5, #c1 (movz/movk);
eor x4, x4, x1; mul x0, x4, x5; ret; 1: mov x0, x1; ret`. -/
def f64hashCode : List Nat :=
  [0xf9400002, 0xf240f85f, 0x54000181, 0xd294c424, 0xf2ad4ac4, 0xf2cdd424, 0xf2e00ea4, 0xd28c77e5,
   0xf2b771e5, 0xf2dded65, 0xf2e00a45, 0xca010084, 0x9b057c80, 0xd65f03c0, 0xaa0103e0, 0xd65f03c0]

/-- The result of a float hash of `x` with seed `h`: `c1 · (c0 ^ h)` if the bits other than the
sign are zero (`±0`), else `h`. -/
theorem fhashIs_result (f : Fmt) (k x : Nat) (h : W64) (P : Prop)
    (hz : classify f x = .zero ↔ P) :
    (P → FHashIs H0 f k x h.toNat
      ((33054211828000289 ^^^ h.toNat) * 23344194077549503 % 18446744073709551616)) ∧
      (¬P → FHashIs H0 f k x h.toNat h.toNat) := by
  refine ⟨fun h0 => ?_, fun h0 => fhashIs_seed f k x _ (fun hc => h0 (hz.1 hc)) h.isLt⟩
  unfold FHashIs; rw [ite_eq_left_iff.mpr (fun h => absurd (hz.2 h0) h), Nat.mul_comm]; rfl

/-- The `±0` branch of a float hash: `(c0 ^ h) · c1` as computed (`eor`, `mul`). -/
theorem fhash_zero (f : Fmt) (k x : Nat) {P : Prop} (hz : classify f x = .zero ↔ P) (h : W64)
    (h0 : P) :
    FHashIs H0 f k x h.toNat ((33054211828000289#64 ^^^ h) * 23344194077549503#64).toNat := by
  rw [BitVec.toNat_mul, BitVec.toNat_xor]; exact (fhashIs_result f k x h P hz).1 h0

/-- The other branch: the seed. -/
theorem fhash_seed (f : Fmt) (k x : Nat) {P : Prop} (hz : classify f x = .zero ↔ P) (h : W64)
    (h0 : ¬P) : FHashIs H0 f k x h.toNat h.toNat :=
  (fhashIs_result f k x h P hz).2 h0

/-- `tst w2, #0x7fffffff` of a 4-byte read: the bits other than the sign are zero. -/
theorem classify32_tst (m : Memory) (a : Nat) :
    classify binary32 (m.readLE a 4) = .zero ↔
      BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 4)) &&& 2147483647#32 = 0#32 := by
  have hx := Memory.readLE_lt m a 4
  have e : (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 4)) &&& 2147483647#32).toNat =
      m.readLE a 4 % 2147483648 := by
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := m.readLE a 4) (by simp at hx; omega),
      Nat.mod_eq_of_lt (a := m.readLE a 4) (by simp at hx; omega)]
    exact Nat.and_two_pow_sub_one_eq_mod _ 31
  rw [classify32_zero, ← BitVec.toNat_inj, e]
  simp

theorem f64hash_impl (d : Nat) : Fhash (toy.link (at0 f64hashCode)) A0 H0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩⟩
  have hr := fhashIs_result binary64 8 (s.mem.readLE (s.regs 0).toNat 8) (s.regs 1) _
    (classify64_zero _)
  janus_run
  · rename_i hz _
    refine hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
      (MemFrame.refl _ _) he ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    rw [BitVec.toNat_mul, BitVec.toNat_xor]
    exact hr.1 hz
  · rename_i hz _
    refine hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
      (MemFrame.refl _ _) he ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    exact hr.2 hz

/-- `ldr w2, [x0]; tst w2, #0x7fffffff; b.ne 1f; mov x4, #c0; mov x5, #c1 (movz/movk);
eor x4, x4, x1; mul x0, x4, x5; ret; 1: mov x0, x1; ret`. -/
def f32hashCode : List Nat :=
  [0xb9400002, 0x7200785f, 0x54000181, 0xd294c424, 0xf2ad4ac4, 0xf2cdd424, 0xf2e00ea4, 0xd28c77e5,
   0xf2b771e5, 0xf2dded65, 0xf2e00a45, 0xca010084, 0x9b057c80, 0xd65f03c0, 0xaa0103e0, 0xd65f03c0]

theorem f32hash_impl (d : Nat) : Fhash (toy.link (at0 f32hashCode)) A0 H0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩⟩
  janus_run
  all_goals
    refine hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
      (MemFrame.refl _ _) he ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
  · exact fhash_zero _ _ _ (classify32_tst _ _) _ (by assumption)
  · exact fhash_seed _ _ _ (classify32_tst _ _) _ (by assumption)

/-- `mov x4, #c0; mov x5, #c1 (movz/movk); ldr x2, [x0]; tst x2, #0x7fffffffffffffff; b.ne 1f;
eor x1, x1, x4; mul x1, x1, x5; 1: ldr x2, [x0, #8]; tst x2, #0x7fffffffffffffff; b.ne 2f;
eor x1, x1, x4; mul x1, x1, x5; 2: mov x0, x1; ret`: the real part, then the imaginary part
with the real part's hash as the seed. -/
def c128hashCode : List Nat :=
  [0xd294c424, 0xf2ad4ac4, 0xf2cdd424, 0xf2e00ea4, 0xd28c77e5, 0xf2b771e5, 0xf2dded65, 0xf2e00a45,
   0xf9400002, 0xf240f85f, 0x54000061, 0xca040021, 0x9b057c21, 0xf9400402, 0xf240f85f, 0x54000061,
   0xca040021, 0x9b057c21, 0xaa0103e0, 0xd65f03c0]

/-- As `c128hashCode` with 32-bit loads (`ldr w2, [x0]`, `ldr w2, [x0, #4]`, `tst w2, #0x7fffffff`). -/
def c64hashCode : List Nat :=
  [0xd294c424, 0xf2ad4ac4, 0xf2cdd424, 0xf2e00ea4, 0xd28c77e5, 0xf2b771e5, 0xf2dded65, 0xf2e00a45,
   0xb9400002, 0x7200785f, 0x54000061, 0xca040021, 0x9b057c21, 0xb9400402, 0x7200785f, 0x54000061,
   0xca040021, 0x9b057c21, 0xaa0103e0, 0xd65f03c0]

/-- `eor x1, x1, x4` computes `c0 ^ h` with the operands the other way round. -/
theorem xor_comm_w (h c : W64) : h ^^^ c = c ^^^ h := BitVec.xor_comm h c

theorem c128hash_impl (d : Nat) : Chash (toy.link (at0 c128hashCode)) A0 H0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, _⟩
  have h8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 2 * 8)
  have h8' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 8) (by omega : (s.regs 0).toNat + 8 + 8 ≤ (s.regs 0).toNat + 2 * 8)
  janus_run
  all_goals
    refine hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
      (MemFrame.refl _ _) he ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, xor_comm_w _ 33054211828000289#64]
    rename_i h1 h2 _
  · exact ⟨_, fhash_zero _ _ _ (classify64_zero _) _ h1, fhash_zero _ _ _ (classify64_zero _) _ h2⟩
  · exact ⟨_, fhash_zero _ _ _ (classify64_zero _) _ h1, fhash_seed _ _ _ (classify64_zero _) _ h2⟩
  · exact ⟨_, fhash_seed _ _ _ (classify64_zero _) _ h1, fhash_zero _ _ _ (classify64_zero _) _ h2⟩
  · exact ⟨_, fhash_seed _ _ _ (classify64_zero _) _ h1, fhash_seed _ _ _ (classify64_zero _) _ h2⟩

theorem c64hash_impl (d : Nat) : Chash (toy.link (at0 c64hashCode)) A0 H0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, _⟩
  have h8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 4 ≤ (s.regs 0).toNat + 2 * 4)
  have h8' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 4) (by omega : (s.regs 0).toNat + 4 + 4 ≤ (s.regs 0).toNat + 2 * 4)
  janus_run
  all_goals
    refine hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
      (MemFrame.refl _ _) he ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, xor_comm_w _ 33054211828000289#64]
    rename_i h1 h2 _
  · exact ⟨_, fhash_zero _ _ _ (classify32_tst _ _) _ h1, fhash_zero _ _ _ (classify32_tst _ _) _ h2⟩
  · exact ⟨_, fhash_zero _ _ _ (classify32_tst _ _) _ h1, fhash_seed _ _ _ (classify32_tst _ _) _ h2⟩
  · exact ⟨_, fhash_seed _ _ _ (classify32_tst _ _) _ h1, fhash_zero _ _ _ (classify32_tst _ _) _ h2⟩
  · exact ⟨_, fhash_seed _ _ _ (classify32_tst _ _) _ h1, fhash_seed _ _ _ (classify32_tst _ _) _ h2⟩

/-! ## Interface hashes -/

/-- `ldr x2, [x0]; cbz x2, 1f; mov x4, #c0; mov x5, #c1 (movz/movk); eor x0, x1, x4;
mul x0, x0, x5; ret; 1: mov x0, x1; ret`: `c1 · (h ^ c0)` (`typehash` of `H0` returns its seed
`h ^ c0`) for a non-nil first word, the seed for nil. The same code serves `interhash`: a
non-nil itab has a non-nil type. -/
def ifaceHashCode : List Nat :=
  [0xf9400002, 0xb4000182, 0xd294c424, 0xf2ad4ac4, 0xf2cdd424, 0xf2e00ea4, 0xd28c77e5, 0xf2b771e5,
   0xf2dded65, 0xf2e00a45, 0xca040020, 0x9b057c00, 0xd65f03c0, 0xaa0103e0, 0xd65f03c0]

/-- The arithmetic of the non-nil interface hash. -/
theorem ihash_arith (x : Nat) (hx : x < 2 ^ 64) :
    (x ^^^ 33054211828000289 % 2 ^ 64) * (23344194077549503 % 2 ^ 64) % 2 ^ 64 =
      c1 * ((x ^^^ c0) % 2 ^ 64) % 2 ^ 64 := by
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx (by decide : c0 < 2 ^ 64))]
  rw [Nat.mul_comm]; rfl

theorem nilinterhash_impl (d : Nat) : Nilinterhash (toy.link (at0 ifaceHashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, ⟨ha1, ha2, ha3⟩, _⟩
  have ha8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  janus_run
  · refine hRet_of ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he ?_
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      unfold IHashIs; simp
  · rename_i h0 _
    refine hRet_of ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he ?_
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      unfold IHashIs
      rw [ite_eq_right_iff.mpr (fun h => absurd h h0)]
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_mul, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      exact ihash_arith _ (s.regs 1).isLt

theorem interhash_impl (d : Nat) : Interhash (toy.link (at0 ifaceHashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, ⟨ha1, ha2, ha3⟩, hok⟩
  have ha8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  janus_run
  · rename_i h0 _
    refine hRet_of ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he ?_
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      unfold IHashIs
      rw [ite_eq_left_iff.mpr (fun h => absurd (by simp only [itabType, h0, ite_true]) h)]
  · rename_i h0 _
    refine hRet_of ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he ?_
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      unfold IHashIs
      rw [ite_eq_right_iff.mpr (fun h => absurd h (hok h0).2.1)]
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_mul, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      exact ihash_arith _ (s.regs 1).isLt

/-! ## Witness states -/

/-- The witness arguments: `X0 = VAL`, `X1 = 7` (a seed), `X2 = 8`. -/
def hashArgs : Nat → W64 := fun i =>
  if i = 0 then BitVec.ofNat 64 IfaceModel.VAL else if i = 1 then 7#64 else if i = 2 then 8#64 else 0

theorem hashArgs_0 : ((MemSat.wstate hashArgs).regs 0).toNat = IfaceModel.VAL := by
  simp [MemSat.wstate, hashArgs, IfaceModel.VAL]

theorem hashArgs_2 : ((MemSat.wstate hashArgs).regs 2).toNat = 8 := by
  simp [MemSat.wstate, hashArgs]

/-- Up to 16 bytes at `VAL` are an input. -/
theorem hashArgs_input (nargs k : Nat) (hk : k ≤ 16) :
    Input (MemSat.wstate hashArgs) 64 nargs ((MemSat.wstate hashArgs).regs 0).toNat k := by
  rw [hashArgs_0]
  exact wstate_input _ _ _ _ (by decide) (by simp only [IfaceModel.VAL]; omega)

/-- `Memhash` is satisfiable. -/
theorem memhash_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Memhash (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 3 s ∧ Input s d 3 (s.regs 0).toNat (s.regs 2).toNat) :=
  ⟨_, _, 64, H0_laws, memhash_impl 64, MemSat.wstate hashArgs, rfl, wstate_hPre _ 3 (by decide),
    by rw [hashArgs_2]; exact hashArgs_input 3 8 (by decide)⟩

/-- `Memhash0` is satisfiable. -/
theorem memhash0_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Memhash0 (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ HPre H d 2 s :=
  ⟨_, _, 64, H0_laws, memhash0_impl 64, MemSat.wstate hashArgs, rfl, wstate_hPre _ 2 (by decide)⟩

/-- `MemhashN` is satisfiable for every `n ≤ 16` (`memhash8/16/128`: `n = 1, 2, 16`). -/
theorem memhashN_satisfiable (n : Nat) (hn : n ≤ 16) : ∃ (H : HashModel) (impl : List Segment) (d : Nat),
    H.Laws ∧ MemhashN (toy.link impl) A0 H d n ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat n) :=
  ⟨_, _, 64, H0_laws, memhashN_impl 64 n, MemSat.wstate hashArgs, rfl, wstate_hPre _ 2 (by decide),
    hashArgs_input 2 n hn⟩

/-- `Memhash32` is satisfiable. -/
theorem memhash32_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Memhash32 (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat 4) :=
  ⟨_, _, 64, H0_laws, memhash32_impl 64, MemSat.wstate hashArgs, rfl, wstate_hPre _ 2 (by decide),
    hashArgs_input 2 4 (by decide)⟩

/-- `Memhash64` is satisfiable. -/
theorem memhash64_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Memhash64 (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ Input s d 2 (s.regs 0).toNat 8) :=
  ⟨_, _, 64, H0_laws, memhash64_impl 64, MemSat.wstate hashArgs, rfl, wstate_hPre _ 2 (by decide),
    hashArgs_input 2 8 (by decide)⟩

/-- `MemhashVarlen` is satisfiable (the closure `VLEN`, size 8). -/
theorem memhashVarlen_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    MemhashVarlen (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ Input s d 2 ((s.regs 26).toNat + 8) 8 ∧ Input s d 2 (s.regs 0).toNat (varlenSize s)) := by
  let r : Nat → W64 := fun i => if i = 26 then BitVec.ofNat 64 VLEN else hashArgs i
  have h0 : ((MemSat.wstate r).regs 0).toNat = IfaceModel.VAL := by
    simp [r, MemSat.wstate, hashArgs, IfaceModel.VAL]
  have h26 : ((MemSat.wstate r).regs 26).toNat = VLEN := by simp [r, MemSat.wstate, VLEN]
  have hsz : varlenSize (MemSat.wstate r) = 8 := by simp only [varlenSize, h26, wstate_mem]; decide
  refine ⟨_, _, 64, H0_laws, memhashVarlen_impl 64, MemSat.wstate r, rfl, wstate_hPre _ 2 (by decide), ?_, ?_⟩
  · rw [h26]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, hsz]; exact wstate_input _ 2 _ _ (by decide) (by decide)

/-- `Strhash` is satisfiable (the string `STR`). -/
theorem strhash_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Strhash (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ StrInput s d 2 (s.regs 0).toNat) := by
  have h0 : ((MemSat.wstate strArgs).regs 0).toNat = STR := by simp [MemSat.wstate, strArgs, STR]
  exact ⟨_, _, 64, H0_laws, strhash_impl 64, MemSat.wstate strArgs, rfl, wstate_hPre _ 2 (by decide),
    by rw [h0]; exact wstate_strInput _ 2⟩

/-- `Fhash` is satisfiable for `float32` and `float64` (the value `42` at `VAL`). -/
theorem fhash_satisfiable (f : Fmt) (k : Nat) (hf : (f = binary32 ∧ k = 4) ∨ (f = binary64 ∧ k = 8)) :
    ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧ Fhash (toy.link impl) A0 H d f k ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
        (HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat k) := by
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, 64, H0_laws, f32hash_impl 64, MemSat.wstate hashArgs, rfl,
      wstate_hPre _ 2 (by decide), rfl, hashArgs_input 2 4 (by decide)⟩
  · exact ⟨_, _, 64, H0_laws, f64hash_impl 64, MemSat.wstate hashArgs, rfl,
      wstate_hPre _ 2 (by decide), rfl, hashArgs_input 2 8 (by decide)⟩

/-- `Chash` is satisfiable for `complex64` and `complex128`. -/
theorem chash_satisfiable (f : Fmt) (k : Nat) (hf : (f = binary32 ∧ k = 4) ∨ (f = binary64 ∧ k = 8)) :
    ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧ Chash (toy.link impl) A0 H d f k ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
        (HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
          Outside (s.regs 0).toNat (2 * k) H.priv) := by
  have ho : ∀ k, k ≤ 16 → Outside ((MemSat.wstate hashArgs).regs 0).toNat k H0.priv := fun k hk => by
    rw [hashArgs_0]; simp [IfaceModel.VAL]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, 64, H0_laws, c64hash_impl 64, MemSat.wstate hashArgs, rfl,
      wstate_hPre _ 2 (by decide), rfl, hashArgs_input 2 8 (by decide), ho 8 (by decide)⟩
  · exact ⟨_, _, 64, H0_laws, c128hash_impl 64, MemSat.wstate hashArgs, rfl,
      wstate_hPre _ 2 (by decide), rfl, hashArgs_input 2 16 (by decide), ho 16 (by decide)⟩

/-- `Typehash` is satisfiable (the type `TD`). -/
theorem typehash_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Typehash (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 3 s ∧ H.Hashable (s.regs 0).toNat s.mem (s.regs 1).toNat) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 IfaceModel.TD else hashArgs i
  have h0 : ((MemSat.wstate r).regs 0).toNat = IfaceModel.TD := by
    simp [r, MemSat.wstate, IfaceModel.TD]
  exact ⟨_, _, 64, H0_laws, typehash_impl 64, MemSat.wstate r, rfl, wstate_hPre _ 3 (by decide),
    by simp only [H0_hashable, h0]⟩

/-- The hashes of the witness `TD`-value do not depend on the callee's window (`H0`'s hashes do
not read memory; `TD`'s `TFlag` is outside the window). -/
theorem wstate_hashFrame (r : Nat → W64) (p : Nat) :
    HashFrame H0 IfaceModel.TD EqHashModel.wmem p (calleeStack (MemSat.wstate r) 64 2) := by
  intro m' hf
  refine ⟨fun h => h, fun _ _ => Iff.rfl, ?_⟩
  simp only [isDirectIface, tyTFlag]
  rw [hf.readLE _ _ ?_]
  simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp [IfaceModel.wsp, IfaceModel.TD]

/-- `Nilinterhash` is satisfiable (the `any` value `EFV = (TD, VAL)`). -/
theorem nilinterhash_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Nilinterhash (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ IfaceInput s d (s.regs 0).toNat ∧
        (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
          H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
            (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
          HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
            (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) (calleeStack s d 2))) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 EFV else hashArgs i
  have h0 : ((MemSat.wstate r).regs 0).toNat = EFV := by simp [r, MemSat.wstate, EFV]
  have ht : EqHashModel.wmem.readLE EFV 8 = IfaceModel.TD := by decide
  refine ⟨_, _, 64, H0_laws, nilinterhash_impl 64, MemSat.wstate r, rfl, wstate_hPre _ 2 (by decide),
    ?_, ?_⟩
  · rw [h0]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, wstate_mem, ht]; exact fun _ => ⟨rfl, wstate_hashFrame r _⟩

/-- `Interhash` is satisfiable (the interface value `IFV = (TAB, VAL)`). -/
theorem interhash_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Interhash (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ IfaceInput s d (s.regs 0).toNat ∧
        (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
          Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
          itabType s.mem (s.regs 0).toNat ≠ 0 ∧
          H.Hashable (itabType s.mem (s.regs 0).toNat) s.mem
            (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) ∧
          HashFrame H (itabType s.mem (s.regs 0).toNat) s.mem
            (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) (calleeStack s d 2))) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 IFV else hashArgs i
  have h0 : ((MemSat.wstate r).regs 0).toNat = IFV := by simp [r, MemSat.wstate, IFV]
  have ht : EqHashModel.wmem.readLE IFV 8 = IfaceModel.TAB := by decide
  have hty : itabType EqHashModel.wmem IFV = IfaceModel.TD := by decide
  have hin : Input (MemSat.wstate r) 64 2 IfaceModel.TAB 16 := by
    refine ⟨by decide, by decide, ?_⟩
    simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [IfaceModel.wsp, IfaceModel.TAB]
  refine ⟨_, _, 64, H0_laws, interhash_impl 64, MemSat.wstate r, rfl, wstate_hPre _ 2 (by decide),
    ?_, ?_⟩
  · rw [h0]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, wstate_mem, ht, hty]; exact fun _ => ⟨hin, by decide, rfl, wstate_hashFrame r _⟩

/-- `Rand` is satisfiable. -/
theorem rand_satisfiable : ∃ (H : HashModel) (impl : List Segment) (d : Nat), H.Laws ∧
    Rand (toy.link impl) A0 H d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ HPre H d 0 s :=
  ⟨_, _, 64, H0_laws, rand_impl 64, MemSat.wstate hashArgs, rfl, wstate_hPre _ 0 (by decide)⟩

end Janus.Contracts.HashSat
