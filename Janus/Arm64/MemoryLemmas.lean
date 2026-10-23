import Janus.Arm64.State

/-!
# Register and memory lemmas

Read-over-write and frame lemmas for the register file (`readZR`/`readSP`/`writeZR`/`writeSP`)
and for byte memory (`Memory.readLE`/`writeLE`/`accessible`, checked `load`/`store`).

Conventions:
* Field projections of `writeZR`/`writeSP` and the "different register" cases are `@[simp]`.
  Lemmas whose side condition is `r ≠ 31` are also `@[simp]`: for concrete register numbers
  `simp` discharges the side condition itself.
* `readLE (writeLE m a n v) a n = v % 256 ^ n` is `readLE_writeLE_self`; disjoint accesses
  commute via `readLE_writeLE_of_disjoint`; `readLE_add` splits a read in two.
-/

namespace Janus.Arm64

/-! ## Registers -/

namespace State

variable (s : State) (r i : Nat) (v : W64)

@[simp] theorem readZR_31 : s.readZR 31 = 0 := rfl
@[simp] theorem readSP_31 : s.readSP 31 = s.sp := rfl

@[simp] theorem readZR_of_ne {r : Nat} (h : r ≠ 31) : s.readZR r = s.regs r := by
  simp [readZR, h]

@[simp] theorem readSP_of_ne {r : Nat} (h : r ≠ 31) : s.readSP r = s.regs r := by
  simp [readSP, h]

@[simp] theorem writeZR_31 : s.writeZR 31 v = s := rfl
@[simp] theorem writeSP_31 : s.writeSP 31 v = { s with sp := v } := rfl

theorem writeSP_eq_writeZR {r : Nat} (h : r ≠ 31) : s.writeSP r v = s.writeZR r v := by
  simp [writeSP, writeZR, h]

@[simp] theorem pc_writeZR : (s.writeZR r v).pc = s.pc := by unfold writeZR; split <;> rfl
@[simp] theorem sp_writeZR : (s.writeZR r v).sp = s.sp := by unfold writeZR; split <;> rfl
@[simp] theorem flags_writeZR : (s.writeZR r v).flags = s.flags := by unfold writeZR; split <;> rfl
@[simp] theorem mem_writeZR : (s.writeZR r v).mem = s.mem := by unfold writeZR; split <;> rfl

@[simp] theorem pc_writeSP : (s.writeSP r v).pc = s.pc := by unfold writeSP; split <;> rfl
@[simp] theorem flags_writeSP : (s.writeSP r v).flags = s.flags := by unfold writeSP; split <;> rfl
@[simp] theorem mem_writeSP : (s.writeSP r v).mem = s.mem := by unfold writeSP; split <;> rfl

@[simp] theorem sp_writeSP_of_ne {r : Nat} (h : r ≠ 31) : (s.writeSP r v).sp = s.sp := by
  simp [writeSP, h]

theorem regs_writeZR {r : Nat} (h : r ≠ 31) :
    (s.writeZR r v).regs = fun i => if i = r then v else s.regs i := by
  simp [writeZR, h]

@[simp] theorem regs_writeZR_self {r : Nat} (h : r ≠ 31) : (s.writeZR r v).regs r = v := by
  simp [writeZR, h]

@[simp] theorem regs_writeZR_of_ne {i r : Nat} (h : i ≠ r) : (s.writeZR r v).regs i = s.regs i := by
  unfold writeZR; split <;> simp [h]

@[simp] theorem regs_writeSP_self {r : Nat} (h : r ≠ 31) : (s.writeSP r v).regs r = v := by
  simp [writeSP, h]

@[simp] theorem regs_writeSP_of_ne {i r : Nat} (h : i ≠ r) : (s.writeSP r v).regs i = s.regs i := by
  unfold writeSP; split <;> simp [h]

@[simp] theorem readZR_writeZR_self {r : Nat} (h : r ≠ 31) : (s.writeZR r v).readZR r = v := by
  simp [h]

@[simp] theorem readZR_writeZR_of_ne {r' r : Nat} (h : r' ≠ r) :
    (s.writeZR r v).readZR r' = s.readZR r' := by
  unfold readZR; split <;> simp [h]

/-- Writing then reading with the SP convention returns the value for every `r`
(including `r = 31`, the stack pointer). -/
@[simp] theorem readSP_writeSP_self : (s.writeSP r v).readSP r = v := by
  by_cases h : r = 31
  · subst h; rfl
  · simp [h]

@[simp] theorem readSP_writeSP_of_ne {r' r : Nat} (h : r' ≠ r) :
    (s.writeSP r v).readSP r' = s.readSP r' := by
  unfold readSP
  by_cases h' : r' = 31
  · subst h'; simp [Ne.symm h]
  · simp [h', h]

@[simp] theorem readSP_writeZR_of_ne {r' r : Nat} (h : r' ≠ r) :
    (s.writeZR r v).readSP r' = s.readSP r' := by
  unfold readSP; split <;> simp [h]

@[simp] theorem readZR_writeSP_of_ne {r' r : Nat} (h : r' ≠ r) :
    (s.writeSP r v).readZR r' = s.readZR r' := by
  unfold readZR; split <;> simp [h]

/-- `readZR` of the stack pointer write: the SP is invisible through the ZR convention. -/
@[simp] theorem readZR_writeSP_31 : (s.writeSP 31 v).readZR r = s.readZR r := by
  unfold readZR; split <;> rfl

end State

/-! ## Memory -/

namespace Memory

variable (m : Memory)

/-! ### `writeLE` frame facts -/

@[simp] theorem regions_writeLE (a n v : Nat) : (m.writeLE a n v).regions = m.regions := rfl

@[simp] theorem accessible_writeLE (a n v b k : Nat) (w : Bool) :
    (m.writeLE a n v).accessible b k w = m.accessible b k w := rfl

theorem bytes_writeLE (a n v x : Nat) :
    (m.writeLE a n v).bytes x =
      if a ≤ x ∧ x < a + n then BitVec.ofNat 8 (v / 256 ^ (x - a)) else m.bytes x := rfl

theorem bytes_writeLE_inside {a n v x : Nat} (h1 : a ≤ x) (h2 : x < a + n) :
    (m.writeLE a n v).bytes x = BitVec.ofNat 8 (v / 256 ^ (x - a)) := by
  simp [bytes_writeLE, h1, h2]

theorem bytes_writeLE_outside {a n v x : Nat} (h : x < a ∨ a + n ≤ x) :
    (m.writeLE a n v).bytes x = m.bytes x := by
  rw [bytes_writeLE, ite_eq_right (by omega)]

@[simp] theorem writeLE_zero (a v : Nat) : m.writeLE a 0 v = m := by
  cases m; simp only [writeLE, Memory.mk.injEq, and_true]; funext x; simp; omega

/-! ### `readLE` -/

@[simp] theorem readLE_zero (a : Nat) : m.readLE a 0 = 0 := rfl

theorem readLE_succ (a n : Nat) :
    m.readLE a (n + 1) = (m.bytes a).toNat + 256 * m.readLE (a + 1) n := rfl

@[simp] theorem readLE_one (a : Nat) : m.readLE a 1 = (m.bytes a).toNat := by
  simp [readLE_succ]

/-- `readLE` only depends on the bytes in `[a, a + n)`. -/
theorem readLE_congr {m m' : Memory} {a n : Nat}
    (h : ∀ i, i < n → m.bytes (a + i) = m'.bytes (a + i)) : m.readLE a n = m'.readLE a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readLE_succ, readLE_succ, ih (a := a + 1) (fun i hi => by
      have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega] at this)]
    have := h 0 (by omega); simp at this; rw [this]

/-- Memories with the same bytes read the same (regions are irrelevant to `readLE`). -/
theorem readLE_of_bytes_eq {m m' : Memory} (h : m.bytes = m'.bytes) (a n : Nat) :
    m.readLE a n = m'.readLE a n :=
  readLE_congr (fun i _ => by rw [h])

theorem readLE_lt (a n : Nat) : m.readLE a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [readLE_succ, Nat.pow_succ]
    have hb := (m.bytes a).isLt
    have hr := ih (a + 1)
    generalize m.readLE (a + 1) n = y at hr ⊢
    generalize 256 ^ n = t at hr ⊢
    simp at hb
    omega

/-- Split a little-endian read: the low `n` bytes and the high `k` bytes. -/
theorem readLE_add (a n k : Nat) :
    m.readLE a (n + k) = m.readLE a n + 256 ^ n * m.readLE (a + n) k := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega, readLE_succ, readLE_succ, ih,
      show a + 1 + n = a + (n + 1) by omega, Nat.pow_succ, Nat.mul_add, Nat.add_assoc,
      Nat.mul_comm (256 ^ n) 256, Nat.mul_assoc]

theorem readLE_eight (a : Nat) : m.readLE a 8 = m.readLE a 4 + 2 ^ 32 * m.readLE (a + 4) 4 :=
  readLE_add m a 4 4

theorem readLE_four (a : Nat) : m.readLE a 4 = m.readLE a 2 + 2 ^ 16 * m.readLE (a + 2) 2 :=
  readLE_add m a 2 2

theorem readLE_two (a : Nat) : m.readLE a 2 = m.readLE a 1 + 2 ^ 8 * m.readLE (a + 1) 1 :=
  readLE_add m a 1 1

theorem readLE_sixteen (a : Nat) :
    m.readLE a 16 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 :=
  readLE_add m a 8 8

/-- The low `j` bytes of an `n`-byte read are a `j`-byte read. -/
theorem readLE_mod (a n j : Nat) (h : j ≤ n) : m.readLE a n % 256 ^ j = m.readLE a j := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  rw [readLE_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (readLE_lt _ _ _)]

/-- The bytes above offset `j` of an `n`-byte read. -/
theorem readLE_div (a n j : Nat) (h : j ≤ n) :
    m.readLE a n / 256 ^ j = m.readLE (a + j) (n - j) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  rw [readLE_add, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt (readLE_lt _ _ _), Nat.zero_add, Nat.add_sub_cancel_left]

/-! ### Read after write -/

private theorem mod_mul_256 (v n : Nat) :
    v % 256 + 256 * (v / 256 % 256 ^ n) = v % 256 ^ (n + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

private theorem div_pow_succ (v i : Nat) : v / 256 ^ (i + 1) = v / 256 / 256 ^ i := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem readLE_writeLE_self (a n v : Nat) : (m.writeLE a n v).readLE a n = v % 256 ^ n := by
  induction n generalizing a v with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [readLE_succ, bytes_writeLE_inside _ (Nat.le_refl a) (by omega)]
    rw [readLE_congr (m' := m.writeLE (a + 1) n (v / 256)) (fun i hi => by
      rw [bytes_writeLE_inside _ (by omega) (by omega), bytes_writeLE_inside _ (by omega) (by omega),
        show a + 1 + i - a = i + 1 by omega, show a + 1 + i - (a + 1) = i by omega,
        div_pow_succ])]
    rw [ih, BitVec.toNat_ofNat, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    exact mod_mul_256 v n

theorem readLE_writeLE_of_disjoint {a n b k : Nat} (v : Nat) (h : b + k ≤ a ∨ a + n ≤ b) :
    (m.writeLE a n v).readLE b k = m.readLE b k :=
  readLE_congr (fun i hi => bytes_writeLE_outside _ (by omega))

/-- A read entirely inside a write sees the corresponding slice of the written value. -/
theorem readLE_writeLE_inside {a n b k : Nat} (v : Nat) (h1 : a ≤ b) (h2 : b + k ≤ a + n) :
    (m.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k := by
  rw [readLE_congr (m' := m.writeLE b k (v / 256 ^ (b - a))) (fun i hi => by
    rw [bytes_writeLE_inside _ (by omega) (by omega), bytes_writeLE_inside _ (by omega) (by omega),
      Nat.div_div_eq_div_mul, ← Nat.pow_add, show b - a + (b + i - b) = b + i - a by omega])]
  exact readLE_writeLE_self _ _ _ _

/-- Splitting a write into its low `n` and high `k` bytes. -/
theorem writeLE_add (a n k v : Nat) :
    m.writeLE a (n + k) v = (m.writeLE a n v).writeLE (a + n) k (v / 256 ^ n) := by
  cases m with
  | mk bytes regions =>
  simp only [writeLE, Memory.mk.injEq, and_true]
  funext x
  by_cases h1 : a ≤ x ∧ x < a + n
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h1]
  · by_cases h2 : a + n ≤ x ∧ x < a + n + k
    · rw [ite_eq_left (by omega), ite_eq_left h2, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show n + (x - (a + n)) = x - a by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h1]

/-- Only the low `n` bytes of the value matter. -/
theorem writeLE_mod (a n v : Nat) : m.writeLE a n (v % 256 ^ n) = m.writeLE a n v := by
  cases m with
  | mk bytes regions =>
  simp only [writeLE, Memory.mk.injEq, and_true]
  funext x
  by_cases h : a ≤ x ∧ x < a + n
  · rw [ite_eq_left h, ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    obtain ⟨j, hj⟩ : ∃ j, x - a = j := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, n = j + (d + 1) := ⟨n - j - 1, by omega⟩
    rw [hj, hd, Nat.pow_add, Nat.mod_mul_right_div_self, Nat.pow_succ,
      Nat.mod_mul_left_mod]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ### Accessibility -/

theorem accessible_iff (a n : Nat) (w : Bool) :
    m.accessible a n w = true ↔
      ∃ r ∈ m.regions, r.base ≤ a ∧ a + n ≤ r.base + r.size ∧ (w = false ∨ r.writable = true) := by
  unfold accessible
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · rintro ⟨r, hr, ⟨h1, h2⟩, h3⟩; exact ⟨r, hr, h1, h2, h3⟩
  · rintro ⟨r, hr, h1, h2, h3⟩; exact ⟨r, hr, ⟨h1, h2⟩, h3⟩

theorem accessible_of_mem {r : Region} {a n : Nat} {w : Bool} (hr : r ∈ m.regions)
    (h1 : r.base ≤ a) (h2 : a + n ≤ r.base + r.size) (h3 : w = false ∨ r.writable = true) :
    m.accessible a n w = true :=
  (accessible_iff m a n w).2 ⟨r, hr, h1, h2, h3⟩

theorem accessible_read_of_write {a n : Nat} (h : m.accessible a n true = true) :
    m.accessible a n false = true := by
  obtain ⟨r, hr, h1, h2, _⟩ := (accessible_iff m a n true).1 h
  exact accessible_of_mem m hr h1 h2 (Or.inl rfl)

/-- A sub-range of an accessible range is accessible. -/
theorem accessible_mono {a n b k : Nat} {w : Bool} (h : m.accessible a n w = true)
    (h1 : a ≤ b) (h2 : b + k ≤ a + n) : m.accessible b k w = true := by
  obtain ⟨r, hr, h3, h4, h5⟩ := (accessible_iff m a n w).1 h
  exact accessible_of_mem m hr (by omega) (by omega) h5

theorem accessible_weaken {a n : Nat} {w : Bool} (h : m.accessible a n w = true) :
    m.accessible a n false = true := by
  cases w
  · exact h
  · exact accessible_read_of_write m h

/-- Accessibility depends only on the region list. -/
theorem accessible_congr {m m' : Memory} (h : m.regions = m'.regions) (a n : Nat) (w : Bool) :
    m.accessible a n w = m'.accessible a n w := by
  simp [accessible, h]

end Memory

/-! ## Checked `load` / `store` -/

section LoadStore

variable (m : Memory) {a n b k : Nat} (v : Nat)

theorem load_eq_ok (h : m.accessible a n false = true) : load m a n = .ok (m.readLE a n) := by
  simp [load, h]

theorem load_eq_error (h : m.accessible a n false = false) :
    load m a n = .error (.outsideAllocation a n) := by
  simp [load, h]

theorem load_ok_iff {x : Nat} :
    load m a n = .ok x ↔ m.accessible a n false = true ∧ x = m.readLE a n := by
  unfold load
  cases h : m.accessible a n false
  · exact ⟨(fun h' => nomatch h'), (fun ⟨h', _⟩ => nomatch h')⟩
  · exact ⟨(fun h' => ⟨rfl, (Except.ok.inj h').symm⟩), (fun ⟨_, hx⟩ => hx ▸ rfl)⟩

theorem store_eq_ok (h : m.accessible a n true = true) :
    store m a n v = .ok (m.writeLE a n v) := by
  simp [store, h, Memory.accessible_read_of_write m h]

theorem store_ok_iff {m' : Memory} :
    store m a n v = .ok m' ↔ m.accessible a n true = true ∧ m' = m.writeLE a n v := by
  unfold store
  cases hw : m.accessible a n true
  · cases m.accessible a n false <;> exact ⟨(fun h' => nomatch h'), (fun ⟨h', _⟩ => nomatch h')⟩
  · rw [Memory.accessible_read_of_write m hw]
    exact ⟨(fun h' => ⟨rfl, (Except.ok.inj h').symm⟩), (fun ⟨_, hx⟩ => hx ▸ rfl)⟩

theorem store_regions {m' : Memory} (h : store m a n v = .ok m') : m'.regions = m.regions := by
  obtain ⟨_, rfl⟩ := (store_ok_iff m v).1 h; rfl

theorem store_accessible {m' : Memory} (h : store m a n v = .ok m') (b k : Nat) (w : Bool) :
    m'.accessible b k w = m.accessible b k w := by
  obtain ⟨_, rfl⟩ := (store_ok_iff m v).1 h; rfl

theorem store_readLE_self {m' : Memory} (h : store m a n v = .ok m') :
    m'.readLE a n = v % 256 ^ n := by
  obtain ⟨_, rfl⟩ := (store_ok_iff m v).1 h; exact Memory.readLE_writeLE_self _ _ _ _

theorem load_store_self {m' : Memory} (h : store m a n v = .ok m') :
    load m' a n = .ok (v % 256 ^ n) := by
  obtain ⟨hw, rfl⟩ := (store_ok_iff m v).1 h
  rw [load_eq_ok _ (by simpa using Memory.accessible_read_of_write m hw),
    Memory.readLE_writeLE_self]

theorem load_store_of_disjoint {m' : Memory} (h : store m a n v = .ok m')
    (hd : b + k ≤ a ∨ a + n ≤ b) : load m' b k = load m b k := by
  obtain ⟨_, rfl⟩ := (store_ok_iff m v).1 h
  simp [load, Memory.readLE_writeLE_of_disjoint _ _ hd]

end LoadStore

end Janus.Arm64
