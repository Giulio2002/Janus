import Janus.Amd64.Tactic

/-!
# Proof support for atomics, string instructions and vector moves

Extensions of the `janus64_exec` / `janus64_post` simp sets of `Janus.Amd64.Tactic` (which this
file does not change) for the instructions added with the atomics and memory-routine coverage:

* sub-register merges read back at the merged width (`SETcc` into a byte register followed by
  `TEST` of that byte, as `CompareAndSwap` results are tested);
* `REP STOSQ` / `REP MOVSB` / `REP MOVSQ`: closed forms of `stosIter` and `movsIter` on
  disjoint buffers, so that a string instruction with a symbolic count is one step;
* byte-level memory lemmas for the overlapping stores of `memmove` / `memclr`.

Every lemma is proved from the model; nothing here is trusted.
-/

namespace Janus.Amd64.Tactic

open Janus Janus.Amd64

/-! ## Sub-register merges -/

/-- An 8-bit register write (`putReg 8`) read back at 8 bits. -/
@[janus64_exec, janus64_post] theorem setWidth8_merge (x : BitVec 64) (c : Nat) (h : c < 256) :
    BitVec.setWidth 8 (x &&& 18446744073709551360#64 ||| BitVec.ofNat 64 c) = BitVec.ofNat 8 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  simp
  omega

/-- A 16-bit register write (`putReg 16`) read back at 16 bits. -/
@[janus64_exec, janus64_post] theorem setWidth16_merge (x : BitVec 64) (c : Nat) (h : c < 65536) :
    BitVec.setWidth 16 (x &&& 18446744073709486080#64 ||| BitVec.ofNat 64 c) = BitVec.ofNat 16 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  simp
  omega

/-- `CMPB m8, $c; JE`: the zero test of an 8-bit difference as a `Nat` equation (for `omega`),
e.g. the CPU-feature bytes `CMPB internal/cpu.X86+off(SB), $1`. -/
@[janus64_exec, janus64_post] theorem bv8_sub_eq_zero (x c : Nat) (hc : c < 256) :
    (BitVec.ofNat 8 x - BitVec.ofNat 8 c = 0#8) = (x % 256 = c) := by
  apply propext
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  rw [Nat.mod_eq_of_lt (a := c) (by omega)]
  have := Nat.mod_lt x (show 256 > 0 by decide)
  omega

/-! ## Negative displacements

`memmove`/`memclr` address the tail of a buffer as `-k(DI)(BX*1)`. The generic
`bv_add_add` would fold the displacement `2^64 - k` into `BitVec.ofNat 64 (n + (2^64 - k))`,
a `Nat` sum with a huge literal on the right; checking such a term makes the kernel unfold
`Nat.add` along the literal (deep recursion). This variant puts the literal on the left, so the
sum is stuck on the variable, and `mod64_add_wrap'` turns it into `n - k`. -/

@[janus64_exec high, janus64_post high] theorem bv_add_add_neg (x : BitVec 64) (a b : Nat)
    (_hb : Nat.ble 9223372036854775808 b = true) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b + a) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 b)]

/-! ## Memory: copies and fills built from several stores -/

open Janus.Arm64.Memory in
/-- A read whose last `n` bytes are exactly the last write. -/
theorem readLE_writeLE_last (m : Memory) {a n b k : Nat} (v : Nat) (h1 : b ≤ a) (h2 : a + n = b + k) :
    (m.writeLE a n v).readLE b k = m.readLE b (a - b) + 256 ^ (a - b) * (v % 256 ^ n) := by
  obtain ⟨j, rfl⟩ : ∃ j, a = b + j := ⟨a - b, by omega⟩
  obtain rfl : k = j + n := by omega
  rw [readLE_add, readLE_writeLE_of_disjoint _ _ (by omega), readLE_writeLE_self,
    Nat.add_sub_cancel_left]

open Janus.Arm64.Memory in
/-- One more chunk of a block copy: if the first `j` bytes at `b` already equal the first `j`
bytes of `M` at `c`, then storing the next `n` bytes of `M` at `b + j` extends the copy. -/
theorem copy_step (m M : Memory) (b c j n : Nat) (h : m.readLE b j = M.readLE c j) :
    (m.writeLE (b + j) n (M.readLE (c + j) n)).readLE b (j + n) = M.readLE c (j + n) := by
  rw [readLE_writeLE_last _ _ (by omega) (by omega), Nat.add_sub_cancel_left, h,
    Nat.mod_eq_of_lt (readLE_lt _ _ _), ← readLE_add]

open Janus.Arm64.Memory in
/-- The first chunk of a block copy. -/
theorem copy_first (m M : Memory) (b c n : Nat) :
    (m.writeLE b n (M.readLE c n)).readLE b n = M.readLE c n := by
  rw [readLE_writeLE_self, Nat.mod_eq_of_lt (readLE_lt _ _ _)]

/-! ### Zero fills

`Zeroed M M' d n`: `M'` is `M` with the `n` bytes at `d` set to zero (same regions). This is
how `memclrNoHeapPointers`' overlapping stores are summarised. -/

def Zeroed (M M' : Memory) (d n : Nat) : Prop :=
  M'.regions = M.regions ∧ ∀ x, M'.bytes x = if d ≤ x ∧ x < d + n then 0 else M.bytes x

theorem Zeroed.refl (M : Memory) (d : Nat) : Zeroed M M d 0 :=
  ⟨rfl, fun x => by rw [ite_eq_right (by omega)]⟩

theorem Zeroed.trans {M M₁ M₂ : Memory} {d k j : Nat} (h₁ : Zeroed M M₁ d k)
    (h₂ : Zeroed M₁ M₂ (d + k) j) : Zeroed M M₂ d (k + j) := by
  refine ⟨h₂.1.trans h₁.1, fun x => ?_⟩
  rw [h₂.2 x, h₁.2 x]
  by_cases a : d + k ≤ x ∧ x < d + k + j <;> by_cases b : d ≤ x ∧ x < d + k <;>
    by_cases c : d ≤ x ∧ x < d + (k + j) <;> simp only [a, b, c, ite_false] <;>
    first | rfl | omega

/-- Shift the start of an already zeroed prefix into the form `Zeroed.trans` expects. -/
theorem Zeroed.congr {M M' : Memory} {d n d' n' : Nat} (h : Zeroed M M' d n) (h1 : d = d')
    (h2 : n = n') : Zeroed M M' d' n' := h1 ▸ h2 ▸ h

/-- A read of zeroed bytes. -/
theorem Zeroed.readLE {M M' : Memory} {d n : Nat} (h : Zeroed M M' d n) {a k : Nat}
    (h1 : d ≤ a) (h2 : a + k ≤ d + n) : M'.readLE a k = 0 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Janus.Arm64.Memory.readLE_succ, ih (by omega) (by omega), h.2, ite_eq_left (by omega)]
    rfl

/-- A read outside the zeroed bytes. -/
theorem Zeroed.readLE_outside {M M' : Memory} {d n : Nat} (h : Zeroed M M' d n) {a k : Nat}
    (h1 : a + k ≤ d ∨ d + n ≤ a) : M'.readLE a k = M.readLE a k :=
  Janus.Arm64.Memory.readLE_congr fun i _ => by rw [h.2, ite_eq_right (by omega)]

theorem Zeroed.accessible {M M' : Memory} {d n : Nat} (h : Zeroed M M' d n) (a k : Nat) (w : Bool) :
    M'.accessible a k w = M.accessible a k w :=
  Janus.Arm64.Memory.accessible_congr h.1 a k w

theorem zb_step {W : Memory} {a k x : Nat} {r : Byte} (h1 : a ≤ x ∧ x < a + k → 0 = r)
    (h2 : ¬(a ≤ x ∧ x < a + k) → W.bytes x = r) : (W.writeLE a k 0).bytes x = r := by
  rw [Janus.Arm64.Memory.bytes_writeLE]
  by_cases h : a ≤ x ∧ x < a + k
  · rw [ite_eq_left h, Nat.zero_div]; exact h1 h
  · rw [ite_eq_right h]; exact h2 h

/-- Prove `Zeroed M M' d n` when `M'` is `M` after a chain of zero stores (`writeLE a k 0`)
whose union is exactly `[d, d + n)`, overlapping or not: byte by byte, peeling one store at a
time, with `omega` for each case. -/
macro "zeroed_writes" : tactic => `(tactic| (
  refine ⟨by simp only [Janus.Arm64.Memory.regions_writeLE], fun x => ?_⟩
  repeat (refine zb_step (fun h => ?_) (fun h => ?_); · rw [ite_eq_left (by omega)])
  rw [ite_eq_right (by omega)]))

/-- Close `r = BitVec.ofNat 64 k` where `r` is a register of a symbolic state (a `setRegF`
chain) holding `ofNat` arithmetic: compare as `Nat` with `omega`. -/
macro "bvn" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp (config := { decide := true }) only [setRegF, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.reducePow,
    Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, land_mask_eq_mod]
  all_goals omega))

theorem bv_ushiftRight_ofNat (m k : Nat) (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> k = BitVec.ofNat 64 (m / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem bv_and_ofNat_mask (m c : Nat) (h : m < 2 ^ 64) (hc : c + 1 < 2 ^ 64) (hp : (c + 1) &&& c = 0) :
    BitVec.ofNat 64 m &&& BitVec.ofNat 64 c = BitVec.ofNat 64 (m % (c + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := c) (by omega), land_mask_eq_mod _ _ hp,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) h)]

/-! ## `REP STOS` and `REP MOVS` -/

/-- The memory after `k` element stores of `v` (`sz` bytes each) at `a`, `a + sz`, …. -/
def fillLEStructural (M : Memory) (a sz v : Nat) : Nat → Memory
  | 0 => M
  | k + 1 => fillLEStructural (M.writeLE a sz v) (a + sz) sz v k

/-- `fillLEStructural`, made opaque to the kernel: it is the `Classical.choose` of the existence of that
value, so no definitional check can unfold it (a literal `k` such as `600` otherwise makes the
kernel unfold 600 nested stores whenever it compares two memory terms; the proofs only use the
equations `fillLE_zero`/`fillLE_succ`). -/
noncomputable def fillLE (M : Memory) (a sz v k : Nat) : Memory :=
  Classical.choose (⟨fillLEStructural M a sz v k, rfl⟩ : ∃ m, m = fillLEStructural M a sz v k)

theorem fillLE_eq_structural (M : Memory) (a sz v k : Nat) : fillLE M a sz v k = fillLEStructural M a sz v k :=
  Classical.choose_spec (⟨fillLEStructural M a sz v k, rfl⟩ : ∃ m, m = fillLEStructural M a sz v k)

theorem fillLE_zero (M : Memory) (a sz v : Nat) : fillLE M a sz v 0 = M := by
  rw [fillLE_eq_structural]; rfl

theorem fillLE_succ (M : Memory) (a sz v k : Nat) :
    fillLE M a sz v (k + 1) = fillLE (M.writeLE a sz v) (a + sz) sz v k := by
  rw [fillLE_eq_structural, fillLE_eq_structural]; rfl

@[janus64_exec, janus64_post] theorem regions_fillLE (M : Memory) (a sz v k : Nat) :
    (fillLE M a sz v k).regions = M.regions := by
  induction k generalizing M a with
  | zero => rw [fillLE_zero]
  | succ k ih => rw [fillLE_succ]; exact ih _ _

@[janus64_exec, janus64_post] theorem accessible_fillLE (M : Memory) (a sz v k b n : Nat) (w : Bool) :
    (fillLE M a sz v k).accessible b n w = M.accessible b n w :=
  Janus.Arm64.Memory.accessible_congr (regions_fillLE M a sz v k) b n w

/-- A fill with zeros, byte by byte. -/
theorem bytes_fillLE_zero (M : Memory) (a sz k x : Nat) :
    (fillLE M a sz 0 k).bytes x = if a ≤ x ∧ x < a + sz * k then 0 else M.bytes x := by
  induction k generalizing M a with
  | zero => simp only [fillLE_zero, Nat.mul_zero, Nat.add_zero]; rw [ite_eq_right (by omega)]
  | succ k ih =>
    simp only [fillLE_succ, ih, Janus.Arm64.Memory.bytes_writeLE, Nat.zero_div, Nat.mul_succ]
    by_cases h1 : a + sz ≤ x ∧ x < a + sz + sz * k <;> by_cases h2 : a ≤ x ∧ x < a + sz <;>
      by_cases h3 : a ≤ x ∧ x < a + (sz * k + sz) <;>
      simp only [h1, h2, h3, ite_false] <;> first | rfl | omega

theorem zeroed_fillLE (M : Memory) (a sz k : Nat) : Zeroed M (fillLE M a sz 0 k) a (sz * k) :=
  ⟨regions_fillLE _ _ _ _ _, bytes_fillLE_zero M a sz k⟩

theorem readLE_fillLE_disjoint (M : Memory) (a sz v k b n : Nat)
    (h : b + n ≤ a ∨ a + sz * k ≤ b) : (fillLE M a sz v k).readLE b n = M.readLE b n := by
  induction k generalizing M a with
  | zero => rw [fillLE_zero]
  | succ k ih =>
    simp only [fillLE_succ]
    rw [ih _ _ (by rw [Nat.mul_succ] at h; omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by rw [Nat.mul_succ] at h; omega)]

theorem State.ext' {s t : State} (h1 : s.regs = t.regs) (h2 : s.rip = t.rip) (h3 : s.flags = t.flags)
    (h4 : s.xmm = t.xmm) (h5 : s.mem = t.mem) (h6 : s.ymmHi = t.ymmHi := by rfl)
    (h7 : s.fsBase = t.fsBase := by rfl) (h8 : s.df = t.df := by rfl)
    (h9 : s.mxcsr = t.mxcsr := by rfl) (h10 : s.x87 = t.x87 := by rfl)
    (h11 : s.fpucw = t.fpucw := by rfl) (h12 : s.zmmHi = t.zmmHi := by rfl)
    (h13 : s.kreg = t.kreg := by rfl) : s = t := by
  cases s; cases t; simp_all

private theorem acc_head {m : Memory} {a sz k : Nat} {w : Bool} (h : m.accessible a (sz * (k + 1)) w = true) :
    m.accessible a sz w = true :=
  Janus.Arm64.Memory.accessible_sub m h (by cases w <;> simp) (Nat.le_refl _) (by rw [Nat.mul_succ]; omega)

private theorem acc_tail {m : Memory} {a sz k : Nat} {w : Bool} (h : m.accessible a (sz * (k + 1)) w = true) :
    m.accessible (a + sz) (sz * k) w = true :=
  Janus.Arm64.Memory.accessible_sub m h (by cases w <;> simp) (by omega) (by rw [Nat.mul_succ]; omega)

/-- `k` `STOS` element steps on a writable, non-wrapping range at `RDI = a`. -/
theorem stosIter_ok (sz v k : Nat) (t : State) (a : Nat) (h7 : t.regs 7 = BitVec.ofNat 64 a)
    (hacc : t.mem.accessible a (sz * k) true = true) (hnw : a + sz * k < 2 ^ 64) :
    stosIter sz v k t = .ok ({ t with mem := fillLE t.mem a sz v k }.setReg 7
      (BitVec.ofNat 64 (a + sz * k))) := by
  induction k generalizing t a with
  | zero =>
    simp only [stosIter, fillLE_zero, Nat.mul_zero, Nat.add_zero, Except.ok.injEq]
    refine State.ext' ?_ rfl rfl rfl rfl
    funext i; simp only [State.setReg]; split <;> simp_all
  | succ k ih =>
    have ha : a < 2 ^ 64 := by omega
    have h7' : (t.regs 7).toNat = a := by rw [h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    have hst : store t.mem a sz v = .ok (t.mem.writeLE a sz v) := store_ok _ _ (acc_head hacc)
    simp only [stosIter, h7', hst]
    refine (ih _ (a + sz) ?_ ?_ ?_).trans ?_
    · simp [State.setReg, h7, BitVec.ofNat_add]
    · exact acc_tail hacc
    · rw [Nat.mul_succ] at hnw; omega
    congr 1
    refine State.ext' ?_ rfl rfl rfl ?_
    · funext i; simp only [State.setReg]; split
      · congr 1; rw [Nat.mul_succ]; omega
      · rfl
    · simp [State.setReg, fillLE_succ]

/-- The memory after `k` `MOVS` element steps from `b` to `a` (`sz` bytes each). -/
def copyLE (M : Memory) (a b sz : Nat) : Nat → Memory
  | 0 => M
  | k + 1 => copyLE (M.writeLE a sz (M.readLE b sz)) (a + sz) (b + sz) sz k

@[janus64_exec, janus64_post] theorem regions_copyLE (M : Memory) (a b sz k : Nat) :
    (copyLE M a b sz k).regions = M.regions := by
  induction k generalizing M a b with
  | zero => rfl
  | succ k ih => exact ih _ _ _

@[janus64_exec, janus64_post] theorem accessible_copyLE (M : Memory) (a b sz k c n : Nat) (w : Bool) :
    (copyLE M a b sz k).accessible c n w = M.accessible c n w :=
  Janus.Arm64.Memory.accessible_congr (regions_copyLE M a b sz k) c n w

/-- `k` `MOVS` element steps from `RSI = b` to `RDI = a` on accessible, non-wrapping ranges. -/
theorem movsIter_ok (sz k : Nat) (t : State) (a b : Nat) (h7 : t.regs 7 = BitVec.ofNat 64 a)
    (h6 : t.regs 6 = BitVec.ofNat 64 b)
    (hacc : t.mem.accessible a (sz * k) true = true) (hsrc : t.mem.accessible b (sz * k) false = true)
    (hnw : a + sz * k < 2 ^ 64) (hnw' : b + sz * k < 2 ^ 64) :
    movsIter sz k t = .ok (({ t with mem := copyLE t.mem a b sz k }.setReg 6
      (BitVec.ofNat 64 (b + sz * k))).setReg 7 (BitVec.ofNat 64 (a + sz * k))) := by
  induction k generalizing t a b with
  | zero =>
    simp only [movsIter, copyLE, Nat.mul_zero, Nat.add_zero, Except.ok.injEq]
    refine State.ext' ?_ rfl rfl rfl rfl
    funext i; simp only [State.setReg]; split <;> (try split) <;> simp_all
  | succ k ih =>
    have ha : a < 2 ^ 64 := by omega
    have hb : b < 2 ^ 64 := by omega
    have h7' : (t.regs 7).toNat = a := by rw [h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
    have h6' : (t.regs 6).toNat = b := by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    have hld : load t.mem b sz = .ok (t.mem.readLE b sz) := load_ok _ (acc_head hsrc)
    have hst : store t.mem a sz (t.mem.readLE b sz) = .ok (t.mem.writeLE a sz (t.mem.readLE b sz)) :=
      store_ok _ _ (acc_head hacc)
    simp only [movsIter, h7', h6', hld, hst]
    refine (ih _ (a + sz) (b + sz) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · simp [State.setReg, h7, BitVec.ofNat_add]
    · simp [State.setReg, h6, BitVec.ofNat_add]
    · exact acc_tail hacc
    · exact acc_tail hsrc
    · rw [Nat.mul_succ] at hnw; omega
    · rw [Nat.mul_succ] at hnw'; omega
    congr 1
    refine State.ext' ?_ rfl rfl rfl ?_
    · funext i; simp only [State.setReg]; split
      · congr 1; rw [Nat.mul_succ]; omega
      · split
        · congr 1; rw [Nat.mul_succ]; omega
        · rfl
    · simp [State.setReg, copyLE]

/-! ### Stepping over a `REP` string instruction

`janus64_run` cannot evaluate `REP STOS`/`REP MOVS` with a symbolic count. Stop in front of one
(`janus64_run until [addr]`) and apply `Reaches.repStos` / `Reaches.repMovs`: they take the
destination (and source) address and the count as explicit values, the accessibility and
no-wrap facts, and continue from the closed-form result state (`fillLE` / `copyLE`). The
program facts are one Boolean (`stepOKAt`), closed by `rfl` (kernel evaluation). -/

/-- `stepOK` with the bytes fetched from the program. -/
def stepOKAt (p : Program) (pc : Nat) (i : Instr) (len : Nat) : Bool :=
  match p.fetch pc with
  | some bs => stepOK p pc bs i len
  | none => false

theorem stepOKAt_spec {p : Program} {pc : Nat} {i : Instr} {len : Nat}
    (h : stepOKAt p pc i len = true) : ∃ bs, stepOK p pc bs i len = true := by
  unfold stepOKAt at h
  split at h
  · exact ⟨_, h⟩
  · cases h

theorem Reaches.repStos {p : Program} {ret : Nat} {t : State} {Q : Outcome → Prop} {c len w : Nat}
    (hret : GoABI.RetAddr p ret) (hpc : t.rip = BitVec.ofNat 64 c)
    (hok : stepOKAt p c (.stos true w) len = true) (a k : Nat) (hdf : t.df = false)
    (h7 : t.regs 7 = BitVec.ofNat 64 a) (h1 : t.regs 1 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64)
    (hacc : t.mem.accessible a (w / 8 * k) true = true) (hnw : a + w / 8 * k < 2 ^ 64)
    (h : Reaches (p.withExit ret)
      ((({ t with mem := fillLE t.mem a (w / 8) (t.getReg w 0).toNat k }.setReg 7
        (BitVec.ofNat 64 (a + w / 8 * k))).setReg 1 0).setRip
        (BitVec.ofNat 64 ((t.rip.toNat + len) % 2 ^ 64))) Q) :
    Reaches (p.withExit ret) t Q := by
  obtain ⟨bs, hok⟩ := stepOKAt_spec hok
  refine Reaches.step_withExit hret hpc hok rfl ?_
  have h1' : (t.regs 1).toNat = k := by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp only [exec, ite_true, hdf, Bool.false_eq_true, ite_false, h1', stosIter_ok _ _ _ t a h7 hacc hnw]
  rw [hdf] at h; exact h

theorem Reaches.repMovs {p : Program} {ret : Nat} {t : State} {Q : Outcome → Prop} {c len w : Nat}
    (hret : GoABI.RetAddr p ret) (hpc : t.rip = BitVec.ofNat 64 c)
    (hok : stepOKAt p c (.movs true w) len = true) (a b k : Nat) (hdf : t.df = false)
    (h7 : t.regs 7 = BitVec.ofNat 64 a) (h6 : t.regs 6 = BitVec.ofNat 64 b)
    (h1 : t.regs 1 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64)
    (hacc : t.mem.accessible a (w / 8 * k) true = true)
    (hsrc : t.mem.accessible b (w / 8 * k) false = true)
    (hnw : a + w / 8 * k < 2 ^ 64) (hnw' : b + w / 8 * k < 2 ^ 64)
    (h : Reaches (p.withExit ret)
      (((({ t with mem := copyLE t.mem a b (w / 8) k }.setReg 6
        (BitVec.ofNat 64 (b + w / 8 * k))).setReg 7 (BitVec.ofNat 64 (a + w / 8 * k))).setReg 1 0).setRip
        (BitVec.ofNat 64 ((t.rip.toNat + len) % 2 ^ 64))) Q) :
    Reaches (p.withExit ret) t Q := by
  obtain ⟨bs, hok⟩ := stepOKAt_spec hok
  refine Reaches.step_withExit hret hpc hok rfl ?_
  have h1' : (t.regs 1).toNat = k := by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp only [exec, ite_true, hdf, Bool.false_eq_true, ite_false, h1', movsIter_ok _ _ t a b h7 h6 hacc hsrc hnw hnw']
  rw [hdf] at h; exact h

end Janus.Amd64.Tactic
