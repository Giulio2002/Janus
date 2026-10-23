import Extracted

/-!
# `ClearWords(b []uint64)`: `clear(b)` zeroes the slice through `runtime.memclrNoHeapPointers`

**Guarantee.** For every slice header `(p, 16, cap)` (a 16-word, 128-byte slice) and every Go call
state `s` of `example.com/basic.ClearWords` such that
* the stack-growth prologue falls through, `SP` is aligned and `[SP-40, SP+16)` is writable (the
  32-byte frame, the saved frame pointer and the spill slot of `p` in the caller's frame),
* the 128 bytes at `p` are writable and `p` is 128-byte aligned,
* the runtime's 32-bit cache `block_size` (a writable `.noptrbss` word at `blockSize`) is writable
  and holds either 0 (not yet initialised, as at program start) or the value memclr itself
  derives from this CPU's `DCZID_EL0` (`zvaCache s.dczid`),
* the buffer, the cache word and the stack window are pairwise disjoint,

the call returns (never faulting or panicking), obeys the ABI, every byte of `b` is 0 afterwards,
the cache holds `zvaCache s.dczid`, and no other byte changes except the stack window (`Frame`).

**For every `DCZID_EL0`.** `DCZID_EL0` is IMPLEMENTATION DEFINED, so it is a field of the
state (`s.dczid`) and the theorem holds for all 32 values: with `DZP = 1` memclr falls back to
`STP` stores; with a block of 64 or 128 bytes it zeroes the buffer with `DC ZVA`; with a
smaller block it uses `STP` on the first call and, once the cache holds the small block size,
`DC ZVA` loops with that block on later calls; with a bigger block than the buffer it uses `STP`.
The proof treats `DZP = 1` once for every `BS` (`case_dzp`) and splits the 16 values with
`DZP = 0` (`case_k`), each for both states of the cache, executing the extracted code of both
functions symbolically. The small-block `DC ZVA` loop goes through an induction lemma
(`zva_loop`).

**Not covered.** Other lengths and alignments (the theorem fixes 128 bytes at a 128-byte
boundary), and a cache holding any other value (the runtime never stores one).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `block_size` (`runtime/memclr_arm64.s`, `identity.json` `skippedData`): memclr's
32-bit cache of the DC ZVA block size. -/
def blockSize : Nat :=
  adrpLdTarget (segAddr Extracted.program "runtime.memclrNoHeapPointers" + 0xf0)
    (segWord Extracted.program "runtime.memclrNoHeapPointers" 60)
    (segWord Extracted.program "runtime.memclrNoHeapPointers" 61) 2

/-- What memclr caches for `DCZID_EL0 = z`: `-1` (as a 32-bit word) when DC ZVA is prohibited,
otherwise the block size `4 << BS`. -/
def zvaCache (z : BitVec 5) : Nat := if z.getLsbD 4 then 0xFFFFFFFF else 4 * 2 ^ (z.toNat % 16)

/-- Every byte in `[lo, hi)` is 0. -/
def ZeroOn (m : Memory) (lo hi : Nat) : Prop := ∀ a, lo ≤ a → a < hi → m.bytes a = 0

@[simp high] theorem zeroOn_empty (m : Memory) {lo hi : Nat} (h : hi ≤ lo) : ZeroOn m lo hi ↔ True :=
  ⟨fun _ => trivial, fun _ _ h1 h2 => absurd (Nat.lt_of_lt_of_le h2 h) (Nat.not_lt.mpr h1)⟩

theorem zeroOn_writeLE_zero (m : Memory) (a k lo hi : Nat) :
    ZeroOn (m.writeLE a k 0) lo hi ↔ ZeroOn m lo (min hi a) ∧ ZeroOn m (max lo (a + k)) hi := by
  constructor
  · intro h
    refine ⟨fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
    · rw [← Memory.bytes_writeLE_outside m (a := a) (n := k) (v := 0) (x := x) (by omega)]
      exact h x h1 (by omega)
    · rw [← Memory.bytes_writeLE_outside m (a := a) (n := k) (v := 0) (x := x) (by omega)]
      exact h x (by omega) h2
  · intro ⟨h1, h2⟩ x hx1 hx2
    by_cases hin : a ≤ x ∧ x < a + k
    · rw [Memory.bytes_writeLE_inside m hin.1 hin.2]; simp
    · rw [Memory.bytes_writeLE_outside m (by omega)]
      by_cases hx : x < a
      · exact h1 x hx1 (by omega)
      · exact h2 x (by omega) hx2

theorem zeroOn_writeLE_disjoint (m : Memory) {a k lo hi : Nat} (v : Nat)
    (h : hi ≤ a ∨ a + k ≤ lo) : ZeroOn (m.writeLE a k v) lo hi ↔ ZeroOn m lo hi := by
  constructor
  · intro h' x h1 h2
    rw [← Memory.bytes_writeLE_outside m (a := a) (n := k) (v := v) (x := x) (by omega)]; exact h' x h1 h2
  · intro h' x h1 h2; rw [Memory.bytes_writeLE_outside m (by omega)]; exact h' x h1 h2

/-- Bytes outside the cleared buffer, the cache word and the stack window keep their value. -/
def Frame (s s' : State) (p : Nat) : Prop :=
  s'.mem.regions = s.mem.regions ∧
  ∀ a, (a < p ∨ p + 128 ≤ a) → (a < blockSize ∨ blockSize + 4 ≤ a) →
    (a < s.sp.toNat - 40 ∨ s.sp.toNat + 16 ≤ a) → s'.mem.bytes a = s.mem.bytes a

/-- Memory `m` after the `DC ZVA` loop zeroed `i` blocks of `B` bytes from `p` upwards. -/
def zeroBlocks (m : Memory) (p B : Nat) : Nat → Memory
  | 0 => m
  | i + 1 => (zeroBlocks m p B i).writeLE (p + B * i) B 0

theorem regions_zeroBlocks (m : Memory) (p B : Nat) :
    ∀ i, (zeroBlocks m p B i).regions = m.regions
  | 0 => rfl
  | i + 1 => by simp [zeroBlocks, regions_zeroBlocks m p B i]

@[janus_acc] theorem accessible_zeroBlocks (m : Memory) (p B i a n : Nat) (w : Bool) :
    (zeroBlocks m p B i).accessible a n w = m.accessible a n w := by
  simp only [Memory.accessible, regions_zeroBlocks]

theorem bytes_zeroBlocks_outside (m : Memory) (p B : Nat) :
    ∀ i a, (a < p ∨ p + B * i ≤ a) → (zeroBlocks m p B i).bytes a = m.bytes a
  | 0, _, _ => rfl
  | i + 1, a, h => by
    simp only [zeroBlocks]
    rw [Memory.bytes_writeLE_outside _ (by rw [Nat.mul_succ] at h; omega),
      bytes_zeroBlocks_outside m p B i a (by rw [Nat.mul_succ] at h; omega)]

theorem readLE_zeroBlocks_disjoint (m : Memory) (p B i : Nat) {a n : Nat}
    (h : a + n ≤ p ∨ p + B * i ≤ a) : (zeroBlocks m p B i).readLE a n = m.readLE a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Memory.readLE]
    rw [bytes_zeroBlocks_outside m p B i a (by omega), ih (by omega)]

theorem zeroOn_zeroBlocks (m : Memory) (p B : Nat) :
    ∀ i, ZeroOn (zeroBlocks m p B i) p (p + B * i)
  | 0 => fun a h1 h2 => absurd h2 (by omega)
  | i + 1 => by
    simp only [zeroBlocks]
    rw [zeroOn_writeLE_zero]
    refine ⟨fun a h1 h2 => zeroOn_zeroBlocks m p B i a h1 (by omega), zeroOn_empty _ (by
      rw [Nat.mul_succ]; omega) |>.mpr trivial⟩

theorem zeroOn_last (m : Memory) (p B i a hi : Nat) (ha : a = p + B * i) (hN : p + B * (i + 1) = hi) :
    ZeroOn ((zeroBlocks m p B i).writeLE a B 0) p hi := by
  subst ha hN; exact zeroOn_zeroBlocks m p B (i + 1)

theorem bytes_last (m : Memory) (p B i a x : Nat) (ha : a = p + B * i) (hx : x < p ∨ p + B * (i + 1) ≤ x) :
    ((zeroBlocks m p B i).writeLE a B 0).bytes x = m.bytes x := by
  subst ha; exact bytes_zeroBlocks_outside m p B (i + 1) x hx

/-- The `DC ZVA` loop head of `memclrNoHeapPointers` (`dc zva, x0`), 0x190 bytes into the
function (layout-independent: derived from the extracted segment). -/
abbrev zvaLoop : Nat := segAddr Extracted.program "runtime.memclrNoHeapPointers" + 0x190

/-- `ClearWords`'s return address from `memclrNoHeapPointers` (the instruction after its `BL`). -/
def retPC : Nat := Extracted.entry + 0x28

/-- The `DC ZVA` loop of `memclrNoHeapPointers` (`dc zva, x0; add x0, x0, x5; subs x1, x1, x5;
b.hs`) for the small blocks `B = 4 << bs`, `bs < 4`, which the runtime uses once its cache
holds that block size: from the loop head with `i` blocks done, the call returns with the
whole buffer zeroed. Proved by induction on the blocks left, one iteration per step. -/
theorem zva_loop (s : State) (p : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (bs : Nat) (hbs : bs < 4) (bsAddr cval : Nat)
    (hp : s.mem.accessible p.toNat 128 true = true) (hp' : p.toNat + 128 ≤ 2 ^ 48)
    (hpal : p.toNat % 128 = 0) (hal : s.sp.toNat % 16 = 0) (hb : 40 ≤ s.sp.toNat)
    (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 40) (40 + 16) true = true)
    (hd1 : p.toNat + 128 ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 56 ≤ p.toNat)
    (hd2 : p.toNat + 128 ≤ bsAddr ∨ bsAddr + 4 ≤ p.toNat)
    (hd3 : bsAddr + 4 ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 56 ≤ bsAddr)
    (hc : s.mem.readLE bsAddr 4 = cval) :
    let B := 4 * 2 ^ bs
    ∀ k (S : State) (i : Nat), i + 1 + k = 128 / B →
      S.pc = BitVec.ofNat 64 zvaLoop → S.regs 0 = p + BitVec.ofNat 64 (B * i) →
      S.regs 1 = BitVec.ofNat 64 (128 - B - B * i) → S.regs 5 = BitVec.ofNat 64 B →
      S.regs 6 = BitVec.ofNat 64 (B - 1) → S.regs 30 = BitVec.ofNat 64 retPC →
      S.sp = s.sp - 32#64 → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
      S.dczid = BitVec.ofNat 5 bs →
      S.mem = zeroBlocks (((s.mem.writeLE (s.sp.toNat - 32) 8 ret).writeLE (s.sp.toNat - 40) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 p.toNat) p.toNat B i →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' =>
        ABIReturn s s' ∧ ZeroOn s'.mem p.toNat (p.toNat + 128) ∧ s'.mem.readLE bsAddr 4 = cval ∧
          s'.mem.regions = s.mem.regions ∧
          ∀ (a : Nat), a < p.toNat ∨ p.toNat + 128 ≤ a → a < bsAddr ∨ bsAddr + 4 ≤ a →
            a < s.sp.toNat - 40 ∨ s.sp.toNat + 16 ≤ a → s'.mem.bytes a = s.mem.bytes a) := by
  intro B k
  janus_eval_nat h_rp : retPC
  have hret' : ret < 2 ^ 64 := by have := hret.user; omega
  janus_cases hbs
  all_goals
    simp only [B, Nat.reducePow, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub] at *
    induction k with
    | zero =>
      intro S i hk hpc h0 h1 h5 h6 h30 hsp h28 h18 hz hm
      janus_run [accessible_zeroBlocks, readLE_zeroBlocks_disjoint, hz, h_rp]
      refine ⟨zeroOn_last _ _ _ _ _ _ (by omega) (by omega), hc, by simp [regions_zeroBlocks],
        fun a h1 h2 h3 => ?_⟩
      rw [bytes_last _ _ _ _ _ _ (by omega) (by omega)]
      simp (disch := omega) only [Memory.bytes_writeLE_outside]
    | succ k ih =>
      intro S i hk hpc h0 h1 h5 h6 h30 hsp h28 h18 hz hm
      janus_run [accessible_zeroBlocks, hz] until [zvaLoop]
      apply ih _ (i + 1)
      all_goals try janus_simp [zeroBlocks]
      all_goals first
        | omega
        | (congr 2; omega)
        | (apply BitVec.eq_of_toNat_eq; simp; omega)
        | (simp only [zeroBlocks]; congr 1; omega)

/-- `zva_loop` from its first iteration (`i = 0`), for the cache value of `DCZID_EL0`. -/
theorem zva_start (s : State) (p : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (bs : Nat) (hbs : bs < 4) (hzs : s.dczid = BitVec.ofNat 5 bs) (bsAddr cval : Nat)
    (hp : s.mem.accessible p.toNat 128 true = true) (hp' : p.toNat + 128 ≤ 2 ^ 48)
    (hpal : p.toNat % 128 = 0) (hal : s.sp.toNat % 16 = 0) (hb : 40 ≤ s.sp.toNat)
    (ha : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 40) (40 + 16) true = true)
    (hd1 : p.toNat + 128 ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 56 ≤ p.toNat)
    (hd2 : p.toNat + 128 ≤ bsAddr ∨ bsAddr + 4 ≤ p.toNat)
    (hd3 : bsAddr + 4 ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 56 ≤ bsAddr)
    (hc : s.mem.readLE bsAddr 4 = cval) (S : State)
    (hpc : S.pc = BitVec.ofNat 64 zvaLoop) (h0 : S.regs 0 = p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (128 - 4 * 2 ^ bs)) (h5 : S.regs 5 = BitVec.ofNat 64 (4 * 2 ^ bs))
    (h6 : S.regs 6 = BitVec.ofNat 64 (4 * 2 ^ bs - 1))
    (h30 : S.regs 30 = BitVec.ofNat 64 retPC)
    (hsp : S.sp = s.sp - 32#64) (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (hz : S.dczid = BitVec.ofNat 5 bs)
    (hm : S.mem = ((s.mem.writeLE (s.sp.toNat - 32) 8 ret).writeLE (s.sp.toNat - 40) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 p.toNat) :
    Reaches (Extracted.program.withExit ret) S (IsReturn fun s' =>
        ABIReturn s s' ∧ ZeroOn s'.mem p.toNat (p.toNat + 128) ∧ s'.mem.readLE bsAddr 4 = cval ∧
          s'.mem.regions = s.mem.regions ∧
          ∀ (a : Nat), a < p.toNat ∨ p.toNat + 128 ≤ a → a < bsAddr ∨ bsAddr + 4 ≤ a →
            a < s.sp.toNat - 40 ∨ s.sp.toNat + 16 ≤ a → s'.mem.bytes a = s.mem.bytes a) := by
  have _ := hzs
  have hN : 0 + 1 + (128 / (4 * 2 ^ bs) - 1) = 128 / (4 * 2 ^ bs) := by
    revert hbs; match bs with
    | 0 | 1 | 2 | 3 => intro; rfl
    | _ + 4 => intro h; omega
  exact zva_loop s p ret hret bs hbs bsAddr cval hp hp' hpal hal hb ha hw hd1 hd2 hd3 hc _ S 0 hN
    hpc (by simp [h0]) (by simp [h1]) h5 h6 h30 hsp h28 h18 hz hm

/-- The theorem for CPUs with `DCZID_EL0 = k` (`correctness` combines the 32 cases). -/
def CaseStmt (k : Nat) : Prop :=
  ∀ (p len cap : BitVec 64), Ensures Extracted.program Extracted.entry [p, len, cap]
      (fun s => s.dczid = BitVec.ofNat 5 k ∧ GuardOK s 0 ∧ StackOK s 40 16 ∧ len.toNat = 16 ∧ Ptr s.mem p 128 true ∧
        p.toNat % 128 = 0 ∧ s.mem.accessible blockSize 4 true = true ∧
        (s.mem.readLE blockSize 4 = 0 ∨ s.mem.readLE blockSize 4 = zvaCache s.dczid) ∧
        Disjoint p.toNat 128 (s.sp.toNat - 40) 56 ∧ Disjoint p.toNat 128 blockSize 4 ∧
        Disjoint blockSize 4 (s.sp.toNat - 40) 56)
      (fun s s' => ZeroOn s'.mem p.toNat (p.toNat + 128) ∧
        s'.mem.readLE blockSize 4 = zvaCache s.dczid ∧ Frame s s' p.toNat)

/-- One `DCZID_EL0` value: execute both functions symbolically, for an empty and for a filled
cache; the small-block `DC ZVA` loop (cached `4 << bs`, `bs < 4`) goes through `zva_start`. -/
macro "clear_case" : tactic => `(tactic| (
  intro p len cap ret hret s hs ⟨hz, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hlen, ⟨hp, hp'⟩, hpal, hca,
    hcache, hd1, hd2, hd3⟩
  janus_intro hs
  janus_eval_nat h_bs : blockSize
  simp only [Disjoint, h_bs] at hd1 hd2 hd3 hca hcache
  have hlen' : len = 16#64 := by apply BitVec.eq_of_toNat_eq; simp [hlen]
  subst hlen'
  simp only [Frame, h_bs, hz]
  simp +decide only [zvaCache, hz, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceMul,
    ite_false, ite_true] at hcache ⊢
  rcases hcache with hc | hc
  all_goals first
    | (have _ : 0 < s.mem.readLE blockSize 4 ∧ s.mem.readLE blockSize 4 < 64 := by rw [h_bs]; omega
       janus_run [hz, hc] until [zvaLoop]
       refine zva_start s p ret hret _ (by decide) hz _ _ hp hp' hpal hal hb ha hw hd1 hd2 hd3 hc _
         ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
       all_goals (janus_eval_nat h_rp : retPC; janus_simp [h_rp]))
    | janus_run [hz, hc]
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (simp (disch := omega) only [zeroOn_writeLE_zero, zeroOn_writeLE_disjoint, zeroOn_empty,
        and_true, true_and]; done)
    | (intro a h1 h2 h3; simp (disch := omega) only [Memory.bytes_writeLE_outside]; done)
    | janus_simp [hc]))

/-- `DZP = 1` (DC ZVA prohibited), for every `BS`: memclr stores `-1` in the cache (or finds it
there) and zeroes the buffer with `STP`. -/
def CaseDZP : Prop :=
  ∀ (p len cap : BitVec 64), Ensures Extracted.program Extracted.entry [p, len, cap]
      (fun s => s.dczid.getLsbD 4 = true ∧ GuardOK s 0 ∧ StackOK s 40 16 ∧ len.toNat = 16 ∧
        Ptr s.mem p 128 true ∧
        p.toNat % 128 = 0 ∧ s.mem.accessible blockSize 4 true = true ∧
        (s.mem.readLE blockSize 4 = 0 ∨ s.mem.readLE blockSize 4 = zvaCache s.dczid) ∧
        Disjoint p.toNat 128 (s.sp.toNat - 40) 56 ∧ Disjoint p.toNat 128 blockSize 4 ∧
        Disjoint blockSize 4 (s.sp.toNat - 40) 56)
      (fun s s' => ZeroOn s'.mem p.toNat (p.toNat + 128) ∧
        s'.mem.readLE blockSize 4 = zvaCache s.dczid ∧ Frame s s' p.toNat)

set_option maxHeartbeats 0 in
theorem case_dzp : CaseDZP := by
  intro p len cap ret hret s hs ⟨hz, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hlen, ⟨hp, hp'⟩, hpal, hca,
    hcache, hd1, hd2, hd3⟩
  janus_intro hs
  janus_eval_nat h_bs : blockSize
  simp only [Disjoint, h_bs] at hd1 hd2 hd3 hca hcache
  have hlen' : len = 16#64 := by apply BitVec.eq_of_toNat_eq; simp [hlen]
  subst hlen'
  simp only [Frame, h_bs, zvaCache, hz, ite_true] at hcache ⊢
  rcases hcache with hc | hc
  all_goals janus_run [hz, hc, BitVec.getLsbD_setWidth]
  all_goals (repeat' refine And.intro ?_ ?_)
  all_goals first
    | (simp (disch := omega) only [zeroOn_writeLE_zero, zeroOn_writeLE_disjoint, zeroOn_empty,
        and_true, true_and]; done)
    | (intro a h1 h2 h3; simp (disch := omega) only [Memory.bytes_writeLE_outside]; done)
    | janus_simp [hc]

set_option maxHeartbeats 0 in
theorem case_0 : CaseStmt 0 := by clear_case
set_option maxHeartbeats 0 in
theorem case_1 : CaseStmt 1 := by clear_case
set_option maxHeartbeats 0 in
theorem case_2 : CaseStmt 2 := by clear_case
set_option maxHeartbeats 0 in
theorem case_3 : CaseStmt 3 := by clear_case
set_option maxHeartbeats 0 in
theorem case_4 : CaseStmt 4 := by clear_case
set_option maxHeartbeats 0 in
theorem case_5 : CaseStmt 5 := by clear_case
set_option maxHeartbeats 0 in
theorem case_6 : CaseStmt 6 := by clear_case
set_option maxHeartbeats 0 in
theorem case_7 : CaseStmt 7 := by clear_case
set_option maxHeartbeats 0 in
theorem case_8 : CaseStmt 8 := by clear_case
set_option maxHeartbeats 0 in
theorem case_9 : CaseStmt 9 := by clear_case
set_option maxHeartbeats 0 in
theorem case_10 : CaseStmt 10 := by clear_case
set_option maxHeartbeats 0 in
theorem case_11 : CaseStmt 11 := by clear_case
set_option maxHeartbeats 0 in
theorem case_12 : CaseStmt 12 := by clear_case
set_option maxHeartbeats 0 in
theorem case_13 : CaseStmt 13 := by clear_case
set_option maxHeartbeats 0 in
theorem case_14 : CaseStmt 14 := by clear_case
set_option maxHeartbeats 0 in
theorem case_15 : CaseStmt 15 := by clear_case

theorem correctness (p len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 40 16 ∧ len.toNat = 16 ∧ Ptr s.mem p 128 true ∧
        p.toNat % 128 = 0 ∧ s.mem.accessible blockSize 4 true = true ∧
        (s.mem.readLE blockSize 4 = 0 ∨ s.mem.readLE blockSize 4 = zvaCache s.dczid) ∧
        Disjoint p.toNat 128 (s.sp.toNat - 40) 56 ∧ Disjoint p.toNat 128 blockSize 4 ∧
        Disjoint blockSize 4 (s.sp.toNat - 40) 56)
      (fun s s' => ZeroOn s'.mem p.toNat (p.toNat + 128) ∧
        s'.mem.readLE blockSize 4 = zvaCache s.dczid ∧ Frame s s' p.toNat) := by
  intro ret hret s hs hpre
  by_cases hdzp : s.dczid.getLsbD 4 = true
  · exact case_dzp p len cap ret hret s hs ⟨hdzp, hpre⟩
  have hz : s.dczid = BitVec.ofNat 5 s.dczid.toNat := by simp
  have hk : s.dczid.toNat < 16 := by
    have key : ∀ k < 32, (BitVec.ofNat 5 k).getLsbD 4 = false → k < 16 := by decide
    exact key _ s.dczid.isLt (by rw [← hz]; simpa using hdzp)
  revert hz
  generalize s.dczid.toNat = k at hk
  intro hz
  have run (h : CaseStmt k) := h p len cap ret hret s hs ⟨hz, hpre⟩
  janus_cases hk
  · exact run case_0
  · exact run case_1
  · exact run case_2
  · exact run case_3
  · exact run case_4
  · exact run case_5
  · exact run case_6
  · exact run case_7
  · exact run case_8
  · exact run case_9
  · exact run case_10
  · exact run case_11
  · exact run case_12
  · exact run case_13
  · exact run case_14
  · exact run case_15

end Proof
