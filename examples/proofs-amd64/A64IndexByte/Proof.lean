import Janus
import Extracted

/-!
# `A64IndexByte(b []byte, c byte) int` on amd64: `bytes.IndexByte` through `indexbytebody`'s AVX2 scan

The same function and statement as the arm64 proof (`examples/proofs/A64IndexByte.lean`, which
names it after the architecture it was written for): `bytes.IndexByte` on 64 bytes returns the
index of the first byte equal to `c`, or `-1` (`indexOf`).

**Guarantee.** For every slice `b` (pointer `p`, length `64`, capacity `cap`), every byte `c` and
every Go call state such that the stack-growth prologue falls through, `[RSP-56, RSP+16)` is
writable, the TLS slot holds `g` (`TlsG`: the code reloads `R14` from `FS:-8` after the ABI0 call),
the 64 bytes at `p` are readable and outside the stack window, and the CPU-feature byte
`internal/cpu.X86.HasAVX2` is readable and `1`, the call returns, obeys the ABI, and returns
`indexOf s.mem p (c mod 256) 64` in `RAX`. No alignment of `p` is needed (`VMOVDQU`).

**What is executed.** `A64IndexByte` spills its arguments to the ABI0 frame and calls
`internal/bytealg.IndexByte.abi0`, which jumps to `indexbytebody`: `MOVD`/`PUNPCKLBW`/`PSHUFL`
broadcast `c`; for 64 bytes the code takes the `avx2` branch (`CMPB HasAVX2, $1`), broadcasts `c`
again with `VPBROADCASTB`, and scans 32-byte chunks with `VMOVDQU`, `VPCMPEQB`, `VPTEST`; at a match
`VPMOVMSKB` and `BSFL` locate the byte (`chunk_ft`, `ctz_msb_cmpeq`), the second chunk is re-read
from `p + 64 - 32`, and the result is stored to the ABI0 result slot and loaded into `RAX`.

**Limits.** The SSE path (`HasAVX2 = 0`) is not covered: it executes `BSFL` on the mask of every
chunk before testing it (`BSFL DX, DX; JNZ ssesuccess`), and the model treats `BSF` of zero as an
undefined result (a fault, as Intel documents the destination as undefined), so a chunk without a
match cannot be stepped past. This is a deliberate conservatism of the ISA model, not of the
code: the precondition `HasAVX2 = 1` selects the path the theorem proves.
-/

namespace Proof

attribute [local irreducible] Janus.Amd64.msbBytes Janus.Amd64.cmpeqBytes
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- `internal/cpu.X86.HasAVX2`, the byte `indexbytebody`'s `CMPB …HasAVX2(SB), $1` (offset `0xb6`)
reads. -/
def hasAVX2 : Nat := ripTarget Extracted.program (segAddr Extracted.program "indexbytebody" + 0xb6)

/-- The index of the first of the `n` bytes at `p` that equals `c`, or `-1` (as on arm64,
`examples/proofs/A64IndexByte.lean`). -/
def indexOf (m : Memory) (p c : Nat) : Nat → Int
  | 0 => -1
  | n + 1 =>
    if m.readLE p 1 = c then 0
    else
      let r := indexOf m (p + 1) c n
      if r < 0 then -1 else r + 1

/-- `MOVB c, AL` into a register holding `p`, read back as a byte. -/
theorem lowbyte (p c : BitVec 64) :
    BitVec.toNat (p &&& 18446744073709551360#64 ||| BitVec.setWidth 64 (BitVec.ofNat 8 (c.toNat % 256))) % 256 =
      c.toNat % 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.or_mod_two_pow, Nat.and_mod_two_pow]
  rw [show (18446744073709551360 : Nat) % 2 ^ 64 % 2 ^ 8 = 0 by decide, Nat.and_zero, Nat.zero_or]
  simp only [BitVec.toNat_ofNat]
  omega

theorem cmpeq_msb_mod (k a b : Nat) (hk : k ≤ 32) :
    msbBytes k (cmpeqBytes k a b) % 4294967296 = msbBytes k (cmpeqBytes k a b) :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (msbBytes_lt k _) (Nat.pow_le_pow_right (by decide) hk))

theorem cmpeq_msb_mod32 (a b : Nat) :
    msbBytes 32 (cmpeqBytes 32 a b) % 4294967296 = msbBytes 32 (cmpeqBytes 32 a b) :=
  cmpeq_msb_mod 32 a b (Nat.le_refl _)

theorem cmpeq_msb_zero (k a b : Nat) :
    (msbBytes k (cmpeqBytes k a b) = 0) = (cmpeqBytes k a b = 0) := by
  apply propext
  induction k generalizing a b with
  | zero => simp [msbBytes, cmpeqBytes]
  | succ k ih =>
    unfold msbBytes cmpeqBytes
    have hl := cmpeqBytes_lt k (a / 256) (b / 256)
    rw [show ((if a % 256 = b % 256 then 255 else 0) + 256 * cmpeqBytes k (a / 256) (b / 256)) % 256 =
        (if a % 256 = b % 256 then 255 else 0) by split <;> omega,
      show ((if a % 256 = b % 256 then 255 else 0) + 256 * cmpeqBytes k (a / 256) (b / 256)) / 256 =
        cmpeqBytes k (a / 256) (b / 256) by split <;> omega]
    have := ih (a / 256) (b / 256)
    split <;> omega

/-- The first matching byte: `BSF` of the `PMOVMSKB` of `PCMPEQB` with a broadcast byte. -/
theorem ctz_msb_cmpeq (k a c : Nat) (hc : c < 256) :
    ctzNat k (msbBytes k (cmpeqBytes k a (replBytes k c))) =
      Janus.Tactic.firstTrue (fun i => decide (a / 256 ^ i % 256 = c)) k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    unfold msbBytes cmpeqBytes replBytes ctzNat
    have hl := cmpeqBytes_lt k (a / 256) ((c + 256 * replBytes k c) / 256)
    rw [show (c + 256 * replBytes k c) % 256 = c by omega,
      show (c + 256 * replBytes k c) / 256 = replBytes k c by omega]
    rw [show ((if a % 256 = c then 255 else 0) + 256 * cmpeqBytes k (a / 256) (replBytes k c)) % 256 =
        (if a % 256 = c then 255 else 0) by split <;> omega,
      show ((if a % 256 = c then 255 else 0) + 256 * cmpeqBytes k (a / 256) (replBytes k c)) / 256 =
        cmpeqBytes k (a / 256) (replBytes k c) by split <;> omega]
    simp only [Janus.Tactic.firstTrue, Nat.pow_zero, Nat.div_one]
    by_cases h : a % 256 = c
    · simp [h]
    · simp only [h, ite_false, decide_false, Bool.false_eq_true]
      rw [show (0 / 128 + 2 * msbBytes k (cmpeqBytes k (a / 256) (replBytes k c))) % 2 = 0 by omega,
        show (0 / 128 + 2 * msbBytes k (cmpeqBytes k (a / 256) (replBytes k c))) / 2 =
          msbBytes k (cmpeqBytes k (a / 256) (replBytes k c)) by omega, ih]
      have hf : (fun i => decide (a / 256 ^ (i + 1) % 256 = c)) =
          (fun i => decide (a / 256 / 256 ^ i % 256 = c)) := by
        funext i; rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
          Nat.div_div_eq_div_mul, Nat.mul_comm]
      simp only [Nat.zero_ne_one, ite_false, hf]
      omega

open Janus.Tactic in
theorem ft_lt_iff (f : Nat → Bool) (n : Nat) : firstTrue f n < n ↔ ∃ i < n, f i = true := by
  induction n generalizing f with
  | zero => simp [firstTrue]
  | succ n ih =>
    simp only [firstTrue]
    cases h0 : f 0
    · simp only [Bool.false_eq_true, ite_false]
      rw [show (firstTrue (fun i => f (i + 1)) n + 1 < n + 1) ↔ firstTrue (fun i => f (i + 1)) n < n by omega, ih]
      constructor
      · rintro ⟨i, hi, h⟩; exact ⟨i + 1, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => simp [h0] at h
        | succ i => exact ⟨i, by omega, h⟩
    · simp only [ite_true]; exact ⟨fun _ => ⟨0, by omega, h0⟩, fun _ => by omega⟩

open Janus.Tactic in
theorem ft_le (f : Nat → Bool) (n : Nat) : firstTrue f n ≤ n := by
  induction n generalizing f with
  | zero => simp [firstTrue]
  | succ n ih =>
    simp only [firstTrue]; split
    · omega
    · exact Nat.succ_le_succ (ih _)

open Janus.Tactic in
theorem ft_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : firstTrue f n = firstTrue g n := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [firstTrue, h 0 (by omega)]
    rw [ih (fun i hi => h (i + 1) (by omega))]

open Janus.Tactic in
theorem indexOf_ft (m : Memory) (p c n : Nat) :
    indexOf m p c n = if ∃ i < n, decide (m.readLE (p + i) 1 = c) = true
      then (firstTrue (fun i => decide (m.readLE (p + i) 1 = c)) n : Int) else -1 := by
  induction n generalizing p with
  | zero => simp [indexOf]
  | succ n ih =>
    simp only [indexOf, firstTrue, Nat.add_zero]
    by_cases h0 : m.readLE p 1 = c
    · have hx : ∃ i < n + 1, decide (m.readLE (p + i) 1 = c) = true := ⟨0, by omega, by simp [h0]⟩
      simp only [h0, ite_true, decide_true, hx]; rfl
    · rw [ih (p + 1)]
      have e : (∃ i < n + 1, decide (m.readLE (p + i) 1 = c) = true) ↔
          ∃ i < n, decide (m.readLE (p + 1 + i) 1 = c) = true := by
        constructor
        · rintro ⟨i, hi, h⟩
          cases i with
          | zero => rw [Nat.add_zero] at h; exact absurd (of_decide_eq_true h) h0
          | succ i => exact ⟨i, by omega, by rw [show p + 1 + i = p + (i + 1) by omega]; exact h⟩
        · rintro ⟨i, hi, h⟩; exact ⟨i + 1, by omega, by rw [show p + (i + 1) = p + 1 + i by omega]; exact h⟩
      have hf : (fun i => decide (m.readLE (p + (i + 1)) 1 = c)) = (fun i => decide (m.readLE (p + 1 + i) 1 = c)) := by
        funext i; rw [show p + (i + 1) = p + 1 + i by omega]
      simp only [h0, decide_false, Bool.false_eq_true, ite_false, e, hf]
      by_cases hx : ∃ i < n, decide (m.readLE (p + 1 + i) 1 = c) = true
      · simp only [hx, ite_true]
        simp only [show ¬ ((firstTrue (fun i => decide (m.readLE (p + 1 + i) 1 = c)) n : Int) < 0) by omega,
          ite_false]
        push_cast; rfl
      · simp only [hx, ite_false]; rfl

theorem byte_eq (m : Memory) (q i : Nat) (h : i < 32) : m.readLE q 32 / 256 ^ i % 256 = m.readLE (q + i) 1 := by
  rw [Janus.Arm64.Memory.readLE_div _ _ _ _ (by omega)]
  obtain ⟨j, hj⟩ : ∃ j, 32 - i = j + 1 := ⟨31 - i, by omega⟩
  rw [hj, Janus.Arm64.Memory.readLE_succ, Janus.Arm64.Memory.readLE_one]
  have := (m.bytes (q + i)).isLt
  omega

theorem cmpeq_zero_iff (k a c : Nat) (hc : c < 256) :
    cmpeqBytes k a (replBytes k c) = 0 ↔ ∀ i < k, a / 256 ^ i % 256 ≠ c := by
  induction k generalizing a with
  | zero => simp [cmpeqBytes]
  | succ k ih =>
    unfold cmpeqBytes replBytes
    rw [show (c + 256 * replBytes k c) % 256 = c by omega,
      show (c + 256 * replBytes k c) / 256 = replBytes k c by omega]
    constructor
    · intro h i hi
      have h1 : a % 256 ≠ c := by intro he; simp [he] at h
      have h2 : cmpeqBytes k (a / 256) (replBytes k c) = 0 := by split at h <;> omega
      cases i with
      | zero => simpa using h1
      | succ i =>
        have := (ih (a / 256)).1 h2 i (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    · intro h
      have h1 : a % 256 ≠ c := by simpa using h 0 (by omega)
      have h2 := (ih (a / 256)).2 (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at this)
      simp [h1, h2]

theorem replBytes_lt (k b : Nat) (hb : b < 256) : replBytes k b < 256 ^ k := by
  induction k with
  | zero => simp [replBytes]
  | succ k ih => unfold replBytes; rw [Nat.pow_succ]; omega

open Janus.Tactic in
/-- The first match among 32 bytes at `q`, from the `PCMPEQB`/`PMOVMSKB`/`BSF` of a chunk. -/
theorem chunk_ft (m : Memory) (q c : Nat) (hc : c < 256) :
    ctzNat 32 (msbBytes 32 (cmpeqBytes 32 (m.readLE q 32) (replBytes 32 c))) =
      firstTrue (fun i => decide (m.readLE (q + i) 1 = c)) 32 := by
  rw [ctz_msb_cmpeq _ _ _ hc]
  exact ft_congr fun i hi => by rw [byte_eq m q i hi]

theorem chunk_none (m : Memory) (q c : Nat) (hc : c < 256) :
    cmpeqBytes 32 (m.readLE q 32) (replBytes 32 c) = 0 ↔ ∀ i < 32, m.readLE (q + i) 1 ≠ c := by
  rw [cmpeq_zero_iff _ _ _ hc]
  exact ⟨fun h i hi => by rw [← byte_eq m q i hi]; exact h i hi,
    fun h i hi => by rw [byte_eq m q i hi]; exact h i hi⟩

open Janus.Tactic in
theorem index_split (m : Memory) (p c : Nat) (hc : c < 256) :
    indexOf m p c 64 =
      if cmpeqBytes 32 (m.readLE p 32) (replBytes 32 c) = 0 then
        (if cmpeqBytes 32 (m.readLE (p + 32) 32) (replBytes 32 c) = 0 then -1
         else ((32 + ctzNat 32 (msbBytes 32 (cmpeqBytes 32 (m.readLE (p + 32) 32) (replBytes 32 c))) : Nat) : Int))
      else ((ctzNat 32 (msbBytes 32 (cmpeqBytes 32 (m.readLE p 32) (replBytes 32 c))) : Nat) : Int) := by
  rw [indexOf_ft, show (64 : Nat) = 32 + 32 from rfl, firstTrue_add, chunk_ft _ _ _ hc, chunk_ft _ _ _ hc]
  have hf : (fun i => (fun i => decide (m.readLE (p + i) 1 = c)) (32 + i)) =
      (fun i => decide (m.readLE (p + 32 + i) 1 = c)) := by
    funext i; simp only [Nat.add_assoc]
  rw [hf]
  by_cases h0 : cmpeqBytes 32 (m.readLE p 32) (replBytes 32 c) = 0
  · have n0 := (chunk_none m p c hc).1 h0
    have hn0 : ¬ ∃ i < 32, decide (m.readLE (p + i) 1 = c) = true := fun ⟨i, hi, h⟩ => n0 i hi (of_decide_eq_true h)
    simp only [h0, ite_true, hn0, ite_false]
    by_cases h1 : cmpeqBytes 32 (m.readLE (p + 32) 32) (replBytes 32 c) = 0
    · have n1 := (chunk_none m (p + 32) c hc).1 h1
      have hn : ¬ ∃ i < 32 + 32, decide (m.readLE (p + i) 1 = c) = true := by
        rintro ⟨i, hi, h⟩
        by_cases hi' : i < 32
        · exact n0 i hi' (of_decide_eq_true h)
        · exact n1 (i - 32) (by omega) (by rw [show p + 32 + (i - 32) = p + i by omega]; exact of_decide_eq_true h)
      simp only [h1, ite_true, hn, ite_false]
    · have : ∃ i < 32, m.readLE (p + 32 + i) 1 = c := by
        apply Classical.byContradiction; intro hne
        exact h1 ((chunk_none m (p + 32) c hc).2 fun i hi he => hne ⟨i, hi, he⟩)
      obtain ⟨i, hi, he⟩ := this
      have hx : ∃ j < 32 + 32, decide (m.readLE (p + j) 1 = c) = true :=
        ⟨32 + i, by omega, by rw [← Nat.add_assoc]; simp [he]⟩
      simp only [h1, ite_false, hx, ite_true]
  · have : ∃ i < 32, m.readLE (p + i) 1 = c := by
      apply Classical.byContradiction; intro hne
      exact h0 ((chunk_none m p c hc).2 fun i hi he => hne ⟨i, hi, he⟩)
    obtain ⟨i, hi, he⟩ := this
    have hx0 : ∃ j < 32, decide (m.readLE (p + j) 1 = c) = true := ⟨i, hi, by simp [he]⟩
    have hx : ∃ j < 32 + 32, decide (m.readLE (p + j) 1 = c) = true := ⟨i, by omega, by simp [he]⟩
    simp only [h0, ite_false, hx, hx0, ite_true]

theorem fin_none : (18446744073709551615#64 : BitVec 64) = BitVec.ofInt 64 (-1) := by decide

theorem fin_one (t p : Nat) (ht : t ≤ 32) (hp : p < 2 ^ 64) :
    BitVec.ofNat 64 (t % 4294967296 + (18446744073709551616 - p + (p + 32)) % 18446744073709551616) =
      BitVec.ofInt 64 ((32 + t : Nat) : Int) := by
  rw [BitVec.ofInt_natCast]; congr 1; omega

theorem fin_zero (t : Nat) (ht : t ≤ 32) :
    BitVec.ofNat 64 (t % 4294967296) = BitVec.ofInt 64 ((t : Nat) : Int) := by
  rw [BitVec.ofInt_natCast]; congr 1; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (p n cap : BitVec 64) (c : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p, n, cap, c]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 56 16 ∧ TlsG s ∧ n.toNat = 64 ∧
        Buffer s p 64 false ∧
        (p.toNat + 64 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat + 16 ≤ p.toNat) ∧
        (s.fsBase.toNat - 8 + 8 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat + 16 ≤ s.fsBase.toNat - 8) ∧
        s.mem.accessible hasAVX2 1 false = true ∧ s.mem.readLE hasAVX2 1 = 1 ∧
        (hasAVX2 + 1 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat + 16 ≤ hasAVX2))
      (fun s s' => s'.regs 0 = BitVec.ofInt 64 (indexOf s.mem p.toNat (c.toNat % 256) 64)) := by
  intro ret hret s hs ⟨hg, ⟨hle, hnw, hacc⟩, htls, hn, ⟨hp', hp⟩, hd, hdt, hav, hav1, hdav⟩
  have hn' : n = 64#64 := BitVec.eq_of_toNat_eq hn
  subst hn'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  have htr := htls.readable
  have htg := htls.g
  have htb := htls.base
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hacc hle hnw hgl hgb hnw2 hgr hd hdt hdav
  simp only [hasAVX2, reduceRipTarget] at hav hav1 hdav
  janus64_run [hav1, Nat.and_self, cmpeq_msb_mod32, cmpeq_msb_zero, lowbyte p c]
  all_goals
    refine ⟨rfl, ?_⟩
    have hc' : c.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [index_split _ _ _ hc']
    simp only [Nat.mod_eq_of_lt (replBytes_lt 32 _ hc')] at *
    simp only [chunk_ft _ _ _ hc']
    have ht0 := ft_le (fun i => decide (s.mem.readLE (p.toNat + i) 1 = c.toNat % 256)) 32
    have ht1 := ft_le (fun i => decide (s.mem.readLE (p.toNat + 32 + i) 1 = c.toNat % 256)) 32
    generalize Janus.Tactic.firstTrue (fun i => decide (s.mem.readLE (p.toNat + i) 1 = c.toNat % 256)) 32 = t0
      at ht0 ⊢
    generalize Janus.Tactic.firstTrue (fun i => decide (s.mem.readLE (p.toNat + 32 + i) 1 = c.toNat % 256)) 32 = t1
      at ht1 ⊢
  · rename_i h0
    rw [if_pos h0, if_pos hbr]
    exact fin_none
  · rename_i h0
    rw [if_pos h0, if_neg hbr]
    exact fin_one _ _ ht1 p.isLt
  · rw [if_neg hbr]
    exact fin_zero _ ht0

end Proof
