import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-! ## Addresses of the runtime globals, recomputed from the extracted `ADRP` pairs -/

def mwd (i : Nat) : Nat := segWord Extracted.program "runtime.mallocgc" i
def nwd (i : Nat) : Nat := segWord Extracted.program "runtime.mallocgcSmallNoscan" i
def nBase : Nat := segAddr Extracted.program "runtime.mallocgcSmallNoscan"

/-- `runtime.debug.malloc` (byte). -/
def debugMalloc : Nat := adrpLdTarget (Extracted.entry + 0x28) (mwd 10) (mwd 11) 0
/-- `runtime.gcBlackenEnabled` (32-bit). -/
def gcBlackenEnabled : Nat := adrpLdTarget (Extracted.entry + 0x48) (mwd 18) (mwd 19) 2
/-- `internal/runtime/gc.SizeToSizeClass8` (bytes). -/
def sizeToClass8 : Nat := adrpLdTarget (nBase + 0x5c) (nwd 23) (nwd 24) 0
/-- `internal/runtime/gc.SizeClassToSize` (16-bit entries). -/
def classToSize : Nat := adrpLdTarget (nBase + 0x9c) (nwd 39) (nwd 40) 0
/-- `runtime.writeBarrier.enabled` (byte). -/
def writeBarrier : Nat := adrpLdTarget (nBase + 0x1e0) (nwd 120) (nwd 121) 0
/-- `runtime.MemProfileRate` (64-bit). -/
def memProfileRate : Nat := adrpLdTarget (nBase + 0x228) (nwd 138) (nwd 139) 3

/-! ## The runtime state a call reads (Go 1.26 linux/arm64 layout) -/

def rd (s : State) (a n : Nat) : Nat := s.mem.readLE a n
def gOf (s : State) : Nat := (s.regs 28).toNat
def mOf (s : State) : Nat := rd s (gOf s + 48) 8
def pOf (s : State) : Nat := rd s (mOf s + 208) 8
def cOf (s : State) : Nat := rd s (pOf s + 56) 8
def scOf (s : State) (size : Nat) : Nat := rd s (sizeToClass8 + (size + 7) / 8) 1
def csOf (s : State) (size : Nat) : Nat := rd s (classToSize + 2 * scOf s size) 2
def spanOf (s : State) (size : Nat) : Nat := rd s (cOf s + 48 + 8 * (2 * scOf s size + 1)) 8

def cacheOf (s : State) (size : Nat) : Nat := rd s (spanOf s size + 56) 8
def fidxOf (s : State) (size : Nat) : Nat := rd s (spanOf s size + 48) 2
def nelemsOf (s : State) (size : Nat) : Nat := rd s (spanOf s size + 50) 2
def baseOf (s : State) (size : Nat) : Nat := rd s (spanOf s size + 24) 8
def eszOf (s : State) (size : Nat) : Nat := rd s (spanOf s size + 104) 8
/-- The free slot `nextFreeFast` takes: `freeindex + ctz(allocCache)`. -/
def resOf (s : State) (size : Nat) : Nat := fidxOf s size + ctzN 64 (cacheOf s size)
/-- Its address: `base + res·elemsize`. -/
def slotOf (s : State) (size : Nat) : Nat := (baseOf s size + resOf s size * eszOf s size) % 2 ^ 64

/-- The extent of the runtime globals the fast path reads (in the binary's data sections). -/
def globLo : Nat := min (min (min debugMalloc gcBlackenEnabled) (min sizeToClass8 classToSize))
  (min writeBarrier memProfileRate)
def globHi : Nat := max (max (max (debugMalloc + 1) (gcBlackenEnabled + 4))
  (max (sizeToClass8 + 129) (classToSize + 136))) (max (writeBarrier + 1) (memProfileRate + 8))

/-- `ptr` with `n` accessible bytes below `2^48`. -/
def Obj (s : State) (a n : Nat) (w : Bool) : Prop := s.mem.accessible a n w = true ∧ a + n ≤ 2 ^ 48

/-- **The runtime state of the fast path** (`MCacheOK`): the current `g`, `m`, `p`, the P's
`mcache`, the span cached for the size class of `size` (noscan), and the globals are readable
(the fields written: writable) and pairwise separate, together with the stack window and the
slot; the size class is valid, the span has a free slot in its `allocCache` that
`nextFreeFast` can take (not the last of a 64-slot block unless it is the span's last), the slot
is zero (`span.needzero = 0`: the runtime's invariant that such a span's free slots are zero),
`elemsize` is the class size, and the slow paths are off: no malloc debugging, no GC assist,
write barrier off, no heap profiling sample due. -/
def MCacheOK (s : State) (size : Nat) : Prop :=
  Obj s (gOf s + 16) 162 true ∧ Obj s (mOf s + 208) 60 true ∧ Obj s (pOf s + 56) 8 false ∧
  pOf s ≠ 0 ∧ Obj s (cOf s) 1136 true ∧ Obj s (spanOf s size + 24) 88 true ∧
  Obj s globLo (globHi - globLo) false ∧ Obj s (slotOf s size) (csOf s size) true ∧
  Spread [(s.sp.toNat - 152, 184), (gOf s + 16, 162), (mOf s + 208, 60), (pOf s + 56, 8),
    (cOf s, 1136), (spanOf s size + 24, 88), (globLo, globHi - globLo), (slotOf s size, csOf s size)] ∧
  scOf s size < 68 ∧ cacheOf s size ≠ 0 ∧ resOf s size < nelemsOf s size ∧
  ((resOf s size + 1) % 64 ≠ 0 ∨ resOf s size + 1 = nelemsOf s size) ∧
  rd s (spanOf s size + 100) 1 = 0 ∧ ZeroBytes s.mem (slotOf s size) (csOf s size) ∧ eszOf s size = csOf s size ∧
  rd s debugMalloc 1 % 2 = 0 ∧ rd s gcBlackenEnabled 4 = 0 ∧ rd s writeBarrier 1 % 2 = 0 ∧
  (rd s (cOf s) 8 + 2 ^ 64 - csOf s size) % 2 ^ 64 < 2 ^ 63 ∧ rd s memProfileRate 8 = rd s (cOf s + 8) 8

theorem ctzN_le (n x : Nat) : ctzN n x ≤ n := by
  induction n generalizing x with
  | zero => simp [ctzN]
  | succ n ih =>
    simp only [ctzN]
    split
    · omega
    · have := ih (x / 2); omega

theorem ctzN_lt (n x : Nat) (h : x % 2 ^ n ≠ 0) : ctzN n x < n := by
  induction n generalizing x with
  | zero => exact absurd (Nat.mod_one x) (by simpa using h)
  | succ n ih =>
    simp only [ctzN]
    split
    · omega
    · rename_i h1
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      have : 2 * y / 2 % 2 ^ n ≠ 0 := by
        rw [Nat.mul_div_cancel_left _ (by decide)]
        intro h2; apply h
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_mod_mul_left, h2]
      have := ih (2 * y / 2) this
      omega

theorem toNat_ofNat_ctzN (x : Nat) : (BitVec.ofNat 64 (ctzN 64 x)).toNat = ctzN 64 x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ctzN_le 64 x; omega)]

theorem toInt_ofNat_ctzN (x : Nat) : (BitVec.ofNat 64 (ctzN 64 x)).toInt = (ctzN 64 x : Int) := by
  have := ctzN_le 64 x
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [toNat_ofNat_ctzN]; omega), toNat_ofNat_ctzN]

theorem rbit64_mod (x : Nat) : rbitNat 64 x % 18446744073709551616 = rbitNat 64 x :=
  Nat.mod_eq_of_lt (rbitNat_lt 64 x)

theorem ofNat_and_65535 (x : Nat) : BitVec.ofNat 64 x &&& 65535#64 = BitVec.ofNat 64 (x % 65536) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (65535 : Nat) % 2 ^ 64 = 2 ^ 16 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 64), Nat.mod_eq_of_lt (by omega : x % 65536 < 2 ^ 64)]

theorem readLE8_mod (m : Memory) (a : Nat) : m.readLE a 8 % 18446744073709551616 = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 8)

theorem rotateRight_zero' (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem or_one_two_mul (x : Nat) : 1 ||| x * 2 = x * 2 + 1 := by
  have := Nat.shiftLeft_add_eq_or_of_lt (i := 1) (b := 1) (by decide) x
  rw [Nat.shiftLeft_eq, Nat.pow_one] at this
  rw [Nat.or_comm, ← this]

/-- The span class `spc = sizeclass << 1 | noscan` as the executor computes it. -/
theorem spanClass_toNat (x : Nat) (h : x < 2 ^ 63) :
    ((1#64 ||| BitVec.ofNat 64 (x * 2)).rotateRight 0).toNat = x * 2 + 1 := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.zero_mod, BitVec.ushiftRight_zero,
    Nat.sub_zero, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mul_mod_left, Nat.or_zero]
  rw [Nat.mod_eq_of_lt (show x * 2 < 2 ^ 64 by omega), or_one_two_mul]

/-- `ubfx` of the span class (below 256). -/
theorem spanClass_mod (x : Nat) (h : x < 68) : (x * 2 + 1) % 256 = 2 * x + 1 := by omega
theorem spanClass_mod' (x : Nat) (h : x < 68) : (2 * x + 1) % 256 = 2 * x + 1 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem correctness (sz typ nz : BitVec 64) :
    Ensures Extracted.program Extracted.entry [sz, typ, nz]
      (fun s => GuardOK s 144 ∧ StackOK s 152 32 ∧ 16 ≤ sz.toNat ∧ sz.toNat ≤ 1016 ∧
        typ.toNat = 0 ∧ MCacheOK s sz.toNat)
      (fun _ _ => True) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hs1, hs2, ht, hok⟩
  janus_intro hs
  janus_eval_nat h_dm : debugMalloc
  janus_eval_nat h_gb : gcBlackenEnabled
  janus_eval_nat h_t8 : sizeToClass8
  janus_eval_nat h_ts : classToSize
  janus_eval_nat h_wb : writeBarrier
  janus_eval_nat h_mp : memProfileRate
  janus_eval_nat h_glo : globLo
  janus_eval_nat h_ghi : globHi
  have hfb : fidxOf s sz.toNat < 2 ^ 16 := Memory.readLE_lt _ _ 2
  have hnb : nelemsOf s sz.toNat < 2 ^ 16 := Memory.readLE_lt _ _ 2
  have hcb : cacheOf s sz.toNat < 2 ^ 64 := Memory.readLE_lt _ _ 8
  have hcsb : csOf s sz.toNat < 2 ^ 16 := Memory.readLE_lt _ _ 2
  obtain ⟨⟨hG, hG'⟩, ⟨hM, hM'⟩, ⟨hP, hP'⟩, hp0, ⟨hC, hC'⟩, ⟨hS, hS'⟩, ⟨hGl, hGl'⟩, ⟨hSl, hSl'⟩,
    hsp, hsc, hca, hres, hblk, hnz, hzero, hesz, hdm, hgb, hwb, hns, hmpr⟩ := hok
  simp only [spread_cons, spread_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and] at hsp
  obtain ⟨⟨a01, a02, a03, a04, a05, a06, a07⟩, ⟨a12, a13, a14, a15, a16, a17⟩, ⟨a23, a24, a25, a26, a27⟩,
    ⟨a34, a35, a36, a37⟩, ⟨a45, a46, a47⟩, ⟨a56, a57⟩, a67⟩ := hsp
  simp only [rd, h_dm, h_gb, h_t8, h_ts, h_wb, h_mp, h_glo, h_ghi, gOf, mOf, pOf, cOf, scOf, csOf,
    spanOf, cacheOf, fidxOf, nelemsOf, baseOf, eszOf, resOf, slotOf] at *
  have hsc8 := Memory.readLE_lt s.mem (1444608 + (sz.toNat + 7) / 8) 1
  have hctz := ctzN_lt 64 _ (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ 8)]; exact hca)
  set_option trace.janus true in
  janus_run [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, spanClass_toNat, spanClass_mod, spanClass_mod',
    clzNat_rbitNat, toNat_ofNat_ctzN, rotateRight_zero', or_one_two_mul,
    toInt_ofNat_ctzN, readLE8_mod, rbit64_mod,
    BitVec.setWidth_ofNat_of_le, BitVec.ofNat_add_ofNat, ofNat_and_65535,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals sorry

end Proof
