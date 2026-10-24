import Extracted

/-!
# `runtime.mallocgc`: the small pointer-free fast path, from the machine code

**Guarantee.** For every request of `sz` bytes with `16 ≤ sz ≤ 1016`, `typ = nil` (pointer-free)
and any `needzero`, and every Go call state of `runtime.mallocgc` (this binary, Go 1.26.0
linux/arm64) in which both stack-growth prologues fall through, the stack window
`[SP-152, SP+32)` is writable and `MCacheOK` holds — the current `g`, its `m`, the `m`'s `p`, the
`p`'s `mcache` and the span the mcache caches for the request's (noscan) size class are readable
(the fields written: writable) and pairwise separate (`Spread`), together with the runtime
globals read and the slot below; the size class is valid; the span's `allocCache` has a bit set
whose slot `freeindex + ctz(allocCache)` is below `nelems` (and is not the last of a 64-slot
block unless it is the span's last: `nextFreeFast`'s refill condition); that slot is non-nil and
zero (`span.needzero = 0`), `elemsize` is the class size; malloc debugging, GC assist and the
write barrier are off and no heap-profile sample is due — the call **returns** (no fault, no
panic, never reaching a slow path), obeys the ABI, and (`FastPost`):

* `X0` is the slot `span.base + elemsize · (freeindex + ctz(allocCache))`, and its `csize` bytes
  are still zero;
* exactly these fields change: `allocCache` (shifted past the slot), `freeindex` and
  `freeIndexForScan` (the slot + 1), `allocCount` (+1), the mcache's `nextSample` (− `csize`),
  `m.mallocing` (back to 0), `m.locks` (back to its value), `g.stackguard0` (re-armed if a
  preemption is pending and `m.locks` drops to 0), and the two stack frames;

and, with Go's size-class tables in memory (`TablesOK`), a page-aligned span base and the slot
inside the runtime-owned ranges `rt`, the result is a `Fresh` object of `blockSize sz true` bytes,
zeroed: **exactly what the contract `MallocgcContract` promises** for such a request
(`fresh_of_fastPost`).

**What is executed and what is not.** `runtime.mallocgc` and `runtime.mallocgcSmallNoscan` with
the inlined `acquirem`, `getMCache`, `nextFreeFast` and `releasem` (281 instructions; 433 steps
over the six paths: `needzero` set or not, `m.locks` and pending preemption) are executed from the
binary. Every slow path is a contract (`janus extract --contract`, see
`scripts/example-contracts.sh`) that `MCacheOK` makes unreachable, so the statement assumes
nothing about them: `mallocgcTiny`, `mallocgcSmallScan*`, `mallocgcLarge`, `(*mcache).nextFree`
(refill from `mcentral`/`mheap`), `memclrNoHeapPointers`, `gcmarknewobject`, `profilealloc`,
`gcTrigger.test`/`gcStart`, `deductAssistCredit`, `pre/postMallocgcDebug`, `throw`. The addresses
of the runtime globals are recomputed from the extracted `ADRP` pairs; the struct field offsets
are Go 1.26's linux/arm64 layout as the code uses them.
-/

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
def resOf (s : State) (size : Nat) : Nat := ctzN 64 (cacheOf s size) + fidxOf s size
/-- Its address: `base + res·elemsize`. -/
def slotOf (s : State) (size : Nat) : Nat :=
  (baseOf s size + eszOf s size * resOf s size % 2 ^ 64) % 2 ^ 64

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
  slotOf s size ≠ 0 ∧ rd s (spanOf s size + 100) 1 = 0 ∧ ZeroBytes s.mem (slotOf s size) (csOf s size) ∧ eszOf s size = csOf s size ∧
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

theorem and63_eq_zero (x : Nat) : (BitVec.ofNat 32 x &&& 63#32 = 0#32) = (x % 64 = 0) := by
  apply propext
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 6 ∣ 2 ^ 32)]

theorem mod256_of_lt (x : Nat) (h : x < 256) : x % 256 = x := Nat.mod_eq_of_lt h

theorem mod65536_of_lt (x : Nat) (h : x < 65536) : x % 65536 = x := Nat.mod_eq_of_lt h

theorem sign_sub (a b : Nat) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).getLsbD 63 == true) =
      decide (2 ^ 63 ≤ (a % 2 ^ 64 + (2 ^ 64 - b % 2 ^ 64)) % 2 ^ 64) := by
  rw [BitVec.getLsbD, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have h1 := Nat.mod_lt (2 ^ 64 - b % 2 ^ 64 + a % 2 ^ 64) (show 0 < 2 ^ 64 by decide)
  simp only [beq_true]
  rw [Nat.add_comm (a % 2 ^ 64)]
  generalize (2 ^ 64 - b % 2 ^ 64 + a % 2 ^ 64) % 2 ^ 64 = y at *
  by_cases h : 2 ^ 63 ≤ y
  · simp [h]; omega
  · simp [h]; omega

theorem readLE2_mod (m : Memory) (a : Nat) : m.readLE a 2 % 18446744073709551616 = m.readLE a 2 :=
  Nat.mod_eq_of_lt (Nat.lt_trans (Memory.readLE_lt m a 2) (by decide))

theorem readLE8_mod (m : Memory) (a : Nat) : m.readLE a 8 % 18446744073709551616 = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 8)

theorem rotateRight_zero' (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem ZeroBytes.writeLE_of {m : Memory} {a n b k v : Nat} (h : ZeroBytes m a n)
    (hd : b + k ≤ a ∨ a + n ≤ b) : ZeroBytes (m.writeLE b k v) a n := by
  intro i hi
  rw [Memory.bytes_writeLE_outside _ (by omega)]
  exact h i hi

theorem ZeroBytes.congr_addr {m : Memory} {a a' n : Nat} (h : ZeroBytes m a n) (he : a = a') :
    ZeroBytes m a' n := he ▸ h

theorem cache_shift (x c : Nat) (hc : c < 64) (hx : x < 2 ^ 64) :
    (if c + 1 < 64 then BitVec.ofNat 64 x >>> ((c + 1) % 64) else 0#64).toNat = x / 2 ^ (c + 1) := by
  split
  · rename_i h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt h,
      Nat.shiftRight_eq_div_pow]
  · rw [show c + 1 = 64 by omega, Nat.div_eq_of_lt hx]; rfl

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

/-- What the fast path does: it returns the slot `nextFreeFast` takes, still zero, and changes
exactly the span's `allocCache`, `freeindex`, `freeIndexForScan` and `allocCount`, the mcache's
`nextSample`, `m.mallocing` (back to 0) and `m.locks` (back to its value), possibly
`g.stackguard0` (`releasem` re-arms a pending preemption), and its own stack frames. -/
def FastPost (s s' : State) (size : Nat) : Prop :=
  (s'.regs 0).toNat = slotOf s size ∧ ZeroBytes s'.mem (slotOf s size) (csOf s size) ∧
  s'.mem.readLE (spanOf s size + 56) 8 = cacheOf s size / 2 ^ (ctzN 64 (cacheOf s size) + 1) ∧
  s'.mem.readLE (spanOf s size + 48) 2 = resOf s size + 1 ∧
  s'.mem.readLE (spanOf s size + 52) 2 = resOf s size + 1 ∧
  s'.mem.readLE (spanOf s size + 96) 2 = (rd s (spanOf s size + 96) 2 + 1) % 65536 ∧
  s'.mem.readLE (cOf s) 8 = (rd s (cOf s) 8 + 2 ^ 64 - csOf s size) % 2 ^ 64 ∧
  s'.mem.readLE (mOf s + 240) 4 = 0 ∧ s'.mem.readLE (mOf s + 264) 4 = rd s (mOf s + 264) 4 ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 152, s.sp.toNat + 32),
    (spanOf s size + 48, spanOf s size + 54), (spanOf s size + 56, spanOf s size + 64),
    (spanOf s size + 96, spanOf s size + 98), (cOf s, cOf s + 8),
    (mOf s + 240, mOf s + 244), (mOf s + 264, mOf s + 268), (gOf s + 16, gOf s + 24)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 30000000 in
theorem fast_path (sz typ nz : BitVec 64) :
    Ensures Extracted.program Extracted.entry [sz, typ, nz]
      (fun s => GuardOK s 144 ∧ StackOK s 152 32 ∧ 16 ≤ sz.toNat ∧ sz.toNat ≤ 1016 ∧
        typ.toNat = 0 ∧ MCacheOK s sz.toNat)
      (fun s s' => FastPost s s' sz.toNat) := by
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
    hsp, hsc, hca, hres, hblk, hs0, hnz, hzero, hesz, hdm, hgb, hwb, hns, hmpr⟩ := hok
  simp only [spread_cons, spread_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and] at hsp
  obtain ⟨⟨a01, a02, a03, a04, a05, a06, a07⟩, ⟨a12, a13, a14, a15, a16, a17⟩, ⟨a23, a24, a25, a26, a27⟩,
    ⟨a34, a35, a36, a37⟩, ⟨a45, a46, a47⟩, ⟨a56, a57⟩, a67⟩ := hsp
  simp only [rd, h_dm, h_gb, h_t8, h_ts, h_wb, h_mp, h_glo, h_ghi, gOf, mOf, pOf, cOf, scOf, csOf,
    spanOf, cacheOf, fidxOf, nelemsOf, baseOf, eszOf, resOf, slotOf, FastPost] at *
  have hsc8 := Memory.readLE_lt s.mem (1444608 + (sz.toNat + 7) / 8) 1
  have hctz := ctzN_lt 64 _ (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ 8)]; exact hca)
  have hbab := Memory.readLE_lt s.mem (s.mem.readLE (s.mem.readLE (s.mem.readLE (s.mem.readLE
    (BitVec.toNat (s.regs 28) + 48) 8 + 208) 8 + 56) 8 + 48 + 8 * (2 * s.mem.readLE
    (1444608 + (sz.toNat + 7) / 8) 1 + 1)) 8 + 24) 8
  have hesb := Memory.readLE_lt s.mem (s.mem.readLE (s.mem.readLE (s.mem.readLE (s.mem.readLE
    (BitVec.toNat (s.regs 28) + 48) 8 + 208) 8 + 56) 8 + 48 + 8 * (2 * s.mem.readLE
    (1444608 + (sz.toNat + 7) / 8) 1 + 1)) 8 + 104) 8
  have hacb := Memory.readLE_lt s.mem (s.mem.readLE (s.mem.readLE (s.mem.readLE (s.mem.readLE
    (BitVec.toNat (s.regs 28) + 48) 8 + 208) 8 + 56) 8 + 48 + 8 * (2 * s.mem.readLE
    (1444608 + (sz.toNat + 7) / 8) 1 + 1)) 8 + 96) 2
  have hnsb := Memory.readLE_lt s.mem (s.mem.readLE (s.mem.readLE (s.mem.readLE
    (BitVec.toNat (s.regs 28) + 48) 8 + 208) 8 + 56) 8) 8
  have hlkb := Memory.readLE_lt s.mem (s.mem.readLE (BitVec.toNat (s.regs 28) + 48) 8 + 264) 4
  simp only [Nat.reducePow] at hbab hesb hacb hnsb hlkb hfb hnb hcb hcsb hsc8
  -- name the runtime state the code reads, to keep the symbolic state small (`h_rd…` are
  -- rewrite rules for the executor)
  generalize h_rdm : s.mem.readLE (BitVec.toNat (s.regs 28) + 48) 8 = mv at *
  generalize h_rdp : s.mem.readLE (mv + 208) 8 = pv at *
  generalize h_rdc : s.mem.readLE (pv + 56) 8 = cv at *
  generalize h_rdsc : s.mem.readLE (1444608 + (sz.toNat + 7) / 8) 1 = scv at *
  generalize h_rdcs : s.mem.readLE (1444768 + 2 * scv) 2 = csv at *
  generalize h_rdsp : s.mem.readLE (cv + 48 + 8 * (2 * scv + 1)) 8 = spv at *
  generalize h_rdca : s.mem.readLE (spv + 56) 8 = cachev at *
  generalize h_rdfi : s.mem.readLE (spv + 48) 2 = fidxv at *
  generalize h_rdne : s.mem.readLE (spv + 50) 2 = nelv at *
  generalize h_rdba : s.mem.readLE (spv + 24) 8 = basev at *
  generalize h_rdes : s.mem.readLE (spv + 104) 8 = eszv at *
  generalize h_rdac : s.mem.readLE (spv + 96) 2 = acv at *
  generalize h_rdns : s.mem.readLE cv 8 = nsv at *
  generalize h_rdlk : s.mem.readLE (mv + 264) 4 = lkv at *

  janus_run [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, spanClass_toNat, spanClass_mod, spanClass_mod',
    clzNat_rbitNat, toNat_ofNat_ctzN, rotateRight_zero', or_one_two_mul,
    toInt_ofNat_ctzN, readLE8_mod, rbit64_mod,
    BitVec.setWidth_ofNat_of_le, BitVec.ofNat_add_ofNat, ofNat_and_65535,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    BitVec.toNat_mul, mod65536_of_lt, mod256_of_lt, sign_sub, readLE2_mod, and63_eq_zero]
  all_goals (repeat' apply And.intro)
  all_goals first
    | omega
    | janus_frame
    | exact cache_shift _ _ hctz hcb
    | ((repeat' split) <;> omega)
    | ((repeat (refine ZeroBytes.writeLE_of ?_ (by first | omega | janus_apart)))
       exact ZeroBytes.congr_addr hzero (by omega))

/-- Go 1.26 `internal/runtime/gc.SizeToSizeClass8` (129 entries). -/
def goSizeToClass8 : List Nat := [0, 1, 2, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23, 24, 24, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32]
/-- Go 1.26 `internal/runtime/gc.SizeClassToSize` (68 entries). -/
def goClassToSize : List Nat := 0 :: sizeClasses

set_option maxRecDepth 100000 in
theorem tables_agree : ∀ n, n < 1017 → 16 ≤ n →
    goClassToSize.getD (goSizeToClass8.getD ((n + 7) / 8) 0) 0 = roundupsize n true ∧
    goSizeToClass8.getD ((n + 7) / 8) 0 < 68 ∧
    roundupsize n true % 8 = 0 ∧ (n % 16 = 0 → roundupsize n true % 16 = 0) ∧
    n ≤ roundupsize n true := by
  decide +kernel

/-- The size-class tables in memory are Go 1.26's (`SizeToSizeClass8`, `SizeClassToSize`). -/
def TablesOK (s : State) : Prop :=
  (∀ i, i < 129 → rd s (sizeToClass8 + i) 1 = goSizeToClass8.getD i 0) ∧
  (∀ j, j < 68 → rd s (classToSize + 2 * j) 2 = goClassToSize.getD j 0)

/-- With Go's tables, the slot's size is `roundupsize`. -/
theorem csOf_eq (s : State) (size : Nat) (ht : TablesOK s) (h1 : 16 ≤ size) (h2 : size ≤ 1016) :
    csOf s size = roundupsize size true ∧ csOf s size % 8 = 0 ∧
      (size % 16 = 0 → csOf s size % 16 = 0) ∧ size ≤ csOf s size := by
  obtain ⟨hc, hs, h8, h16, hle⟩ := tables_agree size (by omega) h1
  have hsc : scOf s size = goSizeToClass8.getD ((size + 7) / 8) 0 := ht.1 _ (by omega)
  have : csOf s size = goClassToSize.getD (scOf s size) 0 := by
    unfold csOf; rw [ht.2 _ (by rw [hsc]; exact hs)]
  rw [this, hsc, hc]
  exact ⟨rfl, h8, h16, hle⟩

theorem mul_mod_of_dvd {a b k : Nat} (h : a % k = 0) : a * b % k = 0 := by
  rw [Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod]

/-- **The fast path meets the allocation contract**: with Go's size-class tables, a span whose
base is page-aligned and whose slot lies in the runtime-owned ranges `rt`, the slot the fast
path returns is a `Fresh` object of `blockSize size true` bytes, zeroed: what
`MallocgcContract` promises for a pointer-free request of `size` bytes. -/
theorem fresh_of_fastPost {s s' : State} {size : Nat} {rt : List (Nat × Nat)}
    (hok : MCacheOK s size) (ht : TablesOK s) (h1 : 16 ≤ size) (h2 : size ≤ 1016)
    (hbase : baseOf s size % 8192 = 0) (hin : InRanges (slotOf s size) (csOf s size) rt)
    (hp : FastPost s s' size) :
    Fresh rt s'.mem (s'.regs 0).toNat size (blockSize size true) true := by
  obtain ⟨hcs, hc8, hc16, hle⟩ := csOf_eq s size ht h1 h2
  have hbs : blockSize size true = csOf s size := by
    rw [hcs]; unfold blockSize; rw [ite_eq_right (by simp; omega)]
  obtain ⟨-, -, -, -, -, -, -, ⟨hacc, hbnd⟩, -, -, -, -, -, -, -, -, hesz, -⟩ := hok
  obtain ⟨hr0, hz, -, -, -, -, -, -, -, hf⟩ := hp
  rw [hbs, hr0]
  have hm8 := mul_mod_of_dvd (b := resOf s size) (show eszOf s size % 8 = 0 by rw [hesz]; exact hc8)
  refine ⟨hin, hbnd, by rw [hf.accessible]; exact hacc, fun _ => ?_, fun h16' => ?_,
    fun _ => fun i hi => hz i (by omega), hle⟩
  · unfold slotOf; omega
  · have hm16 := mul_mod_of_dvd (b := resOf s size)
      (show eszOf s size % 16 = 0 by rw [hesz]; exact hc16 h16')
    unfold slotOf; omega


/-- **The allocator fast path, from the machine code** (see the module documentation). -/
theorem correctness (sz typ nz : BitVec 64) (rt : List (Nat × Nat)) :
    Ensures Extracted.program Extracted.entry [sz, typ, nz]
      (fun s => GuardOK s 144 ∧ StackOK s 152 32 ∧ 16 ≤ sz.toNat ∧ sz.toNat ≤ 1016 ∧
        typ.toNat = 0 ∧ MCacheOK s sz.toNat ∧ TablesOK s ∧ baseOf s sz.toNat % 8192 = 0 ∧
        InRanges (slotOf s sz.toNat) (csOf s sz.toNat) rt)
      (fun s s' => FastPost s s' sz.toNat ∧
        Fresh rt s'.mem (s'.regs 0).toNat sz.toNat (blockSize sz.toNat true) true) := by
  intro ret hret s hs ⟨hg, hst, h1, h2, ht, hok, htab, hb, hin⟩
  exact (fast_path sz typ nz ret hret s hs ⟨hg, hst, h1, h2, ht, hok⟩).mono
    fun s' ⟨habi, hp⟩ => ⟨habi, hp, fresh_of_fastPost hok htab h1 h2 hb hin hp⟩

end Proof
