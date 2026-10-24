import Janus.Spec.Map

/-!
# Small Swiss-table maps (Go 1.26), concretely

The concrete layout of a **small** `map[uint64]uint64` in Go 1.26 (`internal/runtime/maps`): a
map with at most 8 entries and no directory, whose entries live in a single group. This is the
well-formedness predicate under which `runtime.mapaccess1_fast64` is verified from its machine
code (`examples/proofs/MapAccess1Small.lean`); `smallModel` packages it as a `MapModel`
(`Janus.Spec.Map`) so the verified behaviour is exactly the `Access1` contract.

Layout (offsets in bytes):

* `Map` header at `mp` (48 bytes): `used` (number of entries) at 0, `seed` at 8, `dirPtr` at 16
  (for a small map: the group), `dirLen` at 24 (`0` for a small map), `globalDepth` at 32,
  `globalShift` at 33, `writing` at 34 (non-zero while a write is in progress),
  `tombstonePossible` at 35, `clearSeq` at 40.
* Group at `g` (136 bytes for 8-byte keys and values): the control word (8 control bytes, byte
  `i` for slot `i`) at 0, then 8 slots of 16 bytes: slot `i` has its key at `8 + 16i` and its
  value at `16 + 16i`. A control byte below `0x80` marks a **full** slot (its low 7 bits are the
  `H2` hash tag); `0x80` is empty, `0xFE` deleted.
* The type descriptor (`abi.SwissMapType`) at `t` has the slot size (`16`) at `t + 88`.

The small-map lookup of Go 1.26 does not hash the key and does not look at `H2` tags: it
compares the key of every full slot (in slot order) until one matches. `SwissSmall` therefore
says what the map holds by the first full slot whose key matches (`lookupSlot`); real maps
never have two full slots with the same key, so this is the unique one.
-/

namespace Janus.Spec.Swiss

open Janus Janus.Arm64 Janus.Spec.Map

/-- Control byte `i` of the group at `g`. -/
def ctrl (mem : Memory) (g i : Nat) : Nat := (mem.bytes (g + i)).toNat

/-- The key of slot `i` of the group at `g`. -/
def slotKey (mem : Memory) (g i : Nat) : Nat := mem.readLE (g + 8 + 16 * i) 8

/-- The address of the value of slot `i` of the group at `g`. -/
def slotVal (g i : Nat) : Nat := g + 16 + 16 * i

/-- The first full slot `j ≥ i` (`j < 8`) holding key `k`. -/
def lookupFrom (mem : Memory) (g k : Nat) (i : Nat) : Option Nat :=
  if h : 8 ≤ i then none
  else if ctrl mem g i < 128 ∧ slotKey mem g i = k then some i else lookupFrom mem g k (i + 1)
termination_by 8 - i

/-- `1` if the control byte `b` marks a full slot, else `0`. -/
def fullBit (b : Nat) : Nat := if b < 128 then 1 else 0

/-- Bit `7` of byte `j - i` is set iff slot `j ≥ i` is full: the control-word mask
`~ctrl & 0x8080808080808080` shifted right by `8i`. -/
def maskFrom (mem : Memory) (g : Nat) (i : Nat) : Nat :=
  if h : 8 ≤ i then 0 else 128 * fullBit (ctrl mem g i) + 256 * maskFrom mem g (i + 1)
termination_by 8 - i

/-- The group pointer of the small map at `mp` (its `dirPtr`). -/
def group (mem : Memory) (mp : Nat) : Nat := mem.readLE (mp + 16) 8

/-- The map at `mp` is a well-formed small Swiss map holding `f`, with every byte of its header
and group inside `heap`. -/
structure SwissSmall (mem : Memory) (heap : Nat × Nat) (mp : Nat)
    (f : AMap (BitVec 64) (BitVec 64)) : Prop where
  nonnil : mp ≠ 0
  hdr : mem.accessible mp 48 false = true
  hdrIn : heap.1 ≤ mp ∧ mp + 48 ≤ heap.2
  dirLen : mem.readLE (mp + 24) 8 = 0
  notWriting : mem.readLE (mp + 34) 1 = 0
  grp : mem.accessible (group mem mp) 136 false = true
  grpIn : heap.1 ≤ group mem mp ∧ group mem mp + 136 ≤ heap.2
  heapBound : heap.2 ≤ 2 ^ 48
  contents : ∀ k : BitVec 64, f k = (lookupFrom mem (group mem mp) k.toNat 0).map
    fun i => BitVec.ofNat 64 (mem.readLE (slotVal (group mem mp) i) 8)
  used : ∃ ks, Keys f ks ∧ mem.readLE mp 8 = ks.length

/-- The runtime environment of `smallModel`: the slot size `16` in the type descriptor at `t`
and the 8-byte zero value at `zv`, both readable, below `2^48`. -/
def SmallEnv (mem : Memory) (t zv : Nat) : Prop :=
  mem.accessible (t + 88) 8 false = true ∧ t + 96 ≤ 2 ^ 48 ∧ mem.readLE (t + 88) 8 = 16 ∧
    mem.accessible zv 8 false = true ∧ zv + 8 ≤ 2 ^ 48 ∧ mem.readLE zv 8 = 0

/-- Small Swiss maps of type descriptor `t`, zero value `zv`, all in `heap`, as a `MapModel`:
the private memory is `heap`, the slot-size word and the zero value. No iterators (`Iter` is
empty: this model is only used for lookups), and 64 bytes of stack. -/
def smallModel (t zv : Nat) (heap : Nat × Nat) : MapModel (BitVec 64) (BitVec 64) where
  Rep mem mp f := SwissSmall mem heap mp f
  Iter _ _ _ _ _ := False
  Typ t' := t' = t
  Env mem _ := SmallEnv mem t zv
  priv := [heap, (t + 88, t + 96), (zv, zv + 8)]
  depth := 64

/-! ## Lemmas -/

@[simp] theorem smallModel_depth (t zv : Nat) (heap : Nat × Nat) : (smallModel t zv heap).depth = 64 := rfl
@[simp] theorem smallModel_priv (t zv : Nat) (heap : Nat × Nat) :
    (smallModel t zv heap).priv = [heap, (t + 88, t + 96), (zv, zv + 8)] := rfl
@[simp] theorem smallModel_rep (t zv : Nat) (heap : Nat × Nat) (m : Memory) (mp : Nat) f :
    (smallModel t zv heap).Rep m mp f = SwissSmall m heap mp f := rfl
@[simp] theorem smallModel_env (t zv : Nat) (heap : Nat × Nat) (m : Memory) (g : BitVec 64) :
    (smallModel t zv heap).Env m g = SmallEnv m t zv := rfl
@[simp] theorem smallModel_typ (t zv : Nat) (heap : Nat × Nat) (t' : Nat) :
    (smallModel t zv heap).Typ t' = (t' = t) := rfl

theorem fullBit_le (b : Nat) : fullBit b ≤ 1 := by unfold fullBit; split <;> omega

theorem maskFrom_eq (mem : Memory) (g i : Nat) (h : i < 8) :
    maskFrom mem g i = 128 * fullBit (ctrl mem g i) + 256 * maskFrom mem g (i + 1) := by
  rw [maskFrom]; simp [show ¬ 8 ≤ i by omega]

theorem maskFrom_ge (mem : Memory) (g i : Nat) (h : 8 ≤ i) : maskFrom mem g i = 0 := by
  rw [maskFrom]; simp [h]

theorem maskFrom_lt (mem : Memory) (g : Nat) : ∀ n i, i + n = 8 → maskFrom mem g i < 2 ^ (8 * n)
  | 0, i, h => by rw [maskFrom_ge _ _ _ (by omega)]; decide
  | n + 1, i, h => by
    rw [maskFrom_eq _ _ _ (by omega)]
    have := maskFrom_lt mem g n (i + 1) (by omega)
    have := fullBit_le (ctrl mem g i)
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
    have : 2 ^ 8 = 256 := rfl
    omega

theorem lookupFrom_eq (mem : Memory) (g k i : Nat) (h : i < 8) :
    lookupFrom mem g k i =
      if ctrl mem g i < 128 ∧ slotKey mem g i = k then some i else lookupFrom mem g k (i + 1) := by
  rw [lookupFrom]; simp [show ¬ 8 ≤ i by omega]

theorem lookupFrom_ge (mem : Memory) (g k i : Nat) (h : 8 ≤ i) : lookupFrom mem g k i = none := by
  rw [lookupFrom]; simp [h]

/-- No full slot at or after `i` (the shifted mask is zero): the search fails. -/
theorem lookupFrom_of_mask_zero (mem : Memory) (g k : Nat) :
    ∀ n i, i + n = 8 → maskFrom mem g i = 0 → lookupFrom mem g k i = none
  | 0, i, h, _ => lookupFrom_ge _ _ _ _ (by omega)
  | n + 1, i, h, hm => by
    rw [maskFrom_eq _ _ _ (by omega)] at hm
    rw [lookupFrom_eq _ _ _ _ (by omega)]
    have h1 : fullBit (ctrl mem g i) = 0 := by omega
    have h2 : ¬ ctrl mem g i < 128 := by unfold fullBit at h1; split at h1 <;> omega
    rw [if_neg (by omega)]
    exact lookupFrom_of_mask_zero mem g k n (i + 1) (by omega) (by omega)

theorem land_byte {c y c' y' : Nat} (hc : c < 256) (hc' : c' < 256) :
    (c + 256 * y) &&& (c' + 256 * y') = (c &&& c') + 256 * (y &&& y') := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hl : c &&& c' < 2 ^ 8 := Nat.and_lt_two_pow _ (by omega)
  rw [Nat.testBit_and, show c + 256 * y = 2 ^ 8 * y + c by omega,
    show c' + 256 * y' = 2 ^ 8 * y' + c' by omega,
    show (c &&& c') + 256 * (y &&& y') = 2 ^ 8 * (y &&& y') + (c &&& c') by omega,
    Nat.testBit_two_pow_mul_add _ (by omega), Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul_add _ hl]
  split <;> simp [Nat.testBit_and]

set_option maxRecDepth 100000 in
theorem byte_mask : ∀ b, b < 256 → (255 - b) &&& 128 = 128 * fullBit b := by decide

/-- The mask the small-map lookup computes from the control word (`MVN`, then `AND` with
`0x8080808080808080`) has bit `8i + 7` set iff slot `i` is full. -/
theorem mask_toNat (mem : Memory) (g : Nat) :
    (~~~(BitVec.ofNat 64 (mem.readLE g 8)) &&& 0x8080808080808080#64).toNat = maskFrom mem g 0 := by
  have hb : ∀ i, (mem.bytes (g + i)).toNat < 256 := fun i => (mem.bytes (g + i)).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have h4 := hb 4; have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [Nat.add_zero] at h0
  rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [maskFrom_eq mem g _ (by decide : (0:Nat) < 8), maskFrom_eq mem g _ (by decide : (1:Nat) < 8),
    maskFrom_eq mem g _ (by decide : (2:Nat) < 8), maskFrom_eq mem g _ (by decide : (3:Nat) < 8),
    maskFrom_eq mem g _ (by decide : (4:Nat) < 8), maskFrom_eq mem g _ (by decide : (5:Nat) < 8),
    maskFrom_eq mem g _ (by decide : (6:Nat) < 8), maskFrom_eq mem g _ (by decide : (7:Nat) < 8),
    maskFrom_ge mem g 8 (by decide), ctrl, Nat.zero_add]
  simp only [Memory.readLE, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
  rw [show 2 ^ 64 - 1 - ((mem.bytes g).toNat + 256 * ((mem.bytes (g + 1)).toNat + 256 *
      ((mem.bytes (g + 2)).toNat + 256 * ((mem.bytes (g + 3)).toNat + 256 * ((mem.bytes (g + 4)).toNat +
      256 * ((mem.bytes (g + 5)).toNat + 256 * ((mem.bytes (g + 6)).toNat + 256 *
      ((mem.bytes (g + 7)).toNat + 256 * 0)))))))) % 2 ^ 64 =
      (255 - (mem.bytes g).toNat) + 256 * ((255 - (mem.bytes (g + 1)).toNat) + 256 *
      ((255 - (mem.bytes (g + 2)).toNat) + 256 * ((255 - (mem.bytes (g + 3)).toNat) + 256 *
      ((255 - (mem.bytes (g + 4)).toNat) + 256 * ((255 - (mem.bytes (g + 5)).toNat) + 256 *
      ((255 - (mem.bytes (g + 6)).toNat) + 256 * ((255 - (mem.bytes (g + 7)).toNat) + 256 * 0))))))) by
        omega,
    show 9259542123273814144 % 2 ^ 64 = 128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 *
      (128 + 256 * (128 + 256 * (128 + 256 * (128 + 256 * 0))))))) by decide]
  rw [land_byte (by omega) (by decide), land_byte (by omega) (by decide),
    land_byte (by omega) (by decide), land_byte (by omega) (by decide),
    land_byte (by omega) (by decide), land_byte (by omega) (by decide),
    land_byte (by omega) (by decide), land_byte (by omega) (by decide)]
  rw [byte_mask _ h0, byte_mask _ h1, byte_mask _ h2, byte_mask _ h3, byte_mask _ h4,
    byte_mask _ h5, byte_mask _ h6, byte_mask _ h7]
  rfl

theorem lookupFrom_lt (mem : Memory) (g k : Nat) :
    ∀ n i, i + n = 8 → ∀ j, lookupFrom mem g k i = some j → j < 8
  | 0, i, hn, j, h => by rw [lookupFrom_ge _ _ _ _ (by omega)] at h; cases h
  | n + 1, i, hn, j, h => by
    rw [lookupFrom_eq _ _ _ _ (by omega)] at h
    split at h
    · cases h; omega
    · exact lookupFrom_lt mem g k n (i + 1) (by omega) j h

theorem lookupFrom_congr {m m' : Memory} {g : Nat}
    (h : ∀ a, g ≤ a → a < g + 136 → m'.bytes a = m.bytes a) (k : Nat) :
    ∀ n i, i + n = 8 → lookupFrom m' g k i = lookupFrom m g k i
  | 0, i, hn => by rw [lookupFrom_ge _ _ _ _ (by omega), lookupFrom_ge _ _ _ _ (by omega)]
  | n + 1, i, hn => by
    rw [lookupFrom_eq m' g k i (by omega), lookupFrom_eq m g k i (by omega),
      lookupFrom_congr h k n (i + 1) (by omega)]
    have hc : ctrl m' g i = ctrl m g i := by unfold ctrl; rw [h _ (by omega) (by omega)]
    have hk : slotKey m' g i = slotKey m g i := by
      unfold slotKey; exact readLE_congr 8 _ (fun j hj => h _ (by omega) (by omega))
    rw [hc, hk]

/-- A small map is unaffected by changes outside its heap. -/
theorem SwissSmall.frame {m m' : Memory} {heap : Nat × Nat} {mp : Nat} {f : AMap (BitVec 64) (BitVec 64)}
    {rs : List (Nat × Nat)} (h : SwissSmall m heap mp f) (ha : Agrees m m' rs) (hh : heap ∈ rs) :
    SwissSmall m' heap mp f := by
  have hin : ∀ a n, heap.1 ≤ a → a + n ≤ heap.2 → m'.readLE a n = m.readLE a n :=
    fun a n h1 h2 => ha.readLE ⟨heap, hh, h1, h2⟩
  have hb : ∀ a, heap.1 ≤ a → a < heap.2 → m'.bytes a = m.bytes a :=
    fun a h1 h2 => ha.2 a ⟨heap, hh, h1, by omega⟩
  have hg : group m' mp = group m mp := by
    unfold group; exact hin _ _ (by have := h.hdrIn; omega) (by have := h.hdrIn; omega)
  have hgi := h.grpIn
  have hdi := h.hdrIn
  refine ⟨h.nonnil, by rw [ha.accessible]; exact h.hdr, h.hdrIn, ?_, ?_, ?_, ?_, h.heapBound, ?_, ?_⟩
  · rw [hin _ _ (by omega) (by omega)]; exact h.dirLen
  · rw [hin _ _ (by omega) (by omega)]; exact h.notWriting
  · rw [hg, ha.accessible]; exact h.grp
  · rw [hg]; exact h.grpIn
  · intro k
    have hL : lookupFrom m' (group m mp) k.toNat 0 = lookupFrom m (group m mp) k.toNat 0 :=
      lookupFrom_congr (fun a h1 h2 => hb a (by omega) (by omega)) _ 8 0 rfl
    rw [h.contents k, hg, hL]
    cases hl : lookupFrom m (group m mp) k.toNat 0 with
    | none => simp only [Option.map_none]
    | some j =>
      have := lookupFrom_lt m _ _ 8 0 rfl j hl
      simp only [Option.map_some]
      rw [hin (slotVal (group m mp) j) 8 (by unfold slotVal; omega) (by unfold slotVal; omega)]
  · obtain ⟨ks, hk, hu⟩ := h.used
    exact ⟨ks, hk, by rw [hin _ _ (by omega) (by omega)]; exact hu⟩

theorem SmallEnv.frame {m m' : Memory} {t zv : Nat} {rs : List (Nat × Nat)} (h : SmallEnv m t zv)
    (ha : Agrees m m' rs) (h1 : (t + 88, t + 96) ∈ rs) (h2 : (zv, zv + 8) ∈ rs) : SmallEnv m' t zv := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨by rw [ha.accessible]; exact a1, a2, ?_, by rw [ha.accessible]; exact a4, a5, ?_⟩
  · rw [ha.readLE ⟨_, h1, Nat.le_refl _, Nat.le_refl _⟩]; exact a3
  · rw [ha.readLE ⟨_, h2, Nat.le_refl _, Nat.le_refl _⟩]; exact a6

/-- `smallModel` satisfies the representation laws. -/
theorem smallModel_laws (t zv : Nat) (heap : Nat × Nat) : (smallModel t zv heap).Laws where
  rep_frame m m' mp f h ha := SwissSmall.frame h ha (by simp [smallModel])
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' g h ha := SmallEnv.frame h ha (by simp [smallModel]) (by simp [smallModel])
  len m mp f h := by
    have h' : SwissSmall m heap mp f := h
    obtain ⟨ks, hk, hu⟩ := h'.used
    refine ⟨Memory.accessible_mono m h'.hdr (Nat.le_refl _) (by omega), by
      have := h'.hdrIn; have := h'.heapBound; omega, fun ks' hk' => ?_⟩
    rw [hu, hk.length_eq hk']
  finite m mp f h := by
    have h' : SwissSmall m heap mp f := h
    obtain ⟨ks, hk, _⟩ := h'.used
    exact ⟨ks, hk⟩

/-! ### What the compiled lookup computes on the mask -/

/-- `LSR #8` as the executor renders it (a rotate and two masks) on a value below `2^64`. -/
theorem lsr8_ofNat (m : Nat) (hm : m < 2 ^ 64) :
    ((BitVec.ofNat 64 m).rotateRight 8 &&& 18446744073709551615#64 &&& 72057594037927935#64) =
      BitVec.ofNat 64 (m / 256) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ofNat]
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide,
    show (72057594037927935 : Nat) = 2 ^ 56 - 1 by decide,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, show (256 : Nat) = 2 ^ 8 by decide,
    Nat.testBit_div_two_pow]
  by_cases h : i < 56
  · simp [h, hi, Nat.add_comm]; omega
  · have : m.testBit (i + 8) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, this]

/-- Bit 7 of the shifted mask (`TBZ W3, #7`) says whether slot `i` is full. -/
theorem maskFrom_bit7 (mem : Memory) (g i : Nat) (hi : i < 8) :
    (BitVec.ofNat 64 (maskFrom mem g i)).getLsbD 7 = decide (ctrl mem g i < 128) := by
  rw [BitVec.getLsbD_ofNat, maskFrom_eq _ _ _ hi, Nat.testBit_eq_decide_div_mod_eq]
  have := fullBit_le (ctrl mem g i)
  unfold fullBit at *
  split <;> simp_all <;> omega

/-- The shifted mask after one more slot. -/
theorem maskFrom_div (mem : Memory) (g i : Nat) (hi : i < 8) :
    maskFrom mem g i / 256 = maskFrom mem g (i + 1) := by
  rw [maskFrom_eq _ _ _ hi]; have := fullBit_le (ctrl mem g i); omega

theorem maskFrom_lt64 (mem : Memory) (g i : Nat) (hi : i ≤ 8) : maskFrom mem g i < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (maskFrom_lt mem g (8 - i) i (by omega))
    (Nat.pow_le_pow_right (by decide) (by omega))

/-! ### The one-bit-per-slot mask (amd64: `PMOVMSKB`, `NOT`, `MOVZX`) -/

/-- Bit `j - i` is set iff slot `j ≥ i` is full: what the amd64 small-map lookup computes from
the control word (`PMOVMSKB` of the bytes' top bits, inverted, low byte) shifted right by `i`. -/
def fullMask (mem : Memory) (g : Nat) (i : Nat) : Nat :=
  if h : 8 ≤ i then 0 else fullBit (ctrl mem g i) + 2 * fullMask mem g (i + 1)
termination_by 8 - i

theorem fullMask_eq (mem : Memory) (g i : Nat) (h : i < 8) :
    fullMask mem g i = fullBit (ctrl mem g i) + 2 * fullMask mem g (i + 1) := by
  rw [fullMask]; simp [show ¬ 8 ≤ i by omega]

theorem fullMask_ge (mem : Memory) (g i : Nat) (h : 8 ≤ i) : fullMask mem g i = 0 := by
  rw [fullMask]; simp [h]

theorem fullMask_lt (mem : Memory) (g : Nat) : ∀ n i, i + n = 8 → fullMask mem g i < 2 ^ n
  | 0, i, h => by rw [fullMask_ge _ _ _ (by omega)]; decide
  | n + 1, i, h => by
    rw [fullMask_eq _ _ _ (by omega)]
    have := fullMask_lt mem g n (i + 1) (by omega)
    have := fullBit_le (ctrl mem g i)
    rw [Nat.pow_succ]
    omega

theorem fullMask_lt64 (mem : Memory) (g i : Nat) (hi : i ≤ 8) : fullMask mem g i < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (fullMask_lt mem g (8 - i) i (by omega))
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem lookupFrom_of_fullMask_zero (mem : Memory) (g k : Nat) :
    ∀ n i, i + n = 8 → fullMask mem g i = 0 → lookupFrom mem g k i = none
  | 0, i, h, _ => lookupFrom_ge _ _ _ _ (by omega)
  | n + 1, i, h, hm => by
    rw [fullMask_eq _ _ _ (by omega)] at hm
    rw [lookupFrom_eq _ _ _ _ (by omega)]
    have h1 : fullBit (ctrl mem g i) = 0 := by omega
    have h2 : ¬ ctrl mem g i < 128 := by unfold fullBit at h1; split at h1 <;> omega
    rw [if_neg (by omega)]
    exact lookupFrom_of_fullMask_zero mem g k n (i + 1) (by omega) (by omega)

end Janus.Spec.Swiss
