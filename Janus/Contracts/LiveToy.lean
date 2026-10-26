import Janus.Contracts.Live

/-!
# The toy runtime of the live-contract witnesses (ISA-independent part)

The live contracts (`Janus.Contracts.Live`, `LiveAmd64`) quantify over an arbitrary runtime
invariant `R : RtInv`. Their non-vacuity witnesses (`LiveSat`, `LiveSatAmd64`) and the
`Witness.nonvacuous` of the live examples need one **concrete** runtime that meets them for every
live set and budget, not only for one call. This file is that runtime's invariant and the facts
about it that do not depend on the instruction set.

The toy runtime is a **bump allocator** over the 64 KiB heap `[HEAP, HEND)`: its only state is the
word at `BUMP`, the address `p` of the next free byte. It is the runtime of a program that never
frees:

* `toyInv tys b L g v` (the invariant, about the view `v` of the runtime's memory): `v[BUMP] = p`,
  `HEAP ≤ p`, `p` 16-aligned, `p + b ≤ HEND` (the budget `b` fits), every live object lies in
  `[HEAP, p)`, the heap from `p` on is zero, the heap, `BUMP` and the barrier buffer `WBUF`
  are writable, and the type descriptors `tys` (`(addr, Size_, PtrBytes)`) read as they say. The
  invariant does not look at the buffer's contents, so it holds whatever the caller stores there;
* an allocation of `K` bytes (16-aligned) returns `p` and stores `p + K` at `BUMP`
  (`toy_alloc`): fresh, zeroed, apart from `L`, and the invariant holds again for `L ++ [(p, p+K)]`
  and the budget `b - K`.
-/

namespace Janus.Contracts.Toy

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts

/-- The bump pointer's cell. -/
def BUMP : Nat := 0x400000
/-- The write barrier's buffer (64 bytes: `gcWriteBarrier1 … 8`). -/
def WBUF : Nat := 0x400100
/-- The heap `[HEAP, HEND)`. -/
def HEAP : Nat := 0x500000
def HEND : Nat := 0x510000

/-- Type descriptors: `(addr, Size_, PtrBytes)`. -/
abbrev Tys := List (Nat × Nat × Nat)

/-- The runtime-owned ranges of the toy: the heap, the bump cell, the buffer and the descriptors. -/
def toyRt (tys : Tys) : List (Nat × Nat) :=
  [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] ++ tys.map fun t => (t.1, t.1 + 16)

/-- The descriptors lie below the bump cell and their fields are words. -/
def TysOK (tys : Tys) : Prop :=
  ∀ t ∈ tys, t.1 + 16 ≤ BUMP ∧ t.2.1 < 2 ^ 64 ∧ t.2.2 < 2 ^ 64

/-- The toy runtime's invariant. -/
def toyInv (tys : Tys) (b : Nat) (L : List (Nat × Nat)) (_g : Nat) (v : Memory) : Prop :=
  ∃ p, v.readLE BUMP 8 = p ∧ HEAP ≤ p ∧ p % 16 = 0 ∧ p + 64 * b ≤ HEND ∧
    (∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p) ∧
    (∀ i, p ≤ i → i < HEND → v.readLE i 1 = 0) ∧
    v.accessible HEAP 0x10000 true = true ∧ v.accessible BUMP 8 true = true ∧
    v.accessible WBUF 64 true = true ∧
    (∀ t ∈ tys, v.readLE t.1 8 = t.2.1 ∧ v.readLE (t.1 + 8) 8 = t.2.2)

theorem toyInv.ext (tys : Tys) (b : Nat) (L : List (Nat × Nat)) (g : Nat) (v v' : Memory)
    (hb : ∀ a, v'.bytes a = v.bytes a) (ha : ∀ a n w, v'.accessible a n w = v.accessible a n w)
    (h : toyInv tys b L g v) : toyInv tys b L g v' := by
  have hr : ∀ a n, v'.readLE a n = v.readLE a n := fun a n =>
    Memory.readLE_congr fun i _ => hb _
  obtain ⟨p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨p, by rw [hr]; exact h1, h2, h3, h4, h5, fun i a b' => by rw [hr]; exact h6 i a b',
    by rw [ha]; exact h7, by rw [ha]; exact h8, by rw [ha]; exact h9,
    fun t ht => by rw [hr, hr]; exact h10 t ht⟩

/-- The toy as a `RtInv`; `ok` says which requests it serves. -/
def toyR (tys : Tys) (ok : Nat → List Nat → Prop) : RtInv := ⟨toyInv tys, ok, toyRt tys, toyInv.ext tys⟩

theorem outside_of_forall {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) :
    Outside a n L := by
  induction L with
  | nil => trivial
  | cons r L ih =>
    obtain ⟨lo, hi⟩ := r
    exact ⟨h _ (List.mem_cons_self ..), ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem inRanges_heap {tys : Tys} {a n : Nat} (h1 : HEAP ≤ a) (h2 : a + n ≤ HEND) :
    InRanges a n (toyRt tys) :=
  ⟨(HEAP, HEND), by simp [toyRt], h1, h2⟩

theorem inRanges_bump (tys : Tys) : InRanges BUMP 8 (toyRt tys) :=
  ⟨(BUMP, BUMP + 8), by simp [toyRt], Nat.le_refl _, Nat.le_refl _⟩

theorem inRanges_wbuf {tys : Tys} {n : Nat} (hn : n ≤ 8) : InRanges WBUF (8 * n) (toyRt tys) :=
  ⟨(WBUF, WBUF + 64), by simp [toyRt], Nat.le_refl _, by omega⟩

theorem inRanges_ty {tys : Tys} {t : Nat × Nat × Nat} (ht : t ∈ tys) {n : Nat} (hn : n ≤ 16) :
    InRanges t.1 n (toyRt tys) :=
  ⟨(t.1, t.1 + 16), by
    simp only [toyRt, List.mem_append, List.mem_cons, List.mem_map]
    exact Or.inr ⟨t, ht, rfl⟩, Nat.le_refl _, by omega⟩

/-- Live objects lie in the heap, so a range below it is outside them. -/
theorem outside_live {L : List (Nat × Nat)} {p : Nat} (hL : ∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p)
    {a n : Nat} (h : a + n ≤ HEAP) : Outside a n L :=
  outside_of_forall fun r hr => Or.inl (by have := hL r hr; omega)

/-- `[a, a+n)` at or above the bump pointer is outside the live objects. -/
theorem outside_live_above {L : List (Nat × Nat)} {p : Nat} (hL : ∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p)
    {a n : Nat} (h : p ≤ a) : Outside a n L :=
  outside_of_forall fun r hr => Or.inr (by have := hL r hr; omega)

/-- The invariant survives the caller filling the barrier's slots. -/
theorem toyInv.frame {tys : Tys} (hty : TysOK tys) {b : Nat} {L : List (Nat × Nat)} {g : Nat}
    {v v' : Memory} {n : Nat} (hn : n ≤ 8) (h : toyInv tys b L g v)
    (hf : MemFrame v v' [(WBUF, WBUF + 8 * n)]) : toyInv tys b L g v' := by
  obtain ⟨p, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hout : ∀ a k, a + k ≤ WBUF → Outside a k [(WBUF, WBUF + 8 * n)] := fun a k h => by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hout' : ∀ a k, WBUF + 64 ≤ a → Outside a k [(WBUF, WBUF + 8 * n)] := fun a k h => by
    simp only [outside_cons, outside_nil, and_true]; omega
  refine ⟨p, ?_, h1, h2, h3, h4, fun i hi hi' => ?_, by rw [hf.accessible]; exact h6,
    by rw [hf.accessible]; exact h7, by rw [hf.accessible]; exact h8, fun t ht => ?_⟩
  · rw [hf.readLE _ _ (hout _ _ (by simp [BUMP, WBUF]))]; exact hp
  · rw [hf.readLE _ _ (hout' _ _ (by simp only [HEAP, WBUF] at *; omega))]; exact h5 i hi hi'
  · have := hty t ht
    rw [hf.readLE _ _ (hout _ _ (by simp only [BUMP, WBUF] at *; omega)),
      hf.readLE _ _ (hout _ _ (by simp only [BUMP, WBUF] at *; omega))]
    exact h9 t ht

/-- The type descriptors read the same in memory as in the view. -/
theorem toy_ty_read {tys : Tys} (hty : TysOK tys) {b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (h : toyInv tys b L g (view (toyRt tys) L m)) {t : Nat × Nat × Nat} (ht : t ∈ tys) :
    m.readLE t.1 8 = t.2.1 ∧ m.readLE (t.1 + 8) 8 = t.2.2 := by
  obtain ⟨p, -, -, -, -, hL, -, -, -, -, h9⟩ := h
  have := hty t ht
  have h1 := h9 t ht
  rw [readLE_view (inRanges_ty ht (n := 8) (by omega)) (outside_live hL (by simp only [BUMP, HEAP] at *; omega))] at h1
  rw [readLE_view (a := t.1 + 8) (InRanges.sub (inRanges_ty ht (n := 16) (by omega)) (by omega) (by omega))
    (outside_live hL (by simp only [BUMP, HEAP] at *; omega))] at h1
  exact h1

/-- **An allocation of `K` bytes** (`K` a multiple of 16 within the budget): from the invariant
for `L` and `b`, the bump pointer `p` (memory's word at `BUMP`) names a block `[p, p + K)` that,
once `p + K` is stored at `BUMP` (`m'`), is a fresh zeroed object of the heap outside `L`; memory
changed only in the runtime's ranges, not in the live objects, and the invariant holds for the
live set with the block and the budget `b - K`. -/
theorem toy_alloc {tys : Tys} (hty : TysOK tys) {b K A : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K) (hb : K ≤ b) (h : toyInv tys b L g (view (toyRt tys) L m)) :
    ∃ p, m.readLE BUMP 8 = p ∧ HEAP ≤ p ∧ p % 16 = 0 ∧ p + A ≤ HEND ∧
      MemFrame m (m.writeLE BUMP 8 (p + A)) (toyRt tys) ∧
      LiveFrame m (m.writeLE BUMP 8 (p + A)) L [] ∧
      ApartAll p K L ∧ ZeroBytes (m.writeLE BUMP 8 (p + A)) p K ∧
      (m.writeLE BUMP 8 (p + A)).accessible p K true = true ∧
      toyInv tys (b - K) (L ++ [(p, p + K)]) g
        (view (toyRt tys) (L ++ [(p, p + K)]) (m.writeLE BUMP 8 (p + A))) := by
  obtain ⟨p, hp, h1, h2, h3, hL, hz, hac, hacB, hacW, hT⟩ := h
  have hbump : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  have hpm : m.readLE BUMP 8 = p := by
    rw [← readLE_view (rt := toyRt tys) (L := L) (inRanges_bump tys) (outside_live hL (by omega))]; exact hp
  have hend : p + A ≤ HEND := by omega
  have hendK : p + K ≤ HEND := by omega
  have hHE : HEND = HEAP + 0x10000 := rfl
  have hlt : p + A < 2 ^ 64 := by simp only [HEND, HEAP] at *; omega
  have hfr : MemFrame m (m.writeLE BUMP 8 (p + A)) (toyRt tys) :=
    MemFrame.of_writeLE m _ (r := (BUMP, BUMP + 8)) (by simp [toyRt]) (Nat.le_refl _) (Nat.le_refl _)
  have hrd : ∀ i, p ≤ i → i < HEND → m.readLE i 1 = 0 := fun i hi hi' => by
    rw [← readLE_view (rt := toyRt tys) (L := L) (inRanges_heap (n := 1) (by omega) (by omega))
      (outside_live_above hL hi)]
    exact hz i hi hi'
  have hwr : ∀ i, HEAP ≤ i → (m.writeLE BUMP 8 (p + A)).readLE i 1 = m.readLE i 1 := fun i hi =>
    Memory.readLE_writeLE_of_disjoint _ _ (by simp only [BUMP, HEAP] at *; omega)
  refine ⟨p, hpm, h1, h2, hend, hfr, ⟨fun a n hin hw => ?_⟩, ?_, fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨r, hr, r1, r2⟩ := hin
    have := hL r hr
    exact Memory.readLE_writeLE_of_disjoint _ _ (by simp only [BUMP, HEAP] at *; omega)
  · intro r hr
    have := hL r hr
    show p + K ≤ r.1 ∨ r.1 + (r.2 - r.1) ≤ p
    omega
  · have := hwr (p + i) (by omega)
    have h0 := hrd (p + i) (by omega) (by omega)
    have : (m.writeLE BUMP 8 (p + A)).readLE (p + i) 1 = 0 := by rw [hwr _ (by omega)]; exact h0
    rw [Memory.readLE_one] at this
    exact BitVec.eq_of_toNat_eq (by simpa using this)
  · rw [hfr.accessible, ← view_accessible (toyRt tys) L m]
    have h2' : p + K ≤ HEAP + 65536 := Nat.le_trans hendK (Nat.le_of_eq hHE)
    exact Memory.accessible_mono (view (toyRt tys) L m) hac h1 h2'
  · have hL' : ∀ r ∈ L ++ [(p, p + K)], HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p + A := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · have := hL r hr; omega
      · rw [List.mem_singleton] at hr; subst hr; simp only []; omega
    have hv : ∀ a n, InRanges a n (toyRt tys) → Outside a n (L ++ [(p, p + K)]) →
        (view (toyRt tys) (L ++ [(p, p + K)]) (m.writeLE BUMP 8 (p + A))).readLE a n =
          (m.writeLE BUMP 8 (p + A)).readLE a n := fun a n h1 h2 => readLE_view h1 h2
    refine ⟨p + A, ?_, by omega, by omega, by omega, hL', fun i hi hi' => ?_, ?_, ?_, ?_, fun t ht => ?_⟩
    · rw [hv _ _ (inRanges_bump tys) (outside_live hL' (by omega)), Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by simpa using hlt)]
    · rw [hv _ _ (inRanges_heap (n := 1) (by omega) (by omega))
        (outside_live_above hL' hi), hwr _ (by omega)]
      exact hrd i (by omega) hi'
    · rw [view_accessible, hfr.accessible, ← view_accessible (toyRt tys) L m]; exact hac
    · rw [view_accessible, hfr.accessible, ← view_accessible (toyRt tys) L m]; exact hacB
    · rw [view_accessible, hfr.accessible, ← view_accessible (toyRt tys) L m]; exact hacW
    · have ht' := hty t ht
      have e1 := (toy_ty_read hty (b := b) (L := L) (g := g) (m := m)
        ⟨p, hp, h1, h2, h3, hL, hz, hac, hacB, hacW, hT⟩ ht)
      refine ⟨?_, ?_⟩
      · rw [hv _ _ (inRanges_ty ht (n := 8) (by omega)) (outside_live hL' (by simp only [BUMP, HEAP] at *; omega)),
          Memory.readLE_writeLE_of_disjoint _ _ (by simp only [BUMP] at *; omega)]
        exact e1.1
      · rw [hv _ _ (InRanges.sub (inRanges_ty ht (n := 16) (by omega)) (by omega) (by omega))
          (outside_live hL' (by simp only [BUMP, HEAP] at *; omega)),
          Memory.readLE_writeLE_of_disjoint _ _ (by simp only [BUMP] at *; omega)]
        exact e1.2

/-- The block of an allocation is `Fresh` (any request size up to the block, any zeroing). -/
theorem toy_fresh {tys : Tys} {m' : Memory} {p K : Nat} (hp : HEAP ≤ p) (hp16 : p % 16 = 0)
    (hend : p + K ≤ HEND) (hz : ZeroBytes m' p K) (hacc : m'.accessible p K true = true)
    (size : Nat) (hs : size ≤ K) (zero hdr : Bool) : Fresh (toyRt tys) m' p size K zero hdr := by
  refine ⟨inRanges_heap hp hend, by simp only [HEND] at hend; omega, hacc, fun _ => by omega,
    fun _ _ => hp16, fun _ i hi => hz i (by omega), hs⟩

/-- A block in the runtime-owned ranges is apart from a window outside them. -/
theorem apart_win {rt win : List (Nat × Nat)} {p K : Nat} (hin : InRanges p K rt)
    (hw : LiveSep win rt) : ApartAll p K win := fun r hr => (hin.apart (hw r hr)).symm

end Janus.Contracts.Toy
