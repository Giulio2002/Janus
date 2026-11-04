import Janus.Contracts.LiveSat

/-!
# Straight-line copies and clears: the memory facts (ISA independent)

The stubs of `LiveStubSlice` (`memmove`, `memclrNoHeapPointers`, and the copy inside `growslice`)
move `n` bytes (a request pinned by the runtime's `ok` predicate) with unrolled loads and stores of
widths 8, 4, 2 and 1 (`chunkList n`, in order, covering exactly `[0, n)`). All loads come before
all stores, so an overlapping `memmove` is correct. This file has the facts about the memory a
list of stores (`applyWrites`) produces: only the written bytes change (`bytes_applyWrites_*`),
the stores copy / clear the right bytes when every store writes the right bytes
(`bytes_applyWrites_cover`), the view of the runtime is unchanged when the destination is inside a
live object or outside the runtime's ranges (`view_applyWrites`).
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.Contracts

/-- A store: address, width in bytes, value. -/
abbrev Wr := Nat × Nat × Nat

/-- The memory after the stores `ws`, in order. -/
def applyWrites (m : Memory) (ws : List Wr) : Memory :=
  ws.foldl (fun m w => m.writeLE w.1 w.2.1 w.2.2) m

@[simp] theorem applyWrites_nil (m : Memory) : applyWrites m [] = m := rfl
@[simp] theorem applyWrites_cons (m : Memory) (w : Wr) (ws : List Wr) :
    applyWrites m (w :: ws) = applyWrites (m.writeLE w.1 w.2.1 w.2.2) ws := rfl

theorem regions_applyWrites (ws : List Wr) : ∀ m : Memory, (applyWrites m ws).regions = m.regions := by
  induction ws with
  | nil => intro m; rfl
  | cons w ws ih => intro m; simp only [applyWrites_cons, ih, Memory.regions_writeLE]

theorem accessible_applyWrites (ws : List Wr) :
    ∀ (m : Memory) (a n : Nat) (w : Bool), (applyWrites m ws).accessible a n w = m.accessible a n w := by
  induction ws with
  | nil => intro m a n w; rfl
  | cons w' ws ih => intro m a n w; simp only [applyWrites_cons, ih, Memory.accessible_writeLE]

/-- A byte outside every store is unchanged. -/
theorem bytes_applyWrites_untouched {x : Nat} (ws : List Wr)
    (h : ∀ w ∈ ws, x < w.1 ∨ w.1 + w.2.1 ≤ x) : ∀ m : Memory, (applyWrites m ws).bytes x = m.bytes x := by
  induction ws with
  | nil => intro m; rfl
  | cons w ws ih =>
    intro m
    rw [applyWrites_cons, ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))]
    exact Memory.bytes_writeLE_outside _ (h w (List.mem_cons_self ..))

/-- If every store writes the bytes `f` prescribes, every byte inside some store is `f`. -/
theorem bytes_applyWrites_cover (f : Nat → Byte) {x : Nat} (ws : List Wr)
    (hv : ∀ w ∈ ws, ∀ i, i < w.2.1 → BitVec.ofNat 8 (w.2.2 / 256 ^ i) = f (w.1 + i))
    (hx : ∃ w ∈ ws, w.1 ≤ x ∧ x < w.1 + w.2.1) : ∀ m : Memory, (applyWrites m ws).bytes x = f x := by
  induction ws with
  | nil => obtain ⟨w, hw, _⟩ := hx; cases hw
  | cons w ws ih =>
    intro m
    by_cases hc : ∃ w' ∈ ws, w'.1 ≤ x ∧ x < w'.1 + w'.2.1
    · rw [applyWrites_cons]
      exact ih (fun w' hw' => hv w' (List.mem_cons_of_mem _ hw')) hc _
    · rw [applyWrites_cons, bytes_applyWrites_untouched ws (fun w' hw' =>
        Classical.byContradiction fun hh => hc ⟨w', hw', by omega, by omega⟩)]
      obtain ⟨w', hw', h1, h2⟩ := hx
      rcases List.mem_cons.1 hw' with rfl | hw'
      · have := IfaceModel.bytes_writeLE_self m w'.1 w'.2.1 w'.2.2 (x - w'.1) (by omega)
        rw [show w'.1 + (x - w'.1) = x by omega] at this
        rw [this]
        have := hv w' (List.mem_cons_self ..) (x - w'.1) (by omega)
        rwa [show w'.1 + (x - w'.1) = x by omega] at this
      · exact absurd ⟨w', hw', h1, h2⟩ hc

/-- Stores inside a live object, or outside the runtime's ranges, do not change the view. -/
theorem view_applyWrites {rt L : List (Nat × Nat)} {dst n : Nat} (ws : List Wr)
    (hws : ∀ w ∈ ws, dst ≤ w.1 ∧ w.1 + w.2.1 ≤ dst + n) (hd : InRanges dst n L ∨ Outside dst n rt)
    (m : Memory) : view rt L (applyWrites m ws) = view rt L m := by
  simp only [view, Memory.mk.injEq, regions_applyWrites, and_true]
  funext x
  by_cases hx : dst ≤ x ∧ x < dst + n
  · have : (inRs rt x && !inRs L x) = false := by
      rcases hd with h | h
      · rw [inRs_of_inRanges h hx.1 hx.2]; simp
      · rw [inRs_of_outside h hx.1 hx.2]; simp
    simp only [this]; simp
  · rw [bytes_applyWrites_untouched ws (fun w hw => by have := hws w hw; omega) m]

/-! ### The stores of a copy or a clear -/

/-- The widths of the unrolled stores for the `r < 8` tail bytes at `base`: 4, 2, 1. -/
def tailChunks (base r : Nat) : List (Nat × Nat) :=
  (if 4 ≤ r then [(base, 4)] else []) ++ (if 2 ≤ r % 4 then [(base + r / 4 * 4, 2)] else []) ++
    (if r % 2 = 1 then [(base + r / 2 * 2, 1)] else [])

/-- The chunks `(offset, width)` of an `n`-byte move: words, then 4, 2, 1. -/
def chunkList (n : Nat) : List (Nat × Nat) :=
  (List.range (n / 8)).map (fun k => (8 * k, 8)) ++ tailChunks (8 * (n / 8)) (n % 8)

theorem chunkList_sub (n : Nat) : ∀ c ∈ chunkList n, c.1 + c.2 ≤ n := by
  intro c hc
  simp only [chunkList, tailChunks, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨k, hk, rfl⟩ | (hc | hc) | hc
  · simp only; omega
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc; simp only; omega
    · simp at hc
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc; simp only; omega
    · simp at hc
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc; simp only; omega
    · simp at hc

theorem chunkList_cover (n : Nat) : ∀ x, x < n → ∃ c ∈ chunkList n, c.1 ≤ x ∧ x < c.1 + c.2 := by
  intro x hx
  by_cases h8 : x < 8 * (n / 8)
  · refine ⟨(8 * (x / 8), 8), ?_, ?_, ?_⟩
    · simp only [chunkList, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl ⟨x / 8, by omega, rfl⟩
    · simp only; omega
    · simp only; omega
  · by_cases h4 : 4 ≤ n % 8 ∧ x < 8 * (n / 8) + 4
    · refine ⟨(8 * (n / 8), 4), ?_, ?_, ?_⟩
      · simp [chunkList, tailChunks, h4.1]
      · simp only; omega
      · simp only; omega
    · by_cases h2 : 2 ≤ (n % 8) % 4 ∧ 8 * (n / 8) + (n % 8) / 4 * 4 ≤ x ∧ x < 8 * (n / 8) + (n % 8) / 4 * 4 + 2
      · refine ⟨(8 * (n / 8) + (n % 8) / 4 * 4, 2), ?_, ?_, ?_⟩
        · have h2' : 2 ≤ n % 4 := by omega
          simp [chunkList, tailChunks, h2']
        · simp only; omega
        · simp only; omega
      · refine ⟨(8 * (n / 8) + (n % 8) / 2 * 2, 1), ?_, ?_, ?_⟩
        · have : n % 2 = 1 := by omega
          simp [chunkList, tailChunks, this]
        · simp only; omega
        · simp only; omega

/-- The stores of `memmove(dst, src, n)`: each chunk of `src` read from the memory `m0` of the call. -/
def copyWrites (m0 : Memory) (dst src n : Nat) : List Wr :=
  (chunkList n).map fun c => (dst + c.1, c.2, m0.readLE (src + c.1) c.2)

/-- The stores of a clear of `n` bytes at `dst`. -/
def clearWrites (dst n : Nat) : List Wr :=
  (chunkList n).map fun c => (dst + c.1, c.2, 0)

theorem copyWrites_sub (m0 : Memory) (dst src n : Nat) :
    ∀ w ∈ copyWrites m0 dst src n, dst ≤ w.1 ∧ w.1 + w.2.1 ≤ dst + n := by
  intro w hw
  simp only [copyWrites, List.mem_map] at hw
  obtain ⟨c, hc, rfl⟩ := hw
  have := chunkList_sub n c hc
  simp only; omega

theorem clearWrites_sub (dst n : Nat) :
    ∀ w ∈ clearWrites dst n, dst ≤ w.1 ∧ w.1 + w.2.1 ≤ dst + n := by
  intro w hw
  simp only [clearWrites, List.mem_map] at hw
  obtain ⟨c, hc, rfl⟩ := hw
  have := chunkList_sub n c hc
  simp only; omega

/-- The copy copies: the bytes read from `r` land at `dst` of the memory `t` the stores are applied to. -/
theorem copied_copyWrites (r t : Memory) (dst src n : Nat) :
    Mem.Copied r (applyWrites t (copyWrites r dst src n)) dst src n := by
  intro i hi
  have hcov := chunkList_cover n i hi
  have := bytes_applyWrites_cover (fun x => r.bytes (src + (x - dst))) (x := dst + i)
    (copyWrites r dst src n) ?_ ?_ t
  · simpa using this
  · intro w hw j hj
    simp only [copyWrites, List.mem_map] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    simp only at hj ⊢
    rw [IfaceModel.byte_of_readLE r c.2 (src + c.1) j hj]
    congr 1; omega
  · obtain ⟨c, hc, h1, h2⟩ := hcov
    exact ⟨(dst + c.1, c.2, r.readLE (src + c.1) c.2),
      List.mem_map.2 ⟨c, hc, rfl⟩, by simp only; omega, by simp only; omega⟩

/-- The clear clears. -/
theorem zeroed_clearWrites (m0 : Memory) (dst n : Nat) :
    Mem.Zeroed (applyWrites m0 (clearWrites dst n)) dst n := by
  intro i hi
  have hcov := chunkList_cover n i hi
  have := bytes_applyWrites_cover (fun _ => (0 : Byte)) (x := dst + i) (clearWrites dst n) ?_ ?_ m0
  · simpa using this
  · intro w hw j hj
    simp only [clearWrites, List.mem_map] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    simp
  · obtain ⟨c, hc, h1, h2⟩ := hcov
    exact ⟨(dst + c.1, c.2, 0), List.mem_map.2 ⟨c, hc, rfl⟩, by simp only; omega, by simp only; omega⟩

/-- A load of `k` bytes needs no reduction modulo `M ≥ 256^k` (the executor reduces the loaded value of a
narrow `LDR`/`MOV` modulo the register or access width). -/
theorem readLE_mod_of_le (m : Memory) (a k M : Nat) (h : 256 ^ k ≤ M) : m.readLE a k % M = m.readLE a k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt m a k) h)

end Janus.Contracts.LiveStub
