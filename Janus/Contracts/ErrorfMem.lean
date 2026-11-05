import Janus.Contracts.Errorf
import Janus.Contracts.LiveToy

/-!
# Sequential byte stores (ISA-independent): the memory model of the `fmt.errorf` witness stubs

`putBytes m a bs`: the memory after storing the bytes `bs` at `a, a+1, …` one at a time (what a
byte loop or a run of `strb`s does). The loops of the witness stubs (decimal conversion, copy)
are proved to leave `putBytes` of the right list, and the stub's whole message is then
`putBytes m mp msg`.
-/

namespace Janus.Contracts.ErrorfMem

open Janus Janus.Arm64 Janus.Spec Janus.Contracts

/-- The memory after storing `bs` at `a`, `a + 1`, … (one byte at a time). -/
def putBytes (m : Memory) (a : Nat) : List Nat → Memory
  | [] => m
  | b :: bs => putBytes (m.writeLE a 1 b) (a + 1) bs

@[simp] theorem putBytes_nil (m : Memory) (a : Nat) : putBytes m a [] = m := rfl

theorem putBytes_cons (m : Memory) (a b : Nat) (bs : List Nat) :
    putBytes m a (b :: bs) = putBytes (m.writeLE a 1 b) (a + 1) bs := rfl

theorem putBytes_append (m : Memory) (a : Nat) (xs ys : List Nat) :
    putBytes m a (xs ++ ys) = putBytes (putBytes m a xs) (a + xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, putBytes_cons, ih, putBytes_cons]
    simp only [List.length_cons]
    rw [show a + 1 + xs.length = a + (xs.length + 1) by omega]

theorem putBytes_snoc (m : Memory) (a b : Nat) (bs : List Nat) :
    putBytes m a (bs ++ [b]) = (putBytes m a bs).writeLE (a + bs.length) 1 b := by
  rw [putBytes_append]; rfl

/-- A store outside the stored range commutes with `putBytes`. -/
theorem putBytes_writeLE_comm (m : Memory) (x v a : Nat) (bs : List Nat) (h : x < a ∨ a + bs.length ≤ x) :
    putBytes (m.writeLE x 1 v) a bs = (putBytes m a bs).writeLE x 1 v := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    rw [putBytes_cons, putBytes_cons, Janus.Arm64.Memory.writeLE_comm m v b (by simp at h; omega),
      ih _ _ (by simp at h ⊢; omega)]

theorem putBytes_accessible (m : Memory) (a : Nat) (bs : List Nat) (x n : Nat) (w : Bool) :
    (putBytes m a bs).accessible x n w = m.accessible x n w := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => rw [putBytes_cons, ih]; simp

theorem putBytes_bytes_out (m : Memory) (a : Nat) (bs : List Nat) (x : Nat) (h : x < a ∨ a + bs.length ≤ x) :
    (putBytes m a bs).bytes x = m.bytes x := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    rw [putBytes_cons, ih _ _ (by simp at h ⊢; omega)]
    rw [Janus.Arm64.Memory.bytes_writeLE (m := m)]
    rw [if_neg (by simp at h; omega)]

theorem putBytes_bytes_in (m : Memory) (a : Nat) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (i : Nat)
    (hi : i < bs.length) : (putBytes m a bs).bytes (a + i) = BitVec.ofNat 8 bs[i] := by
  induction bs generalizing m a i with
  | nil => simp at hi
  | cons b bs ih =>
    rw [putBytes_cons]
    cases i with
    | zero =>
      rw [putBytes_bytes_out _ _ _ _ (Or.inl (by omega)), Janus.Arm64.Memory.bytes_writeLE (m := m), if_pos ⟨by omega, by omega⟩]
      simp
    | succ j =>
      have := ih (m.writeLE a 1 b) (a + 1) (fun x hx => hb x (List.mem_cons_of_mem _ hx)) j (by simpa using hi)
      rw [show a + (j + 1) = a + 1 + j by omega, this]
      simp

theorem strBytes_putBytes (m : Memory) (a : Nat) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    strBytes (putBytes m a bs) a bs.length = bs := by
  apply List.ext_getElem (by simp [strBytes])
  intro i h1 h2
  simp only [strBytes, List.getElem_map, List.getElem_range]
  rw [putBytes_bytes_in m a bs hb i h2]
  simp [Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))]

theorem strBytes_succ (m : Memory) (p n : Nat) :
    strBytes m p (n + 1) = (m.bytes p).toNat :: strBytes m (p + 1) n := by
  simp only [strBytes, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem strBytes_zero (m : Memory) (p : Nat) : strBytes m p 0 = [] := rfl

theorem strBytes_putBytes_out (m : Memory) (a : Nat) (bs : List Nat) (p n : Nat) (h : p + n ≤ a ∨ a + bs.length ≤ p) :
    strBytes (putBytes m a bs) p n = strBytes m p n := by
  simp only [strBytes]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [putBytes_bytes_out]
  omega

theorem readLE_putBytes_out (m : Memory) (a : Nat) (bs : List Nat) (p n : Nat) (h : p + n ≤ a ∨ a + bs.length ≤ p) :
    (putBytes m a bs).readLE p n = m.readLE p n := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    rw [putBytes_cons, ih _ _ (by simp at h ⊢; omega)]
    exact Memory.readLE_writeLE_of_disjoint _ _ (by simp at h; omega)

theorem putBytes_frame (m : Memory) {rs : List (Nat × Nat)} (a : Nat) (bs : List Nat)
    (hin : bs = [] ∨ InRanges a bs.length rs) : MemFrame m (putBytes m a bs) rs := by
  induction bs generalizing m a with
  | nil => exact MemFrame.refl _ _
  | cons b bs ih =>
    have hin' : InRanges a (b :: bs).length rs := by
      rcases hin with h | h
      · simp at h
      · exact h
    obtain ⟨r, hr, h1, h2⟩ := hin'
    rw [putBytes_cons]
    have f1 : MemFrame m (m.writeLE a 1 b) rs := MemFrame.of_writeLE m b hr h1 (by simp at h2; omega)
    have f2 := ih (m.writeLE a 1 b) (a + 1)
      (by by_cases e : bs = []; · exact Or.inl e
          · exact Or.inr ⟨r, hr, by omega, by simp at h2 ⊢; omega⟩)
    exact f1.trans f2 (fun x n h => ⟨h, h⟩)

theorem view_putBytes (rt L : List (Nat × Nat)) (m : Memory) (a : Nat) (bs : List Nat)
    (hin : bs = [] ∨ InRanges a bs.length L) : view rt L (putBytes m a bs) = view rt L m := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    have hin' : InRanges a (b :: bs).length L := by
      rcases hin with h | h
      · simp at h
      · exact h
    obtain ⟨r, hr, h1, h2⟩ := hin'
    rw [putBytes_cons, ih _ _ (by by_cases e : bs = []; · exact Or.inl e
                                  · exact Or.inr ⟨r, hr, by omega, by simp at h2 ⊢; omega⟩),
      view_writeLE_live ⟨r, hr, h1, by simp at h2; omega⟩]

theorem strBytes_writeLE_out (m : Memory) (a k v p n : Nat) (h : p + n ≤ a ∨ a + k ≤ p) :
    strBytes (m.writeLE a k v) p n = strBytes m p n := by
  simp only [strBytes]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [Janus.Arm64.Memory.bytes_writeLE (m := m)]
  rw [if_neg (by omega)]

@[simp] theorem putBytes_regions (m : Memory) (a : Nat) (bs : List Nat) : (putBytes m a bs).regions = m.regions := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => rw [putBytes_cons, ih]; simp

end Janus.Contracts.ErrorfMem
