import Janus.Tactic.Basic

/-!
# Specification vocabulary

Reusable predicates for stating theorems about Go functions on memory.

* `Ptr m p n w`: the `n` bytes at pointer `p` are accessible (writable if `w`) in `m`, and lie
  below `2^48` (the user address space, so they never wrap around `2^64` and are untagged).
* `Disjoint p n q k`, `Disjoint32 p q`: byte ranges do not overlap.
* `Aliasing p q`: two `*[32]byte`-like pointers are equal or disjoint (the only overlap Go code
  produces between two `*uint256.Int`).
* `OnlyWrites m m' p n`: `m'` differs from `m` at most in `[p, p+n)` and has the same regions.
  `Unchanged m m'` is `OnlyWrites` with nothing written.
* `val256 m p`: the 32 bytes at `p` read little-endian, which is the value
  `z[0] + 2^64 z[1] + 2^128 z[2] + 2^192 z[3]` of a `[4]uint64` (limb 0 least significant).
  `limb m p i` is the `i`-th 64-bit limb; `val256_limbs` splits a value into limbs.
* `toInt256` / `ofInt256`: two's complement.
* `sumWords m p n`: the sum of the `n` 64-bit words at `p` (a `[]uint64` buffer).
-/

namespace Janus.Spec

open Janus Janus.Arm64

/-- `n` bytes at `p` are inside one region of `m` (writable if `w`, with no read-only region
overlapping them) and below `2^48`. The bound is implied by `accessible` (`Ptr.of_accessible`);
it is stated separately so that destructuring a `Ptr` gives `omega` the no-wrap fact. -/
def Ptr (m : Memory) (p : W64) (n : Nat) (w : Bool) : Prop :=
  m.accessible p.toNat n w = true ∧ p.toNat + n ≤ 2 ^ 48

/-- A readable (`w = false`) or writable (`w = true`) 32-byte object at `p`. -/
abbrev Ptr32 (m : Memory) (p : W64) (w : Bool) : Prop := Ptr m p 32 w

/-- `[p, p+n)` and `[q, q+k)` do not overlap. -/
def Disjoint (p n q k : Nat) : Prop := p + n ≤ q ∨ q + k ≤ p

/-- Two 32-byte objects do not overlap. -/
abbrev Disjoint32 (p q : Nat) : Prop := Disjoint p 32 q 32

/-- Two pointers to 32-byte objects are equal or disjoint. -/
def Aliasing (p q : W64) : Prop := p = q ∨ Disjoint32 p.toNat q.toNat

/-- `m'` agrees with `m` outside `[p, p+n)` and has the same regions. -/
def OnlyWrites (m m' : Memory) (p n : Nat) : Prop :=
  m'.regions = m.regions ∧ ∀ a, a < p ∨ p + n ≤ a → m'.bytes a = m.bytes a

/-- `m'` has the same bytes and regions as `m`. -/
def Unchanged (m m' : Memory) : Prop := m'.regions = m.regions ∧ ∀ a, m'.bytes a = m.bytes a

/-- The 256-bit little-endian value at `p` (`uint256.Int` / `[4]uint64`). -/
def val256 (m : Memory) (p : Nat) : Nat := m.readLE p 32

/-- The `i`-th 64-bit limb at `p`. -/
def limb (m : Memory) (p i : Nat) : Nat := m.readLE (p + 8 * i) 8

/-- Two's complement value of a 256-bit word. -/
def toInt256 (v : Nat) : Int := if v < 2 ^ 255 then v else (v : Int) - 2 ^ 256

/-- The 256-bit word of an integer (modulo `2^256`). -/
def ofInt256 (i : Int) : Nat := (i % 2 ^ 256).toNat

/-- Sum of the `n` little-endian 64-bit words at `p`. -/
def sumWords (m : Memory) (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumWords m p n + m.readLE (p + 8 * n) 8

theorem val256_limbs (m : Memory) (p : Nat) :
    val256 m p = m.readLE p 8 + 2 ^ 64 * m.readLE (p + 8) 8 + 2 ^ 128 * m.readLE (p + 16) 8 +
      2 ^ 192 * m.readLE (p + 24) 8 := by
  unfold val256
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, Memory.readLE_add, Memory.readLE_add,
    Memory.readLE_add]
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.reducePow]
  omega

theorem val256_lt (m : Memory) (p : Nat) : val256 m p < 2 ^ 256 := Memory.readLE_lt m p 32

theorem limb_lt (m : Memory) (p i : Nat) : limb m p i < 2 ^ 64 := Memory.readLE_lt m _ 8

theorem sumWords_succ (m : Memory) (p n : Nat) :
    sumWords m p (n + 1) = sumWords m p n + m.readLE (p + 8 * n) 8 := rfl

@[simp] theorem sumWords_zero (m : Memory) (p : Nat) : sumWords m p 0 = 0 := rfl

theorem Aliasing.symm {p q : W64} (h : Aliasing p q) : Aliasing q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.symm h)

theorem Ptr.accessible {m : Memory} {p : W64} {n : Nat} {w : Bool} (h : Ptr m p n w) :
    m.accessible p.toNat n w = true := h.1

theorem Ptr.noWrap {m : Memory} {p : W64} {n : Nat} {w : Bool} (h : Ptr m p n w) :
    p.toNat + n ≤ 2 ^ 48 := h.2

theorem Ptr.of_accessible {m : Memory} {p : W64} {n : Nat} {w : Bool}
    (h : m.accessible p.toNat n w = true) : Ptr m p n w := ⟨h, Memory.accessible_bound m h⟩

/-- `OnlyWrites` for a chain of writes inside `[p, p+n)`. -/
theorem onlyWrites_refl (m : Memory) (p n : Nat) : OnlyWrites m m p n := ⟨rfl, fun _ _ => rfl⟩

theorem onlyWrites_writeLE {m m' : Memory} {p n a k : Nat} (v : Nat) (h : OnlyWrites m m' p n)
    (h1 : p ≤ a) (h2 : a + k ≤ p + n) : OnlyWrites m (m'.writeLE a k v) p n :=
  ⟨by rw [Memory.regions_writeLE]; exact h.1, fun b hb => by
    rw [Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb⟩

theorem unchanged_refl (m : Memory) : Unchanged m m := ⟨rfl, fun _ => rfl⟩

/-- Read-only results: the same memory, viewed through `OnlyWrites` with an empty range. -/
theorem Unchanged.onlyWrites {m m' : Memory} (h : Unchanged m m') (p : Nat) :
    OnlyWrites m m' p 0 := ⟨h.1, fun a _ => h.2 a⟩

end Janus.Spec

namespace Janus.Spec
attribute [janus_post] val256_limbs
end Janus.Spec

namespace Janus.Spec
open Janus Janus.Arm64

@[janus_post] theorem onlyWrites_writeLE_iff {m m' : Memory} {p n a k : Nat} (v : Nat)
    (h1 : p ≤ a) (h2 : a + k ≤ p + n) :
    OnlyWrites m (m'.writeLE a k v) p n ↔ OnlyWrites m m' p n :=
  ⟨fun h => ⟨by rw [← Memory.regions_writeLE m' a k v]; exact h.1, fun b hb => by
      rw [← h.2 b hb, Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => onlyWrites_writeLE v h h1 h2⟩

@[janus_post] theorem onlyWrites_self (m : Memory) (p n : Nat) : OnlyWrites m m p n ↔ True :=
  ⟨fun _ => trivial, fun _ => onlyWrites_refl m p n⟩

@[janus_post] theorem unchanged_self (m : Memory) : Unchanged m m ↔ True :=
  ⟨fun _ => trivial, fun _ => unchanged_refl m⟩

end Janus.Spec

namespace Janus.Spec
open Janus Janus.Arm64

/-- The stack at a Go call: `SP` is 16-byte aligned, and the caller owns writable memory from
`below` bytes under `SP` (the callee's frames) to `above` bytes over it (the argument/spill
area of the caller's frame), below `2^48`. A conjunction of plain arithmetic facts, so that it
can be destructured into hypotheses for `omega`. -/
def StackOK (s : State) (below above : Nat) : Prop :=
  s.sp.toNat % 16 = 0 ∧ below ≤ s.sp.toNat ∧ s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - below) (below + above) true = true

/-- The stack-growth prologue falls through: `g` (`X28`) points at a readable `stackguard0`
below `SP - adj`. Same as `GoABI.StackGuardOK`, but stated with the raw terms. -/
def GuardOK (s : State) (adj : Nat) : Prop :=
  (s.regs 28).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 28).toNat + 16) 8 + adj < s.sp.toNat

theorem guardOK_iff (s : State) (adj : Nat) : GuardOK s adj ↔ GoABI.StackGuardOK s adj :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

theorem stackOK_stackWritable {s : State} {below above : Nat} (h : StackOK s below above) :
    GoABI.StackWritable s below above ∧ GoABI.SPAligned s :=
  ⟨⟨h.2.1, h.2.2.2⟩, h.1⟩

end Janus.Spec

/-! ## Word copies (loop invariants for copy loops) -/

namespace Janus.Spec
open Janus Janus.Arm64

/-- `m` after copying the first `i` 64-bit words from `src` to `dst` (word `k` of `src` read from
`m` itself). The memory at the head of a copy loop after `i` iterations. -/
def copyWords (m : Memory) (dst src : Nat) : Nat → Memory
  | 0 => m
  | i + 1 => (copyWords m dst src i).writeLE (dst + 8 * i) 8 (m.readLE (src + 8 * i) 8)

theorem copyWords_zero (m : Memory) (dst src : Nat) : copyWords m dst src 0 = m := rfl

theorem copyWords_succ (m : Memory) (dst src i : Nat) :
    copyWords m dst src (i + 1) =
      (copyWords m dst src i).writeLE (dst + 8 * i) 8 (m.readLE (src + 8 * i) 8) := rfl

@[janus_exec, janus_post] theorem regions_copyWords (m : Memory) (dst src i : Nat) :
    (copyWords m dst src i).regions = m.regions := by
  induction i with
  | zero => rfl
  | succ i ih => rw [copyWords_succ, Memory.regions_writeLE, ih]

@[janus_exec, janus_post, janus_acc] theorem accessible_copyWords (m : Memory) (dst src i a n : Nat)
    (w : Bool) : (copyWords m dst src i).accessible a n w = m.accessible a n w :=
  Memory.accessible_congr (regions_copyWords m dst src i) a n w

theorem bytes_copyWords_outside (m : Memory) (dst src i a : Nat) (h : a < dst ∨ dst + 8 * i ≤ a) :
    (copyWords m dst src i).bytes a = m.bytes a := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [copyWords_succ, Memory.bytes_writeLE_outside _ (by omega), ih (by omega)]

/-- Reads outside the copied part of `dst` see the original memory. -/
@[janus_exec, janus_post] theorem readLE_copyWords_outside (m : Memory) (dst src i a k : Nat)
    (h : a + k ≤ dst ∨ dst + 8 * i ≤ a) :
    (copyWords m dst src i).readLE a k = m.readLE a k :=
  Memory.readLE_congr (fun j hj => bytes_copyWords_outside m dst src i (a + j) (by omega))

/-- Word `j < i` of `dst` holds word `j` of `src`, if the source does not overlap the copied
part of `dst`. -/
theorem readLE_copyWords_inside (m : Memory) (dst src i j : Nat) (hj : j < i)
    (hd : src + 8 * i ≤ dst ∨ dst + 8 * i ≤ src) :
    (copyWords m dst src i).readLE (dst + 8 * j) 8 = m.readLE (src + 8 * j) 8 := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [copyWords_succ]
    by_cases h : j = i
    · subst h
      rw [Janus.Tactic.readLE_writeLE_same _ _ _ rfl, Nat.mod_eq_of_lt (Memory.readLE_lt _ _ 8)]
    · rw [Janus.Tactic.readLE_writeLE_disjoint _ _ (by omega), ih (by omega) (by omega)]

/-- Only `[dst, dst + 8i)` changes. -/
theorem onlyWrites_copyWords (m : Memory) (dst src i : Nat) :
    OnlyWrites m (copyWords m dst src i) dst (8 * i) :=
  ⟨regions_copyWords m dst src i, fun a h => bytes_copyWords_outside m dst src i a h⟩

end Janus.Spec
