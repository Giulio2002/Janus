import Janus.Arm64.MemoryLemmas
import Janus.Tactic.Common

/-!
# Stack growth: the goroutine stack, the copy, and the adjusted pointers (both ISAs)

Go 1.26 grows a goroutine stack by copying it (`runtime/stack.go`: `newstack`, `copystack`,
`adjustframe`, `adjustpointers`, `adjustctxt`). This file is the ISA-independent model of that
copy, used by the `morestack` contracts (`Janus/Contracts/Stack.lean`, `StackAmd64.lean`):

* **The goroutine's stack** `[lo, hi)`: `g.stack.lo` at `g + 0`, `g.stack.hi` at `g + 8`,
  `g.stackguard0` at `g + 16` (`GStack`). Without a preemption request the guard is
  `lo + stackGuard` (`stackGuard = 928` on linux/arm64 and linux/amd64).
* **A move** relocates the used part of the stack from `[base, hi)` to `[base + hi' - hi, hi')`,
  `hi'` the new stack's top (`copystack`: `delta = new.hi - old.hi`, the copy of
  `[old.hi - used, old.hi)` to `new.hi - used`). Every 8-byte word that the stack maps classify
  as a pointer and whose value lies in the old stack `[lo, hi)` is adjusted by the same amount
  (`adjustpointer`); every other byte is copied unchanged. `Moved` is that relation, stated so
  that two moves compose into one (`Moved.trans`): this is the relocation invariance of the
  postconditions (`docs/PROOFS.md`, "Stack growth").
* **The stack maps.** Which words are pointers is the compiler's liveness information, which the
  runtime reads from the pclntab: per function its SP delta at each pc (`pcsp`), the argument and
  local pointer bitmaps at each call site (`FUNCDATA_ArgsPointerMaps`, `FUNCDATA_LocalsPointerMaps`
  selected by `PCDATA_StackMapIndex`) and its stack objects (`FUNCDATA_StackObjects`). A
  `FrameTable` is that table, abstract: theorems quantify over every table and assume only that
  it agrees with the entries `janus extract` copied from the binary for the extracted functions
  (`FrameTable.Agrees`, `Janus/Spec/StackMaps.lean`). **Trusted:** the stack maps are correct,
  i.e. the compiler's liveness information marks exactly the slots that hold pointers.
* **The unwinder.** `copystack` walks the frames from the goroutine's saved context with
  `runtime.unwinder` (`traceback.go`) and calls `adjustframe` on each. `Chain` is that walk (a
  relation, deterministic: `Chain.unique`), and `framesCls` the set of adjusted words.

Pointers into the stack from non-stack memory are not adjusted by the runtime; Go's escape
analysis guarantees there are none, and the contracts require it (a theorem whose heap held a
pointer into the stack is not covered: the moved memory says nothing about such a heap word).
-/

namespace Janus.Spec.Stack

open Janus Janus.Arm64

/-! ## Constants (Go 1.26, linux/arm64 and linux/amd64) -/

/-- `runtime.stackGuard` = `stackNosplit (800) + stackSystem (0) + abi.StackSmall (128)`. -/
def stackGuard : Nat := 928
/-- `runtime.maxstacksize` on 64-bit platforms (`proc.go`: 1 GB); a larger stack throws
`stack overflow`. -/
def maxstacksize : Nat := 1000000000

/-! ## Moves and adjusted pointers -/

/-- `adjustpointer` for a move of the stack `[lo, hi)` to the top `hi'`: a value inside the old
stack is moved with it, any other value is kept. -/
def adjustWord (lo hi hi' v : Nat) : Nat := if lo ≤ v ∧ v < hi then v + hi' - hi else v

/-- The bytes `[a, a + n)` and the ranges `rs` (`(base, end)` pairs) are apart: an alias of
`Janus.Outside` for range lists of the `(lo, hi)` form. -/
abbrev Away (a n : Nat) (rs : List (Nat × Nat)) : Prop := Outside a n rs

/-- `m'` is `m` with the used stack `[base, hi)` of the stack `[lo, hi)` moved to the top `hi'`:
every word classified as a pointer by `cls` holds its value adjusted (`adjustWord`: a value in
the old stack is shifted by `hi' - hi`; a value outside the stack pools `pool` is kept; a value
in another part of the pools is unconstrained), every other byte is copied, except the bytes of
the ranges `ex` (old addresses), which the relation leaves unconstrained (memory a callee may
write: its argument spill slots, the objects it stores to). `base`, `hi` and `hi'` are 8-aligned,
and the old stack's bottom moves to an address of at least 4096 (`4096 + hi ≤ lo + hi'`: Go
never maps the first page, and the subtraction `a + hi' - hi` never truncates on the stack). `Moved` describes one
copy or several in sequence (`Moved.trans`), and no move at all (`Moved.refl`). -/
structure Moved (cls : Nat → Bool) (pool : List (Nat × Nat)) (lo hi hi' base : Nat)
    (ex : List (Nat × Nat)) (m m' : Memory) : Prop where
  aligned : base % 8 = 0 ∧ hi % 8 = 0 ∧ hi' % 8 = 0
  grows : 4096 ≤ lo ∧ 4096 + hi ≤ lo + hi' ∧ lo ≤ base ∧ base ≤ hi
  ptr : ∀ a, base ≤ a → a + 8 ≤ hi → a % 8 = 0 → cls a = true → Outside a 8 ex →
    (lo ≤ m.readLE a 8 → m.readLE a 8 < hi → m'.readLE (a + hi' - hi) 8 = m.readLE a 8 + hi' - hi) ∧
    (Outside (m.readLE a 8) 1 pool → m'.readLE (a + hi' - hi) 8 = m.readLE a 8)
  byte : ∀ a, base ≤ a → a < hi → cls (a - a % 8) = false → Outside a 1 ex →
    m'.bytes (a + hi' - hi) = m.bytes a

namespace Moved

variable {cls : Nat → Bool} {pool ex : List (Nat × Nat)} {lo hi hi' base : Nat} {m m' : Memory}

/-- No move: the stack stays where it is. -/
theorem refl (cls : Nat → Bool) (pool ex : List (Nat × Nat)) (m : Memory) {lo hi base : Nat}
    (hal : base % 8 = 0 ∧ hi % 8 = 0) (h4k : 4096 ≤ lo) (hlb : lo ≤ base) (hbh : base ≤ hi) :
    Moved cls pool lo hi hi base ex m m :=
  ⟨⟨hal.1, hal.2, hal.2⟩, ⟨h4k, by omega, hlb, hbh⟩,
   fun a _ _ _ _ _ => ⟨fun _ _ => by rw [Nat.add_sub_cancel, Nat.add_sub_cancel],
     fun _ => by rw [Nat.add_sub_cancel]⟩,
   fun a _ _ _ _ => by rw [Nat.add_sub_cancel]⟩

/-- Fewer constrained bytes: a larger exception list. -/
theorem mono_ex {ex' : List (Nat × Nat)} (h : Moved cls pool lo hi hi' base ex m m')
    (hsub : ∀ a n, Outside a n ex' → Outside a n ex) : Moved cls pool lo hi hi' base ex' m m' :=
  ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 h5 => h.ptr a h1 h2 h3 h4 (hsub _ _ h5),
   fun a h1 h2 h3 h4 => h.byte a h1 h2 h3 (hsub _ _ h4)⟩

/-- Fewer constrained bytes, judged only on the region. -/
theorem mono_ex' {ex' : List (Nat × Nat)} (h : Moved cls pool lo hi hi' base ex m m')
    (hsub : ∀ a n, base ≤ a → Outside a n ex' → Outside a n ex) : Moved cls pool lo hi hi' base ex' m m' :=
  ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 h5 => h.ptr a h1 h2 h3 h4 (hsub _ _ h1 h5),
   fun a h1 h2 h3 h4 => h.byte a h1 h2 h3 (hsub _ _ h1 h4)⟩

/-- A smaller moved region (a higher base). -/
theorem mono_base {base' : Nat} (h : Moved cls pool lo hi hi' base ex m m') (hb : base ≤ base')
    (hb' : base' ≤ hi) (hal : base' % 8 = 0) : Moved cls pool lo hi hi' base' ex m m' :=
  ⟨⟨hal, h.aligned.2⟩, ⟨h.grows.1, h.grows.2.1, by have := h.grows.2.2.1; omega, hb'⟩,
   fun a h1 h2 h3 h4 h5 => h.ptr a (by omega) h2 h3 h4 h5,
   fun a h1 h2 h3 h4 => h.byte a (by omega) h2 h3 h4⟩

/-- Reads of bytes of a word the classification calls a non-pointer are copied. -/
theorem readLE_scalar (h : Moved cls pool lo hi hi' base ex m m') {a n : Nat}
    (h1 : base ≤ a) (h2 : a + n ≤ hi)
    (hc : ∀ i, i < n → cls ((a + i) - (a + i) % 8) = false) (hx : Outside a n ex) :
    m'.readLE (a + hi' - hi) n = m.readLE a n := by
  have hg := h.grows
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Memory.readLE_succ, Memory.readLE_succ]
    have hb : m'.bytes (a + hi' - hi) = m.bytes a :=
      h.byte a h1 (by omega) (by simpa using hc 0 (by omega)) (Outside.of_sub hx (by omega) (by omega))
    have hr : m'.readLE (a + hi' - hi + 1) n = m.readLE (a + 1) n := by
      rw [show a + hi' - hi + 1 = (a + 1) + hi' - hi by omega]
      exact ih (by omega) (by omega)
        (fun i hi' => by have := hc (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega] at this)
        (Outside.of_sub hx (by omega) (by omega))
    rw [hb, hr]

/-- A word classified as a pointer that points into the old stack is moved with it. -/
theorem readLE_ptr (h : Moved cls pool lo hi hi' base ex m m') {a : Nat} (h1 : base ≤ a)
    (h2 : a + 8 ≤ hi) (hal : a % 8 = 0) (hc : cls a = true) (hx : Outside a 8 ex)
    (hlo : lo ≤ m.readLE a 8) (hhi : m.readLE a 8 < hi) :
    m'.readLE (a + hi' - hi) 8 = m.readLE a 8 + hi' - hi :=
  (h.ptr a h1 h2 hal hc hx).1 hlo hhi

/-- A word classified as a pointer whose value is outside every stack is copied. -/
theorem readLE_ptr_out (h : Moved cls pool lo hi hi' base ex m m') {a : Nat} (h1 : base ≤ a)
    (h2 : a + 8 ≤ hi) (hal : a % 8 = 0) (hc : cls a = true) (hx : Outside a 8 ex)
    (hout : Outside (m.readLE a 8) 1 pool) : m'.readLE (a + hi' - hi) 8 = m.readLE a 8 :=
  (h.ptr a h1 h2 hal hc hx).2 hout

/-- An 8-aligned word is copied whatever its classification when its value is outside every
stack (a code address, a heap pointer, a small integer the pools do not contain). -/
theorem readLE_word_out (h : Moved cls pool lo hi hi' base ex m m') {a : Nat} (h1 : base ≤ a)
    (h2 : a + 8 ≤ hi) (hal : a % 8 = 0) (hx : Outside a 8 ex)
    (hout : Outside (m.readLE a 8) 1 pool) : m'.readLE (a + hi' - hi) 8 = m.readLE a 8 := by
  cases hc : cls a
  · exact h.readLE_scalar h1 h2 (fun i hi => by
      rw [show (a + i) - (a + i) % 8 = a by omega]; exact hc) hx
  · exact h.readLE_ptr_out h1 h2 hal hc hx hout

/-- **Two moves compose into one** (relocation invariance of `Moved`). The second move's
classification, at the moved addresses, is the first one's; its stack is the first move's new
stack `[lo₂, hi₂)`, which lies inside the pools and contains the moved image of the old stack;
its exception list contains the moved image of the first's. -/
theorem trans {cls₂ : Nat → Bool} {ex₂ : List (Nat × Nat)} {lo₂ hi₃ : Nat} {m'' : Memory}
    (h₁ : Moved cls pool lo hi hi' base ex m m')
    (h₂ : Moved cls₂ pool lo₂ hi' hi₃ (base + hi' - hi) ex₂ m' m'')
    (hcls : ∀ a, base ≤ a → a < hi → cls₂ (a + hi' - hi) = cls a)
    (hlo : lo₂ ≤ lo + hi' - hi)
    (hex : ∀ a n, base ≤ a → Outside a n ex → Outside (a + hi' - hi) n ex₂) :
    Moved cls pool lo hi hi₃ base ex m m'' := by
  obtain ⟨⟨ha1, ha2, ha3⟩, hg0, hg1, hg2, hg3⟩ := h₁.aligned, h₁.grows
  obtain ⟨⟨-, -, hb3⟩, hk0, hk1, hk2, hk3⟩ := h₂.aligned, h₂.grows
  refine ⟨⟨ha1, ha2, hb3⟩, ⟨hg0, by omega, hg2, hg3⟩, fun a h1 h2 h3 h4 h5 => ?_, fun a h1 h2 h3 h4 => ?_⟩
  · have hA : a + hi' - hi + hi₃ - hi' = a + hi₃ - hi := by omega
    have hc₂ : cls₂ (a + hi' - hi) = true := by rw [hcls a h1 (by omega)]; exact h4
    have h5' := hex a 8 h1 h5
    refine ⟨fun hl hh => ?_, fun hout => ?_⟩
    · have e₁ := h₁.readLE_ptr h1 h2 h3 h4 h5 hl hh
      have e₂ := h₂.readLE_ptr (a := a + hi' - hi) (by omega) (by omega) (by omega) hc₂ h5'
        (by rw [e₁]; omega) (by rw [e₁]; omega)
      rw [← hA, e₂, e₁]; omega
    · have e₁ := h₁.readLE_ptr_out h1 h2 h3 h4 h5 hout
      have e₂ := h₂.readLE_ptr_out (a := a + hi' - hi) (by omega) (by omega) (by omega) hc₂ h5'
        (by rw [e₁]; exact hout)
      rw [← hA, e₂, e₁]
  · have hA : a + hi' - hi + hi₃ - hi' = a + hi₃ - hi := by omega
    have hc₂ : cls₂ (a + hi' - hi - (a + hi' - hi) % 8) = false := by
      rw [show a + hi' - hi - (a + hi' - hi) % 8 = (a - a % 8) + hi' - hi by omega,
        hcls _ (by omega) (by omega)]
      exact h3
    rw [← hA, h₂.byte (a + hi' - hi) (by omega) (by omega) hc₂ (hex a 1 h1 h4), h₁.byte a h1 h2 h3 h4]

end Moved

namespace Moved

variable {cls : Nat → Bool} {pool ex : List (Nat × Nat)} {lo hi hi' base : Nat} {m m' : Memory}

/-- No move, from memory that agrees on the region outside `ex`: the stack did not grow, and the
callee only wrote outside the region or inside `ex`. -/
theorem of_agree (cls : Nat → Bool) (pool : List (Nat × Nat)) {m m' : Memory} {lo hi base : Nat}
    {ex : List (Nat × Nat)} (hal : base % 8 = 0 ∧ hi % 8 = 0) (h4k : 4096 ≤ lo) (hlb : lo ≤ base)
    (hbh : base ≤ hi) (hag : ∀ a, base ≤ a → a < hi → Outside a 1 ex → m'.bytes a = m.bytes a) :
    Moved cls pool lo hi hi base ex m m' := by
  have hrd : ∀ a, base ≤ a → a + 8 ≤ hi → Outside a 8 ex → m'.readLE a 8 = m.readLE a 8 :=
    fun a h1 h2 hx => Memory.readLE_congr fun i hi' =>
      hag (a + i) (by omega) (by omega) (Outside.of_sub hx (by omega) (by omega))
  refine ⟨⟨hal.1, hal.2, hal.2⟩, ⟨h4k, by omega, hlb, hbh⟩, fun a h1 h2 _ _ hx => ?_, fun a h1 h2 _ hx => ?_⟩
  · rw [Nat.add_sub_cancel, Nat.add_sub_cancel, hrd a h1 h2 hx]; exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  · rw [Nat.add_sub_cancel]; exact hag a h1 h2 hx

/-- Change the memory before the move on bytes the relation does not constrain (`ex`) or
outside the region. -/
theorem congr_src {m₀ : Memory} (h : Moved cls pool lo hi hi' base ex m m')
    (hag : ∀ a, base ≤ a → a < hi → Outside a 1 ex → m₀.bytes a = m.bytes a) :
    Moved cls pool lo hi hi' base ex m₀ m' := by
  have hrd : ∀ a, base ≤ a → a + 8 ≤ hi → Outside a 8 ex → m₀.readLE a 8 = m.readLE a 8 :=
    fun a h1 h2 hx => Memory.readLE_congr fun i hi' =>
      hag (a + i) (by omega) (by omega) (Outside.of_sub hx (by omega) (by omega))
  refine ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 hx => ?_, fun a h1 h2 h3 hx => ?_⟩
  · rw [hrd a h1 h2 hx]; exact h.ptr a h1 h2 h3 h4 hx
  · rw [hag a h1 h2 hx]; exact h.byte a h1 h2 h3 hx

/-- Change the memory after the move outside the moved image (`ex'` at moved addresses). -/
theorem congr_dst {m'' : Memory} (h : Moved cls pool lo hi hi' base ex m m')
    (hag : ∀ a, base ≤ a → a < hi → Outside a 1 ex → m''.bytes (a + hi' - hi) = m'.bytes (a + hi' - hi)) :
    Moved cls pool lo hi hi' base ex m m'' := by
  obtain ⟨hg0, hg1, hg2, hg3⟩ := h.grows
  have hrd : ∀ a, base ≤ a → a + 8 ≤ hi → Outside a 8 ex →
      m''.readLE (a + hi' - hi) 8 = m'.readLE (a + hi' - hi) 8 :=
    fun a h1 h2 hx => Memory.readLE_congr fun i hi'' => by
      rw [show a + hi' - hi + i = (a + i) + hi' - hi by omega]
      exact hag (a + i) (by omega) (by omega) (Outside.of_sub hx (by omega) (by omega))
  refine ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 hx => ?_, fun a h1 h2 h3 hx => ?_⟩
  · rw [hrd a h1 h2 hx]; exact h.ptr a h1 h2 h3 h4 hx
  · rw [hag a h1 h2 hx]; exact h.byte a h1 h2 h3 hx

/-- Two classifications that agree on the region give the same relation. -/
theorem cls_congr {cls' : Nat → Bool} (h : Moved cls pool lo hi hi' base ex m m')
    (hc : ∀ a, base ≤ a → a < hi → cls' a = cls a) : Moved cls' pool lo hi hi' base ex m m' := by
  refine ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 hx => ?_, fun a h1 h2 h3 hx => ?_⟩
  · rw [hc a h1 (by omega)] at h4; exact h.ptr a h1 h2 h3 h4 hx
  · have := h.aligned.1
    rw [hc _ (by omega) (by omega)] at h3; exact h.byte a h1 h2 h3 hx

/-- A byte outside word-aligned ranges lies in a word outside them. -/
theorem _root_.Janus.Spec.Stack.outside_word {ex : List (Nat × Nat)} (hal : ∀ r ∈ ex, r.1 % 8 = 0 ∧ r.2 % 8 = 0)
    {a : Nat} (ha : Outside a 1 ex) : Outside (a - a % 8) 8 ex := by
  induction ex with
  | nil => trivial
  | cons r ex ih =>
    obtain ⟨r1, r2⟩ := r
    simp only [outside_cons] at ha ⊢
    have := hal (r1, r2) (List.mem_cons_self ..)
    exact ⟨by simp only at this; omega, ih (fun r hr => hal r (List.mem_cons_of_mem _ hr)) ha.2⟩

/-- Two classifications that agree on the region's words outside the (word-aligned) exceptions
give the same relation: the relation says nothing about the words of `ex`. -/
theorem cls_congr' {cls' : Nat → Bool} (h : Moved cls pool lo hi hi' base ex m m')
    (hal : ∀ r ∈ ex, r.1 % 8 = 0 ∧ r.2 % 8 = 0)
    (hc : ∀ a, base ≤ a → a < hi → a % 8 = 0 → Outside a 8 ex → cls' a = cls a) :
    Moved cls' pool lo hi hi' base ex m m' := by
  have hb := h.aligned.1
  have hw : ∀ a, Outside a 1 ex → Outside (a - a % 8) 8 ex := fun a ha => outside_word hal ha
  refine ⟨h.aligned, h.grows, fun a h1 h2 h3 h4 hx => ?_, fun a h1 h2 h3 hx => ?_⟩
  · rw [hc a h1 (by omega) h3 hx] at h4; exact h.ptr a h1 h2 h3 h4 hx
  · rw [hc _ (by omega) (by omega) (by omega) (hw a hx)] at h3; exact h.byte a h1 h2 h3 hx

/-- **Two moves compose into one**, with the exceptions of both: the result leaves free `ex₃`,
which must cover `ex` and the preimage of the second move's `ex₂`. -/
theorem trans' {cls₂ : Nat → Bool} {ex₂ ex₃ : List (Nat × Nat)} {lo₂ hi₃ : Nat} {m'' : Memory}
    (h₁ : Moved cls pool lo hi hi' base ex m m')
    (h₂ : Moved cls₂ pool lo₂ hi' hi₃ (base + hi' - hi) ex₂ m' m'')
    (hcls : ∀ a, base ≤ a → a < hi → cls₂ (a + hi' - hi) = cls a)
    (hlo : lo₂ ≤ lo + hi' - hi)
    (hex : ∀ a n, base ≤ a → Outside a n ex₃ → Outside a n ex ∧ Outside (a + hi' - hi) n ex₂) :
    Moved cls pool lo hi hi₃ base ex₃ m m'' := by
  obtain ⟨⟨ha1, ha2, ha3⟩, hg0, hg1, hg2, hg3⟩ := h₁.aligned, h₁.grows
  obtain ⟨⟨-, -, hb3⟩, hk0, hk1, hk2, hk3⟩ := h₂.aligned, h₂.grows
  refine ⟨⟨ha1, ha2, hb3⟩, ⟨hg0, by omega, hg2, hg3⟩, fun a h1 h2 h3 h4 h5 => ?_, fun a h1 h2 h3 h4 => ?_⟩
  · have hA : a + hi' - hi + hi₃ - hi' = a + hi₃ - hi := by omega
    have hc₂ : cls₂ (a + hi' - hi) = true := by rw [hcls a h1 (by omega)]; exact h4
    obtain ⟨h5a, h5b⟩ := hex a 8 h1 h5
    refine ⟨fun hl hh => ?_, fun hout => ?_⟩
    · have e₁ := h₁.readLE_ptr h1 h2 h3 h4 h5a hl hh
      have e₂ := h₂.readLE_ptr (a := a + hi' - hi) (by omega) (by omega) (by omega) hc₂ h5b
        (by rw [e₁]; omega) (by rw [e₁]; omega)
      rw [← hA, e₂, e₁]; omega
    · have e₁ := h₁.readLE_ptr_out h1 h2 h3 h4 h5a hout
      have e₂ := h₂.readLE_ptr_out (a := a + hi' - hi) (by omega) (by omega) (by omega) hc₂ h5b
        (by rw [e₁]; exact hout)
      rw [← hA, e₂, e₁]
  · have hA : a + hi' - hi + hi₃ - hi' = a + hi₃ - hi := by omega
    obtain ⟨h4a, h4b⟩ := hex a 1 h1 h4
    have hc₂ : cls₂ (a + hi' - hi - (a + hi' - hi) % 8) = false := by
      rw [show a + hi' - hi - (a + hi' - hi) % 8 = (a - a % 8) + hi' - hi by omega,
        hcls _ (by omega) (by omega)]
      exact h3
    rw [← hA, h₂.byte (a + hi' - hi) (by omega) (by omega) hc₂ h4b, h₁.byte a h1 h2 h3 h4a]

end Moved

/-! ## The goroutine's stack descriptor -/

/-- Offsets in `runtime.g` (Go 1.26): `stack.lo`, `stack.hi`, `stackguard0`. -/
def gStackLo : Nat := 0
def gStackHi : Nat := 8
def gStackguard0 : Nat := 16

/-- The goroutine at `g` runs on the stack `[lo, hi)` with no preemption request pending: its
`stack.lo`, `stack.hi` and `stackguard0` words read `lo`, `hi` and `lo + stackGuard`, and are
readable (`newstack`'s `stackguard0 == stackPreempt` case is a scheduler request from another
thread, outside the single-threaded model). -/
def GStack (m : Memory) (g lo hi : Nat) : Prop :=
  g + 24 ≤ 2 ^ 48 ∧ m.accessible g 24 false = true ∧
    m.readLE (g + gStackLo) 8 = lo ∧ m.readLE (g + gStackHi) 8 = hi ∧
    m.readLE (g + gStackguard0) 8 = lo + stackGuard

/-- **No pointer into a goroutine stack lives outside the stacks** (Go's escape analysis: a
pointer into a stack is never stored in the heap or in globals). No word of `m` outside the
stack pools `pool` and the runtime's own memory `rt` points into a pool. `copystack` adjusts only
the words of the stack, so such a word would be left pointing at the old stack; the `morestack`
contract's precondition (`MorestackPre.noptr`) excludes it. -/
def NoStackPtr (m : Memory) (pool rt : List (Nat × Nat)) : Prop :=
  ∀ a, Outside a 8 (pool ++ rt) → Outside (m.readLE a 8) 1 pool

/-- `NoStackPtr` survives any change inside the pools and the runtime's memory. -/
theorem NoStackPtr.of_frame {m m' : Memory} {pool rt : List (Nat × Nat)} (h : NoStackPtr m pool rt)
    (hf : MemFrame m m' (pool ++ rt)) : NoStackPtr m' pool rt :=
  fun a ha => by rw [hf.readLE a 8 ha]; exact h a ha

/-- `NoStackPtr` survives a store inside the pools (a store to the stack). -/
theorem NoStackPtr.writeLE {m : Memory} {pool rt : List (Nat × Nat)} (h : NoStackPtr m pool rt)
    {a k : Nat} (v : Nat) (hin : InRanges a k pool) : NoStackPtr (m.writeLE a k v) pool rt :=
  h.of_frame ((MemFrame.refl m _).writeLE_inRanges v (hin.append_left rt))

/-- Memory of zero bytes reads `0`. -/
theorem readLE_zeros (rs : List Region) (a n : Nat) : (⟨fun _ => 0, rs⟩ : Memory).readLE a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [Memory.readLE_succ, ih]; rfl

/-- `GStack` determines the stack bounds. -/
theorem GStack.unique {m : Memory} {g lo hi lo' hi' : Nat} (h : GStack m g lo hi)
    (h' : GStack m g lo' hi') : lo = lo' ∧ hi = hi' := by
  obtain ⟨-, -, a1, a2, -⟩ := h; obtain ⟨-, -, b1, b2, -⟩ := h'
  exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩

/-- A byte outside a frame's ranges is unchanged. -/
theorem _root_.Janus.MemFrame.bytes {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs)
    {a : Nat} (ha : Outside a 1 rs) : m'.bytes a = m.bytes a := by
  have := h.readLE a 1 ha
  simp only [Memory.readLE, Nat.mul_zero, Nat.add_zero] at this
  exact BitVec.eq_of_toNat_eq this

/-- The descriptor survives changes outside it. -/
theorem GStack.of_frame {m m' : Memory} {g lo hi : Nat} {rs : List (Nat × Nat)} (h : GStack m g lo hi)
    (hf : MemFrame m m' rs) (hg : Outside g 24 rs) : GStack m' g lo hi := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, by rw [hf.accessible]; exact h2, ?_, ?_, ?_⟩
  · rw [hf.readLE _ _ (Outside.of_sub hg (by simp [gStackLo]) (by simp [gStackLo]))]; exact h3
  · rw [hf.readLE _ _ (Outside.of_sub hg (by simp [gStackHi]) (by simp [gStackHi]))]; exact h4
  · rw [hf.readLE _ _ (Outside.of_sub hg (by simp [gStackguard0]) (by simp [gStackguard0]))]; exact h5

/-! ## The frame table (the pclntab's stack maps) -/

/-- The unwinding information the runtime reads from the pclntab, by pc (Go 1.26
`runtime/symtab.go`, `stkframe.go`). For a pc inside a function:

* `valid pc`: `findfunc(pc).valid()`;
* `entry pc`: the function's entry;
* `spdelta pc`: `funcspdelta(f, pc)`, the frame size at `pc` (`pcsp`);
* `maxspd pc`: `funcMaxSPDelta(f)`, the largest frame size of the function;
* `stop pc`: the function ends the unwinding (`FuncFlagTopFrame`, or `FuncFlagSPWrite`);
* `injected pc`: the function is a call the runtime injects (`sigpanic`, `asyncPreempt`,
  `debugCallV2`), after which the unwinder changes its caller's continuation pc; walks through
  such frames are not modelled (`Chain` excludes them);
* `locals pc`, `args pc`: the locals and arguments pointer bitmaps (one `Bool` per 8-byte word) of
  a frame suspended at the continuation `pc` (`getStackMap`: the stack map index at `pc - 1`, the
  first map at the entry);
* `objs pc`: the stack objects (`off`, pointer bitmap of the object): offset from `varp` if
  negative, from `argp` otherwise. -/
structure FrameTable where
  valid : Nat → Bool
  entry : Nat → Nat
  spdelta : Nat → Nat
  maxspd : Nat → Nat
  stop : Nat → Bool
  injected : Nat → Bool
  locals : Nat → List Bool
  args : Nat → List Bool
  objs : Nat → List (Int × List Bool)

/-- A pc the table knows is a code address, never inside a goroutine stack pool. -/
def FrameTable.CodeOutside (FT : FrameTable) (pool : List (Nat × Nat)) : Prop :=
  ∀ pc, FT.valid pc = true → Outside pc 1 pool ∧ pc < 2 ^ 48

/-- The architecture: on arm64 (`usesLR`) the return address is in the link register and saved
at `0(SP)` of the frame, `sys.MinFrameSize = 8`; on amd64 it is pushed by `CALL` at `fp - 8`. -/
inductive Arch where
  | arm64
  | amd64
deriving DecidableEq

/-- `frame.fp` of a frame with `pc`, `sp`. -/
def Arch.fp (A : Arch) (FT : FrameTable) (pc sp : Nat) : Nat :=
  match A with
  | .arm64 => sp + FT.spdelta pc
  | .amd64 => sp + FT.spdelta pc + 8

/-- `frame.varp` (`resolveInternal`, frame pointers enabled). -/
def Arch.varp (A : Arch) (sp fp : Nat) : Nat :=
  let v := match A with | .arm64 => fp | .amd64 => fp - 8
  if sp < v then v - 8 else v

/-- `frame.argp = frame.fp + sys.MinFrameSize`. -/
def Arch.argp (A : Arch) (fp : Nat) : Nat :=
  match A with | .arm64 => fp + 8 | .amd64 => fp

/-- The smallest locals area `getStackMap` reads a locals map for (exclusive). -/
def Arch.minLocals (A : Arch) : Nat := match A with | .arm64 => 16 | .amd64 => 0

/-- Word `a` is `base + 8 i` with bit `i` of `bs` set (`base` an integer, so that the bases
`varp - 8·n` and `varp + off` need no side conditions). -/
def bitsAt (base : Int) (bs : List Bool) (a : Nat) : Bool :=
  decide (base ≤ (a : Int)) && (((a : Int) - base).toNat % 8 == 0) &&
    bs.getD (((a : Int) - base).toNat / 8) false

/-- The address of a stack object at offset `off` (`adjustframe`: from `varp` when negative, from
`argp` otherwise). -/
def objBase (varp argp : Nat) (off : Int) : Int :=
  if off < 0 then (varp : Int) + off else (argp : Int) + off

/-- The words `adjustframe` adjusts in the frame of the function at `pc` with `sp`, `fp`: the
saved frame pointer (when `argp - varp = 16`), the locals map (`locals.n` words ending at `varp`,
read only when the frame is larger than `minLocals`), the arguments map from `argp`, and the
pointer words of the stack objects already allocated (`p ≥ sp`). -/
def frameCls (A : Arch) (FT : FrameTable) (pc sp fp a : Nat) : Bool :=
  let varp := A.varp sp fp
  let argp := A.argp fp
  (decide (argp = varp + 16) && a == varp) ||
  (decide (A.minLocals + sp < varp) &&
    bitsAt ((varp : Int) - 8 * ((FT.locals pc).length : Int)) (FT.locals pc) a) ||
  bitsAt (argp : Int) (FT.args pc) a ||
  (FT.objs pc).any (fun o => decide ((sp : Int) ≤ objBase varp argp o.1) &&
    bitsAt (objBase varp argp o.1) o.2 a)

/-- A frame on the walk: its continuation `pc`, `sp` and `fp`. -/
structure Frame where
  pc : Nat
  sp : Nat
  fp : Nat
deriving DecidableEq

/-- The return address the unwinder reads for the frame `pc`, `sp`, `fp` (`resolveInternal`): on
arm64 the given link register of the innermost frame when it has no frame yet (`sp = fp`), else
the word at `0(sp)`; on amd64 the word at `fp - 8`. -/
def Arch.lrOf (A : Arch) (m : Memory) (sp fp : Nat) (lr0 : Option Nat) : Nat :=
  match A with
  | .arm64 => if sp < fp then m.readLE sp 8 else lr0.getD (m.readLE sp 8)
  | .amd64 => m.readLE (fp - 8) 8

/-- The address the unwinder reads the return address from (`lrOf`, when it reads memory). -/
def Arch.lrSlot (A : Arch) (sp fp : Nat) : Nat := match A with | .arm64 => sp | .amd64 => fp - 8

/-- **The unwinder's walk** (`runtime.unwinder`, `traceback.go`) from the frame with continuation
`pc` and stack pointer `sp` (and, for the innermost arm64 frame, link register `lr0`) to the end
of the stack: every pc is a known function's, every frame ends at or below the stack top `hi`,
and the walk ends at a function that stops it (`goexit`'s `TopFrame` flag). A walk that meets an
unknown return address throws in the runtime (`unknown caller pc`); such stacks are not
`Chain`s. -/
inductive Chain (A : Arch) (FT : FrameTable) (m : Memory) (hi : Nat) :
    Nat → Nat → Option Nat → List Frame → Prop where
  | stop {pc sp : Nat} {lr0 : Option Nat} : FT.valid pc = true → FT.stop pc = true →
      FT.injected pc = false → sp + 8 ≤ hi → A.fp FT pc sp ≤ hi → Chain A FT m hi pc sp lr0 [⟨pc, sp, A.fp FT pc sp⟩]
  | cons {pc sp : Nat} {lr0 : Option Nat} {fs : List Frame} : FT.valid pc = true →
      FT.stop pc = false → FT.injected pc = false → sp + 8 ≤ hi → A.fp FT pc sp ≤ hi →
      Chain A FT m hi (A.lrOf m sp (A.fp FT pc sp) lr0) (A.fp FT pc sp) none fs →
      Chain A FT m hi pc sp lr0 (⟨pc, sp, A.fp FT pc sp⟩ :: fs)

/-- The words `copystack` adjusts in the frames `fs`. -/
def framesCls (A : Arch) (FT : FrameTable) (fs : List Frame) (a : Nat) : Bool :=
  fs.any (fun f => frameCls A FT f.pc f.sp f.fp a)

@[simp] theorem framesCls_nil (A : Arch) (FT : FrameTable) (a : Nat) : framesCls A FT [] a = false := rfl
@[simp] theorem framesCls_cons (A : Arch) (FT : FrameTable) (f : Frame) (fs : List Frame) (a : Nat) :
    framesCls A FT (f :: fs) a = (frameCls A FT f.pc f.sp f.fp a || framesCls A FT fs a) := rfl

theorem Chain.unique {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat} {lr0 : Option Nat}
    {fs fs' : List Frame} (h : Chain A FT m hi pc sp lr0 fs) (h' : Chain A FT m hi pc sp lr0 fs') :
    fs = fs' := by
  induction h generalizing fs' with
  | stop hv hs _ _ hf =>
    cases h' with
    | stop => rfl
    | cons _ hs' => rw [hs] at hs'; cases hs'
  | cons hv hs _ _ hf hc ih =>
    cases h' with
    | stop _ hs' => rw [hs] at hs'; cases hs'
    | cons _ _ _ _ _ hc' => rw [ih hc']

theorem Arch.le_fp (A : Arch) (FT : FrameTable) (pc sp : Nat) : sp ≤ A.fp FT pc sp := by
  cases A <;> simp only [Arch.fp] <;> omega

/-- Every frame of a walk lies between its starting `sp` and the stack top. -/
theorem Chain.bounds {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat} {lr0 : Option Nat}
    {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) :
    ∀ f ∈ fs, sp ≤ f.sp ∧ f.sp ≤ f.fp ∧ f.sp + 8 ≤ hi ∧ f.fp ≤ hi ∧ FT.valid f.pc = true ∧
      f.fp = A.fp FT f.pc f.sp := by
  induction h with
  | @stop pc sp _ hv hs _ h8 hf =>
    intro f hf'; simp only [List.mem_singleton] at hf'; subst hf'
    exact ⟨Nat.le_refl _, A.le_fp FT pc sp, h8, hf, hv, rfl⟩
  | @cons pc sp _ _ hv hs _ h8 hf hc ih =>
    intro f hf'
    rcases List.mem_cons.1 hf' with rfl | hf'
    · exact ⟨Nat.le_refl _, A.le_fp FT pc sp, h8, hf, hv, rfl⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih f hf'
      exact ⟨Nat.le_trans (A.le_fp FT pc sp) h1, h2, h3, h4, h5, h6⟩

theorem Chain.valid_head {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat}
    {lr0 : Option Nat} {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) : FT.valid pc = true := by
  cases h <;> assumption

/-! ## Moving frames (relocation invariance of the walk and of the classification)

A move of the stack with top `hi` to the top `hi'` maps an address `a` of the old stack to
`a + hi' - hi` (natural numbers: the new stack may lie below the old one; every address involved
is at least `hi - hi'`, the size condition of `Moved`). -/

/-- A frame moved with the stack. -/
def Frame.mv (hi hi' : Nat) (f : Frame) : Frame := ⟨f.pc, f.sp + hi' - hi, f.fp + hi' - hi⟩

theorem Arch.fp_mv (A : Arch) (FT : FrameTable) (pc sp hi hi' : Nat) (h : hi ≤ sp + hi') :
    A.fp FT pc (sp + hi' - hi) = A.fp FT pc sp + hi' - hi := by
  cases A <;> simp only [Arch.fp] <;> omega

theorem Arch.varp_mv (A : Arch) {sp fp hi hi' : Nat} (h : sp ≤ fp) (h8 : 16 + hi ≤ fp + hi')
    (hs : hi ≤ sp + hi') (h16 : 16 ≤ fp) :
    A.varp (sp + hi' - hi) (fp + hi' - hi) = A.varp sp fp + hi' - hi := by
  cases A <;> simp only [Arch.varp] <;> split <;> split <;> omega

theorem Arch.argp_mv (A : Arch) (fp hi hi' : Nat) (h : hi ≤ fp + hi') :
    A.argp (fp + hi' - hi) = A.argp fp + hi' - hi := by
  cases A <;> simp only [Arch.argp] <;> omega

theorem bitsAt_mv (base : Int) (bs : List Bool) (a hi hi' : Nat) (h : hi ≤ a + hi') :
    bitsAt (base + hi' - hi) bs (a + hi' - hi) = bitsAt base bs a := by
  simp only [bitsAt]
  rw [show ((a + hi' - hi : Nat) : Int) - (base + hi' - hi) = (a : Int) - base by omega]
  simp only [show (base + hi' - hi ≤ ((a + hi' - hi : Nat) : Int)) = (base ≤ (a : Int)) from
    propext (by omega)]

theorem objBase_mv (varp argp hi hi' : Nat) (off : Int) (h1 : hi ≤ varp + hi') (h2 : hi ≤ argp + hi') :
    objBase (varp + hi' - hi) (argp + hi' - hi) off = objBase varp argp off + hi' - hi := by
  simp only [objBase]; split <;> omega

/-- **The classification is relocation invariant**: a moved frame, at the moved address,
classifies like the frame. -/
theorem frameCls_mv (A : Arch) (FT : FrameTable) {pc sp fp : Nat} (a hi hi' : Nat) (h : sp ≤ fp)
    (h16 : 16 ≤ fp) (hs : 16 + hi ≤ sp + hi') (ha : hi ≤ a + hi') :
    frameCls A FT pc (sp + hi' - hi) (fp + hi' - hi) (a + hi' - hi) = frameCls A FT pc sp fp a := by
  have hv := A.varp_mv (hi := hi) (hi' := hi') h (by omega) (by omega) h16
  have hvl : fp ≤ A.varp sp fp + 16 := by cases A <;> simp only [Arch.varp] <;> split <;> omega
  have hag : fp ≤ A.argp fp := by cases A <;> simp only [Arch.argp] <;> omega
  simp only [frameCls, hv, A.argp_mv fp hi hi' (by omega)]
  have e1 : (((A.varp sp fp + hi' - hi : Nat) : Int) - 8 * ((FT.locals pc).length : Int)) =
      (((A.varp sp fp : Nat) : Int) - 8 * ((FT.locals pc).length : Int)) + hi' - hi := by omega
  rw [e1, bitsAt_mv _ _ _ _ _ ha,
    show ((A.argp fp + hi' - hi : Nat) : Int) = ((A.argp fp : Nat) : Int) + hi' - hi by omega,
    bitsAt_mv _ _ _ _ _ ha]
  have e2 : (A.argp fp + hi' - hi = A.varp sp fp + hi' - hi + 16) = (A.argp fp = A.varp sp fp + 16) :=
    propext (by omega)
  have e3 : (a + hi' - hi == A.varp sp fp + hi' - hi) = (a == A.varp sp fp) :=
    Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; omega)
  have e4 : (A.minLocals + (sp + hi' - hi) < A.varp sp fp + hi' - hi) = (A.minLocals + sp < A.varp sp fp) :=
    propext (by omega)
  simp only [e2, e3, e4]
  congr 1
  apply List.any_congr rfl
  intro o
  rw [objBase_mv _ _ _ _ _ (by omega) (by omega), bitsAt_mv _ _ _ _ _ ha]
  have e5 : (((sp + hi' - hi : Nat) : Int) ≤ objBase (A.varp sp fp) (A.argp fp) o.1 + hi' - hi) =
      ((sp : Int) ≤ objBase (A.varp sp fp) (A.argp fp) o.1) := propext (by omega)
  simp only [e5]

theorem framesCls_mv (A : Arch) (FT : FrameTable) (fs : List Frame) (a hi hi' : Nat)
    (h : ∀ f ∈ fs, f.sp ≤ f.fp ∧ 16 ≤ f.fp ∧ 16 + hi ≤ f.sp + hi') (ha : hi ≤ a + hi') :
    framesCls A FT (fs.map (Frame.mv hi hi')) (a + hi' - hi) = framesCls A FT fs a := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, framesCls_cons, Frame.mv]
    obtain ⟨h1, h2, h3⟩ := h f (List.mem_cons_self ..)
    rw [frameCls_mv A FT a hi hi' h1 h2 h3 ha, ih (fun f' hf' => h f' (List.mem_cons_of_mem _ hf'))]

theorem Arch.lrOf_mv (A : Arch) {m m' : Memory} {sp fp hi hi' : Nat} (lr0 : Option Nat)
    (h : sp ≤ fp) (h16 : 16 ≤ fp) (hs : 16 + hi ≤ sp + hi')
    (hslot : m'.readLE (A.lrSlot sp fp + hi' - hi) 8 = m.readLE (A.lrSlot sp fp) 8) :
    A.lrOf m' (sp + hi' - hi) (fp + hi' - hi) lr0 = A.lrOf m sp fp lr0 := by
  cases A <;> simp only [Arch.lrOf, Arch.lrSlot] at hslot ⊢
  · rw [hslot]; simp only [show (sp + hi' - hi < fp + hi' - hi) = (sp < fp) from propext (by omega)]
  · rw [show fp + hi' - hi - 8 = fp - 8 + hi' - hi by omega, hslot]

/-- **The walk is relocation invariant**: in memory whose return-address slots hold, at the
moved addresses, what they held, the walk from the moved frame is the moved walk. -/
theorem Chain.mv {A : Arch} {FT : FrameTable} {m m' : Memory} {hi pc sp : Nat}
    {lr0 : Option Nat} {fs : List Frame} (hi' : Nat) (h : Chain A FT m hi pc sp lr0 fs)
    (h16 : 16 ≤ sp) (hs : 16 + hi ≤ sp + hi')
    (hslot : ∀ f ∈ fs, FT.stop f.pc = false →
      m'.readLE (A.lrSlot f.sp f.fp + hi' - hi) 8 = m.readLE (A.lrSlot f.sp f.fp) 8) :
    Chain A FT m' hi' pc (sp + hi' - hi) lr0 (fs.map (Frame.mv hi hi')) := by
  induction h with
  | stop hv hs' hinj h8 hf =>
    rename_i pc sp lr0
    simp only [List.map_cons, List.map_nil, Frame.mv]
    rw [← A.fp_mv FT pc sp hi hi' (by omega)]
    exact .stop hv hs' hinj (by omega) (by rw [A.fp_mv FT pc sp hi hi' (by omega)]; omega)
  | cons hv hs' hinj h8 hf hc ih =>
    rename_i pc sp lr0 fs
    simp only [List.map_cons, Frame.mv]
    have hfp := A.le_fp FT pc sp
    rw [← A.fp_mv FT pc sp hi hi' (by omega)]
    have hl := A.lrOf_mv lr0 (m := m) (m' := m') (sp := sp) (fp := A.fp FT pc sp) (hi := hi) (hi' := hi')
      hfp (by omega) hs (hslot ⟨pc, sp, A.fp FT pc sp⟩ (List.mem_cons_self ..) hs')
    refine .cons hv hs' hinj (by omega) (by rw [A.fp_mv FT pc sp hi hi' (by omega)]; omega) ?_
    rw [A.fp_mv FT pc sp hi hi' (by omega), hl]
    exact ih (by omega) (by omega) (fun f hf hst => hslot f (List.mem_cons_of_mem _ hf) hst)

/-- The pclntab facts every Go binary's table has: frame sizes are multiples of 8. -/
def FrameTable.Aligned (FT : FrameTable) : Prop := ∀ pc, FT.spdelta pc % 8 = 0

theorem Chain.aligned {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat} {lr0 : Option Nat}
    {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) (hal : FT.Aligned) (hsp : sp % 8 = 0) :
    ∀ f ∈ fs, f.sp % 8 = 0 ∧ f.fp % 8 = 0 := by
  induction h with
  | stop =>
    rename_i pc sp _ _ _ _ _ _
    intro f hf; simp only [List.mem_singleton] at hf; subst hf
    have := hal pc
    exact ⟨hsp, by cases A <;> simp only [Arch.fp] <;> omega⟩
  | cons _ _ _ _ _ _ ih =>
    rename_i pc sp _ _ _ _ _ _ _ _
    have := hal pc
    have hfp : A.fp FT pc sp % 8 = 0 := by cases A <;> simp only [Arch.fp] <;> omega
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨hsp, hfp⟩
    · exact ih hfp f hf

/-- In a walk started without a link register (every frame but an arm64 innermost one), every
frame that does not stop the walk holds, in its return-address slot, a known pc: the next
frame's. -/
theorem Chain.slot_valid {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat}
    {fs : List Frame} (h : Chain A FT m hi pc sp none fs) :
    ∀ f ∈ fs, FT.stop f.pc = false → FT.valid (m.readLE (A.lrSlot f.sp f.fp) 8) = true := by
  generalize hl : (none : Option Nat) = lr0 at h
  induction h with
  | stop _ hs _ _ _ =>
    intro f hf hst; simp only [List.mem_singleton] at hf; subst hf; simp only at hst; rw [hs] at hst
    cases hst
  | cons hv hs _ _ hf hc ih =>
    rename_i pc sp lr0 fs
    subst hl
    intro f hmem hst
    rcases List.mem_cons.1 hmem with rfl | hmem
    · have hnext := hc.valid_head
      cases A <;> simp only [Arch.lrOf, Arch.lrSlot, Option.getD_none] at hnext ⊢
      · split at hnext <;> exact hnext
      · exact hnext
    · exact ih rfl f hmem hst

/-- A walk in the moved region, in the memory after a move, is the moved walk: its return-address
slots hold known pcs, which are outside the stack pools and so copied whatever the stack maps say
about the slot. -/
theorem Chain.moved {A : Arch} {FT : FrameTable} {cls : Nat → Bool} {pool ex : List (Nat × Nat)}
    {lo hi hi' base pc sp : Nat} {m m' : Memory} {fs : List Frame}
    (hm : Moved cls pool lo hi hi' base ex m m') (h : Chain A FT m hi pc sp none fs)
    (hcode : FT.CodeOutside pool) (hal : FT.Aligned) (hsp : sp % 8 = 0) (hb : base ≤ sp)
    (hex : ∀ f ∈ fs, FT.stop f.pc = false → Outside (A.lrSlot f.sp f.fp) 8 ex) :
    Chain A FT m' hi' pc (sp + hi' - hi) none (fs.map (Frame.mv hi hi')) := by
  obtain ⟨hg0, hg1, hg2, hg3⟩ := hm.grows
  have hbd := h.bounds
  have hall := h.aligned hal hsp
  refine Chain.mv hi' h (by omega) (by omega) fun f hf hst => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hbd f hf
  obtain ⟨a1, a2⟩ := hall f hf
  have hv := (hcode _ (h.slot_valid f hf hst)).1
  cases A
  · exact hm.readLE_word_out (by simp only [Arch.lrSlot]; omega) (by simp only [Arch.lrSlot]; omega)
      (by simp only [Arch.lrSlot]; omega) (hex f hf hst) hv
  · have : f.sp + 8 ≤ f.fp := by rw [h6]; simp only [Arch.fp]; omega
    exact hm.readLE_word_out (by simp only [Arch.lrSlot]; omega) (by simp only [Arch.lrSlot]; omega)
      (by simp only [Arch.lrSlot]; omega) (hex f hf hst) hv

/-- The classification of the moved walk, at moved addresses, is the walk's. -/
theorem Chain.framesCls_mv {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat}
    {lr0 : Option Nat} {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) {hi' a : Nat}
    (h16 : 16 ≤ sp) (hs : 16 + hi ≤ sp + hi') (ha : hi ≤ a + hi') :
    framesCls A FT (fs.map (Frame.mv hi hi')) (a + hi' - hi) = framesCls A FT fs a :=
  _root_.Janus.Spec.Stack.framesCls_mv A FT fs a hi hi' (fun f hf => by
    obtain ⟨h1, h2, -, -, -, -⟩ := h.bounds f hf; exact ⟨h2, by omega, by omega⟩) ha

/-- **The stack maps describe a frame's own words.** A frame's adjusted words (its saved frame
pointer, locals, arguments, stack objects) lie at or above its stack pointer. This holds for every
pclntab the Go linker writes (locals and stack objects are inside the frame, arguments above it),
and a theorem states it of the abstract table. -/
def FrameTable.InFrame (A : Arch) (FT : FrameTable) : Prop :=
  ∀ pc sp a, a < sp → frameCls A FT pc sp (A.fp FT pc sp) a = false

/-- A walk classifies nothing below its starting stack pointer. -/
theorem Chain.framesCls_below {A : Arch} {FT : FrameTable} {m : Memory} {hi pc sp : Nat}
    {lr0 : Option Nat} {fs : List Frame} (h : Chain A FT m hi pc sp lr0 fs) (hin : FT.InFrame A)
    {a : Nat} (ha : a < sp) : framesCls A FT fs a = false := by
  have hb := h.bounds
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [framesCls_cons, Bool.or_eq_false_iff]
    obtain ⟨h1, -, -, -, -, h6⟩ := hb f (List.mem_cons_self ..)
    refine ⟨?_, ?_⟩
    · rw [h6]; exact hin _ _ _ (by omega)
    · exact List.any_eq_false.2 fun f' hf' => by
        obtain ⟨h1', -, -, -, -, h6'⟩ := hb f' (List.mem_cons_of_mem _ hf')
        rw [h6']; simpa using hin f'.pc f'.sp a (by omega)

/-- A table with no pointer maps and no stack objects satisfies `InFrame` (the saved frame
pointer slot is never below the frame). -/
theorem FrameTable.inFrame_of_empty (A : Arch) (FT : FrameTable) (hal : FT.Aligned)
    (hl : ∀ pc, FT.locals pc = []) (ha : ∀ pc, FT.args pc = []) (ho : ∀ pc, FT.objs pc = []) :
    FT.InFrame A := by
  intro pc sp a h
  have hv : sp ≤ A.varp sp (A.fp FT pc sp) := by
    have := hal pc
    unfold Arch.varp Arch.fp
    cases A <;> dsimp only <;> split <;> omega
  have hne : a ≠ A.varp sp (A.fp FT pc sp) := by omega
  simp [frameCls, hl, ha, ho, bitsAt, hne]

/-! ## The binary's frame records (`janus extract --frames`)

`Extracted.frames` lists, for every extracted function, what the runtime reads about it from the
pclntab (decoded by `cmd/janus/frames.go`): its pc range, argument size, `FuncID` and flags, its
SP delta and stack-map index as pc-value runs, its argument and local pointer maps and its stack
objects. A stack-growth theorem assumes its frame table agrees with them (`FrameTable.Agrees`):
the stack maps a proof relies on are the binary's, re-derived by `janus check`. -/

/-- One function's frame record. A run `(limit, v)` of `pcsp`/`stackIdx` gives the value `v` for
the pcs below `limit` (and at or above the previous run's limit). -/
structure FuncRec where
  name : String
  entry : Nat
  size : Nat
  args : Int
  funcID : Nat
  flag : Nat
  maxspd : Nat
  pcsp : List (Nat × Int)
  stackIdx : List (Nat × Int)
  argMaps : List (List Bool)
  localMaps : List (List Bool)
  objs : List (Int × List Bool)

/-- The value of a pc-value table at `pc` (`-1` past its end, as `pcvalue` returns). -/
def runAt : List (Nat × Int) → Nat → Int
  | [], _ => -1
  | (l, v) :: rs, pc => if pc < l then v else runAt rs pc

/-- `funcspdelta(f, pc)`. -/
def FuncRec.spdeltaAt (r : FuncRec) (pc : Nat) : Nat := (runAt r.pcsp pc).toNat

/-- The stack map index `getStackMap` uses for a frame suspended at the continuation `pc`: the
index at `pc - 1`, the first map at the entry or where the table has none (`-1`). -/
def FuncRec.mapIdx (r : FuncRec) (pc : Nat) : Nat :=
  let i := if pc = r.entry then -1 else runAt r.stackIdx (pc - 1)
  if i < 0 then 0 else i.toNat

/-- The locals pointer map at the continuation `pc`. -/
def FuncRec.localsAt (r : FuncRec) (pc : Nat) : List Bool := r.localMaps.getD (r.mapIdx pc) []

/-- The arguments pointer map at the continuation `pc` (`argMapInternal`: none for a function
without stack arguments). -/
def FuncRec.argsAt (r : FuncRec) (pc : Nat) : List Bool :=
  if 8 ≤ r.args then r.argMaps.getD (r.mapIdx pc) [] else []

/-- `FuncFlagTopFrame` or `FuncFlagSPWrite`: the walk ends at this function. -/
def FuncRec.stop (r : FuncRec) : Bool := r.flag % 4 != 0

/-- `FuncID_asyncPreempt` (3), `FuncID_debugCallV2` (6), `FuncID_sigpanic` (20). -/
def FuncRec.injected (r : FuncRec) : Bool := r.funcID == 3 || r.funcID == 6 || r.funcID == 20

/-- **The frame table agrees with the binary's frame records** at every pc of every extracted
function. -/
def FrameTable.Agrees (FT : FrameTable) (rs : List FuncRec) : Prop :=
  ∀ r ∈ rs, ∀ pc, r.entry ≤ pc → pc < r.entry + r.size →
    FT.valid pc = true ∧ FT.entry pc = r.entry ∧ FT.spdelta pc = r.spdeltaAt pc ∧
    FT.maxspd pc = r.maxspd ∧ FT.stop pc = r.stop ∧ FT.injected pc = r.injected ∧
    FT.locals pc = r.localsAt pc ∧ FT.args pc = r.argsAt pc ∧ FT.objs pc = r.objs

/-- The frame table that is exactly the records (and knows nothing else): the witness tables of
the examples. -/
def FrameTable.ofRecs (rs : List FuncRec) (extra : FrameTable) : FrameTable :=
  let find (pc : Nat) := rs.find? (fun r => decide (r.entry ≤ pc ∧ pc < r.entry + r.size))
  { valid := fun pc => match find pc with | some _ => true | none => extra.valid pc
    entry := fun pc => match find pc with | some r => r.entry | none => extra.entry pc
    spdelta := fun pc => match find pc with | some r => r.spdeltaAt pc | none => extra.spdelta pc
    maxspd := fun pc => match find pc with | some r => r.maxspd | none => extra.maxspd pc
    stop := fun pc => match find pc with | some r => r.stop | none => extra.stop pc
    injected := fun pc => match find pc with | some r => r.injected | none => extra.injected pc
    locals := fun pc => match find pc with | some r => r.localsAt pc | none => extra.locals pc
    args := fun pc => match find pc with | some r => r.argsAt pc | none => extra.args pc
    objs := fun pc => match find pc with | some r => r.objs | none => extra.objs pc }

/-- `ofRecs` agrees with records whose pc ranges do not overlap. -/
theorem FrameTable.ofRecs_agrees (rs : List FuncRec) (extra : FrameTable)
    (hdisj : ∀ r ∈ rs, ∀ pc, r.entry ≤ pc → pc < r.entry + r.size →
      rs.find? (fun r' => decide (r'.entry ≤ pc ∧ pc < r'.entry + r'.size)) = some r) :
    (FrameTable.ofRecs rs extra).Agrees rs := by
  intro r hr pc h1 h2
  have := hdisj r hr pc h1 h2
  unfold FrameTable.ofRecs
  dsimp only
  rw [this]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Each field of `ofRecs` at `pc` is a record's or `extra`'s. -/
theorem FrameTable.ofRecs_spec (rs : List FuncRec) (extra : FrameTable) (pc : Nat) :
    (∃ r ∈ rs, (FrameTable.ofRecs rs extra).spdelta pc = r.spdeltaAt pc ∧
      (FrameTable.ofRecs rs extra).locals pc = r.localsAt pc ∧
      (FrameTable.ofRecs rs extra).args pc = r.argsAt pc ∧ (FrameTable.ofRecs rs extra).objs pc = r.objs) ∨
    ((FrameTable.ofRecs rs extra).spdelta pc = extra.spdelta pc ∧
      (FrameTable.ofRecs rs extra).locals pc = extra.locals pc ∧
      (FrameTable.ofRecs rs extra).args pc = extra.args pc ∧
      (FrameTable.ofRecs rs extra).objs pc = extra.objs pc) := by
  unfold FrameTable.ofRecs
  dsimp only
  cases h : rs.find? (fun r => decide (r.entry ≤ pc ∧ pc < r.entry + r.size)) with
  | none => right; exact ⟨rfl, rfl, rfl, rfl⟩
  | some r => left; exact ⟨r, List.mem_of_find?_eq_some h, rfl, rfl, rfl, rfl⟩

theorem runAt_mod8 {rs : List (Nat × Int)} (h : ∀ x ∈ rs, x.2.toNat % 8 = 0) (pc : Nat) :
    (runAt rs pc).toNat % 8 = 0 := by
  induction rs with
  | nil => rfl
  | cons x rs ih =>
    simp only [runAt]
    split
    · exact h x (List.mem_cons_self ..)
    · exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- A record whose maps mark nothing (every argument and local map empty or all-false: rendered
empty) and that has no stack objects. -/
def FuncRec.NoPtrs (r : FuncRec) : Prop :=
  (∀ m ∈ r.argMaps, m = []) ∧ (∀ m ∈ r.localMaps, m = []) ∧ r.objs = [] ∧
    ∀ x ∈ r.pcsp, x.2.toNat % 8 = 0

theorem FuncRec.NoPtrs.locals {r : FuncRec} (h : r.NoPtrs) (pc : Nat) : r.localsAt pc = [] := by
  unfold FuncRec.localsAt
  rw [List.getD_eq_getElem?_getD]
  cases hm : r.localMaps[r.mapIdx pc]? with
  | none => rfl
  | some m => exact h.2.1 m (List.mem_of_getElem? hm)

theorem FuncRec.NoPtrs.args {r : FuncRec} (h : r.NoPtrs) (pc : Nat) : r.argsAt pc = [] := by
  unfold FuncRec.argsAt
  split
  · rw [List.getD_eq_getElem?_getD]
    cases hm : r.argMaps[r.mapIdx pc]? with
    | none => rfl
    | some m => exact h.1 m (List.mem_of_getElem? hm)
  · rfl

/-- The table built from pointer-free records and an `extra` table without maps is aligned and
satisfies `InFrame`. -/
theorem FrameTable.ofRecs_laws (A : Arch) (rs : List FuncRec) (extra : FrameTable)
    (hr : ∀ r ∈ rs, r.NoPtrs) (hal : extra.Aligned) (hl : ∀ pc, extra.locals pc = [])
    (ha : ∀ pc, extra.args pc = []) (ho : ∀ pc, extra.objs pc = []) :
    (FrameTable.ofRecs rs extra).Aligned ∧ (FrameTable.ofRecs rs extra).InFrame A := by
  have hal' : (FrameTable.ofRecs rs extra).Aligned := by
    intro pc
    rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact runAt_mod8 (hr r hm).2.2.2 pc
    · rw [h1]; exact hal pc
  refine ⟨hal', FrameTable.inFrame_of_empty A _ hal' (fun pc => ?_) (fun pc => ?_) (fun pc => ?_)⟩
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, -, h2, -⟩ | ⟨-, h2, -⟩
    · rw [h2]; exact (hr r hm).locals pc
    · rw [h2]; exact hl pc
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, -, -, h3, -⟩ | ⟨-, -, h3, -⟩
    · rw [h3]; exact (hr r hm).args pc
    · rw [h3]; exact ha pc
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, -, -, -, h4⟩ | ⟨-, -, -, h4⟩
    · rw [h4]; exact (hr r hm).2.2.1
    · rw [h4]; exact ho pc

/-- **arm64 frames keep their words above their stack pointer**, for a table whose frames are
aligned, whose locals maps fit inside the frame whenever `getStackMap` reads them (a frame of at
most 24 bytes has its locals ignored: `varp - sp ≤ minLocals`), and which has no stack objects. -/
theorem FrameTable.inFrame_arm64 (FT : FrameTable) (hal : FT.Aligned)
    (hfit : ∀ pc, FT.spdelta pc ≤ 24 ∨ 8 * (FT.locals pc).length + 8 ≤ FT.spdelta pc)
    (ho : ∀ pc, FT.objs pc = []) : FT.InFrame Arch.arm64 := by
  intro pc sp a h
  have h8 := hal pc
  have hb : ∀ (b : Int) (bs : List Bool), (a : Int) < b → bitsAt b bs a = false := by
    intro b bs hlt; simp only [bitsAt]; rw [decide_eq_false (by omega)]; rfl
  have hfp : Arch.arm64.fp FT pc sp = sp + FT.spdelta pc := rfl
  have harg : Arch.arm64.argp (sp + FT.spdelta pc) = sp + FT.spdelta pc + 8 := rfl
  have hml : Arch.arm64.minLocals = 16 := rfl
  have ha : bitsAt ((sp + FT.spdelta pc + 8 : Nat) : Int) (FT.args pc) a = false := hb _ _ (by omega)
  by_cases hz : FT.spdelta pc = 0
  · have hv : Arch.arm64.varp sp (sp + FT.spdelta pc) = sp := by simp [Arch.varp, hz]
    simp only [frameCls, hfp, hv, harg, hml, ho, List.any_nil, Bool.or_false, ha]
    have e1 : (a == sp) = false := by simp; omega
    have e2 : decide (16 + sp < sp) = false := decide_eq_false (by omega)
    rw [e1, e2]; simp
  · have hv : Arch.arm64.varp sp (sp + FT.spdelta pc) = sp + FT.spdelta pc - 8 := by
      simp only [Arch.varp]; rw [if_pos (by omega)]
    simp only [frameCls, hfp, hv, harg, hml, ho, List.any_nil, Bool.or_false, ha]
    have e1 : (a == sp + FT.spdelta pc - 8) = false := by simp; omega
    rw [e1, Bool.and_false, Bool.false_or]
    rcases hfit pc with h1 | h1
    · rw [decide_eq_false (by omega)]; rfl
    · rw [hb (((sp + FT.spdelta pc - 8 : Nat) : Int) - 8 * ((FT.locals pc).length : Int)) _ (by omega),
        Bool.and_false]

/-- The longest locals map of a record. -/
def FuncRec.maxLocals (r : FuncRec) : Nat := r.localMaps.foldr (fun m n => max m.length n) 0

theorem FuncRec.length_localsAt (r : FuncRec) (pc : Nat) : (r.localsAt pc).length ≤ r.maxLocals := by
  unfold FuncRec.localsAt FuncRec.maxLocals
  rw [List.getD_eq_getElem?_getD]
  generalize r.mapIdx pc = i
  induction r.localMaps generalizing i with
  | nil => simp
  | cons m ms ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.getD_some, List.foldr_cons]; exact Nat.le_max_left _ _
    | succ i => simp only [List.getElem?_cons_succ, List.foldr_cons]; exact Nat.le_trans (ih i) (Nat.le_max_right _ _)

/-- A record's frames fit its locals maps and it has no stack objects (checked by evaluation on
the binary's record). -/
def FuncRec.Fits (r : FuncRec) : Prop :=
  r.objs = [] ∧ ∀ x ∈ r.pcsp, x.2.toNat % 8 = 0 ∧ (x.2.toNat ≤ 24 ∨ 8 * r.maxLocals + 8 ≤ x.2.toNat)

theorem runAt_mem {rs : List (Nat × Int)} (pc : Nat) : runAt rs pc = -1 ∨ ∃ x ∈ rs, runAt rs pc = x.2 := by
  induction rs with
  | nil => left; rfl
  | cons x rs ih =>
    simp only [runAt]
    split
    · right; exact ⟨x, List.mem_cons_self .., rfl⟩
    · rcases ih with h | ⟨y, hy, h⟩
      · left; exact h
      · right; exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

/-- The table built from fitting records and an `extra` table without frames or stack objects is
aligned and satisfies `InFrame` on arm64. -/
theorem FrameTable.ofRecs_laws_arm64 (rs : List FuncRec) (extra : FrameTable)
    (hr : ∀ r ∈ rs, r.Fits) (hsd : ∀ pc, extra.spdelta pc = 0) (ho : ∀ pc, extra.objs pc = []) :
    (FrameTable.ofRecs rs extra).Aligned ∧ (FrameTable.ofRecs rs extra).InFrame Arch.arm64 := by
  have hv : ∀ r ∈ rs, ∀ pc, r.spdeltaAt pc % 8 = 0 ∧
      (r.spdeltaAt pc ≤ 24 ∨ 8 * (r.localsAt pc).length + 8 ≤ r.spdeltaAt pc) := by
    intro r hm pc
    have hl' := r.length_localsAt pc
    unfold FuncRec.spdeltaAt
    rcases runAt_mem (rs := r.pcsp) pc with h | ⟨x, hx, h⟩
    · rw [h]; exact ⟨rfl, .inl (by decide)⟩
    · rw [h]
      obtain ⟨h1, h2⟩ := (hr r hm).2 x hx
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exact .inl h2
      · exact .inr (by omega)
  have hal' : (FrameTable.ofRecs rs extra).Aligned := by
    intro pc
    rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact (hv r hm pc).1
    · rw [h1, hsd]
  refine ⟨hal', FrameTable.inFrame_arm64 _ hal' (fun pc => ?_) (fun pc => ?_)⟩
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, h1, h2, -⟩ | ⟨h1, h2, -⟩
    · rw [h1, h2]; exact (hv r hm pc).2
    · rw [h1, hsd]; left; decide
  · rcases FrameTable.ofRecs_spec rs extra pc with ⟨r, hm, -, -, -, h4⟩ | ⟨-, -, -, h4⟩
    · rw [h4]; exact (hr r hm).1
    · rw [h4]; exact ho pc

end Janus.Spec.Stack
