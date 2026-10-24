import Janus.Spec.Basic
import Janus.Tactic.Common

/-!
# Go maps, abstractly

A Go map value is a pointer to a runtime `internal/runtime/maps.Map` header (`nil` for a nil
map). This file gives the abstract view a theorem is stated in, and the **representation
interface** that connects it to memory. The runtime's Swiss-table layout (directories, tables,
groups, control words, `H2` tags) never appears here: theorems quantify over every
representation `M : MapModel K V` that satisfies the laws (`MapModel.Laws`) and the runtime
contracts (`Janus.Contracts.Map`), so they hold for the real runtime as soon as *some* such
representation describes it (see docs/RUNTIME-CONTRACTS.md, "Maps").

* `AMap K V := K → Option V`: the abstract map. `AMap.empty`, `AMap.set`, `AMap.erase`.
* `Keys f ks`: `ks` lists the keys of `f`, each exactly once (an iteration order). A map whose
  keys can be listed is finite; `Keys.perm` says any two listings are permutations of each other.
* `sumValues f ks`: the sum of the values of `f` in the order `ks`, as a natural number;
  `sumValues_keys` says it does not depend on the order.
* `MapModel K V`: an abstract representation: `Rep mem mp f` (the non-nil map at `mp`
  holds `f` in memory `mem`), `Iter mem it mp f ks` (the iterator at `it` over the map at `mp`
  still has to produce the keys `ks`, the current one first), `Typ t` (the type descriptor at
  `t` is the one this model is about, e.g. `map[uint64]uint64`), `Env mem g` (the runtime around
  the map is usable: allocator, `g`, zero value, ...), `priv` (the address ranges of the
  runtime's private memory, all map storage included) and `depth` (the stack bytes below `SP`
  a map runtime call may use).
* `IsMap M mem mp f`: `mp` is a Go map value holding `f`: `nil` with `f` empty, or `Rep`.
* `Agrees m m' rs`: `m'` has the same regions as `m` and the same bytes inside the ranges `rs`
  (so a representation that lives in `rs` is unaffected by the change from `m` to `m'`).
-/

namespace Janus.Spec.Map

open Janus Janus.Arm64

/-! ## The abstract map -/

/-- A Go map's contents: the value stored under each key, or `none`. -/
abbrev AMap (K V : Type) := K → Option V

/-- The empty map (also the contents of a nil map). -/
def AMap.empty {K V : Type} : AMap K V := fun _ => none

/-- `f` with `k` mapped to `v` (`m[k] = v`). -/
def AMap.set {K V : Type} [DecidableEq K] (f : AMap K V) (k : K) (v : V) : AMap K V :=
  fun k' => if k' = k then some v else f k'

/-- `f` without `k` (`delete(m, k)`). -/
def AMap.erase {K V : Type} [DecidableEq K] (f : AMap K V) (k : K) : AMap K V :=
  fun k' => if k' = k then none else f k'

@[simp] theorem AMap.empty_apply {K V : Type} (k : K) : (AMap.empty : AMap K V) k = none := rfl

@[simp] theorem AMap.set_same {K V : Type} [DecidableEq K] (f : AMap K V) (k : K) (v : V) :
    f.set k v k = some v := by simp [AMap.set]

@[simp] theorem AMap.erase_same {K V : Type} [DecidableEq K] (f : AMap K V) (k : K) :
    f.erase k k = none := by simp [AMap.erase]

theorem AMap.set_other {K V : Type} [DecidableEq K] (f : AMap K V) {k k' : K} (v : V)
    (h : k' ≠ k) : f.set k v k' = f k' := by simp [AMap.set, h]

theorem AMap.erase_other {K V : Type} [DecidableEq K] (f : AMap K V) {k k' : K}
    (h : k' ≠ k) : f.erase k k' = f k' := by simp [AMap.erase, h]

/-- `ks` lists every key of `f` exactly once: one possible iteration order of the map. -/
def Keys {K V : Type} (f : AMap K V) (ks : List K) : Prop :=
  ks.Nodup ∧ ∀ k, k ∈ ks ↔ (f k).isSome

/-- Any two listings of the keys are permutations of each other. -/
theorem Keys.perm {K V : Type} {f : AMap K V} {ks ks' : List K} (h : Keys f ks)
    (h' : Keys f ks') : ks.Perm ks' :=
  (List.perm_ext_iff_of_nodup h.1 h'.1).2 fun k => by rw [h.2, h'.2]

/-- The number of keys does not depend on the listing. -/
theorem Keys.length_eq {K V : Type} {f : AMap K V} {ks ks' : List K} (h : Keys f ks)
    (h' : Keys f ks') : ks.length = ks'.length := (h.perm h').length_eq

theorem keys_empty {K V : Type} : Keys (AMap.empty : AMap K V) [] :=
  ⟨List.nodup_nil, fun k => by simp⟩

theorem Keys.eq_nil_of_empty {K V : Type} {ks : List K} (h : Keys (AMap.empty : AMap K V) ks) :
    ks = [] := by
  cases ks with
  | nil => rfl
  | cons k _ => exact absurd ((h.2 k).1 (List.mem_cons_self ..)) (by simp)

/-- The sum of the values of `f` (missing keys count as `0`), taken in the order `ks`. -/
def sumValues {K : Type} (f : AMap K (BitVec 64)) (ks : List K) : Nat :=
  (ks.map fun k => ((f k).getD 0).toNat).sum

theorem sumValues_nil {K : Type} (f : AMap K (BitVec 64)) : sumValues f [] = 0 := rfl

theorem sumValues_cons {K : Type} (f : AMap K (BitVec 64)) (k : K) (ks : List K) :
    sumValues f (k :: ks) = ((f k).getD 0).toNat + sumValues f ks := rfl

theorem sumValues_append {K : Type} (f : AMap K (BitVec 64)) (ks ks' : List K) :
    sumValues f (ks ++ ks') = sumValues f ks + sumValues f ks' := by
  simp [sumValues, List.sum_append]

theorem natSum_perm {l l' : List Nat} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The sum of the values is the same for every iteration order. -/
theorem sumValues_perm {K : Type} (f : AMap K (BitVec 64)) {ks ks' : List K}
    (h : ks.Perm ks') : sumValues f ks = sumValues f ks' := natSum_perm (h.map _)

theorem sumValues_keys {K : Type} {f : AMap K (BitVec 64)} {ks ks' : List K} (h : Keys f ks)
    (h' : Keys f ks') : sumValues f ks = sumValues f ks' := sumValues_perm f (h.perm h')

/-! ## Memory ranges -/

/-- `m'` has the regions of `m` and the same bytes at every address inside the ranges `rs`. -/
def Agrees (m m' : Memory) (rs : List (Nat × Nat)) : Prop :=
  m'.regions = m.regions ∧ ∀ a, InRanges a 1 rs → m'.bytes a = m.bytes a

theorem Agrees.refl (m : Memory) (rs : List (Nat × Nat)) : Agrees m m rs := ⟨rfl, fun _ _ => rfl⟩

theorem Agrees.trans {m m' m'' : Memory} {rs : List (Nat × Nat)} (h : Agrees m m' rs)
    (h' : Agrees m' m'' rs) : Agrees m m'' rs :=
  ⟨h'.1.trans h.1, fun a ha => (h'.2 a ha).trans (h.2 a ha)⟩

theorem readLE_congr {m m' : Memory} : ∀ (n a : Nat),
    (∀ j, j < n → m'.bytes (a + j) = m.bytes (a + j)) → m'.readLE a n = m.readLE a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.readLE]
    have h0 : m'.bytes a = m.bytes a := h 0 (by omega)
    have h1 : m'.readLE (a + 1) n = m.readLE (a + 1) n :=
      readLE_congr n (a + 1) fun j hj => by
        have := h (j + 1) (by omega); rwa [show a + (j + 1) = a + 1 + j by omega] at this
    rw [h0, h1]

/-- Reads inside the ranges agree. -/
theorem Agrees.readLE {m m' : Memory} {rs : List (Nat × Nat)} (h : Agrees m m' rs) {a n : Nat}
    (hin : InRanges a n rs) : m'.readLE a n = m.readLE a n :=
  readLE_congr n a fun j hj => h.2 _ (by
    obtain ⟨r, hr, h1, h2⟩ := hin; exact ⟨r, hr, by omega, by omega⟩)

/-- What is accessible agrees (the regions are the same). -/
theorem Agrees.accessible {m m' : Memory} {rs : List (Nat × Nat)} (h : Agrees m m' rs) (a n : Nat)
    (w : Bool) : m'.accessible a n w = m.accessible a n w := by
  unfold Memory.accessible; rw [h.1]

/-- A store outside the ranges keeps them. -/
theorem Agrees.writeLE {m m' : Memory} {rs : List (Nat × Nat)} (h : Agrees m m' rs) {a n : Nat}
    (v : Nat) (ho : Outside a n rs) : Agrees m (m'.writeLE a n v) rs := by
  refine ⟨h.1, fun b hb => ?_⟩
  have hd : a + n ≤ b ∨ b + 1 ≤ a := by
    obtain ⟨r, hr, h1, h2⟩ := hb; have := MemFrame.outside_mem ho hr; omega
  have hn : ¬ (a ≤ b ∧ b < a + n) := by omega
  simp only [Memory.writeLE, hn, ite_false]
  exact h.2 b hb

theorem agrees_writeLE (m : Memory) {rs : List (Nat × Nat)} {a n : Nat} (v : Nat)
    (ho : Outside a n rs) : Agrees m (m.writeLE a n v) rs := (Agrees.refl m rs).writeLE v ho

/-- A frame that only changes memory outside `rs` (a `MemFrame` whose ranges avoid `rs`) keeps
`rs`. -/
theorem Agrees.of_memFrame {m m' : Memory} {rs ws : List (Nat × Nat)} (h : MemFrame m m' ws)
    (hreg : m'.regions = m.regions) (ho : ∀ a, InRanges a 1 rs → Outside a 1 ws) :
    Agrees m m' rs := by
  refine ⟨hreg, fun a ha => ?_⟩
  have := h.readLE a 1 (ho a ha)
  simp only [Memory.readLE] at this
  exact BitVec.eq_of_toNat_eq (by omega)

/-! ## The representation interface -/

/-- An abstract representation of Go maps with keys `K` and values `V` in memory. Theorems
quantify over every `MapModel`; only the laws and the runtime contracts constrain it. -/
structure MapModel (K V : Type) where
  /-- `Rep mem mp f`: in memory `mem`, the (non-nil) map whose header is at `mp` holds `f`. -/
  Rep : Memory → Nat → AMap K V → Prop
  /-- `Iter mem it mp f ks`: the iterator struct at `it`, iterating over the map at `mp`
  (holding `f`), still has to produce the keys `ks`, in this order, the current one first. -/
  Iter : Memory → Nat → Nat → AMap K V → List K → Prop
  /-- `Typ t`: `t` is the address of the runtime type descriptor (`abi.SwissMapType`) of the
  map type this model describes. -/
  Typ : Nat → Prop
  /-- `Env mem g`: the runtime around the maps is usable in `mem` by the goroutine `g`: its
  allocator can serve what a map operation needs (no out-of-memory), the zero value is zero,
  and so on. Abstract: it is only ever passed from a precondition to a contract. -/
  Env : Memory → W64 → Prop
  /-- The runtime's private memory, as ranges `[lo, hi)`: every map header, directory, table
  and group, the zero value, and whatever else the map runtime reads or writes besides the
  caller's stack. A theorem's precondition says the caller's own memory is outside it. -/
  priv : List (Nat × Nat)
  /-- How many bytes below `SP` a call into the map runtime may use for its frames. -/
  depth : Nat

/-- `mp` is a Go map value holding `f` in `mem`: a nil map (`mp = 0`) is empty; a non-nil one
is represented according to `M`. -/
def IsMap {K V : Type} (M : MapModel K V) (mem : Memory) (mp : Nat) (f : AMap K V) : Prop :=
  if mp = 0 then f = AMap.empty else M.Rep mem mp f

/-- The size of the runtime's iterator struct (`internal/runtime/maps.Iter`, Go 1.26) in
bytes; the compiler allocates and zeroes it in the frame of the function with the `range`. -/
def iterSize : Nat := 96

/-- What the compiled code of a `range` loop reads from the iterator struct at `it`, after
`mapIterStart`/`mapIterNext`: the key pointer at `it + 0` is `0` when the iteration is over;
otherwise it points to the current key `k`, and the element pointer at `it + 8` points to its
value `f k`. Both pointers point into the runtime's private memory. -/
def IterView {K : Type} (priv : List (Nat × Nat)) (keyBytes : Nat) (keyOf : Nat → K)
    (mem : Memory) (it : Nat) (f : AMap K (BitVec 64)) : List K → Prop
  | [] => mem.readLE it 8 = 0
  | k :: _ =>
    let kp := mem.readLE it 8
    let ep := mem.readLE (it + 8) 8
    kp ≠ 0 ∧ mem.accessible kp keyBytes false = true ∧ InRanges kp keyBytes priv ∧
      keyOf (mem.readLE kp keyBytes) = k ∧
      mem.accessible ep 8 false = true ∧ InRanges ep 8 priv ∧
      mem.readLE ep 8 = ((f k).getD 0).toNat

/-- The laws every representation satisfies (facts about the runtime's data layout, not about
any runtime function):

* `rep_frame`, `iter_frame`, `env_frame`: the representation lives in the private memory (and
  an iterator also in its own struct): changing memory elsewhere does not affect it;
* `len`: the first word of a map header is the number of entries (`Map.used`, which the
  compiler reads inline for `len(m)`), and the header is readable;
* `finite`: a represented map has finitely many keys. -/
structure MapModel.Laws {K V : Type} (M : MapModel K V) : Prop where
  rep_frame : ∀ m m' mp f, M.Rep m mp f → Agrees m m' M.priv → M.Rep m' mp f
  iter_frame : ∀ m m' it mp f ks, M.Iter m it mp f ks →
    Agrees m m' (M.priv ++ [(it, it + iterSize)]) → M.Iter m' it mp f ks
  env_frame : ∀ m m' g, M.Env m g → Agrees m m' M.priv → M.Env m' g
  len : ∀ m mp f, M.Rep m mp f → m.accessible mp 8 false = true ∧ mp + 8 ≤ 2 ^ 48 ∧
    ∀ ks, Keys f ks → m.readLE mp 8 = ks.length
  finite : ∀ m mp f, M.Rep m mp f → ∃ ks, Keys f ks

theorem isMap_nil {K V : Type} {M : MapModel K V} {mem : Memory} {f : AMap K V} :
    IsMap M mem 0 f ↔ f = AMap.empty := by simp [IsMap]

theorem isMap_of_ne {K V : Type} {M : MapModel K V} {mem : Memory} {mp : Nat} {f : AMap K V}
    (h : mp ≠ 0) : IsMap M mem mp f ↔ M.Rep mem mp f := by simp [IsMap, h]

theorem IsMap.frame {K V : Type} {M : MapModel K V} (hl : M.Laws) {m m' : Memory} {mp : Nat}
    {f : AMap K V} (h : IsMap M m mp f) (ha : Agrees m m' M.priv) : IsMap M m' mp f := by
  unfold IsMap at *
  split
  · next h0 => simpa [h0] using h
  · next h0 => exact hl.rep_frame _ _ _ _ (by simpa [h0] using h) ha

theorem IsMap.finite {K V : Type} {M : MapModel K V} (hl : M.Laws) {m : Memory} {mp : Nat}
    {f : AMap K V} (h : IsMap M m mp f) : ∃ ks, Keys f ks := by
  unfold IsMap at h
  split at h
  · exact ⟨[], h ▸ keys_empty⟩
  · exact hl.finite _ _ _ h

end Janus.Spec.Map
