import Janus.Tactic.Basic

/-!
# Read-only data (`Program.data`, `Program.DataLoaded`)

`dataRead p a n` is the little-endian value of the `n` bytes at `a` when they lie inside one data
segment of `p` (copied from `.rodata` by the extractor). Under `p.DataLoaded m` memory agrees with
it and the bytes are readable (`readLE_of_dataRead`, `accessible_of_dataRead`).

`janus_data h` (in `Janus.Tactic.Core`) turns `h : p.DataLoaded m` into hypotheses the symbolic
executor uses automatically: `m.accessible base len false = true` per data segment, and
`∀ a n, (dataRead p a n).isSome = true → m.readLE a n = dataReadD p a n`, whose side condition and
right-hand side are evaluated on literal addresses (by `decide` and the `reduceDataReadD` simproc).
-/

namespace Janus.Tactic

open Janus Janus.Arm64

/-- Little-endian value of a byte list. -/
def leOfBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leOfBytes bs

/-- The data segment containing `[a, a+n)`. -/
def dataSegAt (p : Program) (a n : Nat) : Option DataSegment :=
  p.data.find? fun d => decide (d.base ≤ a) && decide (a + n ≤ d.base + d.bytes.length)

/-- The `n`-byte little-endian value at `a` in the program's read-only data. -/
def dataRead (p : Program) (a n : Nat) : Option Nat :=
  (dataSegAt p a n).map fun d => leOfBytes ((d.bytes.drop (a - d.base)).take n)

/-- `dataRead` with a default, for use as a rewrite target. -/
def dataReadD (p : Program) (a n : Nat) : Nat := (dataRead p a n).getD 0

private theorem dataSegAt_spec {p : Program} {a n : Nat} {d : DataSegment}
    (h : dataSegAt p a n = some d) :
    d ∈ p.data ∧ d.base ≤ a ∧ a + n ≤ d.base + d.bytes.length := by
  unfold dataSegAt at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

private theorem readLE_eq_leOfBytes (m : Memory) (bs : List Nat) (a : Nat)
    (hb : ∀ i (h : i < bs.length), (m.bytes (a + i)).toNat = bs[i]) :
    m.readLE a bs.length = leOfBytes bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, Memory.readLE_succ, leOfBytes]
    have h0 := hb 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, ih (a + 1) (fun i hi => by
      have := hb (i + 1) (by simp; omega)
      rw [show a + (i + 1) = a + 1 + i by omega] at this
      simpa using this)]

theorem readLE_of_dataRead {p : Program} {m : Memory} (h : p.DataLoaded m) {a n v : Nat}
    (hv : dataRead p a n = some v) : m.readLE a n = v := by
  unfold dataRead at hv
  cases hd : dataSegAt p a n with
  | none => rw [hd] at hv; cases hv
  | some d =>
    rw [hd] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    obtain ⟨hmem, h1, h2⟩ := dataSegAt_spec hd
    obtain ⟨_, hbytes⟩ := h d hmem
    subst hv
    have hlen : ((d.bytes.drop (a - d.base)).take n).length = n := by
      simp; omega
    conv => lhs; rw [← hlen]
    apply readLE_eq_leOfBytes
    intro i hi
    have hi' : i < n := by rw [hlen] at hi; exact hi
    have := hbytes (a - d.base + i) (by omega)
    rw [show d.base + (a - d.base + i) = a + i by omega] at this
    rw [this]
    simp [List.getElem_take, List.getElem_drop]

theorem accessible_of_dataRead {p : Program} {m : Memory} (h : p.DataLoaded m) {a n : Nat}
    (hv : (dataRead p a n).isSome = true) : m.accessible a n false = true := by
  unfold dataRead at hv
  cases hd : dataSegAt p a n with
  | none => rw [hd] at hv; cases hv
  | some d =>
    obtain ⟨hmem, h1, h2⟩ := dataSegAt_spec hd
    obtain ⟨hreg, _⟩ := h d hmem
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
    obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, hw⟩, _⟩⟩ := hreg
    exact Memory.accessible_of_mem m hr (by omega) (by omega) hw

/-- The rewrite rule `janus_data` installs. -/
theorem readLE_dataReadD {p : Program} {m : Memory} (h : p.DataLoaded m) (a n : Nat)
    (hv : (dataRead p a n).isSome = true) : m.readLE a n = dataReadD p a n := by
  cases hd : dataRead p a n with
  | none => rw [hd] at hv; cases hv
  | some v => rw [readLE_of_dataRead h hd]; simp [dataReadD, hd]

/-- Each data segment is readable. -/
theorem accessible_of_dataLoaded {p : Program} {m : Memory} (h : p.DataLoaded m) (k : Nat)
    (hk : k < p.data.length) :
    m.accessible (p.data[k]).base (p.data[k]).bytes.length false = true := by
  obtain ⟨hreg, _⟩ := h _ (List.getElem_mem hk)
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
  obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, hw⟩, _⟩⟩ := hreg
  exact Memory.accessible_of_mem m hr hb he hw

/-- A writable range is disjoint from every read-only data object (whose bytes memory holds
read-only, `Program.DataLoaded`): a write needs every overlapping region to be writable. Used by
`janus_data hd [hw]`. -/
theorem disjoint_of_dataLoaded {p : Program} {m : Memory} (h : p.DataLoaded m) (k : Nat)
    (hk : k < p.data.length) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ (p.data[k]).base ∨ (p.data[k]).base + (p.data[k]).bytes.length ≤ a := by
  obtain ⟨hreg, _⟩ := h _ (List.getElem_mem hk)
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
  obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, _⟩, hro⟩⟩ := hreg
  simp only [Memory.accessible, Bool.and_eq_true, Bool.not_true, Bool.false_or,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  rcases hw.2 r hr with (h1 | h1) | h1
  · rw [hro] at h1; cases h1
  · omega
  · omega

/-- `disjoint_of_dataLoaded` with the object's bounds as literals, checked as Boolean facts (the
form `janus_data hd [hw]` produces, so the elaborator never unfolds the data list). -/
theorem disjoint_of_dataLoaded' {p : Program} {m : Memory} (h : p.DataLoaded m) (k : Nat)
    {base len : Nat}
    (hbl : (p.data[k]?.map (fun d => (d.base, d.bytes.length)) == some (base, len)) = true)
    {a n : Nat} (hw : m.accessible a n true = true) : a + n ≤ base ∨ base + len ≤ a := by
  simp only [beq_iff_eq, Option.map_eq_some_iff, Prod.mk.injEq] at hbl
  obtain ⟨d, hd, rfl, rfl⟩ := hbl
  have hk : k < p.data.length := (List.getElem?_eq_some_iff.mp hd).1
  have hdk : p.data[k] = d := (List.getElem?_eq_some_iff.mp hd).2
  have := disjoint_of_dataLoaded h k hk hw
  rw [hdk] at this
  exact this

end Janus.Tactic
