import Janus.Program
import Janus.Arm64.MemoryLemmas

/-!
# Writable globals: "holds its link-time initial value"

A Go package variable lives in a writable section: `.data` / `.noptrdata` when it has a constant
initialiser (`var karatsubaThreshold = 40`), `.bss` / `.noptrbss` when it is zero. Its contents at
a call are whatever the program stored there, so the extractor never copies them as `Program.data`.
`janus extract --global SYM` records the **link-time image** of the named symbols in
`Program.globals` (`GlobalSegment`: address, size and the file bytes, none for `.bss`), copied byte
for byte from the ELF file like read-only data, and `janus verify` re-extracts and compares it.

A theorem uses it in one of two ways (both ISAs; `Memory` is shared):

* `GlobalsInit Extracted.program.globals s.mem ["pkg.x", …]`: at the call, every named global
  holds exactly its link-time image, in one writable region below `2^48`. This is the state of a
  program that has not written the variable, typically a tuning constant such as math/big's
  `karatsubaThreshold`. **It is not the value after package initialisation** when that writes
  the variable: a variable set by an `init` function or by a non-constant initialiser
  (`internal/cpu.X86.HasADX`, `runtime.writeBarrier`) has the link-time image `0`, and its
  run-time value differs. For those, quantify instead.
* `GlobalIs Extracted.program.globals s.mem "pkg.x" v`: the global's bytes, read little-endian,
  are `v` (in one writable region below `2^48`). A theorem that takes `v` as a parameter holds for
  every value the program may have stored. `GlobalsInit.globalIs` specialises it to the image
  (`GlobalSegment.initVal`), so the initial-value theorem is a corollary.

**Satisfiability.** `globalsInit_image` proves that the predicate holds in the link-time image
itself (`globalsImage`: the globals' bytes in one writable region each, over any memory whose
regions do not clash with them), under a Boolean well-formedness check (`globalsImageOK`) that
`decide` evaluates. A witness theorem (`Proof.Witness.nonvacuous`) builds its call state on that
memory, so a statement that assumes `GlobalsInit` is never vacuous by accident: the names must be
globals of the extraction (`janus-audit` also rejects a name that is not, round 8 I1), and the
image is a model.
-/

namespace Janus.Spec

open Janus Janus.Arm64

/-- The global of `gs` named `n` (the first, if the name repeats). -/
def globalNamed (gs : List GlobalSegment) (n : String) : Option GlobalSegment :=
  gs.find? (·.name == n)

/-- The address of the global named `n` (`0` if there is none; `janus-audit` rejects a name that
is not a global of the extraction). -/
def globalAddr (gs : List GlobalSegment) (n : String) : Nat :=
  ((globalNamed gs n).map (·.base)).getD 0

/-- The little-endian value of `k` bytes of the image of `g` from offset `off` (each byte taken
modulo 256, as memory holds bytes). -/
def _root_.Janus.GlobalSegment.imageLE (g : GlobalSegment) (off : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => g.byte off % 256 + 256 * g.imageLE (off + 1) k

/-- The link-time value of the whole global, little-endian. -/
def _root_.Janus.GlobalSegment.initVal (g : GlobalSegment) : Nat := g.imageLE 0 g.size

/-- Memory `m` holds the link-time image of `g`: its `size` bytes lie in one writable region
below `2^48` (no read-only region overlaps them), and byte `i` is the image's. -/
def GlobalHolds (m : Memory) (g : GlobalSegment) : Prop :=
  m.accessible g.base g.size true = true ∧
    ∀ i, i < g.size → m.bytes (g.base + i) = BitVec.ofNat 8 (g.byte i)

/-- Every global named in `names` is a global of `gs` and holds its link-time image in `m`. -/
def GlobalsInit (gs : List GlobalSegment) (m : Memory) (names : List String) : Prop :=
  ∀ n ∈ names, ∃ g, globalNamed gs n = some g ∧ GlobalHolds m g

/-- The global named `n` holds the value `v`: its bytes, read little-endian, are `v`, in one
writable region below `2^48`. -/
def GlobalIs (gs : List GlobalSegment) (m : Memory) (n : String) (v : Nat) : Prop :=
  ∃ g, globalNamed gs n = some g ∧ m.accessible g.base g.size true = true ∧
    m.readLE g.base g.size = v

/-! ## Using the predicates -/

theorem GlobalHolds.readLE {m : Memory} {g : GlobalSegment} (h : GlobalHolds m g) :
    ∀ {off k : Nat}, off + k ≤ g.size → m.readLE (g.base + off) k = g.imageLE off k := by
  intro off k hk
  induction k generalizing off with
  | zero => rfl
  | succ k ih =>
    rw [Memory.readLE_succ, GlobalSegment.imageLE, h.2 off (by omega), BitVec.toNat_ofNat,
      show g.base + off + 1 = g.base + (off + 1) by omega, ih (by omega)]

theorem GlobalHolds.accessible {m : Memory} {g : GlobalSegment} (h : GlobalHolds m g)
    {off k : Nat} (hk : off + k ≤ g.size) (w : Bool) :
    m.accessible (g.base + off) k w = true :=
  Memory.accessible_sub m h.1 (Or.inr rfl) (by omega) (by omega)

theorem GlobalsInit.holds {gs : List GlobalSegment} {m : Memory} {names : List String}
    (h : GlobalsInit gs m names) {n : String} (hn : n ∈ names) {g : GlobalSegment}
    (hg : globalNamed gs n = some g) : GlobalHolds m g := by
  obtain ⟨g', hg', hh⟩ := h n hn
  rw [hg] at hg'
  cases hg'
  exact hh

/-- Fewer names: a weaker precondition. -/
theorem GlobalsInit.sub {gs : List GlobalSegment} {m : Memory} {names names' : List String}
    (h : GlobalsInit gs m names) (hs : ∀ n ∈ names', n ∈ names) : GlobalsInit gs m names' :=
  fun n hn => h n (hs n hn)

/-- A global holding its link-time image holds the value `initVal`: a theorem stated for every
value of the global (`GlobalIs`) applies to the initial one. -/
theorem GlobalsInit.globalIs {gs : List GlobalSegment} {m : Memory} {names : List String}
    (h : GlobalsInit gs m names) {n : String} (hn : n ∈ names) {g : GlobalSegment}
    (hg : globalNamed gs n = some g) : GlobalIs gs m n g.initVal := by
  have hh := h.holds hn hg
  refine ⟨g, hg, hh.1, ?_⟩
  have := hh.readLE (off := 0) (k := g.size) (by omega)
  simpa [GlobalSegment.initVal] using this

/-- What `GlobalIs` says once the global's record is known (`hg` is `rfl` for a literal
`Extracted.program.globals` and name). -/
theorem GlobalIs.elim {gs : List GlobalSegment} {m : Memory} {n : String} {v : Nat}
    {g : GlobalSegment} (h : GlobalIs gs m n v) (hg : globalNamed gs n = some g) :
    m.accessible g.base g.size true = true ∧ m.readLE g.base g.size = v := by
  obtain ⟨g', hg', h1, h2⟩ := h
  rw [hg] at hg'
  cases hg'
  exact ⟨h1, h2⟩

theorem GlobalIs.accessible {gs : List GlobalSegment} {m : Memory} {n : String} {v : Nat}
    {g : GlobalSegment} (h : GlobalIs gs m n v) (hg : globalNamed gs n = some g) (w : Bool) :
    m.accessible g.base g.size w = true :=
  Memory.accessible_sub m (h.elim hg).1 (Or.inr rfl) (Nat.le_refl _) (Nat.le_refl _)

theorem GlobalIs.readLE {gs : List GlobalSegment} {m : Memory} {n : String} {v : Nat}
    {g : GlobalSegment} (h : GlobalIs gs m n v) (hg : globalNamed gs n = some g) :
    m.readLE g.base g.size = v :=
  (h.elim hg).2

/-- The value of a global is less than `256 ^ size`. -/
theorem GlobalIs.lt {gs : List GlobalSegment} {m : Memory} {n : String} {v : Nat}
    {g : GlobalSegment} (h : GlobalIs gs m n v) (hg : globalNamed gs n = some g) :
    v < 256 ^ g.size := by
  rw [← h.readLE hg]; exact Memory.readLE_lt m _ _

theorem globalAddr_of {gs : List GlobalSegment} {n : String} {g : GlobalSegment}
    (hg : globalNamed gs n = some g) : globalAddr gs n = g.base := by
  simp [globalAddr, hg]

/-! ## Parts of a global, its raw image, and flags -/

/-- Bytes `[off, off + k)` of the global named `n`, read little-endian, are `v`; the whole global
lies in one writable region below `2^48`. For a field of a struct-typed variable
(`internal/cpu.X86.HasADX`, the `enabled` word of `runtime.writeBarrier`). -/
def GlobalBytesIs (gs : List GlobalSegment) (m : Memory) (n : String) (off k v : Nat) : Prop :=
  ∃ g, globalNamed gs n = some g ∧ off + k ≤ g.size ∧ m.accessible g.base g.size true = true ∧
    m.readLE (g.base + off) k = v

/-- The raw link-time image of the global named `n`: its `size` bytes as the ELF file holds them
(zeros for `.bss`), `[]` if there is no such global. A theorem can state the initial bytes with
it (`GlobalsInit` says memory holds exactly these bytes). -/
def globalImage (gs : List GlobalSegment) (n : String) : List Nat :=
  match globalNamed gs n with
  | some g => (List.range g.size).map g.byte
  | none => []

/-- The link-time value of the global named `n`, little-endian (`0` if there is none). -/
def globalInitVal (gs : List GlobalSegment) (n : String) : Nat :=
  match globalNamed gs n with
  | some g => g.initVal
  | none => 0

theorem GlobalBytesIs.elim {gs : List GlobalSegment} {m : Memory} {n : String} {off k v : Nat}
    {g : GlobalSegment} (h : GlobalBytesIs gs m n off k v) (hg : globalNamed gs n = some g) :
    off + k ≤ g.size ∧ m.accessible g.base g.size true = true ∧ m.readLE (g.base + off) k = v := by
  obtain ⟨g', hg', h1, h2, h3⟩ := h
  rw [hg] at hg'
  cases hg'
  exact ⟨h1, h2, h3⟩

/-- The field read with its own access width is accessible (for reading or writing). -/
theorem GlobalBytesIs.accessible {gs : List GlobalSegment} {m : Memory} {n : String}
    {off k v : Nat} {g : GlobalSegment} (h : GlobalBytesIs gs m n off k v)
    (hg : globalNamed gs n = some g) (w : Bool) : m.accessible (g.base + off) k w = true := by
  obtain ⟨h1, h2, -⟩ := h.elim hg
  exact Memory.accessible_sub m h2 (Or.inr rfl) (by omega) (by omega)

/-- The whole global is the field at offset 0 of its full size. -/
theorem GlobalIs.bytesIs {gs : List GlobalSegment} {m : Memory} {n : String} {v : Nat}
    {g : GlobalSegment} (h : GlobalIs gs m n v) (hg : globalNamed gs n = some g) :
    GlobalBytesIs gs m n 0 g.size v := by
  obtain ⟨h1, h2⟩ := h.elim hg
  exact ⟨g, hg, by omega, h1, by simpa using h2⟩

/-- Under `GlobalsInit`, every field of a named global holds its link-time bytes. -/
theorem GlobalsInit.bytesIs {gs : List GlobalSegment} {m : Memory} {names : List String}
    (h : GlobalsInit gs m names) {n : String} (hn : n ∈ names) {g : GlobalSegment}
    (hg : globalNamed gs n = some g) {off k : Nat} (hk : off + k ≤ g.size) :
    GlobalBytesIs gs m n off k (g.imageLE off k) :=
  ⟨g, hg, hk, (h.holds hn hg).1, (h.holds hn hg).readLE hk⟩

/-- Under `GlobalsInit`, memory holds the raw image `globalImage` byte for byte. -/
theorem GlobalsInit.image {gs : List GlobalSegment} {m : Memory} {names : List String}
    (h : GlobalsInit gs m names) {n : String} (hn : n ∈ names) {g : GlobalSegment}
    (hg : globalNamed gs n = some g) (i : Nat) (hi : i < g.size) :
    (m.bytes (g.base + i)).toNat = (globalImage gs n)[i]?.getD 0 % 256 := by
  rw [(h.holds hn hg).2 i hi]
  simp [globalImage, hg, hi]

/-- Both values of a flag (a `bool` global or field, one byte read as `0` / non-zero): a theorem
that holds for every value of a run-time flag such as `hasADX` is proved by one case per path,
each with the byte the code tests. -/
theorem GlobalBytesIs.flag_cases {gs : List GlobalSegment} {m : Memory} {n : String}
    {off v : Nat} {g : GlobalSegment} (h : GlobalBytesIs gs m n off 1 v)
    (hg : globalNamed gs n = some g) {Q : Prop}
    (h0 : m.readLE (g.base + off) 1 = 0 → v = 0 → Q)
    (h1 : m.readLE (g.base + off) 1 ≠ 0 → v ≠ 0 → v < 256 → Q) : Q := by
  obtain ⟨-, -, hr⟩ := h.elim hg
  by_cases hz : m.readLE (g.base + off) 1 = 0
  · exact h0 hz (hr ▸ hz)
  · exact h1 hz (hr ▸ hz) (hr ▸ Memory.readLE_lt m _ 1)

/-! ## Satisfiability: the link-time image -/

/-- The global of `gs` whose bytes contain address `a`, if any. -/
def globalAt (gs : List GlobalSegment) (a : Nat) : Option GlobalSegment :=
  gs.find? fun g => decide (g.base ≤ a ∧ a < g.base + g.size)

/-- The link-time image of the globals `gs` laid over memory `m`: each global's bytes at its
address and one writable region per global (before `m`'s regions); everything else is `m`'s. -/
def globalsImage (gs : List GlobalSegment) (m : Memory) : Memory :=
  { bytes := fun a => match globalAt gs a with
      | some g => BitVec.ofNat 8 (g.byte (a - g.base))
      | none => m.bytes a
    regions := gs.map (fun g => { base := g.base, size := g.size, writable := true }) ++ m.regions }

/-- The image is well formed: every global ends below `2^48`, two globals either do not overlap
or cover the same bytes with the same image (two names for one object, e.g. `math/big.natOne->8`
and `math/big.intOne->32+8->8`), and every region of `m` is writable or disjoint from every
global (so stores to a global are allowed). A Boolean, for `decide`. -/
def globalsImageOK (gs : List GlobalSegment) (m : Memory) : Bool :=
  gs.all fun g => decide (g.base + g.size ≤ 2 ^ 48) &&
    gs.all (fun g' => (g'.base == g.base && g'.size == g.size && g'.init == g.init) ||
      decide (g.base + g.size ≤ g'.base) || decide (g'.base + g'.size ≤ g.base)) &&
    m.regions.all fun r => r.writable || decide (g.base + g.size ≤ r.base) || decide (r.base + r.size ≤ g.base)

/-- The link-time image satisfies `GlobalsInit` for every list of names of globals of `gs`. -/
theorem globalsInit_image (gs : List GlobalSegment) (m : Memory) (names : List String)
    (hok : globalsImageOK gs m = true)
    (hn : names.all (fun n => (globalNamed gs n).isSome) = true) :
    GlobalsInit gs (globalsImage gs m) names := by
  intro n hmem
  have hsome := List.all_eq_true.1 hn n hmem
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨g, hg, ?_, ?_⟩
  all_goals have hgm : g ∈ gs := List.mem_of_find?_eq_some hg
  all_goals have hgok := List.all_eq_true.1 hok g hgm
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hgok
  all_goals obtain ⟨⟨hb, hdis⟩, hreg⟩ := hgok
  · refine (Memory.accessible_iff _ _ _ _).2 ⟨⟨{ base := g.base, size := g.size, writable := true },
      ?_, Nat.le_refl _, Nat.le_refl _, hb, Or.inr rfl⟩, fun _ r hr => ?_⟩
    · exact List.mem_append_left _ (List.mem_map.2 ⟨g, hgm, rfl⟩)
    · rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨g', _, rfl⟩ := List.mem_map.1 hr
        exact Or.inl rfl
      · rcases hreg r hr with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  · intro i hi
    have hex : (globalAt gs (g.base + i)).isSome := by
      unfold globalAt
      rw [List.find?_isSome]
      exact ⟨g, hgm, by simp; omega⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hex
    have hpy := List.find?_some hy
    have hym := List.mem_of_find?_eq_some hy
    simp only [decide_eq_true_eq] at hpy
    simp only [globalsImage, hy]
    rcases hdis y hym with (h | h) | h
    · simp only [beq_iff_eq] at h
      obtain ⟨⟨hb', -⟩, hi'⟩ := h
      simp [GlobalSegment.byte, hb', hi']
    · omega
    · omega

end Janus.Spec
