import Janus.Spec.Basic
import Janus.Tactic.Data

/-!
# Dynamic calls: interface methods, method values and closures

A dynamic call (`BLR`/`BR` on arm64, `CALL reg` on amd64) jumps to a register value that the
code loaded from memory: an interface method from the interface's itab, a closure's function from
its funcval. Janus does not guess where it goes. A theorem **states** which code it reaches, as
hypotheses on the memory the call reads, and the symbolic executor then follows the call to that
code (and uses its `Summary`, or executes it), like a direct call. The printed statement shows
these assumptions.

Go's representations (Go 1.26, both ISAs, `internal/abi`):

* A non-empty interface value is two words `(tab, data)`: `tab` points to an `abi.ITab`
  (`Inter`, `Type`, `Hash`, then `Fun[k]` at offset `24 + 8k`: the code address of method `k` of
  the dynamic type, methods sorted by name), `data` to the value (or is the value, for
  pointer-shaped types). For a conversion the compiler can see, the itab is a static read-only
  object `go:itab.<T>,<I>` in `.rodata`; `janus extract --targets` copies it into
  `Program.data` (under that name) and copies the code of its methods.
* A func value is a pointer to a funcval: word 0 is the code address, the captured variables
  (or pointers to them, for variables the closure modifies) follow from offset 8. The call passes
  the funcval pointer in the closure context register (`X26` on arm64, `RDX` on amd64), from
  which the closure reads its variables. A method value `x.M` is a closure `T.M-fm` capturing
  `x`.

Vocabulary (all ISA-independent: both ISAs use `Janus.Arm64.Memory`):

* `ItabIs ds m tab name`: `tab` is the address of the static itab `name` among the extracted data
  objects `ds` (`Extracted.program.data`), and memory `m` holds that itab's bytes, read-only. So
  `Fun[k]` reads the method address copied from the binary.
* `FuncvalIs m fv fn`: the funcval at `fv` holds the code address `fn` (`segAddr p "pkg.F.func1"`).
* `ClosureCtx m fv vars`: the words after it hold the captured `vars`.

`janus_dyn h₁ h₂ …` (`Janus.Tactic.Dynamic`) turns such hypotheses into the equations the
executor uses (literal addresses and values).
-/

namespace Janus.Spec

open Janus Janus.Arm64 Janus.Tactic

/-! ## Data objects by name -/

/-- The extracted data object named `name`. -/
def dataNamed (ds : List DataSegment) (name : String) : Option DataSegment :=
  ds.find? (·.name == name)

/-- Its address (`0` if there is none). -/
def dataAddr (ds : List DataSegment) (name : String) : Nat :=
  ((dataNamed ds name).map (·.base)).getD 0

/-- Its length in bytes (`0` if there is none). -/
def dataLen (ds : List DataSegment) (name : String) : Nat :=
  ((dataNamed ds name).map (·.bytes.length)).getD 0

/-- The `n`-byte little-endian value at offset `off` of the object (`0` if there is none). -/
def dataWord (ds : List DataSegment) (name : String) (off n : Nat) : Nat :=
  ((dataNamed ds name).map fun d => leOfBytes ((d.bytes.drop off).take n)).getD 0

/-- Offset of `Fun[0]` in `abi.ITab` (after `Inter`, `Type`, `Hash` and padding). -/
def itabFunOffset : Nat := 24

/-- The code address in slot `Fun[k]` of the itab `name`, as copied from the binary. -/
def itabFun (ds : List DataSegment) (name : String) (k : Nat) : Nat :=
  dataWord ds name (itabFunOffset + 8 * k) 8

/-- Memory `m` holds the data object `d` at its address, in a read-only region below `2^48`
(the condition `Program.DataLoaded` states for every object). -/
def SegLoaded (m : Memory) (d : DataSegment) : Prop :=
  (m.regions.any fun r => r.base ≤ d.base && d.base + d.bytes.length ≤ r.base + r.size
      && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < d.bytes.length), (m.bytes (d.base + i)).toNat = d.bytes[i]

/-! ## The predicates -/

/-- The itab word `tab` of an interface value points to the static itab `name`
(`"go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"`: dynamic type
`*MulHasher`, interface `Hasher`) of the extracted data `ds`, and memory `m` holds its bytes
read-only. Its `Fun[k]` slot then holds the address of the dynamic type's method `k`
(`itabFun ds name k`, read from the binary). -/
def ItabIs (ds : List DataSegment) (m : Memory) (tab : W64) (name : String) : Prop :=
  ∃ d, dataNamed ds name = some d ∧ tab.toNat = d.base ∧ SegLoaded m d

/-- The funcval at `fv` is readable and its code word is `fn` (the function a call of this
func value runs). -/
def FuncvalIs (m : Memory) (fv : W64) (fn : Nat) : Prop :=
  m.accessible fv.toNat 8 false = true ∧ m.readLE fv.toNat 8 = fn

/-- The words after the code word of the funcval at `fv` are readable and hold `vars`, the
closure's captured variables in the compiler's order (a variable the closure modifies is
captured by reference: its word is a pointer). -/
def ClosureCtx (m : Memory) (fv : W64) (vars : List W64) : Prop :=
  m.accessible (fv.toNat + 8) (8 * vars.length) false = true ∧
    ∀ i (h : i < vars.length), m.readLE (fv.toNat + 8 + 8 * i) 8 = vars[i].toNat

/-! ## Lemmas -/

theorem dataNamed_mem {ds : List DataSegment} {name : String} {d : DataSegment}
    (h : dataNamed ds name = some d) : d ∈ ds := List.mem_of_find?_eq_some h

theorem dataNamed_name {ds : List DataSegment} {name : String} {d : DataSegment}
    (h : dataNamed ds name = some d) : d.name = name := by
  have := List.find?_some h
  simpa using this

private theorem readLE_eq_leOfBytes' (m : Memory) (bs : List Nat) (a : Nat)
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

/-- A read inside a loaded object returns its bytes. -/
theorem SegLoaded.readLE {m : Memory} {d : DataSegment} (h : SegLoaded m d) (off n : Nat)
    (hn : off + n ≤ d.bytes.length) :
    m.readLE (d.base + off) n = leOfBytes ((d.bytes.drop off).take n) := by
  have hlen : ((d.bytes.drop off).take n).length = n := by simp; omega
  conv => lhs; rw [← hlen]
  apply readLE_eq_leOfBytes'
  intro i hi
  have hi' : i < n := by rw [hlen] at hi; exact hi
  have := h.2 (off + i) (by omega)
  rw [show d.base + (off + i) = d.base + off + i by omega] at this
  rw [this]
  simp [List.getElem_take, List.getElem_drop]

/-- A loaded object is readable. -/
theorem SegLoaded.accessible {m : Memory} {d : DataSegment} (h : SegLoaded m d) :
    m.accessible d.base d.bytes.length false = true := by
  have h1 := h.1
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  obtain ⟨r, hr, ⟨⟨⟨h2, h3⟩, h4⟩, _⟩⟩ := h1
  exact Memory.accessible_of_mem m hr h2 h3 h4

/-- A loaded object (in a read-only region) is disjoint from every writable range. -/
theorem SegLoaded.disjoint_of_writable {m : Memory} {d : DataSegment} (h : SegLoaded m d)
    {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a := by
  have h1 := h.1
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  obtain ⟨r, hr, ⟨⟨⟨h2, h3⟩, _⟩, hro⟩⟩ := h1
  obtain ⟨_, hall⟩ := (Memory.accessible_iff m a n true).1 hw
  rcases hall rfl r hr with hrw | hd | hd
  · rw [hro] at hrw; cases hrw
  · omega
  · omega

/-- `Program.DataLoaded` (arm64) provides every object. -/
theorem SegLoaded.of_dataLoaded {p : Program} {m : Memory} (h : p.DataLoaded m) {d : DataSegment}
    (hd : d ∈ p.data) : SegLoaded m d := h d hd

/-- An itab named in `p.data` is loaded when all of `p.data` is. -/
theorem ItabIs.of_dataLoaded {p : Program} {m : Memory} {tab : W64} {name : String}
    (h : p.DataLoaded m) (hn : (dataNamed p.data name).isSome = true)
    (ht : tab.toNat = dataAddr p.data name) : ItabIs p.data m tab name := by
  cases hd : dataNamed p.data name with
  | none => rw [hd] at hn; cases hn
  | some d =>
    refine ⟨d, hd, ?_, SegLoaded.of_dataLoaded h (dataNamed_mem hd)⟩
    simp [ht, dataAddr, hd]

theorem ItabIs.toNat_eq {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) : tab.toNat = dataAddr ds name := by
  obtain ⟨d, hd, ht, _⟩ := h
  simp [dataAddr, hd, ht]

/-- The itab word, as the literal address of the itab (`hb` evaluates `dataAddr`). -/
theorem ItabIs.tab_lit {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    {base : Nat} (h : ItabIs ds m tab name) (hb : dataAddr ds name = base) :
    tab = BitVec.ofNat 64 base := by
  apply BitVec.eq_of_toNat_eq
  rw [h.toNat_eq, hb, BitVec.toNat_ofNat]
  have := BitVec.isLt tab
  rw [← hb, ← h.toNat_eq]
  exact (Nat.mod_eq_of_lt this).symm

/-- The itab is readable. -/
theorem ItabIs.accessible {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) :
    m.accessible (dataAddr ds name) (dataLen ds name) false = true := by
  obtain ⟨d, hd, _, hl⟩ := h
  simpa [dataAddr, dataLen, hd] using hl.accessible

/-- An `n`-byte read inside the itab returns the copied bytes. -/
theorem ItabIs.readLE {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) (off n : Nat) (hn : off + n ≤ dataLen ds name) :
    m.readLE (dataAddr ds name + off) n = dataWord ds name off n := by
  obtain ⟨d, hd, _, hl⟩ := h
  simp only [dataLen, dataAddr, dataWord, hd, Option.map_some, Option.getD_some] at hn ⊢
  exact hl.readLE off n hn

/-- Slot `Fun[k]`: the method address read from the binary. -/
theorem ItabIs.readFun {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) (k : Nat) (hk : itabFunOffset + 8 * k + 8 ≤ dataLen ds name) :
    m.readLE (tab.toNat + (itabFunOffset + 8 * k)) 8 = itabFun ds name k := by
  rw [h.toNat_eq]; exact h.readLE _ 8 hk

/-- `ItabIs.readLE` at literal addresses, for the tactic: `hb`, `hl`, `hv` are evaluations. -/
theorem ItabIs.readLE_lit {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) {base len a v : Nat} (off n : Nat) (hb : dataAddr ds name = base)
    (hl : dataLen ds name = len) (hn : off + n ≤ len) (ha : base + off = a)
    (hv : dataWord ds name off n = v) : m.readLE a n = v := by
  subst hb hl ha hv; exact h.readLE off n hn

theorem ItabIs.accessible_lit {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) {base len : Nat} (hb : dataAddr ds name = base)
    (hl : dataLen ds name = len) : m.accessible base len false = true := by
  subst hb hl; exact h.accessible

/-- The itab is disjoint from every writable range (it is in a read-only region). -/
theorem ItabIs.disjoint_lit {ds : List DataSegment} {m : Memory} {tab : W64} {name : String}
    (h : ItabIs ds m tab name) {base len a n : Nat} (hb : dataAddr ds name = base)
    (hl : dataLen ds name = len) (hw : m.accessible a n true = true) :
    a + n ≤ base ∨ base + len ≤ a := by
  subst hb hl
  obtain ⟨d, hd, _, hs⟩ := h
  simpa [dataAddr, dataLen, hd] using hs.disjoint_of_writable hw

theorem FuncvalIs.read_lit {m : Memory} {fv : W64} {fn v : Nat} (h : FuncvalIs m fv fn)
    (hv : fn = v) : m.readLE fv.toNat 8 = v := hv ▸ h.2

theorem FuncvalIs.accessible {m : Memory} {fv : W64} {fn : Nat} (h : FuncvalIs m fv fn) :
    m.accessible fv.toNat 8 false = true := h.1

theorem FuncvalIs.bound {m : Memory} {fv : W64} {fn : Nat} (h : FuncvalIs m fv fn) :
    fv.toNat + 8 ≤ 2 ^ 48 := Memory.accessible_bound m h.1

/-- Captured variable `i`, at the literal offset `c = 8 + 8 i`. -/
theorem ClosureCtx.read_lit {m : Memory} {fv : W64} {vars : List W64} (h : ClosureCtx m fv vars)
    (i : Nat) (hi : i < vars.length) {c : Nat} {v : W64} (hc : 8 + 8 * i = c) (hv : vars[i] = v) :
    m.readLE (fv.toNat + c) 8 = v.toNat := by
  subst hc hv; rw [← Nat.add_assoc]; exact h.2 i hi

theorem ClosureCtx.accessible_lit {m : Memory} {fv : W64} {vars : List W64}
    (h : ClosureCtx m fv vars) {n : Nat} (hn : 8 * vars.length = n) :
    m.accessible (fv.toNat + 8) n false = true := hn ▸ h.1

/-- A closure context whose variables are given by a list is a conjunction of reads. -/
theorem closureCtx_cons {m : Memory} {fv : W64} {v : W64} {vars : List W64}
    (h0 : m.accessible (fv.toNat + 8) (8 * (vars.length + 1)) false = true)
    (h1 : m.readLE (fv.toNat + 8) 8 = v.toNat)
    (hr : ∀ i (h : i < vars.length), m.readLE (fv.toNat + 8 + 8 * (i + 1)) 8 = vars[i].toNat) :
    ClosureCtx m fv (v :: vars) := by
  refine ⟨by simpa using h0, fun i hi => ?_⟩
  cases i with
  | zero => simpa using h1
  | succ i => simpa using hr i (by simp at hi; omega)

end Janus.Spec
