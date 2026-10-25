import Janus.Spec.Map
import Janus.Spec.Dynamic

/-!
# Go type descriptors, itabs and the interface runtime, abstractly (Go 1.26)

The vocabulary of the interface runtime contracts (`Janus.Contracts.Iface`, arm64, and
`Janus.Contracts.IfaceAmd64`): the in-memory layout of the type metadata the compiled code and
the runtime read (`internal/abi`, Go 1.26, both 64-bit ISAs), and the **abstract model**
`IfaceModel` of what the runtime computes from it. Everything is ISA-independent (both ISAs use
`Janus.Arm64.Memory`).

## Layout (`internal/abi/type.go`, `iface.go`, `switch.go`)

| Object | Fields (byte offsets) |
| --- | --- |
| `abi.Type` (48 bytes) | `Size_` 0, `PtrBytes` 8, `Hash` 16 (`uint32`), `TFlag` 20 (`uint8`), `Align_` 21, `FieldAlign_` 22, `Kind_` 23, `Equal` 24 (func pointer), `GCData` 32, `Str` 40, `PtrToThis` 44 |
| `abi.InterfaceType` (80 bytes) | `Type` 0, `PkgPath` 48, `Methods` 56 (slice: pointer 56, length 64, capacity 72) |
| `abi.ITab` | `Inter` 0, `Type` 8, `Hash` 16 (`uint32`, a copy of `Type.Hash`), `Fun[k]` 24 + 8k |
| `abi.TypeAssert` (24 bytes) | `Cache` 0, `Inter` 8, `CanFail` 16 (`bool`) |
| `abi.TypeAssertCache` | `Mask` 0, entry `i` at 8 + 16i: `Typ`, `Itab` |
| `abi.InterfaceSwitch` | `Cache` 0, `NCases` 8, `Cases[i]` 16 + 8i |
| `abi.InterfaceSwitchCache` | `Mask` 0, entry `i` at 8 + 24i: `Typ`, `Case`, `Itab` |

`TFlag` bits: `TFlagUncommon` 1, `TFlagRegularMemory` 8 (equality and hashing may treat the value
as `Size_` plain bytes), `TFlagDirectIface` 32 (the value is stored directly in the data word of
an interface: pointer-shaped types).

An interface value is two words: the type word (`*abi.Type` for `any`, `*abi.ITab` otherwise;
`0` for a nil interface) and the data word (a pointer to the value, or the value itself for a
direct-interface type).

## The model

What the runtime *computes* from that metadata is not transcribed (method-set matching by name
and package path, `itabTable` probing, the hash tables of type-assertion caches, the generated
equality functions). A theorem quantifies over **every** `R : IfaceModel` satisfying the laws
`R.Laws`; only the laws and the contracts constrain it:

| Field | Meaning (Go 1.26 runtime) |
| --- | --- |
| `R.itab inter typ` | `getitab(inter, typ, true)`: `some tab` (the itab, `tab ≠ 0`) if `typ` implements the non-empty interface `inter`, `none` if not. A function: the runtime keeps one itab per pair for the whole execution (`itabTable` only grows) |
| `R.eq t m x y` | `t.Equal(x, y)`: whether the values of type `t` at `x` and `y` (in memory `m`) are equal |
| `R.Comparable t m x y` | comparing them neither panics (`t.Equal` is not nil, no uncomparable dynamic type inside) nor needs more than `R.depth` bytes of stack |
| `R.IsType t` | `t` is a type descriptor of the program (static or created by `reflect`) |
| `R.IsInter i` | `i` is the descriptor of a non-empty interface type |
| `R.Env m g` | the runtime is usable by the goroutine `g` in `m` (allocator room, `itabTable`, the `m`'s random state, …) |
| `R.priv` | the runtime's own memory, as ranges: heap arenas, `itabTable`, persistent allocations, `runtime.zeroVal`, `runtime.staticuint64s`, the empty caches, and every type descriptor, interface type and itab (also the read-only ones in `.rodata`) |
| `R.depth` | stack bytes below `SP` an interface runtime call may use |

The laws (`IfaceModel.Laws`) are facts about the runtime's data, not about a runtime function:
the environment lives in `R.priv` (`env_frame`); descriptors are readable, inside `R.priv`
(`type_desc`, `inter_desc`); an itab is never at address `0` (`itab_ne`); and, from
`TFlagRegularMemory`, equality of such types is equality of their `Size_` bytes (`regular`),
never panics, and a direct-interface type is always comparable (`direct`).

`StaticItabs R ds` is a separate hypothesis: every static itab `go:itab.<T>,<I>` among the
extracted data objects `ds` is the one `getitab` returns for its pair. True for a statically
linked Go 1.26 binary: the linker lists every reachable `go:itab.*` symbol in `runtime.itablink`
(`cmd/link/internal/ld/typelink.go`), `itabsinit` adds them all to `itabTable` at start-up before
any Go code runs, and `getitab` only creates an itab for a pair it does not find there.

## Caches

The compiled code of a type assertion to a non-empty interface and of a type switch with
interface cases probes a cache before calling the runtime (`cmd/compile/internal/ssagen`): from
`h = typ.Hash`, entry `h & Mask`, `h+1 & Mask`, … until an entry's `Typ` is the dynamic type (a
hit: use its `Itab`/`Case`) or `0` (a miss: call `runtime.typeAssert`/`runtime.interfaceSwitch`).
`TACacheOK`/`ISCacheOK` state what the runtime maintains (`buildTypeAssertCache`,
`buildInterfaceSwitchCache`): `Mask + 1` is a power of two, every used entry holds the runtime's
answer for its type, and at least one entry is empty, so every probe ends. A descriptor's cache
starts as `runtime.emptyTypeAssertCache` / `runtime.emptyInterfaceSwitchCache` (`Mask = 0` and
one empty entry: `TACacheOK.empty`, `ISCacheOK.empty`).
-/

namespace Janus.Spec.Type

open Janus Janus.Arm64 Janus.Spec.Map Janus.Tactic

/-! ## Layout -/

/-- `unsafe.Sizeof(abi.Type{})`. -/
def typeDescSize : Nat := 48
/-- `unsafe.Sizeof(abi.InterfaceType{})`. -/
def interDescSize : Nat := 80
/-- The fixed part of an `abi.ITab` (`Inter`, `Type`, `Hash`, padding, `Fun[0]`). -/
def itabSize : Nat := 32

/-- `TFlagUncommon`. -/
def tflagUncommon : Nat := 1
/-- `TFlagRegularMemory`. -/
def tflagRegularMemory : Nat := 8
/-- `TFlagDirectIface`. -/
def tflagDirectIface : Nat := 32

/-- `t.Size_`. -/
def tySize (m : Memory) (t : Nat) : Nat := m.readLE t 8
/-- `t.PtrBytes`. -/
def tyPtrBytes (m : Memory) (t : Nat) : Nat := m.readLE (t + 8) 8
/-- `t.Hash` (32 bits). -/
def tyHash (m : Memory) (t : Nat) : Nat := m.readLE (t + 16) 4
/-- `t.TFlag` (8 bits). -/
def tyTFlag (m : Memory) (t : Nat) : Nat := m.readLE (t + 20) 1
/-- `t.Kind_` (8 bits). -/
def tyKind (m : Memory) (t : Nat) : Nat := m.readLE (t + 23) 1
/-- `t.Equal` (a code address, `0` for an uncomparable type). -/
def tyEqual (m : Memory) (t : Nat) : Nat := m.readLE (t + 24) 8

/-- `t.IsDirectIface()`: `TFlag & TFlagDirectIface ≠ 0`. -/
def isDirectIface (m : Memory) (t : Nat) : Bool := (tyTFlag m t).testBit 5
/-- `t.TFlag & TFlagRegularMemory ≠ 0`. -/
def isRegularMemory (m : Memory) (t : Nat) : Bool := (tyTFlag m t).testBit 3

/-- `len(inter.Methods)` of an `abi.InterfaceType`. -/
def interMethods (m : Memory) (i : Nat) : Nat := m.readLE (i + 64) 8

/-- The itab at `tab` is readable and its `Inter` and `Type` words are `inter` and `typ`. -/
def ItabAt (priv : List (Nat × Nat)) (m : Memory) (tab inter typ : Nat) : Prop :=
  tab + itabSize ≤ 2 ^ 48 ∧ m.accessible tab itabSize false = true ∧ InRanges tab itabSize priv ∧
    m.readLE tab 8 = inter ∧ m.readLE (tab + 8) 8 = typ

/-! ## The model -/

/-- An abstract model of the interface runtime (see the module documentation). -/
structure IfaceModel where
  /-- `getitab(inter, typ, true)`: the itab of the pair, if `typ` implements `inter`. -/
  itab : Nat → Nat → Option Nat
  /-- `t.Equal(x, y)` on the values at `x` and `y` in memory `m`. -/
  eq : Nat → Memory → Nat → Nat → Bool
  /-- Comparing the values at `x` and `y` with `t.Equal` returns (no panic, stack within
  `depth`). -/
  Comparable : Nat → Memory → Nat → Nat → Prop
  /-- `t` is a type descriptor. -/
  IsType : Nat → Prop
  /-- `i` is the descriptor of a non-empty interface type. -/
  IsInter : Nat → Prop
  /-- The runtime is usable in `m` by the goroutine `g`. -/
  Env : Memory → W64 → Prop
  /-- The runtime's own memory. -/
  priv : List (Nat × Nat)
  /-- Stack bytes below `SP` an interface runtime call may use. -/
  depth : Nat

/-- The laws of the model (see the module documentation). -/
structure IfaceModel.Laws (R : IfaceModel) : Prop where
  env_frame : ∀ m m' g, R.Env m g → Agrees m m' R.priv → R.Env m' g
  type_desc : ∀ m g t, R.Env m g → R.IsType t →
    t ≠ 0 ∧ t + typeDescSize ≤ 2 ^ 48 ∧ m.accessible t typeDescSize false = true ∧
      InRanges t typeDescSize R.priv
  inter_desc : ∀ m g i, R.Env m g → R.IsInter i →
    R.IsType i ∧ i + interDescSize ≤ 2 ^ 48 ∧ m.accessible i interDescSize false = true ∧
      InRanges i interDescSize R.priv ∧ 0 < interMethods m i
  itab_ne : ∀ i t tab, R.itab i t = some tab → tab ≠ 0
  /-- A `TFlagRegularMemory` type that is not direct compares its `Size_` bytes. -/
  regular : ∀ m g t x y, R.Env m g → R.IsType t → isRegularMemory m t = true →
    isDirectIface m t = false →
    m.accessible x (tySize m t) false = true → m.accessible y (tySize m t) false = true →
    R.Comparable t m x y ∧ R.eq t m x y = (m.readLE x (tySize m t) == m.readLE y (tySize m t))
  /-- A `TFlagRegularMemory` direct-interface type (a pointer) is comparable. -/
  direct : ∀ m g t x y, R.Env m g → R.IsType t → isRegularMemory m t = true →
    isDirectIface m t = true → R.Comparable t m x y

/-- The data object `d` is a static itab (`go:itab.<T>,<I>`), with its `Inter` and `Type`
words. -/
def isItabName (name : String) : Bool := name.startsWith "go:itab."

/-- `getitab` returns the static itab of every pair the extracted data `ds` has a
`go:itab.*` object for (see the module documentation). -/
def StaticItabs (R : IfaceModel) (ds : List DataSegment) : Prop :=
  ∀ d ∈ ds, isItabName d.name = true → 16 ≤ d.bytes.length →
    R.itab (leOfBytes (d.bytes.take 8)) (leOfBytes ((d.bytes.drop 8).take 8)) = some d.base

/-- `StaticItabs` for the itab named `name`: its `Inter` and `Type` words (`dataWord`). -/
theorem StaticItabs.named {R : IfaceModel} {ds : List DataSegment} (h : StaticItabs R ds)
    {name : String} {d : DataSegment} (hd : dataNamed ds name = some d)
    (hn : isItabName name = true) (hl : 16 ≤ d.bytes.length) :
    R.itab (dataWord ds name 0 8) (dataWord ds name 8 8) = some (dataAddr ds name) := by
  have hmem := dataNamed_mem hd
  have hname := dataNamed_name hd
  have := h d hmem (by rw [hname]; exact hn) hl
  simpa [dataWord, dataAddr, hd] using this

/-! ## Interface switches: the runtime's answer -/

/-- `interfaceSwitch`'s answer for the dynamic type `t` and the cases `cs` (interface types):
the index of the first case `t` implements and its itab, else `(len cs, 0)`. -/
def switchCase (R : IfaceModel) (t : Nat) : List Nat → Nat × Nat
  | [] => (0, 0)
  | c :: cs => match R.itab c t with
    | some tab => (0, tab)
    | none => ((switchCase R t cs).1 + 1, (switchCase R t cs).2)

@[simp] theorem switchCase_nil (R : IfaceModel) (t : Nat) : switchCase R t [] = (0, 0) := rfl

theorem switchCase_cons (R : IfaceModel) (t c : Nat) (cs : List Nat) :
    switchCase R t (c :: cs) = match R.itab c t with
      | some tab => (0, tab)
      | none => ((switchCase R t cs).1 + 1, (switchCase R t cs).2) := rfl

/-- A one-case switch. -/
theorem switchCase_single (R : IfaceModel) (t c : Nat) :
    switchCase R t [c] = ((R.itab c t).isNone.toNat, (R.itab c t).getD 0) := by
  rw [switchCase_cons]; cases R.itab c t <;> rfl

/-! ## Caches -/

/-- Entry `i` of a type-assertion cache at `c`: its `Typ` word. -/
def taTyp (m : Memory) (c i : Nat) : Nat := m.readLE (c + 8 + 16 * i) 8
/-- Entry `i` of a type-assertion cache at `c`: its `Itab` word. -/
def taItab (m : Memory) (c i : Nat) : Nat := m.readLE (c + 16 + 16 * i) 8

/-- The type-assertion cache at `c` for the interface `inter` is well formed (see the module
documentation): `Mask = 2^k - 1`, every entry readable and in the runtime's memory, every used
entry holding `getitab`'s answer for its type (`0` if the type does not implement `inter`), and
at least one entry empty. -/
def TACacheOK (R : IfaceModel) (m : Memory) (c inter : Nat) : Prop :=
  ∃ k, m.readLE c 8 = 2 ^ k - 1 ∧ c + 8 + 16 * 2 ^ k ≤ 2 ^ 48 ∧
    m.accessible c (8 + 16 * 2 ^ k) false = true ∧ InRanges c (8 + 16 * 2 ^ k) R.priv ∧
    (∀ i, i < 2 ^ k → taTyp m c i ≠ 0 → taItab m c i = (R.itab inter (taTyp m c i)).getD 0) ∧
    ∃ i, i < 2 ^ k ∧ taTyp m c i = 0

/-- Entry `i` of an interface-switch cache at `c`: its `Typ` word. -/
def isTyp (m : Memory) (c i : Nat) : Nat := m.readLE (c + 8 + 24 * i) 8
/-- Entry `i` of an interface-switch cache at `c`: its `Case` word. -/
def isCase (m : Memory) (c i : Nat) : Nat := m.readLE (c + 16 + 24 * i) 8
/-- Entry `i` of an interface-switch cache at `c`: its `Itab` word. -/
def isItab (m : Memory) (c i : Nat) : Nat := m.readLE (c + 24 + 24 * i) 8

/-- The interface-switch cache at `c` for the cases `cs` is well formed: as `TACacheOK`, with
24-byte entries holding `interfaceSwitch`'s answer (`switchCase`). -/
def ISCacheOK (R : IfaceModel) (m : Memory) (c : Nat) (cs : List Nat) : Prop :=
  ∃ k, m.readLE c 8 = 2 ^ k - 1 ∧ c + 8 + 24 * 2 ^ k ≤ 2 ^ 48 ∧
    m.accessible c (8 + 24 * 2 ^ k) false = true ∧ InRanges c (8 + 24 * 2 ^ k) R.priv ∧
    (∀ i, i < 2 ^ k → isTyp m c i ≠ 0 →
      isCase m c i = (switchCase R (isTyp m c i) cs).1 ∧
      isItab m c i = (switchCase R (isTyp m c i) cs).2) ∧
    ∃ i, i < 2 ^ k ∧ isTyp m c i = 0

/-- An empty cache (`runtime.emptyTypeAssertCache`: `Mask = 0`, one entry with `Typ = 0`). -/
theorem TACacheOK.empty {R : IfaceModel} {m : Memory} {c inter : Nat} (hb : c + 24 ≤ 2 ^ 48)
    (ha : m.accessible c 24 false = true) (hin : InRanges c 24 R.priv)
    (h0 : m.readLE c 8 = 0) (h1 : m.readLE (c + 8) 8 = 0) : TACacheOK R m c inter :=
  ⟨0, by simpa using h0, by simpa using hb, by simpa using ha, by simpa using hin,
    fun i hi => by simp at hi; subst hi; simp [taTyp, h1],
    ⟨0, by decide, by simpa [taTyp] using h1⟩⟩

/-- An empty cache (`runtime.emptyInterfaceSwitchCache`: `Mask = 0`, one 24-byte entry with
`Typ = 0`). -/
theorem ISCacheOK.empty {R : IfaceModel} {m : Memory} {c : Nat} {cs : List Nat}
    (hb : c + 32 ≤ 2 ^ 48) (ha : m.accessible c 32 false = true) (hin : InRanges c 32 R.priv)
    (h0 : m.readLE c 8 = 0) (h1 : m.readLE (c + 8) 8 = 0) : ISCacheOK R m c cs :=
  ⟨0, by simpa using h0, by simpa using hb, by simpa using ha, by simpa using hin,
    fun i hi => by simp at hi; subst hi; simp [isTyp, h1],
    ⟨0, by decide, by simpa [isTyp] using h1⟩⟩

/-- The type-assertion descriptor at `d` (`abi.TypeAssert`): its `Cache` word. -/
def taCache (m : Memory) (d : Nat) : Nat := m.readLE d 8
/-- Its `Inter` word. -/
def taInter (m : Memory) (d : Nat) : Nat := m.readLE (d + 8) 8
/-- Its `CanFail` byte (`true`: the comma-ok form). -/
def taCanFail (m : Memory) (d : Nat) : Bool := m.readLE (d + 16) 1 != 0

/-- The type-assertion descriptor at `d` is usable: its 24 bytes readable, its `Cache` word
writable (the runtime replaces the cache), its `Inter` a non-empty interface type, its cache well
formed. -/
def TADescOK (R : IfaceModel) (m : Memory) (d : Nat) : Prop :=
  d + 24 ≤ 2 ^ 48 ∧ m.accessible d 24 false = true ∧ m.accessible d 8 true = true ∧
    R.IsInter (taInter m d) ∧ TACacheOK R m (taCache m d) (taInter m d)

/-- The interface-switch descriptor at `d` (`abi.InterfaceSwitch`) with the cases `cs`: readable,
its `Cache` word writable, `NCases = len cs`, `Cases[i] = cs[i]`, every case a non-empty
interface type, its cache well formed. -/
def ISDescOK (R : IfaceModel) (m : Memory) (d : Nat) (cs : List Nat) : Prop :=
  d + 16 + 8 * cs.length ≤ 2 ^ 48 ∧ m.accessible d (16 + 8 * cs.length) false = true ∧
    m.accessible d 8 true = true ∧ m.readLE (d + 8) 8 = cs.length ∧
    (∀ i (h : i < cs.length), m.readLE (d + 16 + 8 * i) 8 = cs[i]) ∧
    (∀ c ∈ cs, R.IsInter c) ∧ ISCacheOK R m (m.readLE d 8) cs

/-! ## Facts used by the cache probes -/

/-- `h & (2^k - 1)` is `h mod 2^k`. -/
theorem and_mask (h k : Nat) : h &&& (2 ^ k - 1) = h % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod h k

/-- One more probe step brings the probe index one step closer (cyclically) to the entry `j`
when the current index `h mod N` is not `j`: the measure of the probe loops. -/
theorem probe_dist (N j h : Nat) (hj : j < N) (hne : h % N ≠ j) :
    (j + N - (h + 1) % N) % N + 1 = (j + N - h % N) % N := by
  have hN : 0 < N := by omega
  have hr := Nat.mod_lt h hN
  have hs : (h + 1) % N = if h % N + 1 = N then 0 else h % N + 1 := by
    rw [Nat.add_mod]
    by_cases h1 : N = 1
    · subst h1; simp [Nat.mod_one]
    · rw [Nat.mod_eq_of_lt (show 1 < N by omega)]
      split
      · next he => rw [he, Nat.mod_self]
      · next he => exact Nat.mod_eq_of_lt (by omega)
  rw [hs]
  generalize h % N = r at *
  split
  · next he =>
    rw [show j + N - 0 = j + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj,
      show j + N - r = j + 1 by omega, Nat.mod_eq_of_lt (by omega)]
  · next he =>
    by_cases hlt : j < r
    · rw [Nat.mod_eq_of_lt (show j + N - (r + 1) < N by omega),
        Nat.mod_eq_of_lt (show j + N - r < N by omega)]
      omega
    · rw [show j + N - (r + 1) = (j - (r + 1)) + N by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega), show j + N - r = (j - r) + N by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega

/-- The cache of a well-formed descriptor is well formed. -/
theorem TADescOK.cache {R : IfaceModel} {m : Memory} {d : Nat} (h : TADescOK R m d) :
    TACacheOK R m (taCache m d) (taInter m d) := h.2.2.2.2

end Janus.Spec.Type

namespace Janus.Spec.Type

open Janus Janus.Arm64 Janus.Spec.Map

/-! ## Comparisons that a frame does not affect -/

/-- Changing memory only inside the ranges `ws` does not change whether, or how, the values of
type `t` at `x` and `y` compare. A function that writes its own stack frame before it calls
`efaceeq` needs this for its result to be the comparison of the values at its entry; it holds
whenever the values are not in that frame (`EqFrame.of_regular` for `TFlagRegularMemory`
types). -/
def EqFrame (R : IfaceModel) (t : Nat) (m : Memory) (x y : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ m', MemFrame m m' ws →
    (R.Comparable t m x y → R.Comparable t m' x y) ∧ R.eq t m' x y = R.eq t m x y ∧
      isDirectIface m' t = isDirectIface m t

theorem agrees_of_memFrame_outside {m m' : Memory} {ws rs : List (Nat × Nat)} (h : MemFrame m m' ws)
    (hws : ∀ a n, InRanges a n rs → Outside a n ws) : Agrees m m' rs :=
  Agrees.of_memFrame h fun a ha => hws a 1 ha

/-- `EqFrame` for a `TFlagRegularMemory` type that is not direct, whose values are outside the
changed ranges `ws`, which are outside the runtime's memory. -/
theorem EqFrame.of_regular {R : IfaceModel} (hl : R.Laws) {m : Memory} {g : W64} {t x y : Nat}
    {ws : List (Nat × Nat)} (henv : R.Env m g) (ht : R.IsType t) (hreg : isRegularMemory m t = true)
    (hnd : isDirectIface m t = false)
    (hx : m.accessible x (tySize m t) false = true) (hy : m.accessible y (tySize m t) false = true)
    (hxo : Outside x (tySize m t) ws) (hyo : Outside y (tySize m t) ws)
    (hws : ∀ a n, InRanges a n R.priv → Outside a n ws) : EqFrame R t m x y ws := by
  intro m' hf
  have hag := agrees_of_memFrame_outside hf hws
  have henv' := hl.env_frame _ _ _ henv hag
  obtain ⟨-, -, -, hin⟩ := hl.type_desc m g t henv ht
  have hdesc : ∀ off n, off + n ≤ typeDescSize → m'.readLE (t + off) n = m.readLE (t + off) n :=
    fun off n hn => hag.readLE (InRanges.sub hin (by omega) (by omega))
  have hsz : tySize m' t = tySize m t := by
    simpa [tySize] using hdesc 0 8 (by simp [typeDescSize])
  have hfl : tyTFlag m' t = tyTFlag m t := hdesc 20 1 (by simp [typeDescSize])
  have hreg' : isRegularMemory m' t = true := by simpa [isRegularMemory, hfl] using hreg
  have hnd' : isDirectIface m' t = false := by simpa [isDirectIface, hfl] using hnd
  have hx' : m'.accessible x (tySize m' t) false = true := by rw [hf.accessible, hsz]; exact hx
  have hy' : m'.accessible y (tySize m' t) false = true := by rw [hf.accessible, hsz]; exact hy
  obtain ⟨-, he⟩ := hl.regular m g t x y henv ht hreg hnd hx hy
  obtain ⟨hc', he'⟩ := hl.regular m' g t x y henv' ht hreg' hnd' hx' hy'
  refine ⟨fun _ => hc', ?_, by rw [hnd', hnd]⟩
  rw [he, he', hsz, hf.readLE _ _ hxo, hf.readLE _ _ hyo]

end Janus.Spec.Type

namespace Janus.Spec.Type

open Janus Janus.Arm64 Janus.Spec.Map

/-! ## Caches and descriptors under frames -/

/-- A cache lives in the runtime's memory: changes elsewhere keep it. -/
theorem TACacheOK.frame {R : IfaceModel} {m m' : Memory} {c inter : Nat} (h : TACacheOK R m c inter)
    (ha : Agrees m m' R.priv) : TACacheOK R m' c inter := by
  obtain ⟨k, hk, hb, hacc, hin, hent, j, hj, hj0⟩ := h
  have hrd : ∀ off n, off + n ≤ 8 + 16 * 2 ^ k → m'.readLE (c + off) n = m.readLE (c + off) n :=
    fun off n hn => ha.readLE (InRanges.sub hin (by omega) (by omega))
  have htyp : ∀ i, i < 2 ^ k → taTyp m' c i = taTyp m c i := fun i hi => by
    unfold taTyp; rw [show c + 8 + 16 * i = c + (8 + 16 * i) by omega]; exact hrd _ _ (by omega)
  have hitab : ∀ i, i < 2 ^ k → taItab m' c i = taItab m c i := fun i hi => by
    unfold taItab; rw [show c + 16 + 16 * i = c + (16 + 16 * i) by omega]; exact hrd _ _ (by omega)
  refine ⟨k, by simpa using (hrd 0 8 (by have := Nat.one_le_two_pow (n := k); omega)).trans hk,
    hb, by rw [ha.accessible]; exact hacc, hin, fun i hi hne => ?_, j, hj, by rw [htyp j hj]; exact hj0⟩
  rw [htyp i hi] at hne ⊢; rw [hitab i hi]; exact hent i hi hne

/-- An interface-switch cache lives in the runtime's memory: changes elsewhere keep it. -/
theorem ISCacheOK.frame {R : IfaceModel} {m m' : Memory} {c : Nat} {cs : List Nat}
    (h : ISCacheOK R m c cs) (ha : Agrees m m' R.priv) : ISCacheOK R m' c cs := by
  obtain ⟨k, hk, hb, hacc, hin, hent, j, hj, hj0⟩ := h
  have hrd : ∀ off n, off + n ≤ 8 + 24 * 2 ^ k → m'.readLE (c + off) n = m.readLE (c + off) n :=
    fun off n hn => ha.readLE (InRanges.sub hin (by omega) (by omega))
  have htyp : ∀ i, i < 2 ^ k → isTyp m' c i = isTyp m c i := fun i hi => by
    unfold isTyp; rw [show c + 8 + 24 * i = c + (8 + 24 * i) by omega]; exact hrd _ _ (by omega)
  have hcase : ∀ i, i < 2 ^ k → isCase m' c i = isCase m c i := fun i hi => by
    unfold isCase; rw [show c + 16 + 24 * i = c + (16 + 24 * i) by omega]; exact hrd _ _ (by omega)
  have hitab : ∀ i, i < 2 ^ k → isItab m' c i = isItab m c i := fun i hi => by
    unfold isItab; rw [show c + 24 + 24 * i = c + (24 + 24 * i) by omega]; exact hrd _ _ (by omega)
  refine ⟨k, by simpa using (hrd 0 8 (by have := Nat.one_le_two_pow (n := k); omega)).trans hk,
    hb, by rw [ha.accessible]; exact hacc, hin, fun i hi hne => ?_, j, hj, by rw [htyp j hj]; exact hj0⟩
  rw [htyp i hi] at hne ⊢; rw [hcase i hi, hitab i hi]; exact hent i hi hne

/-- A type-assertion descriptor outside the changed ranges `ws` (which avoid the runtime's
memory) stays well formed. -/
theorem TADescOK.frame {R : IfaceModel} {m m' : Memory} {d : Nat} {ws : List (Nat × Nat)}
    (h : TADescOK R m d) (hf : MemFrame m m' ws) (hd : Outside d 24 ws)
    (hws : ∀ a n, InRanges a n R.priv → Outside a n ws) : TADescOK R m' d := by
  obtain ⟨hb, hacc, hw, hi, hc⟩ := h
  have hci : taCache m' d = taCache m d := hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))
  have hii : taInter m' d = taInter m d := hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))
  refine ⟨hb, by rw [hf.accessible]; exact hacc, by rw [hf.accessible]; exact hw, by rw [hii]; exact hi, ?_⟩
  rw [hci, hii]; exact hc.frame (agrees_of_memFrame_outside hf hws)

/-- `taCanFail` of a descriptor outside the changed ranges. -/
theorem taCanFail_frame {m m' : Memory} {d : Nat} {ws : List (Nat × Nat)} (hf : MemFrame m m' ws)
    (hd : Outside d 24 ws) : taCanFail m' d = taCanFail m d := by
  unfold taCanFail; rw [hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))]

/-- `taInter` of a descriptor outside the changed ranges. -/
theorem taInter_frame {m m' : Memory} {d : Nat} {ws : List (Nat × Nat)} (hf : MemFrame m m' ws)
    (hd : Outside d 24 ws) : taInter m' d = taInter m d :=
  hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))

/-- An interface-switch descriptor outside the changed ranges stays well formed. -/
theorem ISDescOK.frame {R : IfaceModel} {m m' : Memory} {d : Nat} {cs : List Nat}
    {ws : List (Nat × Nat)} (h : ISDescOK R m d cs) (hf : MemFrame m m' ws)
    (hd : Outside d (16 + 8 * cs.length) ws)
    (hws : ∀ a n, InRanges a n R.priv → Outside a n ws) : ISDescOK R m' d cs := by
  obtain ⟨hb, hacc, hw, hn, hcs, hi, hc⟩ := h
  have hrd : ∀ off n, off + n ≤ 16 + 8 * cs.length → m'.readLE (d + off) n = m.readLE (d + off) n :=
    fun off n hn => hf.readLE _ _ (Outside.of_sub hd (by omega) (by omega))
  refine ⟨hb, by rw [hf.accessible]; exact hacc, by rw [hf.accessible]; exact hw,
    by rw [hrd 8 8 (by omega)]; exact hn, fun i hi => ?_, hi, ?_⟩
  · rw [show d + 16 + 8 * i = d + (16 + 8 * i) by omega, hrd _ _ (by omega),
      ← show d + 16 + 8 * i = d + (16 + 8 * i) by omega]; exact hcs i hi
  · have := hrd 0 8 (by omega); simp only [Nat.add_zero] at this
    rw [this]; exact hc.frame (agrees_of_memFrame_outside hf hws)

end Janus.Spec.Type

namespace Janus.Spec.Type

/-- The probe measure is `0` exactly at the target entry. -/
theorem probe_zero {N j r : Nat} (hj : j < N) (hr : r < N) (h : (j + N - r) % N = 0) : r = j := by
  by_cases hlt : r ≤ j
  · rw [show j + N - r = (j - r) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h; omega

/-- The probe measure is below the table size. -/
theorem probe_lt {N j r : Nat} (hN : 0 < N) : (j + N - r) % N < N := Nat.mod_lt _ hN

end Janus.Spec.Type
