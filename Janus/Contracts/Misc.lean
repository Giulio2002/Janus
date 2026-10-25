import Janus.Spec.Dynamic

/-!
# The runtime's data objects and CPU feature flags (both ISAs)

Compiled Go code reads a few runtime **variables** directly, without calling the runtime:

| Variable (Go 1.26) | Read by | Contents | Here |
| --- | --- | --- | --- |
| `runtime.staticuint64s` | `any(b)` for a byte or bool `b` (`walk/convert.go`): the data word is `&staticuint64s[b]` | `[256]uint64{0, 1, …, 255}` | `StaticUint64s`, from the extracted copy (`StaticUint64s.of_dataLoaded`) |
| `runtime.zeroVal` | `any(T{})` for a zero composite literal of at most 1024 bytes (`walk/order.go`); the map runtime's zero value | 1024 zero bytes | `ZeroVal` (stated) |
| `runtime.inf` | `runtime.complex128div` (`copysign(inf, c)`, `inf * …`) | `+∞` (`0x7FF0000000000000`) | `RuntimeInf` (stated) |
| `runtime.cgoAlwaysFalse` | every cgo wrapper (`if _Cgo_always_false { _Cgo_use(p) }`) | `false` | `CgoAlwaysFalse` (stated) |
| `runtime.x86HasPOPCNT`, `x86HasSSE41`, `x86HasFMA`, `x86HasAVX`, `arm64HasATOMICS` | the compiler's feature tests in front of `POPCNT`, `ROUNDSD`, `VFMADD231SD`, the AVX paths, `LDADDAL`/`CASAL` | what `CPUID` / `HWCAP` reported at start-up | `CpuFlag` (a hypothesis with the flag's value as a parameter) |

**How each one enters a theorem.**

* `staticuint64s` is in a read-only section of the Go 1.26 binary (`.rodata`), so the extractor
  copies it like every read-only object the code references (`Program.data`); a theorem assumes
  `Program.DataLoaded` as for any other constant, and `StaticUint64s.of_dataLoaded` turns the
  extracted bytes (checked against `staticuint64sBytes` by `decide`) into the table's meaning.
  Nothing about it is trusted beyond `DataLoaded`.
* The others live in writable sections (`.noptrbss`), so the binary does not fix their contents
  and the extractor does not copy them (`identity.json`, `skippedData`). A theorem states what it
  assumes about them as an explicit hypothesis on the call state's memory, at the address the
  code computes (recomputed from the extracted instruction words, as for every writable
  global). These are claims about the Go 1.26 runtime: `zeroVal` is never written (the runtime
  only reads it; Go code cannot write through an interface's data word); `inf` is set by the
  runtime's package initialiser (`var inf = float64frombits(0x7FF0000000000000)`), which runs
  before any user code, and never changed; `cgoAlwaysFalse` is never written (cgo relies on the
  compiler not knowing that).
* **CPU feature flags** are set once by `runtime.cpuinit` from `internal/cpu` (`CPUID`/`XGETBV`
  on amd64, `HWCAP` on arm64) before any user code runs, and never changed. A theorem about code
  that tests one does **not** pick a path: it takes the flag's value `b` as a parameter, assumes
  `CpuFlag m a b` and states its result for every `b` (or separately for each). The model
  executes every instruction it decodes, so a path that uses an instruction the CPU may lack is
  meaningful exactly under the runtime's promise that the flag is set only when the CPU has the
  feature (docs/SOUNDNESS.md, "CPU feature flags").

Every predicate is satisfiable (the `_satisfiable` theorems below): no hypothesis built from them
is contradictory by itself, and each example proves `Witness.nonvacuous` for its whole statement.
-/

namespace Janus.Contracts.Misc

open Janus Janus.Arm64 Janus.Spec Janus.Tactic

/-! ## `runtime.staticuint64s` -/

/-- The bytes of `runtime.staticuint64s`: the little-endian words `0, 1, …, 255`. -/
def staticuint64sBytes : List Nat := (List.range 256).flatMap fun i => [i, 0, 0, 0, 0, 0, 0, 0]

/-- The 2048 bytes at `a` are readable and hold `staticuint64s`: word `i` is `i`. -/
def StaticUint64s (m : Memory) (a : Nat) : Prop :=
  a + 2048 ≤ 2 ^ 48 ∧ m.accessible a 2048 false = true ∧ ∀ i, i < 256 → m.readLE (a + 8 * i) 8 = i

theorem staticuint64sBytes_length : staticuint64sBytes.length = 2048 := by decide +kernel

theorem staticuint64sBytes_word : ∀ i, i < 256 →
    leOfBytes ((staticuint64sBytes.drop (8 * i)).take 8) = i := by decide +kernel

/-- A loaded data object with the bytes of `staticuint64s` is the table. -/
theorem StaticUint64s.of_seg {m : Memory} {d : DataSegment} (h : SegLoaded m d)
    (hb : d.bytes = staticuint64sBytes) : StaticUint64s m d.base := by
  have hacc := h.accessible
  have h1 := h.1
  rw [hb, staticuint64sBytes_length] at hacc
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨r, -, ⟨⟨⟨-, h3⟩, h4⟩, -⟩⟩ := h1
  rw [hb, staticuint64sBytes_length] at h3
  refine ⟨by omega, hacc, fun i hi => ?_⟩
  rw [h.readLE (8 * i) 8 (by rw [hb, staticuint64sBytes_length]; omega), hb]
  exact staticuint64sBytes_word i hi

/-- The extracted `runtime.staticuint64s` is the table, when the program's data is loaded
(`h` is `Program.DataLoaded` of either ISA, which unfolds to this). -/
theorem StaticUint64s.of_loaded {ds : List DataSegment} {m : Memory} (h : ∀ d ∈ ds, SegLoaded m d)
    {d : DataSegment} (hd : dataNamed ds "runtime.staticuint64s" = some d)
    (hb : d.bytes = staticuint64sBytes) : StaticUint64s m (dataAddr ds "runtime.staticuint64s") := by
  have := StaticUint64s.of_seg (h d (dataNamed_mem hd)) hb
  simpa [dataAddr, hd] using this

/-- The box `&staticuint64s[b]` holds `b`. -/
theorem StaticUint64s.read {m : Memory} {a : Nat} (h : StaticUint64s m a) {b : Nat} (hb : b < 256) :
    m.readLE (a + 8 * b) 8 = b := h.2.2 b hb

/-- … and is readable. -/
theorem StaticUint64s.accessible {m : Memory} {a : Nat} (h : StaticUint64s m a) {b : Nat}
    (hb : b < 256) : m.accessible (a + 8 * b) 8 false = true :=
  Memory.accessible_mono _ h.2.1 (by omega) (by omega)

/-! ## `runtime.zeroVal` -/

/-- `abi.ZeroValSize`: the size of `runtime.zeroVal`. -/
def zeroValSize : Nat := 1024

/-- The `zeroValSize` bytes at `a` are readable and zero (`runtime.zeroVal`). -/
def ZeroVal (m : Memory) (a : Nat) : Prop :=
  a + zeroValSize ≤ 2 ^ 48 ∧ m.accessible a zeroValSize false = true ∧
    ∀ i, i < zeroValSize → (m.bytes (a + i)).toNat = 0

theorem readLE_of_zero {m : Memory} {a : Nat} :
    ∀ n, (∀ i, i < n → (m.bytes (a + i)).toNat = 0) → m.readLE a n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [Memory.readLE_succ]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0, readLE_of_zero (a := a + 1) n (fun i hi => by
      have := h (i + 1) (by omega); rwa [show a + (i + 1) = a + 1 + i by omega] at this)]

/-- Every read inside `zeroVal` returns `0`. -/
theorem ZeroVal.read {m : Memory} {a : Nat} (h : ZeroVal m a) {off n : Nat}
    (hn : off + n ≤ zeroValSize) : m.readLE (a + off) n = 0 :=
  readLE_of_zero n fun i hi => by
    have := h.2.2 (off + i) (by omega); rwa [show a + (off + i) = a + off + i by omega] at this

/-- … and is readable. -/
theorem ZeroVal.accessible {m : Memory} {a : Nat} (h : ZeroVal m a) {off n : Nat}
    (hn : off + n ≤ zeroValSize) : m.accessible (a + off) n false = true :=
  Memory.accessible_mono _ h.2.1 (by omega) (by omega)

/-! ## `runtime.inf` -/

/-- The encoding of `+∞` in binary64. -/
def infBits : Nat := 0x7FF0000000000000

/-- The 8 bytes at `a` are readable and hold `+∞` (`runtime.inf`, after the runtime's package
initialisation). -/
def RuntimeInf (m : Memory) (a : Nat) : Prop :=
  a + 8 ≤ 2 ^ 48 ∧ m.accessible a 8 false = true ∧ m.readLE a 8 = infBits

/-! ## `runtime.cgoAlwaysFalse` -/

/-- The byte at `a` is readable and `false` (`runtime.cgoAlwaysFalse`, cgo's
`_Cgo_always_false`). -/
def CgoAlwaysFalse (m : Memory) (a : Nat) : Prop :=
  a + 1 ≤ 2 ^ 48 ∧ m.accessible a 1 false = true ∧ m.readLE a 1 = 0

/-! ## CPU feature flags -/

/-- The Go `bool` at `a` (`runtime.x86HasPOPCNT`, …, `runtime.arm64HasATOMICS`) is readable and
holds `b`: `1` when the CPU has the feature, `0` when not. -/
def CpuFlag (m : Memory) (a : Nat) (b : Bool) : Prop :=
  a + 1 ≤ 2 ^ 48 ∧ m.accessible a 1 false = true ∧ m.readLE a 1 = if b then 1 else 0

theorem CpuFlag.read_true {m : Memory} {a : Nat} (h : CpuFlag m a true) : m.readLE a 1 = 1 := h.2.2
theorem CpuFlag.read_false {m : Memory} {a : Nat} (h : CpuFlag m a false) : m.readLE a 1 = 0 := h.2.2

/-! ## Satisfiability

Each predicate holds for some memory (here: one readable region holding the expected bytes),
so none of them is contradictory. The examples' `Witness.nonvacuous` theorems show the stronger
fact that a whole theorem's hypotheses hold together, at the addresses of the real binary. -/

/-- A memory with one read-only region `[a, a + n)` whose bytes are `f`. -/
def roMem (a n : Nat) (f : Nat → Nat) : Memory :=
  ⟨fun x => BitVec.ofNat 8 (f x), [⟨a, n, false⟩]⟩

theorem roMem_accessible (a n : Nat) (f : Nat → Nat) (h : a + n ≤ 2 ^ 48) :
    (roMem a n f).accessible a n false = true := by
  apply Memory.accessible_of_mem _ (r := ⟨a, n, false⟩) (by simp [roMem]) (Nat.le_refl _)
    (by simp) (by simpa using h)

theorem staticUint64s_satisfiable : ∃ m a, StaticUint64s m a := by
  refine ⟨roMem 0x10000 2048 fun x => if 0x10000 ≤ x ∧ (x - 0x10000) % 8 = 0 then (x - 0x10000) / 8 else 0,
    0x10000, by decide, roMem_accessible _ _ _ (by decide), ?_⟩
  intro i hi
  have : ∀ i, i < 256 → (roMem 0x10000 2048 fun x =>
      if 0x10000 ≤ x ∧ (x - 0x10000) % 8 = 0 then (x - 0x10000) / 8 else 0).readLE (0x10000 + 8 * i) 8 = i := by
    decide +kernel
  exact this i hi

theorem zeroVal_satisfiable : ∃ m a, ZeroVal m a :=
  ⟨roMem 0x10000 zeroValSize fun _ => 0, 0x10000, by decide,
    roMem_accessible _ _ _ (by decide), fun _ _ => by simp [roMem]⟩

theorem runtimeInf_satisfiable : ∃ m a, RuntimeInf m a :=
  ⟨roMem 0x10000 8 fun x => if x = 0x10007 then 0x7F else if x = 0x10006 then 0xF0 else 0, 0x10000,
    by decide, roMem_accessible _ _ _ (by decide), by decide⟩

theorem cgoAlwaysFalse_satisfiable : ∃ m a, CgoAlwaysFalse m a :=
  ⟨roMem 0x10000 1 fun _ => 0, 0x10000, by decide, roMem_accessible _ _ _ (by decide), by decide⟩

theorem cpuFlag_satisfiable (b : Bool) : ∃ m a, CpuFlag m a b :=
  ⟨roMem 0x10000 1 fun _ => if b then 1 else 0, 0x10000, by decide,
    roMem_accessible _ _ _ (by decide), by cases b <;> decide⟩

end Janus.Contracts.Misc
