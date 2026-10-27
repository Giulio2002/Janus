import Janus.Eface
import Janus.Spec.Type

/-!
# Panics, `defer`, `recover`, abstractly (Go 1.26)

The ISA-independent vocabulary of the panic/defer/recover contracts
(`Janus.Contracts.Panic`, `Janus.Contracts.PanicAmd64`). The in-memory machinery is read from
`$GOROOT/src/runtime/panic.go` and `signal_unix.go` (Go 1.26): `_panic`/`_defer` records, the
open-coded defer bitmask + funcdata `FUNCDATA_OpenCodedDeferInfo`, `gopanic`, `gorecover`,
`deferproc`/`deferprocStack`/`deferprocat`/`deferrangefunc`, `deferreturn`, `panicrangestate`
and the signal handler's `sigpanic` (a memory fault or divide becomes a Go panic).

As with the map and interface runtime (`Janus.Spec.Map`, `Janus.Spec.Type`), what the runtime
*is* stays abstract: a theorem quantifies over **every** model `P : PanicRuntime` satisfying the
laws `P.Laws`; only the laws and the contracts (`Janus.Contracts.Panic`) constrain it. The
layout that the compiled code itself reads or writes (the panic value in the argument registers,
the open-coded `deferBits` byte and closure slots in the frame, the named result slots) is not
abstract — it is executed from the binary.

## Runtime error values

A runtime panic (`s[i]` out of range, `x/0`, a nil dereference, …) panics with a value of a
runtime type implementing `error` (`runtime.boundsError`, `errorString`, `runtime.PanicNilError`,
…). The compiled code never inspects it, so the model keeps it opaque: each kind of runtime
error is an `ErrKind`, and the model gives one interface value `P.err k` for it (a non-nil
`error`, i.e. its type word is non-zero and in the runtime's memory). This is exactly the
information a specification can use: "panics with a `runtime.Error` of kind `k`".
-/

namespace Janus.Spec

open Janus Janus.Arm64

/-- The kinds of runtime-error panic the Go 1.26 compiler and runtime raise (the panic values of
`runtime/panic.go` and the `sigpanic` cases of `signal_unix.go`). The data a `boundsError`
carries (the index and length) is not modelled: the compiled code never reads a panic value, so
a specification states only the kind. -/
inductive ErrKind where
  /-- `index out of range` / slice-bounds errors (`runtime.boundsError`, `abi.Bounds*`). -/
  | bounds
  /-- `integer divide by zero` (`runtime.divideError`). -/
  | divide
  /-- `negative shift amount` (`runtime.shiftError`). -/
  | shift
  /-- `integer overflow` (`runtime.overflowError`). -/
  | overflow
  /-- `floating point error` (`runtime.floatError`). -/
  | float
  /-- `invalid memory address or nil pointer dereference` (`runtime.memoryError`; `sigpanic`
  via `panicmem`). -/
  | mem
  /-- `out-of-range immediate for simd intrinsic` (`runtime.simdImmError`). -/
  | simdImm
  /-- An interface type assertion that failed (`runtime.panicdottype*`, `panicnildottype`:
  `*TypeAssertionError`). -/
  | dottype
  /-- `makeslice: len/cap out of range` (`runtime.panicmakeslice*`). -/
  | makeslice
  /-- `unsafe.Slice`/`unsafe.String` length or nil-pointer errors (`runtime.panicunsafe*`). -/
  | unsafeOp
  /-- A `panicwrap` (bad method-value receiver). -/
  | wrap
  /-- A range-over-func misuse (`runtime.panicrangestate`: `rangeDoneError` and friends). -/
  | rangeState
deriving DecidableEq, Repr, Inhabited

/-- The `ErrKind` a panic stub raises, by its linked runtime name (`runtime/panic.go`). `none`
for `runtime.gopanic` (which panics with the user's value, not a runtime error) and for stubs
that are not a single-kind runtime panic. -/
def panicStubErr : String → Option ErrKind
  | "runtime.goPanicIndex" | "runtime.goPanicIndexU"
  | "runtime.goPanicSliceAlen" | "runtime.goPanicSliceAlenU"
  | "runtime.goPanicSliceAcap" | "runtime.goPanicSliceAcapU"
  | "runtime.goPanicSliceB" | "runtime.goPanicSliceBU"
  | "runtime.goPanicSlice3Alen" | "runtime.goPanicSlice3AlenU"
  | "runtime.goPanicSlice3Acap" | "runtime.goPanicSlice3AcapU"
  | "runtime.goPanicSlice3B" | "runtime.goPanicSlice3BU"
  | "runtime.goPanicSlice3C" | "runtime.goPanicSlice3CU"
  | "runtime.goPanicSliceConvert"
  | "runtime.panicBounds" | "runtime.panicBounds64"
  | "runtime.panicBounds32" | "runtime.panicBounds32X" => some .bounds
  | "runtime.panicdivide" => some .divide
  | "runtime.panicshift" => some .shift
  | "runtime.panicoverflow" => some .overflow
  | "runtime.panicfloat" => some .float
  | "runtime.panicmem" | "runtime.panicmemAddr" => some .mem
  | "runtime.panicSimdImm" => some .simdImm
  | "runtime.panicdottypeE" | "runtime.panicdottypeI" | "runtime.panicnildottype" => some .dottype
  | "runtime.panicmakeslicelen" | "runtime.panicmakeslicecap" => some .makeslice
  | "runtime.panicunsafeslicelen" | "runtime.panicunsafeslicelen1"
  | "runtime.panicunsafeslicenilptr" | "runtime.panicunsafeslicenilptr1"
  | "runtime.panicunsafestringlen" | "runtime.panicunsafestringnilptr" => some .unsafeOp
  | "runtime.panicwrap" => some .wrap
  | "runtime.panicrangestate" => some .rangeState
  | _ => none

/-! ## The goroutine's panic and defer bookkeeping

The runtime keeps, per goroutine, a chain of `_panic` records (`g._panic`, linked by `p.link`:
the active panic first, then the panics it aborted) and a chain of `_defer` records (`g._defer`,
the most recent first). The model reads both as lists (`PanicRuntime.panics`, `.defers`); the
contracts say how each runtime call changes them. -/

/-- An entry of a goroutine's `_panic` chain (`runtime._panic`, Go 1.26). -/
structure PanicRec where
  /-- `p.arg`: the panic value (`⟨0, 0⟩` for a `Goexit`). -/
  arg : Eface
  /-- `p.goexit`: the entry is a `runtime.Goexit`, not a panic (`recover` returns `nil`). -/
  goexit : Bool := false
  /-- The stack pointer of the frame that started it (the caller of `gopanic`/`Goexit`). A
  recovery that resumes the frame at `SP = sp` drops every entry with `start ≤ sp`
  (`runtime.recovery`: `p.startSP < sp`). -/
  start : Nat
  /-- `p.recovered`: a `recover` stopped this panic. -/
  recovered : Bool := false
deriving DecidableEq, Repr

/-- A record of a goroutine's `_defer` chain (`runtime._defer`, Go 1.26): the stack pointer of
the frame it belongs to (`d.sp`), the funcvals it will call, in the order the runtime calls them
(one for a `deferproc`/`deferprocStack` record; for a range-over-func record, made by
`deferrangefunc` with `d.rangefunc` set, the calls the loop body added with `deferprocat`, most
recent first, which `deferconvert` turns into plain records), and, for a range-over-func record,
the token `deferrangefunc` returned (the data word of the `any`). -/
structure DeferRec where
  sp : Nat
  fns : List Nat
  token : Option Nat := none
deriving DecidableEq, Repr

/-- The records of the frame at `sp` that the runtime runs for it: the maximal prefix of the chain
whose records belong to `sp` (`nextDefer`: `d.sp == p.sp`). -/
def frameRecs (sp : Nat) (ds : List DeferRec) : List DeferRec := ds.takeWhile (·.sp == sp)

/-- The chain after the frame's records were run (`popDefer`). -/
def frameRest (sp : Nat) (ds : List DeferRec) : List DeferRec := ds.dropWhile (·.sp == sp)

/-- The funcvals the frame at `sp` runs from its records, in order. -/
def recFns (sp : Nat) (ds : List DeferRec) : List Nat := (frameRecs sp ds).flatMap (·.fns)

/-- The open-coded deferred calls pending in a `deferBits` byte `b`, as slot indices, in the
order the runtime calls them: highest bit first (`nextDefer`: `7 - LeadingZeros8(bits)`). -/
def openBits (b : Nat) : List Nat := [7, 6, 5, 4, 3, 2, 1, 0].filter (fun i => b.testBit i)

/-- The function metadata the panic runtime reads for a frame of an extracted function, from the
binary's `.gopclntab` (`janus extract` renders the list as `Extracted.funcs`): its entry and size,
its frame size (the pcsp value in its body: the frame's caller SP is `SP + frame`), the offset of
its `deferreturn` call (`_func.deferreturn`, `0` for none), and `FUNCDATA_OpenCodedDeferInfo`
(the offsets of the `deferBits` byte and of the first closure slot below the frame's `varp`). -/
structure FuncInfo where
  name : String
  entry : Nat
  size : Nat
  frame : Nat
  deferreturn : Nat
  openDefer : Option (Nat × Nat)
deriving DecidableEq, Repr, Inhabited

namespace FuncInfo

/-- The function of `T` whose code contains `pc` (`runtime.findfunc`). -/
def find (T : List FuncInfo) (pc : Nat) : Option FuncInfo :=
  T.find? (fun f => decide (f.entry ≤ pc ∧ pc < f.entry + f.size))

/-- The function of `T` named `name` (`default` if there is none). -/
def named (T : List FuncInfo) (name : String) : FuncInfo := (T.find? (·.name == name)).getD default

/-- The entry SP of the frame of `f` whose `SP` is `sp` (the caller's `SP` before the call; on
amd64 it points at the return address): `sp + frame`. A panic that runs every deferred call of the
frame and goes on to the caller has left the call whose entry SP this is. -/
def bound (f : FuncInfo) (sp : Nat) : Nat := sp + f.frame

/-- The frame's `varp` (`traceback.go`: `fp` minus the return-address word on amd64, minus the
saved frame pointer on both ISAs): `sp + frame - 8` on arm64 and amd64 alike. -/
def varp (f : FuncInfo) (sp : Nat) : Nat := sp + f.frame - 8

/-- The address of the frame's `deferBits` byte (`initOpenCodedDefers`: `varp - deferBitsOffset`). -/
def bitsAt (f : FuncInfo) (sp : Nat) : Nat := f.varp sp - ((f.openDefer.map (·.1)).getD 0)

/-- The address of the frame's first closure slot (`varp - slotsOffset`); slot `i` is 8 bytes per
index above it. -/
def slotsAt (f : FuncInfo) (sp : Nat) : Nat := f.varp sp - ((f.openDefer.map (·.2)).getD 0)

/-- Where `recovery` resumes the frame: its `deferreturn` call (`entry + _func.deferreturn`). -/
def resume (f : FuncInfo) : Nat := f.entry + f.deferreturn

end FuncInfo

/-- An abstract model of the Go 1.26 panic runtime (both ISAs use `Janus.Arm64.Memory`). A
theorem that mentions a runtime panic quantifies over every `P` satisfying `P.Laws`.

The goroutine's bookkeeping is read from memory as lists (`panics`, `defers`), with the state
`recovery` leaves for `deferreturn` (`saved`) and the runtime's capacity for further records
(`room`); all of it lives in the runtime's memory `P.priv` (`Laws`). -/
structure PanicRuntime where
  /-- The interface value a runtime panic of kind `k` carries: a non-nil `error`. One value per
  kind for the whole run. -/
  err : ErrKind → Eface
  /-- The runtime's private memory, as ranges: the type descriptors of the runtime error types,
  the goroutine's `_panic`/`_defer` bookkeeping, the deferpool. -/
  priv : List (Nat × Nat)
  /-- Stack bytes below `SP` a panic-runtime call may use. -/
  depth : Nat
  /-- The runtime around panics is usable in `m` (the error-type descriptors are in place, …). -/
  Env : Memory → Prop
  /-- Goroutine `g`'s `_panic` chain in `m`, the active entry first. -/
  panics : Memory → Nat → List PanicRec
  /-- Goroutine `g`'s `_defer` chain in `m`, the most recent record first. -/
  defers : Memory → Nat → List DeferRec
  /-- The open-coded defers a recovery left pending for `deferreturn` (`gp.param`'s
  `savedOpenDeferState`): the addresses of the frame's `deferBits` byte and first slot. -/
  saved : Memory → Nat → Option (Nat × Nat)
  /-- The return point (in `gopanic`/`Goexit`) of the deferred call the active panic is running:
  `recover` succeeds only in a function called directly from there. -/
  rp : Memory → Nat → Nat
  /-- How many more `_panic`/`_defer` records the runtime can take for goroutine `g` without
  failing (an allocation that would throw `out of memory`). A call that adds one needs
  `0 < room` and consumes at most one; the real runtime's stack-allocated `_panic` records and its
  deferpool leave this as large as the theorem needs. -/
  room : Memory → Nat → Nat
  /-- `pc` lies in a compiler-generated wrapper function (`abi.FuncIDWrapper`), which `recover`
  skips when it looks for the deferred call. -/
  wrapper : Nat → Prop

namespace PanicRuntime

variable (P : PanicRuntime)

/-- No panic or `Goexit` is active on goroutine `g` (`g._panic == nil`): `recover()` returns `nil`. -/
def Calm (m : Memory) (g : Nat) : Prop := P.panics m g = []

/-- Goroutine `g` has an active, unrecovered panic with value `v` (the top of its chain), and the
deferred call it is running returns to `rp` (a return point inside `runtime.gopanic`). -/
def Panicking (m : Memory) (g : Nat) (v : Eface) (rp : Nat) : Prop :=
  ∃ r rs, P.panics m g = r :: rs ∧ r.arg = v ∧ r.goexit = false ∧ r.recovered = false ∧ P.rp m g = rp

/-- The current panic of goroutine `g` has been recovered (`_panic.recovered`). -/
def Recovered (m : Memory) (g : Nat) : Prop := ∃ r rs, P.panics m g = r :: rs ∧ r.recovered = true

end PanicRuntime

/-- The laws of a panic-runtime model: the runtime-error values are genuine non-nil errors, and
the runtime's state lives in `P.priv`. The data word is left free (the compiled code never reads
it). -/
structure PanicRuntime.Laws (P : PanicRuntime) : Prop where
  /-- Every runtime-error value has a non-zero type word (a non-nil `error`). -/
  err_typ_ne : ∀ (k : ErrKind), (P.err k).typ ≠ 0
  /-- Distinct kinds have distinct error values (the runtime has one global per kind). -/
  err_inj : ∀ (k k' : ErrKind), P.err k = P.err k' → k = k'
  /-- A positive depth (the runtime uses the stack). -/
  depth_pos : 0 < P.depth
  /-- The environment lives in `P.priv`: memory changes elsewhere (with the same accessible
  ranges) keep it. -/
  env_frame : ∀ m m', P.Env m → Map.Agrees m m' P.priv → P.Env m'
  /-- The goroutine's bookkeeping lives in `P.priv` too. -/
  panics_frame : ∀ m m' g, Map.Agrees m m' P.priv → P.panics m' g = P.panics m g
  defers_frame : ∀ m m' g, Map.Agrees m m' P.priv → P.defers m' g = P.defers m g
  saved_frame : ∀ m m' g, Map.Agrees m m' P.priv → P.saved m' g = P.saved m g
  rp_frame : ∀ m m' g, Map.Agrees m m' P.priv → P.rp m' g = P.rp m g
  room_frame : ∀ m m' g, Map.Agrees m m' P.priv → P.room m' g = P.room m g

namespace PanicRuntime.Laws

variable {P : PanicRuntime} (hl : P.Laws)
include hl

theorem panicking_frame (m m' : Memory) (g : Nat) (v : Eface) (rp : Nat) (h : P.Panicking m g v rp)
    (ha : Map.Agrees m m' P.priv) : P.Panicking m' g v rp := by
  unfold PanicRuntime.Panicking at *; rw [hl.panics_frame m m' g ha, hl.rp_frame m m' g ha]; exact h

theorem calm_frame (m m' : Memory) (g : Nat) (h : P.Calm m g) (ha : Map.Agrees m m' P.priv) :
    P.Calm m' g := by
  unfold PanicRuntime.Calm at *; rw [hl.panics_frame m m' g ha]; exact h

theorem recovered_frame (m m' : Memory) (g : Nat) (h : P.Recovered m g)
    (ha : Map.Agrees m m' P.priv) : P.Recovered m' g := by
  unfold PanicRuntime.Recovered at *; rw [hl.panics_frame m m' g ha]; exact h

omit hl in
/-- A calm goroutine has no active panic. -/
theorem calm_not_panicking (m : Memory) (g : Nat) (v : Eface) (rp : Nat) (h : P.Calm m g) :
    ¬ P.Panicking m g v rp := by
  rintro ⟨r, rs, hp, -⟩; unfold PanicRuntime.Calm at h; rw [h] at hp; cases hp

end PanicRuntime.Laws

/-- A `boundsError` value (`index out of range`, `slice bounds out of range`): the runtime error
of kind `bounds`. A specification of an out-of-range access says the call panics with this. -/
def PanicRuntime.boundsError (P : PanicRuntime) : Eface := P.err ErrKind.bounds

/-- The nil-pointer / invalid-memory error (`sigpanic` → `panicmem`). -/
def PanicRuntime.nilError (P : PanicRuntime) : Eface := P.err ErrKind.mem

/-- The divide-by-zero error. -/
def PanicRuntime.divideError (P : PanicRuntime) : Eface := P.err ErrKind.divide

end Janus.Spec
