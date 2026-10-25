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

/-- An abstract model of the Go 1.26 panic runtime (both ISAs use `Janus.Arm64.Memory`). A
theorem that mentions a runtime panic quantifies over every `P` satisfying `P.Laws`. -/
structure PanicRuntime where
  /-- The interface value a runtime panic of kind `k` carries: a non-nil `error`. One value per
  kind for the whole run. -/
  err : ErrKind → Eface
  /-- The runtime's private memory, as ranges: the type descriptors of the runtime error types,
  the goroutine's `_panic`/`_defer` chains, the deferpool. -/
  priv : List (Nat × Nat)
  /-- Stack bytes below `SP` a panic-runtime call may use. -/
  depth : Nat
  /-- The runtime around panics is usable in `m` (the error-type descriptors are in place, the
  goroutine's panic/defer chain is empty, …). -/
  Env : Memory → Prop
  /-- `Panicking m g v rp`: goroutine `g` has an active, unrecovered panic with value `v`, and the
  deferred call that panic is running returns to `rp` (a return point inside `runtime.gopanic`).
  Only the `gopanic` contract establishes it. -/
  Panicking : Memory → Nat → Eface → Nat → Prop
  /-- No panic is active on goroutine `g` (`g._panic == nil`): `recover()` returns `nil`. -/
  Calm : Memory → Nat → Prop
  /-- The current panic of goroutine `g` has been recovered (`_panic.recovered`). -/
  Recovered : Memory → Nat → Prop
  /-- `pc` lies in a compiler-generated wrapper function (`abi.FuncIDWrapper`), which `recover`
  skips when it looks for the deferred call. -/
  wrapper : Nat → Prop

/-- The laws of a panic-runtime model: the runtime-error values are genuine non-nil errors
living in `P.priv`. The data word is left free (the compiled code never reads it). -/
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
  /-- The panic state lives in `P.priv` too. -/
  panicking_frame : ∀ m m' g v rp, P.Panicking m g v rp → Map.Agrees m m' P.priv →
    P.Panicking m' g v rp
  calm_frame : ∀ m m' g, P.Calm m g → Map.Agrees m m' P.priv → P.Calm m' g
  recovered_frame : ∀ m m' g, P.Recovered m g → Map.Agrees m m' P.priv → P.Recovered m' g
  /-- A calm goroutine has no active panic. -/
  calm_not_panicking : ∀ m g v rp, P.Calm m g → ¬ P.Panicking m g v rp

/-- A `boundsError` value (`index out of range`, `slice bounds out of range`): the runtime error
of kind `bounds`. A specification of an out-of-range access says the call panics with this. -/
def PanicRuntime.boundsError (P : PanicRuntime) : Eface := P.err ErrKind.bounds

/-- The nil-pointer / invalid-memory error (`sigpanic` → `panicmem`). -/
def PanicRuntime.nilError (P : PanicRuntime) : Eface := P.err ErrKind.mem

/-- The divide-by-zero error. -/
def PanicRuntime.divideError (P : PanicRuntime) : Eface := P.err ErrKind.divide

end Janus.Spec
