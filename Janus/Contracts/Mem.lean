import Janus.Contracts.Iface
import Janus.Float.Spec
import Janus.Arm64.FloatLemmas
import Janus.Tactic.Vector

/-!
# Contracts of the Go equality and typed-memory runtime (arm64)

Go 1.26 compares values with `runtime.memequal` (inline `==` on arrays and strings), with the
types' equality functions (`Type.Equal`, called by the map and interface runtime and by
compiler-generated `type:.eq.T` functions: `memequal0/8/16/32/64/128`, `memequal_varlen`,
`f32equal`, `f64equal`, `c64equal`, `c128equal`, `strequal`, `interequal`, `nilinterequal`), and
copies or clears memory that holds pointers with `typedmemmove`, `typedmemclr` and
`memclrHasPointers` (`runtime/alg.go`, `runtime/mbarrier.go`, `internal/bytealg/equal_arm64.s`).
A theorem about a function that calls one leaves it out (`janus extract --contract
runtime.memequal`, …) and takes its behaviour as a hypothesis: a `Summary` at its address whose
pre- and postcondition are the definitions below. See docs/RUNTIME-CONTRACTS.md, "Equality,
hashing and typed memory".

| Runtime function (Go 1.26) | Arguments (arm64) | Contract | Result |
| --- | --- | --- | --- |
| `memequal(a, b, n)` | `X0, X1, X2` | `Memequal` | the `n` bytes at `a` and `b` agree |
| `memequal0/8/16/32/64/128(a, b)` | `X0, X1` | `MemequalN 0/1/2/4/8/16` | the `k` bytes agree |
| `memequal_varlen(a, b)` | `X0, X1`, size at `8(X26)` | `MemequalVarlen` | as `memequal` with the closure's size |
| `f32equal`, `f64equal(a, b)` | `X0, X1` | `Fequal binary32 4`, `Fequal binary64 8` | `feq`: IEEE `==` (`NaN ≠ NaN`, `+0 = -0`) |
| `c64equal`, `c128equal(a, b)` | `X0, X1` | `Cequal binary32 4`, `Cequal binary64 8` | both parts `feq` |
| `strequal(a, b)` | `X0, X1` (pointers to string headers) | `Strequal` | equal lengths and bytes |
| `interequal`, `nilinterequal(a, b)` | `X0, X1` (pointers to interface values) | `Interequal`, `Nilinterequal` | equal first words and `ifaceeq`/`efaceeq` (`Janus.Contracts.Iface`) |
| `typedmemmove(typ, dst, src)` | `X0, X1, X2` | `TypedMemmove` | `dst` holds the `typ.Size_` bytes of `src` |
| `typedmemclr(typ, ptr)` | `X0, X1` | `TypedMemclr` | `typ.Size_` zero bytes at `ptr` |
| `memclrHasPointers(ptr, n)` | `X0, X1` | `MemclrHasPointers` | `n` zero bytes at `ptr` |

**The frame.** Each contract has a stack bound `d` (a parameter): the call returns to `X30` with
`SP`, `X18`, `X28` (`g`), `X29` and `FPCR` preserved, every other general register, the SIMD&FP
registers, the flags and `FPSR` (whose cumulative exception bits a comparison may set)
arbitrary, the memory regions unchanged, and bytes changed only in `[SP - d, SP - 8)` (never the
caller's frame-pointer slot), in the argument spill slots `[SP + 8, SP + 8 + 8·nargs)` and, for
the contracts over a model `M` (`MemModel`: the typed-memory functions) or `R` (`IfaceModel`:
`interequal`, `nilinterequal`), in the runtime's private memory; the typed-memory functions
also write their destination. The equality functions do not write runtime memory. Each
precondition requires the stack guard at least `d` bytes below `SP` (no stack growth), an
admissible `X30`, an aligned `SP` and the window `[SP - d, SP + 8 + 8·nargs)` writable
(`CallOK`), and the stack-guard word `16(g)` outside the callee's part of the window (a caller
that pushes its frame and calls on re-reads it); every input must be readable, below `2^48` and
outside the callee's part of the window (a callee writes its frame before reading its inputs).
`memequal` has no spill slots (`Memequal` is stated with `nargs = 0`): it is `NOFRAME` assembly
that writes no memory, and `strequal`/`memequal_varlen` call it without room for them. The floating-point contracts
require `FPCR = 0` (what Linux starts a process with and Go never changes: round to nearest, no
flushing, no traps).

**The write barrier.** `typedmemmove` and `typedmemclr` call `bulkBarrierPreWrite` when the
write barrier is on and the type has pointers; `memclrHasPointers` calls it always, and it
returns at once when the barrier is off. The contracts are parametric in the address `wb` of the
flag word `runtime.writeBarrier` and require it to be off (`WriteBarrierOff`, the negation of
agent/rtstr's `WriteBarrierOn`): with the barrier on the barrier's buffer (runtime memory)
changes as well, which a contract with the barrier on (work package R5) states.

**Not covered.** `memclrHasPointers` (through `bulkBarrierPreWrite`) throws on a pointer or a
length that is not a multiple of 8; the contract requires both aligned. `interequal` and
`nilinterequal` panic on an uncomparable dynamic type; the contracts require it comparable
(`Iface.EqOK`).
-/

namespace Janus.Contracts.Mem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Float

/-! ## Go's equality on floats -/

/-- Go's `x == y` on the IEEE encodings `x`, `y` of the format `f`: `false` if either is a NaN,
otherwise equality of the values (so `+0 == -0`, and `x == x` for every non-NaN `x`). -/
def feq (f : Fmt) (x y : Nat) : Bool :=
  !(isNaN f x || isNaN f y) && Val.eq (valueOf f x) (valueOf f y)

/-! ## The common shape -/

/-- What every equality runtime call with `nargs` register arguments needs (arm64): the stack
guard at least `d` bytes below `SP` (the function's stack check falls through) and the ABI
conditions of `CallOK` (admissible `X30`, aligned `SP`, the window `[SP - d, SP + 8 + 8·nargs)`
writable). -/
def EqPre (d nargs : Nat) (s : State) : Prop :=
  StackGuardOK s d ∧ CallOK s d nargs ∧ Outside ((s.regs 28).toNat + 16) 8 (calleeStack s d nargs)

/-- The return of an equality runtime call from `s` to `s'` (arm64): to `X30`, with `X18`,
`X28`, `X29`, `SP` and `FPCR` kept, the result registers `r` (`P r`), and memory changed only in
the callee's stack window. -/
def EqRet (d nargs : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r v fl fs m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, fpsr := fs,
                               mem := m, pc := s.regs 30 } ∧
    MemFrame s.mem m (calleeStack s d nargs) ∧ P r

/-- An input of `n` bytes at `a` of a call at `s` (`nargs` arguments, stack bound `d`):
readable, below `2^48`, outside the callee's stack window. -/
def Input (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n false = true ∧ Outside a n (calleeStack s d nargs)

/-- A Go `bool` result: the low byte of `X0`. -/
def BoolRes (r : Nat → W64) (b : Bool) : Prop := (r 0).toNat % 256 = b.toNat

/-! ## `memequal` and the fixed-size equality functions -/

/-- **`runtime.memequal(a, b, n)`** (`X0 = a`, `X1 = b`, `X2 = n`): whether the `n` bytes at `a`
and `b` agree (`true` for `n = 0`). -/
def Memequal (p : Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 0 s ∧ Input s d 0 (s.regs 0).toNat (s.regs 2).toNat ∧
      Input s d 0 (s.regs 1).toNat (s.regs 2).toNat)
    (fun s s' => EqRet d 0 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat (s.regs 2).toNat == s.mem.readLE (s.regs 1).toNat (s.regs 2).toNat))

/-- **`runtime.memequal0/8/16/32/64/128(a, b)`** (`X0 = a`, `X1 = b`): whether the `n` bytes at
`a` and `b` agree, `n = 0, 1, 2, 4, 8, 16` (`memequal0` reads nothing and returns `true`). -/
def MemequalN (p : Program) (addr d n : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat n ∧ Input s d 2 (s.regs 1).toNat n)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat n == s.mem.readLE (s.regs 1).toNat n))

/-- The size a `memequal_varlen` closure carries: the word at `8(X26)`. -/
def varlenSize (s : State) : Nat := s.mem.readLE ((s.regs 26).toNat + 8) 8

/-- **`runtime.memequal_varlen(a, b)`** (`X0 = a`, `X1 = b`, the closure context `X26` pointing at
a funcval whose second word is the size `n`): as `memequal(a, b, n)`. -/
def MemequalVarlen (p : Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ Input s d 2 ((s.regs 26).toNat + 8) 8 ∧
      Input s d 2 (s.regs 0).toNat (varlenSize s) ∧ Input s d 2 (s.regs 1).toNat (varlenSize s))
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat (varlenSize s) == s.mem.readLE (s.regs 1).toNat (varlenSize s)))

/-! ## Floating-point and complex equality -/

/-- **`runtime.f32equal(a, b)`** (`Fequal binary32 4`) and **`runtime.f64equal(a, b)`**
(`Fequal binary64 8`): Go's `==` (`feq`) on the floats at `a` and `b`. -/
def Fequal (p : Program) (addr d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat k ∧
      Input s d 2 (s.regs 1).toNat k)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (feq f (s.mem.readLE (s.regs 0).toNat k) (s.mem.readLE (s.regs 1).toNat k)))

/-- **`runtime.c64equal(a, b)`** (`Cequal binary32 4`) and **`runtime.c128equal(a, b)`**
(`Cequal binary64 8`): Go's `==` on complex numbers, both the real parts (at `a`, `b`) and the
imaginary parts (at `a + k`, `b + k`) `feq`. -/
def Cequal (p : Program) (addr d : Nat) (f : Fmt) (k : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
      Input s d 2 (s.regs 1).toNat (2 * k))
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r
      (feq f (s.mem.readLE (s.regs 0).toNat k) (s.mem.readLE (s.regs 1).toNat k) &&
        feq f (s.mem.readLE ((s.regs 0).toNat + k) k) (s.mem.readLE ((s.regs 1).toNat + k) k)))

/-! ## Strings and interfaces -/

/-- The string header at `h` in `m`: its data pointer and its length. -/
def strPtr (m : Memory) (h : Nat) : Nat := m.readLE h 8
def strLen (m : Memory) (h : Nat) : Nat := m.readLE (h + 8) 8

/-- The string whose header is at `h` is an input of the call at `s`: the header (16 bytes) and
the `len` bytes it points to. -/
def StrInput (s : State) (d nargs h : Nat) : Prop :=
  Input s d nargs h 16 ∧ Input s d nargs (strPtr s.mem h) (strLen s.mem h)

/-- Go's `==` on the strings with headers at `a` and `b`: equal lengths and equal bytes. -/
def strEq (m : Memory) (a b : Nat) : Bool :=
  strLen m a == strLen m b && m.readLE (strPtr m a) (strLen m a) == m.readLE (strPtr m b) (strLen m b)

/-- **`runtime.strequal(a, b)`** (`X0 = a`, `X1 = b`, pointers to string headers): `strEq`. -/
def Strequal (p : Program) (addr d : Nat) : Prop :=
  Summary p addr
    (fun s => EqPre d 2 s ∧ StrInput s d 2 (s.regs 0).toNat ∧ StrInput s d 2 (s.regs 1).toNat)
    (fun s s' => EqRet d 2 s s' fun r => BoolRes r (strEq s.mem (s.regs 0).toNat (s.regs 1).toNat))

/-- The interface value at `a` is an input of an interface-runtime call at `s` (`R`, stack
bound `d`): its two words readable, below `2^48`, outside the callee's window. -/
def IfaceInput (s : State) (d a : Nat) : Prop := Input s d 2 a 16

/-- What an `interequal`/`nilinterequal` call with stack bound `d` needs of the interface model
`R`: its environment, the stack guard, `CallOK`, and the window outside `R.priv`. -/
def IfacePre (R : IfaceModel) (d : Nat) (s : State) : Prop :=
  R.Env s.mem (s.regs 28) ∧ StackGuardOK s d ∧ CallOK s d 2 ∧
    Outside (s.sp.toNat - d) (d + 8 + 8 * 2) R.priv ∧
    Outside ((s.regs 28).toNat + 16) 8 (calleeStack s d 2)

/-- The return of an `interequal`/`nilinterequal` call (arm64): as `EqRet`, and memory may also
change in `R.priv`, after which `R.Env` holds again. -/
def IfaceRet (R : IfaceModel) (d : Nat) (s s' : State) (P : (Nat → W64) → Prop) : Prop :=
  ∃ r v fl fs m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, fpsr := fs,
                               mem := m, pc := s.regs 30 } ∧
    MemFrame s.mem m (R.priv ++ calleeStack s d 2) ∧ R.Env m (s.regs 28) ∧ P r

/-- **`runtime.nilinterequal(a, b)`** (`X0 = a`, `X1 = b`, pointers to `any` values
`(type, data)`): equal type words and `efaceeq(type, data_a, data_b)` (`Iface.efaceEqual`). When
the type words agree the values must be comparable (`Iface.EqOK`) and their comparison must not
depend on the callee's window (`EqFrame`). -/
def Nilinterequal (p : Program) (addr : Nat) (R : IfaceModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => IfacePre R d s ∧ IfaceInput s d (s.regs 0).toNat ∧ IfaceInput s d (s.regs 1).toNat ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8 →
        Iface.EqOK R s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
          (s.mem.readLE ((s.regs 1).toNat + 8) 8) ∧
        EqFrame R (s.mem.readLE (s.regs 0).toNat 8) s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8)
          (s.mem.readLE ((s.regs 1).toNat + 8) 8) (R.priv ++ calleeStack s d 2)))
    (fun s s' => IfaceRet R d s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat 8 == s.mem.readLE (s.regs 1).toNat 8 &&
        Iface.efaceEqual R s.mem (s.mem.readLE (s.regs 0).toNat 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8)))

/-- **`runtime.interequal(a, b)`** (`X0 = a`, `X1 = b`, pointers to non-empty interface values
`(itab, data)`): equal itab words and `ifaceeq(itab, data_a, data_b)` (`Iface.ifaceEqual`). When
the itabs agree and are not nil, the itab must be readable with a non-nil type whose values
compare (`EqOK`) independently of the callee's window (`EqFrame`, and the itab outside it). -/
def Interequal (p : Program) (addr : Nat) (R : IfaceModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => IfacePre R d s ∧ IfaceInput s d (s.regs 0).toNat ∧ IfaceInput s d (s.regs 1).toNat ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8 →
        s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        Outside (s.mem.readLE (s.regs 0).toNat 8) 16 R.priv ∧
        s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
        Iface.EqOK R s.mem (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) ∧
        EqFrame R (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8) s.mem
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8)
          (R.priv ++ calleeStack s d 2)))
    (fun s s' => IfaceRet R d s s' fun r => BoolRes r
      (s.mem.readLE (s.regs 0).toNat 8 == s.mem.readLE (s.regs 1).toNat 8 &&
        Iface.ifaceEqual R s.mem (s.mem.readLE (s.regs 0).toNat 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8)))

/-! ## Typed memory -/

/-- An abstract model of the runtime around the typed-memory functions: what "the runtime is
usable" means (`Env m g`, e.g. the write-barrier buffer and the GC metadata in place) and the
runtime's private memory (`priv`). A theorem quantifies over every model satisfying `Laws`. -/
structure MemModel where
  /-- The runtime is usable in `m` by the goroutine `g`. -/
  Env : Memory → W64 → Prop
  /-- The runtime's own memory. -/
  priv : List (Nat × Nat)

/-- The laws of a `MemModel`: the environment lives in the private memory (changes elsewhere,
with the same accessible ranges, keep it). -/
structure MemModel.Laws (M : MemModel) : Prop where
  env_frame : ∀ m m' g, M.Env m g → Agrees m m' M.priv → M.Env m' g

/-- The write barrier is off: the 32-bit flag word `runtime.writeBarrier` (`enabled`, then
padding and `needed`) at `wb` is zero (the negation of agent/rtstr's `WriteBarrierOn`). -/
def WriteBarrierOff (m : Memory) (wb : Nat) : Prop := m.readLE wb 4 = 0

/-- What a typed-memory call with `nargs` arguments and stack bound `d` needs (arm64): the
environment, the stack guard, `CallOK`, the window outside `M.priv`, the write-barrier flag at
`wb` readable (outside the callee's window and below `2^48`) and off. -/
def TPre (M : MemModel) (wb d nargs : Nat) (s : State) : Prop :=
  M.Env s.mem (s.regs 28) ∧ StackGuardOK s d ∧ CallOK s d nargs ∧
    Outside (s.sp.toNat - d) (d + 8 + 8 * nargs) M.priv ∧ Input s d nargs wb 4 ∧
    WriteBarrierOff s.mem wb ∧ Outside ((s.regs 28).toNat + 16) 8 (calleeStack s d nargs)

/-- The destination of a typed-memory call: `n` writable bytes at `a`, below `2^48`, outside the
callee's window and outside the runtime's memory. -/
def Dest (M : MemModel) (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n true = true ∧ Outside a n (calleeStack s d nargs) ∧
    Outside a n M.priv

/-- The return of a typed-memory call (arm64): as `EqRet`, with memory changed only in
`M.priv`, the callee's window and `extra` (the destination), and `M.Env` again. -/
def TRet (M : MemModel) (d nargs : Nat) (extra : List (Nat × Nat)) (s s' : State)
    (P : Memory → Prop) : Prop :=
  ∃ r v fl fs m, s' = { s with regs := Map.keepABI s.regs r, vregs := v, flags := fl, fpsr := fs,
                               mem := m, pc := s.regs 30 } ∧
    MemFrame s.mem m (M.priv ++ calleeStack s d nargs ++ extra) ∧ M.Env m (s.regs 28) ∧ P m

/-- The `n` bytes at `dst` in `m` are those at `src` in `m₀`. -/
def Copied (m₀ m : Memory) (dst src n : Nat) : Prop := ∀ i, i < n → m.bytes (dst + i) = m₀.bytes (src + i)

/-- The `n` bytes at `a` in `m` are zero. -/
def Zeroed (m : Memory) (a n : Nat) : Prop := ∀ i, i < n → m.bytes (a + i) = 0

/-- **`runtime.typedmemmove(typ, dst, src)`** (`X0 = typ`, `X1 = dst`, `X2 = src`) with the write
barrier off: `dst` receives a copy of the `typ.Size_` bytes at `src` (which may overlap it). -/
def TypedMemmove (p : Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 3 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
      Outside (s.regs 0).toNat 16 (calleeStack s d 3) ∧
      Input s d 3 (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat) ∧
      Dest M s d 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => TRet M d 3 [((s.regs 1).toNat, (s.regs 1).toNat + typSize s.mem (s.regs 0).toNat)] s s'
      fun m => Copied s.mem m (s.regs 1).toNat (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.typedmemclr(typ, ptr)`** (`X0 = typ`, `X1 = ptr`) with the write barrier off: the
`typ.Size_` bytes at `ptr` become zero. -/
def TypedMemclr (p : Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 2 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
      Outside (s.regs 0).toNat 16 (calleeStack s d 2) ∧
      Dest M s d 2 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => TRet M d 2 [((s.regs 1).toNat, (s.regs 1).toNat + typSize s.mem (s.regs 0).toNat)] s s'
      fun m => Zeroed m (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.memclrHasPointers(ptr, n)`** (`X0 = ptr`, `X1 = n`, both multiples of 8) with the
write barrier off: the `n` bytes at `ptr` become zero. -/
def MemclrHasPointers (p : Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
      Dest M s d 2 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => TRet M d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] s s'
      fun m => Zeroed m (s.regs 0).toNat (s.regs 1).toNat)

/-! ## The callees of the typed-memory functions

The proofs of `typedmemmove`, `typedmemclr` and `memclrHasPointers` from their machine code
(`examples/proofs/TypedMemmove.lean`, …) use these contracts of the assembly functions they call
(`memmove`, `memclrNoHeapPointers`; arbitrary sizes) and of the barrier (`bulkBarrierPreWrite`,
which with the barrier off returns at once). -/

/-- **`runtime.memmove(dst, src, n)`** (`X0 = dst`, `X1 = src`, `X2 = n`): `dst` receives a copy
of the `n` bytes at `src` (which may overlap it). -/
def Memmove (p : Program) (addr : Nat) (M : MemModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => M.Env s.mem (s.regs 28) ∧ EqPre d 3 s ∧ Outside (s.sp.toNat - d) (d + 8 + 8 * 3) M.priv ∧
      Input s d 3 (s.regs 1).toNat (s.regs 2).toNat ∧ Dest M s d 3 (s.regs 0).toNat (s.regs 2).toNat)
    (fun s s' => TRet M d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] s s'
      fun m => Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)

/-- **`runtime.memclrNoHeapPointers(ptr, n)`** (`X0 = ptr`, `X1 = n`): the `n` bytes at `ptr`
become zero. -/
def MemclrNoHeapPointers (p : Program) (addr : Nat) (M : MemModel) (d : Nat) : Prop :=
  Summary p addr
    (fun s => M.Env s.mem (s.regs 28) ∧ EqPre d 2 s ∧ Outside (s.sp.toNat - d) (d + 8 + 8 * 2) M.priv ∧
      Dest M s d 2 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => TRet M d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] s s'
      fun m => Zeroed m (s.regs 0).toNat (s.regs 1).toNat)

/-- **`runtime.bulkBarrierPreWrite(dst, src, size, typ)`** (`X0`–`X3`) with the barrier off and
`dst`, `src`, `size` multiples of 8: returns without changing anything but its stack window. -/
def BulkBarrierOff (p : Program) (addr : Nat) (M : MemModel) (wb d : Nat) : Prop :=
  Summary p addr
    (fun s => TPre M wb d 4 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
      (s.regs 2).toNat % 8 = 0)
    (fun s s' => TRet M d 4 [] s s' fun _ => True)

end Janus.Contracts.Mem

namespace Janus.Contracts.Mem

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-! ## Proof tools -/

/-- How a proof from a function's code ends (arm64): the final state keeps `SP`, `X18`, `X28`,
`X29` and the system registers, returns to `X30`, and its memory and registers satisfy the
contract; then it is `EqRet`. -/
theorem EqRet.intro {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hf : MemFrame s.mem s'.mem (calleeStack s d nargs)) (hp : P s'.regs) : EqRet d nargs s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, ?_, hf, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

end Janus.Contracts.Mem

namespace Janus.Contracts.Mem

open Janus Janus.Arm64 Janus.Float

/-! ## Floating-point comparison (arm64) -/

theorem typeOf_isNaN (f : Fmt) (x : Nat) : (FP.typeOf f x).isNaN = isNaN f x := by
  unfold FP.typeOf isNaN; cases classify f x <;> rfl

/-- `FCMP` with `FPCR = 0` sets `Z` exactly for Go's `==` (`feq`): not for a NaN, and for equal
values (so for `+0` and `-0`). -/
@[janus_exec, janus_post] theorem fpCompare_z (f : Fmt) (sig : Bool) (a b : Nat) :
    (flagsOfNzcv (FP.fpCompare f 0 sig a b).1).z = feq f a b := by
  simp only [FP.fpCompare, FP.unpack_ieee FP.IEEEMode.zero, typeOf_isNaN, feq]
  cases isNaN f a <;> cases isNaN f b <;> simp [flagsOfNzcv]
  split <;> simp_all
  split <;> simp

end Janus.Contracts.Mem

namespace Janus.Contracts.Mem

open Janus Janus.Arm64

/-! ## Comparing memory word by word -/

/-- 32 bytes are equal iff their four words are. -/
theorem readLE_32_eq_iff (m : Memory) (a b : Nat) :
    m.readLE a 32 = m.readLE b 32 ↔
      m.readLE a 8 = m.readLE b 8 ∧ m.readLE (a + 8) 8 = m.readLE (b + 8) 8 ∧
      m.readLE (a + 16) 8 = m.readLE (b + 16) 8 ∧ m.readLE (a + 24) 8 = m.readLE (b + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Tactic.readLE_add_eq_iff, show 24 = 8 + 16 from rfl,
    Tactic.readLE_add_eq_iff, show 16 = 8 + 8 from rfl, Tactic.readLE_add_eq_iff, Nat.add_assoc]

/-- 16 bytes are equal iff their two words are. -/
theorem readLE_16_eq_iff (m : Memory) (a b : Nat) :
    m.readLE a 16 = m.readLE b 16 ↔
      m.readLE a 8 = m.readLE b 8 ∧ m.readLE (a + 8) 8 = m.readLE (b + 8) 8 := by
  rw [show 16 = 8 + 8 from rfl, Tactic.readLE_add_eq_iff]

end Janus.Contracts.Mem

namespace Janus.Contracts.Mem

/-- `EOR` then a zero test (`memequal`'s word compare) decides equality. -/
theorem xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    revert this; cases a.testBit i <;> cases b.testBit i <;> simp
  · rintro rfl; exact Nat.xor_self a

end Janus.Contracts.Mem

namespace Janus.Contracts.Mem
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- What a Go function needs to call an equality runtime function with stack bound `d` from
inside a frame of `frame` bytes below its `SP` (so the callee runs with `SP - frame`), with
`above` bytes of its caller's frame it may write (its argument spill slots): the stack guard at
least `d + frame` below `SP`, an aligned `SP`, `8 ≤ d`, the window
`[SP - d - frame, SP + above)` writable and below `2^48`, and the guard word `16(g)` outside it. -/
def CallerOK (s : State) (d frame above : Nat) : Prop :=
  StackGuardOK s (d + frame) ∧ s.sp.toNat % 16 = 0 ∧ 8 ≤ d ∧ d + frame ≤ s.sp.toNat ∧
    s.sp.toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - (d + frame)) (d + frame + above) true = true ∧
    Outside ((s.regs 28).toNat + 16) 8 [(s.sp.toNat - (d + frame), s.sp.toNat + above)]

/-- The caller's window. -/
def callerWindow (s : State) (d frame above : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - (d + frame), s.sp.toNat + above)]

/-- `EqPre` at a call site `S`, from the caller's `CallerOK` at its entry `s`: `S` is `frame`
bytes below the caller's `SP`, keeps `g`, has an admissible return address, and its memory
differs from the entry's only inside the caller's window. -/
theorem EqPre.of_caller {s S : State} {d frame above nargs : Nat} (hc : CallerOK s d frame above)
    (hf : MemFrame s.mem S.mem (callerWindow s d frame above))
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hg : S.regs 28 = s.regs 28)
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) (hfr : frame % 16 = 0)
    (hn : 8 + 8 * nargs ≤ frame + above) : EqPre d nargs S := by
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout⟩ := hc
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  simp only [callerWindow, outside_cons, outside_nil, and_true] at hout hf
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hf.accessible]; exact hg2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp]
    rw [hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Memory.accessible_mono _ hst (by omega) (by omega)
  · simp only [calleeStack, outside_cons, outside_nil, and_true, hg, hsp]; omega

/-- `Input` at a call site `S` (see `EqPre.of_caller`) of a range readable at the caller's entry
and outside the caller's window. -/
theorem Input.of_caller {s S : State} {d frame above nargs a n : Nat}
    (hf : MemFrame s.mem S.mem (callerWindow s d frame above))
    (hsp : S.sp.toNat = s.sp.toNat - frame) (hn : 8 + 8 * nargs ≤ frame + above)
    (hfr : frame ≤ s.sp.toNat)
    (hb : a + n ≤ 2 ^ 48) (hacc : s.mem.accessible a n false = true)
    (ho : Outside a n (callerWindow s d frame above)) : Input S d nargs a n := by
  simp only [callerWindow, outside_cons, outside_nil, and_true] at ho
  refine ⟨hb, by rw [hf.accessible]; exact hacc, ?_⟩
  simp only [calleeStack, outside_cons, outside_nil, and_true, hsp]
  omega

/-- After an `EqRet` return, the caller's reads outside the callee's window are unchanged. -/
theorem EqRet.memFrame {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (h : EqRet d nargs s s' P) : MemFrame s.mem s'.mem (calleeStack s d nargs) := by
  obtain ⟨r, v, fl, fs, m, rfl, hf, -⟩ := h
  exact hf

end Janus.Contracts.Mem
