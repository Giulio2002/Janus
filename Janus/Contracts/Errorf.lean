import Janus.Spec.Errorf
import Janus.Contracts.Pool

/-!
# Contract of `fmt.errorf` for one goroutine (arm64)

`fmt.Errorf(format, a...)` is a small inlinable wrapper: a compiled call is a call of
`fmt.errorf(format string, a []any) error` (`fmt/errors.go`, Go 1.26; both ISAs, checked on
`GOARCH=arm64` and `amd64`: `fmt.Errorf(...)` becomes `CALL fmt.errorf`). The worker takes a
printer from a `sync.Pool` (`newPrinter`), runs `doPrintf` (the format interpreter, reflection for
operands), builds the message with `string(p.buf)` and allocates a `*fmt.wrapError`; a theorem
that calls it leaves all of that out (`janus extract --contract fmt.errorf`; the extractor pins the
function to package `fmt`'s code) and takes this contract as a hypothesis: a `Summary` at its
address, for **any** code at that address. See docs/RUNTIME-CONTRACTS.md, "fmt.Errorf".

| Go source | Function (Go 1.26, ABIInternal) | Contract | Result |
| --- | --- | --- | --- |
| `fmt.Errorf("%w: have %d, want %d bytes", ErrBad, n, 32)` | `fmt.errorf` (`X0`,`X1` the format; `X2`,`X3`,`X4` the `[]any`; result `X0` itab, `X1` data) | `ErrorfLive` | a `*fmt.wrapError` whose `Unwrap()` is the `%w` operand and whose text is `render` |

**The closed set (v1).** The format is `%w` followed by literal bytes and `%d` verbs
(`Janus.Spec.Errorf.parseFmt`); the slice holds exactly `1 + #%d` interface values: first the `%w`
operand, a **`*errors.errorString`** (type word `E.tErr`, data word a non-nil pointer to the
string header `s`), then one `int` (type word `E.tInt`, data word a pointer to the 8-byte value)
per `%d`. Every other call (any other verb, `%%`, flags, `%v`, `%s`, a second `%w`, a missing
or surplus operand, an operand of another type, a nil `%w`) is a call this contract says nothing
about: `ArgsOK` is part of the precondition. The text must not exceed `B` bytes.

**What the contract says.** The result is the error interface `(E.iWrap, d)`, `E.iWrap` the itab of
`*fmt.wrapError` as `error`, and `d` a fresh 32-byte `wrapError {msg string; err error}`:

* `msg` is the string `render segs (text of the %w operand) (the int operands)`, read **from
  memory** at the call: the `s` field of the errorString (header at the operand's data pointer,
  bytes by `strBytes`) and the 64-bit values the `%d` operands point to (two's complement). No
  parameter supplies a text.
* `err` is `(E.iErr, e)`, `E.iErr` the itab of `*errors.errorString` as `error` and `e` the **data
  word of the `%w` operand itself**: `Unwrap()` returns exactly the operand, so `errors.Is(err,
  ErrBadBufferLength)` is provable for a sentinel global.

**Parameters.** `tErr`, `iErr`, `tInt`, `iWrap` (the fields of `Env`) are addresses of the
program's type descriptors and itabs (symbols of the extraction), and `B` bounds the message
length. They are plain numbers: a theorem fixes them from the binary, like the type word `T` of
the `sync.Pool` contracts.

**Allocation.** `d` is a fresh heap object (apart from the live set `L`, inside the runtime-owned
ranges, outside the callee's window); the message bytes stay live (`range0 mp |msg|`, like the
string contracts: Go may return a pointer into read-only static data for a one-byte string). The
budget drops by the two visible blocks (`32` and `roundupsize |msg|`); the printer's scratch
buffers are the runtime's (as `sync.Pool`'s).

**Frame.** The call returns to `X30` with `SP`, `X18`, `X28` (`g`) and `X29` preserved, every
other general register, the SIMD registers and the flags arbitrary, and bytes changed only in
`rt` and the callee's stack window. Neither the operands nor the format are written.
-/

namespace Janus.Contracts.Errorf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Pool

/-- The program's type descriptors and itabs the contract names (addresses of its symbols). -/
structure Env where
  /-- `type:*errors.errorString`: the type word of the `%w` operand. -/
  tErr : Nat
  /-- `go:itab.*errors.errorString,error`: the itab of the `err` field of the result. -/
  iErr : Nat
  /-- `type:int`: the type word of a `%d` operand. -/
  tInt : Nat
  /-- `go:itab.*fmt.wrapError,error`: the itab word of the result. -/
  iWrap : Nat

/-- The type word of operand `i` of the `[]any` at `sp`. -/
def operandT (m : Memory) (sp i : Nat) : Nat := m.readLE (sp + 16 * i) 8
/-- The data word of operand `i`. -/
def operandD (m : Memory) (sp i : Nat) : Nat := m.readLE (sp + 16 * i + 8) 8

/-- The `int` value operand `i` points to. -/
def intOf (m : Memory) (sp i : Nat) : Int := toSigned (m.readLE (operandD m sp i) 8)

/-- The `%d` operands (operands `1 …`). -/
def ints (m : Memory) (sp n : Nat) : List Int := (List.range n).map fun j => intOf m sp (j + 1)

/-- The `s` field of the errorString the `%w` operand points to. -/
def errTxt (m : Memory) (sp : Nat) : List Nat :=
  strBytes m (m.readLE (operandD m sp 0) 8) (m.readLE (operandD m sp 0 + 8) 8)

/-- The segments of the format at `(fp, fl)`. -/
def segsOf (m : Memory) (fp fl : Nat) : List Seg := (parseFmt (strBytes m fp fl)).getD []

/-- The message `fmt.errorf` builds. -/
def msgOf (m : Memory) (fp fl sp : Nat) : List Nat :=
  render (segsOf m fp fl) (errTxt m sp) (ints m sp (nDec (segsOf m fp fl)))

/-- **The calls the contract covers**: a format of the closed set, the right operands, all of it
readable, a message of at most `B` bytes. `(fp, fl)` is the format, `(sp, sl, sc)` the `[]any`. -/
def ArgsOK (E : Env) (B : Nat) (m : Memory) (fp fl sp sl sc : Nat) : Prop :=
  (parseFmt (strBytes m fp fl)).isSome ∧ sl = 1 + nDec (segsOf m fp fl) ∧ sl ≤ sc ∧
    Readable m fp fl ∧ Readable m sp (16 * sl) ∧
    operandT m sp 0 = E.tErr ∧ operandD m sp 0 ≠ 0 ∧ Readable m (operandD m sp 0) 16 ∧
    Readable m (m.readLE (operandD m sp 0) 8) (m.readLE (operandD m sp 0 + 8) 8) ∧
    (∀ j, j < nDec (segsOf m fp fl) →
      operandT m sp (j + 1) = E.tInt ∧ operandD m sp (j + 1) ≠ 0 ∧ Readable m (operandD m sp (j + 1)) 8) ∧
    (msgOf m fp fl sp).length ≤ B ∧ B < 2 ^ 40

/-- What the call reads: the format, the `[]any` array, the errorString header and text, the
`int` words. They lie outside the callee's stack window. -/
def errorfReads (m : Memory) (fp fl sp : Nat) : List (Nat × Nat) :=
  [(fp, fl), (sp, 16 * (1 + nDec (segsOf m fp fl))), (operandD m sp 0, 16),
    (m.readLE (operandD m sp 0) 8, m.readLE (operandD m sp 0 + 8) 8)] ++
    (List.range (nDec (segsOf m fp fl))).map fun j => (operandD m sp (j + 1), 8)

/-- The budget the call spends: the `wrapError` block and the message block. -/
def errorfCost (m : Memory) (fp fl sp : Nat) : Nat :=
  wrapBytes + (if (msgOf m fp fl sp).length = 0 then 0 else roundupsize (msgOf m fp fl sp).length true)

/-- What the call leaves, as a statement about the call's memory `m0` and arguments, the live set
`L`, the window `win`, the new memory `m` and the result words `(iw, d)`. -/
def ErrorfPost (E : Env) (R : RtInv) (m0 : Memory) (fp fl sp : Nat) (win L : List (Nat × Nat))
    (b g iw d : Nat) (m : Memory) : Prop :=
  iw = E.iWrap ∧ d + wrapBytes ≤ 2 ^ 48 ∧ m.accessible d wrapBytes true = true ∧
    m.readLE (d + 8) 8 = (msgOf m0 fp fl sp).length ∧
    strBytes m (m.readLE d 8) (msgOf m0 fp fl sp).length = msgOf m0 fp fl sp ∧
    Readable m (m.readLE d 8) (msgOf m0 fp fl sp).length ∧
    m.readLE (d + wrapErrOffset) 8 = E.iErr ∧ m.readLE (d + wrapErrOffset + 8) 8 = operandD m0 sp 0 ∧
    FreshFrom [(d, d + wrapBytes)] L ∧ InRanges d wrapBytes R.rt ∧
    LiveSep [(d, d + wrapBytes)] win ∧ LiveSep (range0 (m.readLE d 8) (msgOf m0 fp fl sp).length) win ∧
    R.inv (b - errorfCost m0 fp fl sp)
      (L ++ ((d, d + wrapBytes) :: range0 (m.readLE d 8) (msgOf m0 fp fl sp).length)) g
      (view R.rt (L ++ ((d, d + wrapBytes) :: range0 (m.readLE d 8) (msgOf m0 fp fl sp).length)) m)

/-- **`fmt.errorf(format, a)`** (arm64; `X0`,`X1` the format, `X2`,`X3`,`X4` the `[]any`; result
`X0` the itab word, `X1` the data word), for the formats of the closed set. -/
def ErrorfLive (p : Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (tErr iErr tInt iWrap B : Nat) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK s stack 5 ∧ StackRoom s stack 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) B s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat (s.regs 4).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (calleeStack s stack 5) ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat, (s.regs 4).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (s.regs 28).toNat s.mem
        (calleeStack s stack 5))
    (fun s s' => LiveRet R stack 5 L s s' fun r m =>
      ErrorfPost (Env.mk tErr iErr tInt iWrap) R s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (calleeStack s stack 5) L b
        (s.regs 28).toNat (r 0).toNat (r 1).toNat m)

end Janus.Contracts.Errorf
