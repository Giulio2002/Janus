import Janus.Spec.String

/-!
# `fmt.Errorf` with one `%w`: the pure model (Go 1.26)

The vocabulary of the `fmt.errorf` contracts (`Janus.Contracts.Errorf`, arm64, and
`Janus.Contracts.ErrorfAmd64`). `fmt.Errorf` is a small inlinable wrapper: a compiled call
`fmt.Errorf(format, a...)` is a call of `fmt.errorf(format string, a []any) error`
(`fmt/errors.go`), which the extractor pins to package `fmt`'s code.

**The closed format set (v1).** The format is `%w` followed by literal bytes and `%d` verbs:
`"%w: have %d, want %d bytes"` is the one the `uint256` library uses. Every other format (a
`%` that is not the leading `%w` or a `%d`, `%%`, flags, widths, `%s`, `%v`, a second `%w`, no
`%w` at all) is outside the contract (`parseFmt` answers `none`), and so is a call whose operand
count differs from `1 + #%d`, whose first operand is not a non-nil `*errors.errorString`, or
whose other operands are not `int`s. For a format in the set, `fmt.errorf` returns a
`*fmt.wrapError{msg string; err error}` holding the rendered text, whose `Unwrap()` is the
`%w` operand.

**The text.** `render F e ns`: the `Error()` text of the `%w` operand (an
`*errors.errorString`: its `s` field, read from memory by the contract), then the literals, with
each `%d` replaced by the decimal digits of the next `int` operand (`decBytes`: `-` and the
digits of the absolute value for a negative number).
-/

namespace Janus.Spec.Errorf

/-- One element of the part of the format after the leading `%w`: a literal byte or a `%d`. -/
inductive Seg where
  | ch (c : Nat)
  | dec
  deriving DecidableEq

/-- The number of `%d` verbs. -/
def nDec : List Seg → Nat
  | [] => 0
  | Seg.dec :: t => nDec t + 1
  | Seg.ch _ :: t => nDec t

/-- The part of the format after `%w`: literal bytes (never `%`) and `%d`; `none` for any other
`%`. -/
def parseRest : List Nat → Option (List Seg)
  | [] => some []
  | 0x25 :: 0x64 :: t => (parseRest t).map (Seg.dec :: ·)
  | 0x25 :: _ => none
  | c :: t => (parseRest t).map (Seg.ch c :: ·)

/-- The formats of the contract: `%w` and then `parseRest`. -/
def parseFmt : List Nat → Option (List Seg)
  | 0x25 :: 0x77 :: t => parseRest t
  | _ => none

/-- The decimal digits of `n`, as bytes. -/
def natBytes (n : Nat) : List Nat := (Nat.toDigits 10 n).map Char.toNat

/-- `%d` of the integer `v`: an optional `-` and the digits. -/
def decBytes (v : Int) : List Nat :=
  if v < 0 then 0x2d :: natBytes v.natAbs else natBytes v.toNat

/-- The text after `%w`'s: the segments with the integers `ns` for the `%d` verbs, in order. -/
def renderRest : List Seg → List Int → List Nat
  | [], _ => []
  | Seg.ch c :: t, ns => c :: renderRest t ns
  | Seg.dec :: t, [] => renderRest t []
  | Seg.dec :: t, n :: ns => decBytes n ++ renderRest t ns

/-- The message of `fmt.Errorf` for a format of the set: the `%w` operand's text `e`, then
`renderRest`. -/
def render (segs : List Seg) (e : List Nat) (ns : List Int) : List Nat := e ++ renderRest segs ns

/-- An `int` read as two's complement from a 64-bit word. -/
def toSigned (v : Nat) : Int := if v < 2 ^ 63 then (v : Int) else (v : Int) - 2 ^ 64

/-- The size of a `fmt.wrapError` (`msg string; err error`): 32 bytes, `msg` at 0, `err` at 16. -/
def wrapBytes : Nat := 32

/-- `wrapError.msg` is at offset 0 (pointer) and 8 (length). -/
def wrapErrOffset : Nat := 16

end Janus.Spec.Errorf
