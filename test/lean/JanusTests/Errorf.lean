import Janus.Spec.Errorf

/-!
# Tests for the `fmt.Errorf` model (`Janus.Spec.Errorf`) against the Go runtime

The vectors below were printed by the real `fmt.Errorf` (Go 1.26.10): `(format, text of the %w
operand, the int operands, err.Error())`. `render` of the parsed format must give the message, and
every format outside the closed set (one leading `%w`, then literal bytes and `%d`) must be
rejected by `parseFmt`. The checks are kernel-evaluated.
-/

namespace JanusTests.Errorf

open Janus.Spec.Errorf

set_option maxRecDepth 20000

def vectors : List (List Nat × List Nat × List Int × List Nat) := [
  ([37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115], [98, 97, 100, 32, 108, 101, 110, 103, 116, 104], [3, 32], [98, 97, 100, 32, 108, 101, 110, 103, 116, 104, 58, 32, 104, 97, 118, 101, 32, 51, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115]),
  ([37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115], [98, 97, 100, 32, 108, 101, 110, 103, 116, 104], [0, 32], [98, 97, 100, 32, 108, 101, 110, 103, 116, 104, 58, 32, 104, 97, 118, 101, 32, 48, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115]),
  ([37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115], [98, 97, 100, 32, 101, 110, 99, 111, 100, 101, 100, 32, 108, 101, 110, 103, 116, 104], [-1, 32], [98, 97, 100, 32, 101, 110, 99, 111, 100, 101, 100, 32, 108, 101, 110, 103, 116, 104, 58, 32, 104, 97, 118, 101, 32, 45, 49, 44, 32, 119, 97, 110, 116, 32, 51, 50, 32, 98, 121, 116, 101, 115]),
  ([37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115], [], [1234567890123, -5], [58, 32, 104, 97, 118, 101, 32, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 44, 32, 119, 97, 110, 116, 32, 45, 53, 32, 98, 121, 116, 101, 115]),
  ([37, 119, 58, 32, 104, 97, 118, 101, 32, 37, 100, 44, 32, 119, 97, 110, 116, 32, 37, 100, 32, 98, 121, 116, 101, 115], [120], [9223372036854775807, -9223372036854775808], [120, 58, 32, 104, 97, 118, 101, 32, 57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 55, 44, 32, 119, 97, 110, 116, 32, 45, 57, 50, 50, 51, 51, 55, 50, 48, 51, 54, 56, 53, 52, 55, 55, 53, 56, 48, 56, 32, 98, 121, 116, 101, 115]),
  ([37, 119], [111, 110, 108, 121], [], [111, 110, 108, 121]),
  ([37, 119, 58, 32, 37, 100], [101], [7], [101, 58, 32, 55]),
  ([37, 119, 37, 100, 37, 100], [101], [1, 22], [101, 49, 50, 50]),
  ([37, 119, 32, 40, 37, 100, 41], [], [-10], [32, 40, 45, 49, 48, 41]),
  ([37, 119, 58, 32, 110, 111, 32, 118, 101, 114, 98, 115], [97, 98, 99], [], [97, 98, 99, 58, 32, 110, 111, 32, 118, 101, 114, 98, 115])
]

/-- The model's message for a vector (`none` for a format outside the set or a wrong operand count). -/
def model (f e : List Nat) (ns : List Int) : Option (List Nat) :=
  match parseFmt f with
  | some segs => if ns.length = nDec segs then some (render segs e ns) else none
  | none => none

theorem vectors_ok : vectors.all (fun v => model v.1 v.2.1 v.2.2.1 == some v.2.2.2) = true := by decide

/-- Formats outside the closed set (as byte strings): `%s`, `%v`, `%%`, a second `%w`, no leading
`%w`, a flag or width, a trailing `%`, and the empty format. -/
def rejected : List (List Nat) := [
  [37, 115], [37, 118], [37, 119, 37, 37], [37, 119, 32, 37, 119], [120, 37, 119], [37, 119, 37, 53, 100],
  [37, 119, 37], [37, 119, 37, 120], [37, 100, 37, 119], []]

theorem rejected_ok : rejected.all (fun f => (parseFmt f).isNone) = true := by decide

/-- A wrong operand count is outside the contract (`ArgsOK` asks for `1 + #%d` operands). -/
theorem count_ok : model [37, 119, 58, 37, 100] [101] [] = none ∧ model [37, 119] [101] [1] = none := by decide

/-- Decimal digits, signs and the extreme values. -/
theorem dec_ok : decBytes 0 = [48] ∧ decBytes (-7) = [45, 55] ∧ decBytes 1234 = [49, 50, 51, 52] ∧
    toSigned (2 ^ 64 - 1) = -1 ∧ toSigned (2 ^ 63) = -(2 ^ 63) ∧ toSigned (2 ^ 63 - 1) = 2 ^ 63 - 1 := by decide

end JanusTests.Errorf
