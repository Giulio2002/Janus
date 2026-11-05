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

/-- The decimal digits of `n`, as bytes (`'0' = 48`): the most significant digit first. -/
def natBytes (n : Nat) : List Nat :=
  if n < 10 then [48 + n] else natBytes (n / 10) ++ [48 + n % 10]
decreasing_by omega

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

theorem natBytes_lt {n : Nat} (h : n < 10) : natBytes n = [48 + n] := by
  rw [natBytes]; simp [h]

theorem natBytes_ge {n : Nat} (h : 10 ≤ n) : natBytes n = natBytes (n / 10) ++ [48 + n % 10] := by
  rw [natBytes]; simp [Nat.not_lt.mpr h]

theorem natBytes_length_pos (n : Nat) : 0 < (natBytes n).length := by
  rw [natBytes]; split <;> simp

theorem natBytes_lt256 (n : Nat) : ∀ b ∈ natBytes n, b < 256 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natBytes]
    split
    · intro b hb; simp at hb; omega
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | hb
      · exact ih (n / 10) (by omega) b hb
      · omega

/-- The digit `k` places from the right of `n`, as a byte. -/
def digitByte (n k : Nat) : Nat := 48 + n / 10 ^ k % 10

/-- Reading the digits of `n` from the right: place `k` of the string is the digit `k`. -/
theorem natBytes_reverse_get (n : Nat) : ∀ k, k < (natBytes n).length →
    (natBytes n).reverse[k]? = some (digitByte n k) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    by_cases h : n < 10
    · rw [natBytes_lt h] at hk ⊢
      have : k = 0 := by simp at hk; omega
      subst this
      simp [digitByte, Nat.mod_eq_of_lt h]
    · have h10 : 10 ≤ n := by omega
      rw [natBytes_ge h10] at hk ⊢
      rw [List.reverse_append]
      cases k with
      | zero => simp [digitByte]
      | succ j =>
        simp only [List.length_append, List.length_singleton] at hk
        have hj : j < (natBytes (n / 10)).length := by omega
        have := ih (n / 10) (by omega) j hj
        simp only [List.reverse_singleton, List.singleton_append, List.getElem?_cons_succ]
        rw [this]
        simp [digitByte, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- The number of digits as the register code computes it: `1 + #{k ∈ 1..m | n / 10^k ≠ 0}`. -/
def cntF (n : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => cntF n m + (if n / 10 ^ (m + 1) ≠ 0 then 1 else 0)

theorem cntF_shift (n : Nat) : ∀ m, cntF n (m + 1) = (if n / 10 ≠ 0 then 1 else 0) + cntF (n / 10) m := by
  intro m
  induction m with
  | zero =>
    show cntF n 0 + (if n / 10 ^ 1 ≠ 0 then 1 else 0) = _ + cntF (n / 10) 0
    simp only [cntF, Nat.pow_one]; omega
  | succ m ih =>
    rw [cntF, ih, cntF]
    have : n / 10 / 10 ^ (m + 1) = n / 10 ^ (m + 1 + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rw [this]
    omega

theorem natBytes_length (n : Nat) : ∀ m, n < 10 ^ (m + 1) → (natBytes n).length = cntF n m := by
  intro m
  induction m generalizing n with
  | zero =>
    intro h
    rw [natBytes_lt (by simpa using h)]; simp [cntF]
  | succ m ih =>
    intro h
    by_cases h10 : n < 10
    · rw [natBytes_lt h10]
      have : n / 10 = 0 := by omega
      have h2 : ∀ k, n / 10 ^ (k + 1) = 0 := fun k => by
        apply Nat.div_eq_of_lt
        have : 10 ≤ 10 ^ (k + 1) := Nat.le_self_pow (by omega) 10
        omega
      have : cntF n (m + 1) = 1 := by
        clear ih h
        induction m with
        | zero =>
          show cntF n 0 + (if n / 10 ^ (0 + 1) ≠ 0 then 1 else 0) = 1
          rw [h2 0]; simp [cntF]
        | succ m ih' => rw [cntF, ih', h2]; simp
      rw [this]; simp
    · have h10' : 10 ≤ n := by omega
      rw [natBytes_ge h10', List.length_append, cntF_shift, ih (n / 10) (by
        rw [Nat.pow_succ] at h
        omega)]
      have : n / 10 ≠ 0 := by omega
      simp [this]; omega

/-- An `int` read as two's complement from a 64-bit word. -/
def toSigned (v : Nat) : Int := if v < 2 ^ 63 then (v : Int) else (v : Int) - 2 ^ 64

/-- The size of a `fmt.wrapError` (`msg string; err error`): 32 bytes, `msg` at 0, `err` at 16. -/
def wrapBytes : Nat := 32

/-- `wrapError.msg` is at offset 0 (pointer) and 8 (length). -/
def wrapErrOffset : Nat := 16

end Janus.Spec.Errorf
