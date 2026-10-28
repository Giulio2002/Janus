/-
Exact byte-level specification of the Go 1.26 builtin `print` / `println` output.

The runtime side is `src/runtime/print.go` (Go 1.26.0); floats and complex numbers go through
`src/internal/strconv` (`ftoa.go`, `ftoadbox.go`, `ctoa.go`). Every function below returns the
exact bytes the corresponding runtime helper hands to `gwrite`.

The float formatter is a *specification*, not a transliteration of Dragonbox: it decodes the
IEEE-754 fields, builds the exact rounding interval with rational (`Nat`) arithmetic and picks
the shortest decimal in it, then lays the digits out with the `'g'` rules of `formatDigits`.
Only core Lean is used.
-/

namespace Janus.Spec.Print

/-! ## Strings, booleans, separators -/

/-- The UTF-8 bytes of `s` (`printstring`: `gwrite(bytes(s))`, print.go:244). -/
def ofString (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map UInt8.toBitVec

/-- `printbool` (print.go:117): `"true"` or `"false"`. -/
def fmtBool (b : Bool) : List (BitVec 8) :=
  if b then ofString "true" else ofString "false"

/-- `printsp` (print.go:109): one space, written between `println` operands. -/
def fmtSp : List (BitVec 8) := [0x20]

/-- `printnl` (print.go:113): the newline that ends a `println`. -/
def fmtNl : List (BitVec 8) := [0x0a]

/-! ## Decimal integers -/

/-- The ASCII digit `'0' + d` (meaningful for `d < 10`). -/
def digit (d : Nat) : BitVec 8 := BitVec.ofNat 8 (48 + d)

/-- The decimal digits of `n`, most significant first, without leading zeros (`"0"` for 0).
This is the output of `strconv.RuntimeFormatBase10` / `formatBase10` (internal/strconv/itoa.go:181),
whose two-digits-at-a-time table loop computes exactly these digits (see `decimal_append_two`). -/
def decimal (n : Nat) : List (BitVec 8) :=
  (if h : n < 10 then [] else decimal (n / 10)) ++ [digit (n % 10)]
termination_by n
decreasing_by omega

theorem decimal_lt10 {n : Nat} (h : n < 10) : decimal n = [digit n] := by
  rw [decimal, dite_eq_left h, Nat.mod_eq_of_lt h]; rfl

theorem decimal_ge10 {n : Nat} (h : 10 ≤ n) :
    decimal n = decimal (n / 10) ++ [digit (n % 10)] := by
  rw [decimal, dite_eq_right (by omega)]

theorem length_decimal_pos (n : Nat) : 0 < (decimal n).length := by
  rw [decimal]; simp

theorem decimal_append_two {n : Nat} (h : 100 ≤ n) :
    decimal n = decimal (n / 100) ++ [digit (n % 100 / 10), digit (n % 10)] := by
  rw [decimal_ge10 (by omega), decimal_ge10 (by omega : 10 ≤ n / 10)]
  have h1 : n / 10 / 10 = n / 100 := by omega
  have h2 : n / 10 % 10 = n % 100 / 10 := by omega
  simp [h1, h2]

/-- `printuint` (print.go:145): the decimal digits of `v`. -/
def fmtUint (v : BitVec 64) : List (BitVec 8) := decimal v.toNat

/-- `printint` (print.go:155): `'-'` and the decimal magnitude for a negative two's-complement
value (the runtime negates in `uint64`, so `-2^63` prints `-9223372036854775808`), otherwise the
decimal digits. -/
def fmtInt (v : BitVec 64) : List (BitVec 8) :=
  (if v.toInt < 0 then ofString "-" else []) ++ decimal v.toInt.natAbs

/-! ## Hexadecimal -/

/-- The lowercase hex digit for `d < 16` (`dig = "0123456789abcdef"`, print.go:177). -/
def hexDigit (d : Nat) : BitVec 8 :=
  if d < 10 then BitVec.ofNat 8 (48 + d) else BitVec.ofNat 8 (87 + d)

/-- The lowercase hex digits of `n` without leading zeros (`"0"` for 0): the loop of
`printhexopts` (print.go:176) with `mindigits = 0`, which stops after the digit for `v < 16`. -/
def hexDigits (n : Nat) : List (BitVec 8) :=
  (if h : n < 16 then [] else hexDigits (n / 16)) ++ [hexDigit (n % 16)]
termination_by n
decreasing_by omega

theorem hexDigits_lt16 {n : Nat} (h : n < 16) : hexDigits n = [hexDigit n] := by
  rw [hexDigits, dite_eq_left h, Nat.mod_eq_of_lt h]; rfl

theorem hexDigits_ge16 {n : Nat} (h : 16 ≤ n) :
    hexDigits n = hexDigits (n / 16) ++ [hexDigit (n % 16)] := by
  rw [hexDigits, dite_eq_right (by omega)]

theorem length_hexDigits_pos (n : Nat) : 0 < (hexDigits n).length := by
  rw [hexDigits]; simp

/-- `printhex` (print.go:196) with the default `minhexdigits = 0`: `"0x"` and the hex digits. -/
def fmtHex (v : BitVec 64) : List (BitVec 8) := ofString "0x" ++ hexDigits v.toNat

/-- `printpointer` (print.go:237): `printhex` of the address. The compiler
(cmd/compile/internal/walk/builtin.go, walkPrint) uses it for pointers, `unsafe.Pointer`, chans,
maps and funcs. Note that a `uintptr` operand goes to `printuint` (decimal), not `printuintptr`;
`printhex` is reached directly only for the runtime-internal type `hex` and `printuintptr` only
for pointers to not-in-heap types. -/
def fmtPointer (v : BitVec 64) : List (BitVec 8) := fmtHex v

/-! ## Slices and interfaces -/

/-- `printslice` (print.go:248): `print("[", len(s), "/", cap(s), "]")` (the length and capacity
are `int`s, so `printint`) followed by `printpointer` of the data pointer. -/
def fmtSlice (ptr len cap : BitVec 64) : List (BitVec 8) :=
  ofString "[" ++ fmtInt len ++ ofString "/" ++ fmtInt cap ++ ofString "]" ++ fmtPointer ptr

/-- `printeface` / `printiface` (print.go:254-260): `print("(", w0, ",", w1, ")")` where both
words are pointers (`_type`/`tab` and `data`), so `printpointer`. -/
def fmtEface (t d : BitVec 64) : List (BitVec 8) :=
  ofString "(" ++ fmtPointer t ++ ofString "," ++ fmtPointer d ++ ofString ")"

/-! ## Floating point: exact rationals

Non-negative rationals as numerator/denominator pairs; only what the shortest-digit search
needs. Denominators are always positive powers of 2 and 10 here. -/

/-- A non-negative rational `num / den` (`den > 0`). -/
structure Frac where
  num : Nat
  den : Nat

/-- `2^k` for an integer `k`. -/
def Frac.pow2 (k : Int) : Frac :=
  if 0 ≤ k then ⟨2 ^ k.toNat, 1⟩ else ⟨1, 2 ^ (-k).toNat⟩

/-- `10^k` for an integer `k`. -/
def Frac.pow10 (k : Int) : Frac :=
  if 0 ≤ k then ⟨10 ^ k.toNat, 1⟩ else ⟨1, 10 ^ (-k).toNat⟩

/-- `n * x`. -/
def Frac.scale (n : Nat) (x : Frac) : Frac := ⟨n * x.num, x.den⟩

/-- `x / u` as a pair `(a, b)` with `x / u = a / b`. -/
def Frac.quot (x u : Frac) : Nat × Nat := (x.num * u.den, x.den * u.num)

/-! ## Floating point: decoding -/

/-- An IEEE-754 binary interchange format (`floatInfo`, internal/strconv/ftoa.go:18). -/
structure Format where
  mantBits : Nat
  expBits : Nat
  bias : Nat

/-- `float64info`: 52 fraction bits, 11 exponent bits, bias 1023. -/
def binary64 : Format := ⟨52, 11, 1023⟩
/-- `float32info`: 23 fraction bits, 8 exponent bits, bias 127. -/
def binary32 : Format := ⟨23, 8, 127⟩

/-- The value classes `genericFtoa` (ftoa.go:72) distinguishes. A finite nonzero value is
`(-1)^neg * m * 2^e` with `m` the integer significand (implicit bit added for normals) and `e`
the exponent of its last place. `asym` marks a power-of-two normal above the smallest normal
exponent, whose lower neighbour is only half an ulp away (ftoa.go:304). -/
inductive Decoded where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | finite (neg : Bool) (m : Nat) (e : Int) (asym : Bool)

/-- Decode the bit pattern `bits` of format `F` (ftoa.go:86-114). -/
def decode (F : Format) (bits : Nat) : Decoded :=
  let neg := (bits >>> (F.expBits + F.mantBits)) % 2 = 1
  let expField := (bits >>> F.mantBits) % 2 ^ F.expBits
  let frac := bits % 2 ^ F.mantBits
  if expField = 2 ^ F.expBits - 1 then
    if frac ≠ 0 then .nan else .inf neg
  else if expField = 0 then
    if frac = 0 then .zero neg
    else .finite neg frac (1 - (F.bias : Int) - F.mantBits) false
  else
    .finite neg (frac + 2 ^ F.mantBits) ((expField : Int) - F.bias - F.mantBits)
      (frac = 0 && expField > 1)

/-! ## Floating point: the shortest round-tripping decimal

`m * 2^e` is recovered by round-to-nearest-even parsing from exactly the decimals in the
interval between the midpoints to its neighbours, the midpoints themselves included iff `m` is
even (ties go to the even significand; ftoa.go:315-318, ftoadbox.go "For decimal to binary
rounding, assumes round to nearest, tie to even"). With `e2 = e - 2` all three points are
integers times `2^e2`: `lo = (4m - g)·2^e2`, `v = 4m·2^e2`, `hi = (4m + 2)·2^e2`, where the lower
gap `g` is 1 for an `asym` value and 2 otherwise.

The output is `d · 10^q` with `q` as large as possible such that some integer `d` puts `d · 10^q`
in the interval (fewest digits), and among those `d` the one nearest to `v / 10^q`. -/

/-- The rounding interval of `m * 2^e` together with the value: `(lo, v, hi, inclusive)`. -/
def interval (m : Nat) (e : Int) (asym : Bool) : Frac × Frac × Frac × Bool :=
  let u := Frac.pow2 (e - 2)
  (Frac.scale (4 * m - if asym then 1 else 2) u, Frac.scale (4 * m) u,
   Frac.scale (4 * m + 2) u, m % 2 = 0)

/-- The range `[dLo, dHi]` of integers `d` with `d · 10^q` inside the interval (empty when
`dLo > dHi`). -/
def candidates (lo hi : Frac) (incl : Bool) (q : Int) : Nat × Nat :=
  let u := Frac.pow10 q
  let (a, b) := hi.quot u
  let dHi := if a % b = 0 && !incl then a / b - 1 else a / b
  let (c, e) := lo.quot u
  let dLo := if c % e = 0 && incl then c / e else c / e + 1
  (dLo, dHi)

/-- Whether some `d · 10^q` lies in the interval. -/
def hasCandidate (lo hi : Frac) (incl : Bool) (q : Int) : Bool :=
  let (dLo, dHi) := candidates lo hi incl q
  dLo ≤ dHi

/-- Search `q, q-1, …` for the first exponent with a candidate, for at most `fuel` steps
(returning the last exponent tried when the fuel runs out). -/
def searchQ (lo hi : Frac) (incl : Bool) : Nat → Int → Int
  | 0, q => q
  | fuel + 1, q => if hasCandidate lo hi incl q then q else searchQ lo hi incl fuel (q - 1)

/-- The largest decimal exponent `q` with a candidate `d · 10^q`, `d ≥ 1`.

Upper end: `hi = a / b < 10^(len a) / 10^(len b - 1)`, so `10^q > hi` (no candidate with
`d ≥ 1`) once `q > len a - len b`; the search starts at `qTop = len a - len b`.
Lower end: at `qMin = min 0 (e - 1)` we have `10^qMin ≤ 2^(e-1)`, while the interval is at least
`3·2^(e-2) > 2^(e-1)` wide, so it contains a multiple of `10^qMin`; the fuel
`qTop - qMin + 1` is therefore never exhausted before a candidate is found. -/
def shortestQ (e : Int) (lo hi : Frac) (incl : Bool) : Int :=
  let qTop : Int := (decimal hi.num).length - (decimal hi.den).length
  let qMin : Int := min 0 (e - 1)
  searchQ lo hi incl (qTop - qMin + 1).toNat qTop

/-- How a value exactly halfway between two candidates is resolved. -/
inductive Tie where
  | even
  | up

/-- The integer nearest to `a / b`, a tie resolved by `t`. -/
def roundFrac (a b : Nat) (t : Tie) : Nat :=
  let d := a / b
  let r := a % b
  if 2 * r < b then d
  else if 2 * r > b then d + 1
  else match t with
    | .even => if d % 2 = 0 then d else d + 1
    | .up => d + 1

/-- Go's tie rule (ftoadbox.go). In the regular case (Algorithm 5.4, `if ρ == 0 {…}`) a tie
goes to the even digit. In the power-of-two case (Algorithm 5.6) `yru` is `y` rounded half up,
and only `if exp == -77 && yru%2 != 0 { yru-- }` turns a tie to even; the constant -77 is the
float64 tie exponent and is used verbatim for float32 as well, so the one float32 tie
(`±2^-12`, `e = -35`) rounds up: `println(float32(1.0/4096))` prints `0.00024414063`. -/
def tieRule (e : Int) (asym : Bool) : Tie :=
  if asym && e ≠ -77 then .up else .even

/-- The shortest decimal significand and exponent `(d, q)` for `m * 2^e` (`m ≥ 1`): the
largest `q` with a candidate, and the candidate nearest to the exact value (clamped into the
candidate range, which makes it the nearest *candidate*). This is the result of Dragonbox
(`dboxFtoa64`/`dboxFtoa32`, ftoadbox.go:33/108) and of `roundShortest` (ftoa.go:262). -/
def shortest (m : Nat) (e : Int) (asym : Bool) : Nat × Int :=
  let (lo, v, hi, incl) := interval m e asym
  let q := shortestQ e lo hi incl
  let (dLo, dHi) := candidates lo hi incl q
  let (a, b) := v.quot (Frac.pow10 q)
  let d := roundFrac a b (tieRule e asym)
  (min dHi (max dLo d), q)

/-! ## Floating point: the `'g'` layout -/

/-- Digit `j` of `ds`, `'0'` outside `[0, nd)` (the padding rule of `fmtF`). -/
def digitAt (ds : List (BitVec 8)) (j : Int) : BitVec 8 :=
  if 0 ≤ j then ds.getD j.toNat (digit 0) else digit 0

/-- The exponent of `%e`: its sign and at least two digits (ftoa.go:438-454). -/
def fmtExp (x : Int) : List (BitVec 8) :=
  (if x < 0 then ofString "-" else ofString "+") ++
    (if x.natAbs < 10 then [digit 0, digit x.natAbs] else decimal x.natAbs)

/-- `fmtE` (ftoa.go:405) with `prec = nd - 1`: the first digit (`'0'` if none), the remaining
digits after a `'.'` if there are any, `'e'`, and the exponent `dp - 1` (0 for no digits). -/
def fmtE (ds : List (BitVec 8)) (dp : Int) : List (BitVec 8) :=
  let first := ds.headD (digit 0)
  let rest := ds.drop 1
  let x : Int := if ds.isEmpty then 0 else dp - 1
  first :: (if rest.isEmpty then [] else ofString "." ++ rest) ++ ofString "e" ++ fmtExp x

/-- `fmtF` (ftoa.go:460) with `prec = max (nd - dp) 0`: the integer part (the first `dp` digits
padded with zeros, or `'0'` when `dp ≤ 0`), then if `prec > 0` a `'.'` and digits
`dp, …, dp + prec - 1` (zeros outside the digit string). -/
def fmtF (ds : List (BitVec 8)) (dp : Int) : List (BitVec 8) :=
  let nd : Int := ds.length
  let prec := (max (nd - dp) 0).toNat
  let intPart :=
    if 0 < dp then ds.take dp.toNat ++ List.replicate (dp - nd).toNat (digit 0) else [digit 0]
  intPart ++
    (if prec = 0 then [] else ofString "." ++ (List.range prec).map (fun (i : Nat) => digitAt ds (dp + i)))

/-- `formatDigits` for `'g'` in shortest mode (ftoa.go:225-254): with `prec = nd` and
`eprec = 6` (`if shortest { eprec = 6 }`), `%e` is used when the exponent `dp - 1` is `< -4` or
`≥ 6`, else `%f`; a `'-'` precedes negative values (including `-0`). Zero has no digits and
`dp = 0`, which yields `"0"`. -/
def fmtG (neg : Bool) (ds : List (BitVec 8)) (dp : Int) : List (BitVec 8) :=
  (if neg then ofString "-" else []) ++
    (if dp - 1 < -4 ∨ dp - 1 ≥ 6 then fmtE ds dp else fmtF ds dp)

/-- `strconv.AppendFloat(dst, x, 'g', -1, bitSize)` for the bit pattern `bits` of format `F`
(`genericFtoa`, ftoa.go:72): `"NaN"` for every NaN (the sign is ignored), `"+Inf"`/`"-Inf"`,
otherwise the shortest digits laid out by `fmtG`. -/
def fmtFloat (F : Format) (bits : Nat) : List (BitVec 8) :=
  match decode F bits with
  | .nan => ofString "NaN"
  | .inf neg => if neg then ofString "-Inf" else ofString "+Inf"
  | .zero neg => fmtG neg [] 0
  | .finite neg m e asym =>
    let (d, q) := shortest m e asym
    let ds := decimal d
    fmtG neg ds (ds.length + q)

/-- `printfloat64` (print.go:125): `strconv.AppendFloat(buf, v, 'g', -1, 64)`. -/
def fmtF64 (v : BitVec 64) : List (BitVec 8) := fmtFloat binary64 v.toNat

/-- `printfloat32` (print.go:130): `strconv.AppendFloat(buf, float64(v), 'g', -1, 32)`; the
widening is exact and `genericFtoa` narrows back to the same float32 (a NaN stays a NaN). -/
def fmtF32 (v : BitVec 32) : List (BitVec 8) := fmtFloat binary32 v.toNat

/-- `AppendComplex` (internal/strconv/ctoa.go:22): `'('`, the real part, the imaginary part
with a `'+'` inserted unless it already starts with `'+'` or `'-'` (so a NaN imaginary part
prints `+NaN`, `+Inf` keeps its own sign), and `"i)"`. -/
def fmtComplex (re im : List (BitVec 8)) : List (BitVec 8) :=
  let im' := match im with
    | c :: _ => if c = 0x2b ∨ c = 0x2d then im else 0x2b :: im
    | [] => 0x2b :: im
  ofString "(" ++ re ++ im' ++ ofString "i)"

/-- `printcomplex128` (print.go:135): `AppendComplex(buf, c, 'g', -1, 128)`, i.e. both parts
formatted as float64 (`bitSize >>= 1`). -/
def fmtC128 (re im : BitVec 64) : List (BitVec 8) := fmtComplex (fmtF64 re) (fmtF64 im)

/-- `printcomplex64` (print.go:140): `AppendComplex(buf, complex128(c), 'g', -1, 64)`, i.e. both
parts formatted as float32 (`bitSize >>= 1` gives 32). -/
def fmtC64 (re im : BitVec 32) : List (BitVec 8) := fmtComplex (fmtF32 re) (fmtF32 im)

/-! ## Sanity checks -/

example : ofString "0x" = [0x30, 0x78] := by decide +kernel
example : fmtUint 0 = ofString "0" := by decide +kernel
example : fmtUint 42 = ofString "42" := by decide +kernel
example : fmtInt (-17) = ofString "-17" := by decide +kernel
example : fmtHex 255 = ofString "0xff" := by decide +kernel
example : fmtHex 0 = ofString "0x0" := by decide +kernel
example : fmtBool true = ofString "true" := by decide +kernel

end Janus.Spec.Print
