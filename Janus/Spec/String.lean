import Janus.Spec.Basic

/-!
# Strings and UTF-8, as the Go 1.26 runtime defines them

The pure specifications the string runtime contracts (`Janus.Contracts.String`,
`Janus.Contracts.StringAmd64`) are stated with. A Go string is its bytes, a `List Nat` of values
below 256 (`strBytes m p n` reads one from memory). Every definition transcribes the Go source
it names, operation for operation, so that "matches Go" is a reading of two short texts side by
side; the test vectors of `JanusTests/String.lean` (produced by the real Go runtime) check the
transcription.

* `decodeRune s k`: `runtime.decoderune(s, k)` (`runtime/utf8.go`), including its answer for
  every invalid input: an ASCII or continuation byte at `k`, a truncated sequence, an overlong
  encoding, a surrogate, a code point above U+10FFFF or `k ≥ len(s)` all give
  `(U+FFFD, k + 1)`.
* `rangeStep s k`: one step of `for i, r := range s` (the compiler inlines the ASCII case and
  calls `decoderune` for a byte `≥ 0x80`).
* `runesFrom s k` / `runes s`: the runes `for range` produces; `countRunes s` their number
  (`runtime.countrunes`).
* `encodeRune i`: `runtime.encoderune` on `uint32(r)`: invalid code points (negative, surrogates,
  above U+10FFFF) encode U+FFFD.
* `intRune v`: the rune `string(rune(v))` encodes for an `int64` `v` (`runtime.intstring`).
-/

namespace Janus.Spec

open Janus Janus.Arm64

/-- The `n` bytes at `p` of memory `m`, as numbers. -/
def strBytes (m : Memory) (p n : Nat) : List Nat := (List.range n).map fun i => (m.bytes (p + i)).toNat

/-- `utf8.RuneError` (`'�'`). -/
def runeError : Nat := 0xFFFD
/-- `utf8.MaxRune` (`'\U0010FFFF'`). -/
def maxRune : Nat := 0x10FFFF

/-- Byte `i` of `s` (0 past the end; only read where Go reads it, after its length check). -/
@[reducible] def byteAt (s : List Nat) (i : Nat) : Nat := s.getD i 0

/-- `s[k + i]` is a continuation byte (`locb <= s[i] && s[i] <= hicb` on `s = s[k:]`), and it
exists. -/
@[reducible] def isCont (s : List Nat) (k i : Nat) : Bool :=
  decide (k + i < s.length) && decide (0x80 ≤ byteAt s (k + i)) && decide (byteAt s (k + i) ≤ 0xBF)

/-- **`runtime.decoderune(s, k)`** (Go 1.26 `runtime/utf8.go`):

```go
func decoderune(s string, k int) (r rune, pos int) {
	pos = k
	if k >= len(s) { return runeError, k + 1 }
	s = s[k:]
	switch {
	case t2 <= s[0] && s[0] < t3:   // 0080-07FF two byte sequence
		if len(s) > 1 && (locb <= s[1] && s[1] <= hicb) {
			r = rune(s[0]&mask2)<<6 | rune(s[1]&maskx)
			pos += 2
			if rune1Max < r { return }
		}
	case t3 <= s[0] && s[0] < t4:   // 0800-FFFF three byte sequence
		if len(s) > 2 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) {
			r = rune(s[0]&mask3)<<12 | rune(s[1]&maskx)<<6 | rune(s[2]&maskx)
			pos += 3
			if rune2Max < r && !(surrogateMin <= r && r <= surrogateMax) { return }
		}
	case t4 <= s[0] && s[0] < t5:   // 10000-1FFFFF four byte sequence
		if len(s) > 3 && (locb <= s[1] && s[1] <= hicb) && (locb <= s[2] && s[2] <= hicb) && (locb <= s[3] && s[3] <= hicb) {
			r = rune(s[0]&mask4)<<18 | rune(s[1]&maskx)<<12 | rune(s[2]&maskx)<<6 | rune(s[3]&maskx)
			pos += 4
			if rune3Max < r && r <= maxRune { return }
		}
	}
	return runeError, k + 1
}
```

(`t2 = 0xC0`, `t3 = 0xE0`, `t4 = 0xF0`, `t5 = 0xF8`, `maskx = 0x3F`, `mask2 = 0x1F`,
`mask3 = 0x0F`, `mask4 = 0x07`, `rune1Max = 0x7F`, `rune2Max = 0x7FF`, `rune3Max = 0xFFFF`,
`locb = 0x80`, `hicb = 0xBF`.) The rune is non-negative here, so it is a `Nat`; `k` is a
non-negative `int` (the callers pass an index). -/
def decodeRune (s : List Nat) (k : Nat) : Nat × Nat :=
  if s.length ≤ k then (0xFFFD, k + 1) else
  let b0 := byteAt s k
  if 0xC0 ≤ b0 ∧ b0 < 0xE0 then
    if isCont s k 1 then
      let r := (b0 &&& 0x1F) <<< 6 ||| (byteAt s (k + 1) &&& 0x3F)
      if 0x7F < r then (r, k + 2) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else if 0xE0 ≤ b0 ∧ b0 < 0xF0 then
    if isCont s k 1 && isCont s k 2 then
      let r := (b0 &&& 0x0F) <<< 12 ||| (byteAt s (k + 1) &&& 0x3F) <<< 6 |||
        (byteAt s (k + 2) &&& 0x3F)
      if 0x7FF < r ∧ ¬(0xD800 ≤ r ∧ r ≤ 0xDFFF) then (r, k + 3) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else if 0xF0 ≤ b0 ∧ b0 < 0xF8 then
    if isCont s k 1 && isCont s k 2 && isCont s k 3 then
      let r := (b0 &&& 0x07) <<< 18 ||| (byteAt s (k + 1) &&& 0x3F) <<< 12 |||
        (byteAt s (k + 2) &&& 0x3F) <<< 6 ||| (byteAt s (k + 3) &&& 0x3F)
      if 0xFFFF < r ∧ r ≤ 0x10FFFF then (r, k + 4) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else (0xFFFD, k + 1)

/-- One step of `for k, r := range s` at index `k < len(s)`, as the compiler emits it
(`cmd/compile/internal/walk/range.go`):

```go
if c := s[k]; c < utf8.RuneSelf { r = rune(c); k++ } else { r, k = decoderune(s, k) }
```
-/
def rangeStep (s : List Nat) (k : Nat) : Nat × Nat :=
  if byteAt s k < 0x80 then (byteAt s k, k + 1) else decodeRune s k

/-- The runes `for range s[k:]` produces from index `k` on (`fuel` bounds the number of
steps; `runesFrom` passes `len(s) - k`, which suffices since every step advances). -/
def runesGo (s : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, k => if k < s.length then (rangeStep s k).1 :: runesGo s fuel (rangeStep s k).2 else []

/-- The runes of `for range` over `s`, starting at byte `k`. -/
def runesFrom (s : List Nat) (k : Nat) : List Nat := runesGo s (s.length - k) k

/-- The runes of `for range s` (`[]rune(s)`). -/
def runes (s : List Nat) : List Nat := runesFrom s 0

/-- **`runtime.countrunes(s)`**: `n := 0; for range s { n++ }; return n`. -/
def countRunes (s : List Nat) : Nat := (runes s).length

/-- The sum of the runes of `s` (wrapping at `2^64`): what `for _, r := range s { sum +=
uint64(r) }` computes. -/
def sumRunes (s : List Nat) : Nat := (runes s).sum % 2 ^ 64

/-- **`runtime.encoderune(p, r)`** on `i = uint32(r)` (Go 1.26 `runtime/utf8.go`): the bytes it
writes.

```go
switch i := uint32(r); {
case i <= rune1Max: p[0] = byte(r); return 1
case i <= rune2Max: p[0] = t2 | byte(r>>6); p[1] = tx | byte(r)&maskx; return 2
case i > maxRune, surrogateMin <= i && i <= surrogateMax: r = runeError; fallthrough
case i <= rune3Max:
	p[0] = t3 | byte(r>>12); p[1] = tx | byte(r>>6)&maskx; p[2] = tx | byte(r)&maskx; return 3
default:
	p[0] = t4 | byte(r>>18); p[1] = tx | byte(r>>12)&maskx
	p[2] = tx | byte(r>>6)&maskx; p[3] = tx | byte(r)&maskx; return 4
}
```

(`byte(x)` is `x mod 256`; `tx = 0x80`.) -/
def encodeRune (i : Nat) : List Nat :=
  let enc3 (r : Nat) : List Nat :=
    [0xE0 ||| (r >>> 12) % 256, 0x80 ||| ((r >>> 6) % 256) &&& 0x3F, 0x80 ||| (r % 256) &&& 0x3F]
  if i ≤ 0x7F then [i % 256]
  else if i ≤ 0x7FF then [0xC0 ||| (i >>> 6) % 256, 0x80 ||| (i % 256) &&& 0x3F]
  else if 0x10FFFF < i ∨ (0xD800 ≤ i ∧ i ≤ 0xDFFF) then enc3 runeError
  else if i ≤ 0xFFFF then enc3 i
  else
    [0xF0 ||| (i >>> 18) % 256, 0x80 ||| ((i >>> 12) % 256) &&& 0x3F,
      0x80 ||| ((i >>> 6) % 256) &&& 0x3F, 0x80 ||| (i % 256) &&& 0x3F]

/-- The rune `runtime.intstring(buf, v)` encodes for the `int64` `v` (given as its 64-bit
pattern): `if int64(rune(v)) != v { v = runeError }`, then `encoderune(b, rune(v))`, which
looks at `uint32(rune(v))`, i.e. `v mod 2^32`. -/
def intRune (v : BitVec 64) : Nat :=
  if -2 ^ 31 ≤ v.toInt ∧ v.toInt < 2 ^ 31 then v.toNat % 2 ^ 32 else runeError

/-- The UTF-8 bytes of the runes `rs` (`uint32` values), each encoded by `encodeRune`:
`string(rs)` (`runtime.slicerunetostring`). -/
def encodeRunes (rs : List Nat) : List Nat := (rs.map encodeRune).flatten

/-! ## Basic facts -/

theorem decodeRune_snd (s : List Nat) (k : Nat) :
    k + 1 ≤ (decodeRune s k).2 ∧ (decodeRune s k).2 ≤ k + 4 := by
  unfold decodeRune
  dsimp only
  repeat' split
  all_goals omega

theorem rangeStep_snd (s : List Nat) (k : Nat) :
    k + 1 ≤ (rangeStep s k).2 ∧ (rangeStep s k).2 ≤ k + 4 := by
  unfold rangeStep
  split
  · simp
  · exact decodeRune_snd s k

theorem and_shl_or_lt2 (a b : Nat) : (a &&& 0x1F) <<< 6 ||| (b &&& 0x3F) < 2 ^ 11 := by
  apply Nat.or_lt_two_pow
  · rw [Nat.shiftLeft_eq]; have := Nat.and_le_right (n := a) (m := 0x1F); omega
  · have := Nat.and_le_right (n := b) (m := 0x3F); omega

theorem and_shl_or_lt3 (a b c : Nat) :
    (a &&& 0x0F) <<< 12 ||| (b &&& 0x3F) <<< 6 ||| (c &&& 0x3F) < 2 ^ 16 := by
  apply Nat.or_lt_two_pow
  · apply Nat.or_lt_two_pow
    · rw [Nat.shiftLeft_eq]; have := Nat.and_le_right (n := a) (m := 0x0F); omega
    · rw [Nat.shiftLeft_eq]; have := Nat.and_le_right (n := b) (m := 0x3F); omega
  · have := Nat.and_le_right (n := c) (m := 0x3F); omega

/-- A rune `decodeRune` returns is at most `U+10FFFF`. -/
theorem decodeRune_fst_le (s : List Nat) (k : Nat) : (decodeRune s k).1 ≤ maxRune := by
  unfold decodeRune maxRune
  dsimp only
  repeat' split
  all_goals first
    | omega
    | (have := and_shl_or_lt2 (byteAt s k) (byteAt s (k + 1)); simp only []; omega)
    | (have := and_shl_or_lt3 (byteAt s k) (byteAt s (k + 1)) (byteAt s (k + 2)); simp only []; omega)
    | (simp only []; omega)

/-- A rune that starts inside `s` ends inside it. -/
theorem decodeRune_snd_le_length (s : List Nat) (k : Nat) (h : k < s.length) :
    (decodeRune s k).2 ≤ s.length := by
  unfold decodeRune
  dsimp only
  repeat' split
  all_goals (try simp only [isCont, Bool.and_eq_true, decide_eq_true_eq] at *)
  all_goals omega

theorem rangeStep_snd_le_length (s : List Nat) (k : Nat) (h : k < s.length) :
    (rangeStep s k).2 ≤ s.length := by
  unfold rangeStep
  split
  · simp only []; omega
  · exact decodeRune_snd_le_length s k h

theorem rangeStep_fst_le (s : List Nat) (k : Nat) :
    (rangeStep s k).1 ≤ maxRune := by
  unfold rangeStep
  split
  · simp only [maxRune]; omega
  · exact decodeRune_fst_le s k

theorem runesGo_fuel (s : List Nat) :
    ∀ n m k, s.length - k ≤ n → s.length - k ≤ m → runesGo s n k = runesGo s m k := by
  intro n
  induction n with
  | zero =>
    intro m k hn _
    cases m with
    | zero => rfl
    | succ m => simp only [runesGo]; rw [if_neg (by omega)]
  | succ n ih =>
    intro m k hn hm
    cases m with
    | zero => simp only [runesGo]; rw [if_neg (by omega)]
    | succ m =>
      simp only [runesGo]
      split
      · have := rangeStep_snd s k
        rw [ih m _ (by omega) (by omega)]
      · rfl

/-- The unfolding of `for range` at index `k`. -/
theorem runesFrom_eq (s : List Nat) (k : Nat) :
    runesFrom s k = if k < s.length then (rangeStep s k).1 :: runesFrom s (rangeStep s k).2 else [] := by
  unfold runesFrom
  split
  · rename_i hk
    obtain ⟨n, hn⟩ : ∃ n, s.length - k = n + 1 := ⟨s.length - k - 1, by omega⟩
    rw [hn]
    simp only [runesGo, if_pos hk]
    have := rangeStep_snd s k
    rw [runesGo_fuel s n (s.length - (rangeStep s k).2) _ (by omega) (Nat.le_refl _)]
  · rename_i hk
    rw [show s.length - k = 0 by omega]
    rfl

theorem runesFrom_of_le (s : List Nat) (k : Nat) (h : s.length ≤ k) : runesFrom s k = [] := by
  rw [runesFrom_eq, if_neg (by omega)]

theorem runesFrom_of_lt (s : List Nat) (k : Nat) (h : k < s.length) :
    runesFrom s k = (rangeStep s k).1 :: runesFrom s (rangeStep s k).2 := by
  rw [runesFrom_eq, if_pos h]

/-- `strBytes` has the length it reads. -/
@[simp] theorem strBytes_length (m : Memory) (p n : Nat) : (strBytes m p n).length = n := by
  simp [strBytes]

/-- Byte `i` of `strBytes`. -/
theorem strBytes_getD (m : Memory) (p n i : Nat) (h : i < n) :
    (strBytes m p n).getD i 0 = (m.bytes (p + i)).toNat := by
  simp [strBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

/-- Byte `i < n` of `strBytes`, as the 1-byte read the machine does. -/
theorem byteAt_strBytes (m : Memory) (p n i : Nat) (h : i < n) :
    byteAt (strBytes m p n) i = m.readLE (p + i) 1 := by
  rw [byteAt, strBytes_getD m p n i h, Memory.readLE_one]

/-- Byte `i` of `strBytes` (`0` past the end). -/
theorem byteAt_strBytes' (m : Memory) (p n i : Nat) :
    byteAt (strBytes m p n) i = if i < n then m.readLE (p + i) 1 else 0 := by
  split
  · exact byteAt_strBytes m p n i ‹_›
  · simp only [byteAt, strBytes, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- Every byte of `strBytes` is below 256. -/
theorem strBytes_lt (m : Memory) (p n : Nat) : ∀ b ∈ strBytes m p n, b < 256 := by
  intro b hb
  simp only [strBytes, List.mem_map, List.mem_range] at hb
  obtain ⟨i, -, rfl⟩ := hb
  exact (m.bytes (p + i)).isLt

/-- Two memories with the same bytes at `[p, p+n)` have the same `strBytes`. -/
theorem strBytes_congr {m m' : Memory} {p q n : Nat} (h : ∀ i, i < n → m'.bytes (q + i) = m.bytes (p + i)) :
    strBytes m' q n = strBytes m p n := by
  simp only [strBytes]
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.1 hi)]

/-- A store outside `[p, p+n)` does not change its bytes. -/
theorem strBytes_writeLE (m : Memory) (p n a k v : Nat) (h : p + n ≤ a ∨ a + k ≤ p) :
    strBytes (m.writeLE a k v) p n = strBytes m p n := by
  apply strBytes_congr
  intro i hi
  exact Memory.bytes_writeLE_outside _ (by omega)

/-- The bytes of a concatenation. -/
theorem strBytes_append (m : Memory) (p a b : Nat) :
    strBytes m p (a + b) = strBytes m p a ++ strBytes m (p + a) b := by
  simp only [strBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.add_assoc]

/-! ## The decoder in arithmetic form

The masks and shifts of `decodeRune` on bytes are sums of digit fields: `decodeRune_eq_arith`
restates it with `%` and `*` only, which `omega` reasons about (proofs about machine code compare
it with the fields the code extracts). -/

theorem or_low (x y i : Nat) (hy : y < 2 ^ i) : x * 2 ^ i ||| y = x * 2 ^ i + y := by
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hy]

theorem or_low' (x y i : Nat) (hy : y < 2 ^ i) : y ||| x * 2 ^ i = x * 2 ^ i + y := by
  rw [Nat.or_comm, or_low x y i hy]

theorem mul_or_mul (x y i : Nat) : x * 2 ^ i ||| y * 2 ^ i = (x ||| y) * 2 ^ i := by
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_or_distrib]

theorem or_mul_low (x y i j : Nat) (hy : y < 2 ^ i) :
    x * 2 ^ (i + j) ||| y * 2 ^ j = x * 2 ^ (i + j) + y * 2 ^ j := by
  rw [Nat.pow_add, ← Nat.mul_assoc, mul_or_mul, or_low _ _ _ hy, Nat.add_mul]

theorem rune2_arith (a b : Nat) : (a &&& 0x1F) <<< 6 ||| (b &&& 0x3F) = a % 32 * 64 + b % 64 := by
  rw [show (0x1F : Nat) = 2 ^ 5 - 1 from rfl, show (0x3F : Nat) = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
    or_low _ _ 6 (Nat.mod_lt _ (by decide))]

theorem rune3_arith (a b c : Nat) :
    (a &&& 0x0F) <<< 12 ||| (b &&& 0x3F) <<< 6 ||| (c &&& 0x3F) = a % 16 * 4096 + b % 64 * 64 + c % 64 := by
  rw [show (0x0F : Nat) = 2 ^ 4 - 1 from rfl, show (0x3F : Nat) = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, or_mul_low (a % 16) (b % 64) 6 6 (Nat.mod_lt _ (by decide)),
    show a % 16 * 2 ^ (6 + 6) + b % 64 * 2 ^ 6 = (a % 16 * 64 + b % 64) * 2 ^ 6 by omega,
    or_low _ _ 6 (Nat.mod_lt _ (by decide))]

theorem rune4_arith (a b c d : Nat) :
    (a &&& 0x07) <<< 18 ||| (b &&& 0x3F) <<< 12 ||| (c &&& 0x3F) <<< 6 ||| (d &&& 0x3F) =
      a % 8 * 262144 + b % 64 * 4096 + c % 64 * 64 + d % 64 := by
  rw [show (0x07 : Nat) = 2 ^ 3 - 1 from rfl, show (0x3F : Nat) = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    or_mul_low (a % 8) (b % 64) 6 12 (Nat.mod_lt _ (by decide)),
    show a % 8 * 2 ^ (6 + 12) + b % 64 * 2 ^ 12 = (a % 8 * 64 + b % 64) * 2 ^ (6 + 6) by omega,
    or_mul_low _ (c % 64) 6 6 (Nat.mod_lt _ (by decide)),
    show (a % 8 * 64 + b % 64) * 2 ^ (6 + 6) + c % 64 * 2 ^ 6 = (a % 8 * 4096 + b % 64 * 64 + c % 64) * 2 ^ 6 by omega,
    or_low _ _ 6 (Nat.mod_lt _ (by decide))]

/-- `decodeRune` with its fields as arithmetic (`decodeRune_eq_arith`). -/
def decodeRuneA (s : List Nat) (k : Nat) : Nat × Nat :=
  if s.length ≤ k then (0xFFFD, k + 1) else
  let b0 := byteAt s k
  if 0xC0 ≤ b0 ∧ b0 < 0xE0 then
    if isCont s k 1 then
      let r := b0 % 32 * 64 + byteAt s (k + 1) % 64
      if 0x7F < r then (r, k + 2) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else if 0xE0 ≤ b0 ∧ b0 < 0xF0 then
    if isCont s k 1 && isCont s k 2 then
      let r := b0 % 16 * 4096 + byteAt s (k + 1) % 64 * 64 + byteAt s (k + 2) % 64
      if 0x7FF < r ∧ ¬(0xD800 ≤ r ∧ r ≤ 0xDFFF) then (r, k + 3) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else if 0xF0 ≤ b0 ∧ b0 < 0xF8 then
    if isCont s k 1 && isCont s k 2 && isCont s k 3 then
      let r := b0 % 8 * 262144 + byteAt s (k + 1) % 64 * 4096 + byteAt s (k + 2) % 64 * 64 +
        byteAt s (k + 3) % 64
      if 0xFFFF < r ∧ r ≤ 0x10FFFF then (r, k + 4) else (0xFFFD, k + 1)
    else (0xFFFD, k + 1)
  else (0xFFFD, k + 1)

theorem decodeRune_eq_arith (s : List Nat) (k : Nat) : decodeRune s k = decodeRuneA s k := by
  unfold decodeRune decodeRuneA
  simp only [rune2_arith, rune3_arith, rune4_arith]

end Janus.Spec
