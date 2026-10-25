import Janus.Contracts.Rt
import Janus.Spec.String

/-!
# Runtime contracts: strings (arm64 and amd64)

The Go 1.26 string helpers the compiler calls (`runtime/string.go`, `runtime/utf8.go`), as
ISA-independent `RtSpec`s (`Janus.Contracts.Rt`): `RtContract p addr rt stack H stringtoslicebyteSpec`
is the arm64 hypothesis a theorem takes for `runtime.stringtoslicebyte`, `RtContract64 …` the
amd64 one. Every spec transcribes the Go source of the function, case by case:

| Go source | runtime entry | spec |
| --- | --- | --- |
| `a + b + …` (2 to 5 operands) | `concatstring2`…`concatstring5(buf, a0, …)` | `concatstringSpec k` |
| `a + b + …` (more) | `concatstrings(buf, a []string)` | `concatstringsSpec` |
| `[]byte(a + b + …)` | `concatbyte2`…`concatbyte5`, `concatbytes` | `concatbyteSpec k`, `concatbytesSpec` |
| `string(b)` | `slicebytetostring(buf, ptr, n)` | `slicebytetostringSpec` |
| `string(b)` not escaping, instrumented | `slicebytetostringtmp(ptr, n)` | `slicebytetostringtmpSpec` |
| `[]byte(s)` | `stringtoslicebyte(buf, s)` | `stringtoslicebyteSpec` |
| `[]rune(s)` | `stringtoslicerune(buf, s)` | `stringtosliceruneSpec` |
| `string(rs)` | `slicerunetostring(buf, a)` | `slicerunetostringSpec` |
| `string(rune(v))` (`int64 v`) | `intstring(buf, v)` | `intstringSpec` |
| `for _, r := range s` (non-ASCII byte) | `decoderune(s, k)` | `decoderuneSpec` |
| `len([]rune(s))` | `countrunes(s)` | `countrunesSpec` |
| C string → Go (cgo, syscalls) | `gostring(p)`, `gostringn(p, l)`, `gobytes(p, n)` | `gostringSpec`, `gostringnSpec`, `gobytesSpec` |

**Results.** A string result `(p, n)` is described by its bytes (`StrOut`): Go strings are
immutable, and the runtime may return memory it does not own fresh (one non-empty operand of a
concatenation is returned as it is, `string(b)` of one byte points into the runtime's
`staticuint64s` table, a result that does not escape lives in the caller's `tmpBuf`). A `[]byte`
or `[]rune` result is writable by the caller, so its backing array is described exactly: the
caller's buffer (zeroed first) when the compiler passed one and the result fits, otherwise a
block inside the runtime-owned ranges `rt` of the size Go computes (`roundupsize`), with the
bytes past the length zero.

**What the contracts exclude** (the precondition): the panic and throw paths (lengths whose
sum overflows, a negative length, `gobytes` beyond `maxAlloc`, `[]rune` of more than `2^46`
runes); operands overlapping the caller's buffer (the runtime copies operand after operand into
it); and, through `H` (round 9 C1), calls the runtime does not serve as described (out of memory,
a stack move). `decoderune` and `countrunes` do not allocate or read runtime state: their specs
ask for the stack check to fall through instead of `H`, and `examples/proofs/SumRunes.lean`
and `examples/proofs/RuneLen.lean` (and their amd64 counterparts) prove that the runtime's own
code meets them.
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Spec

/-! ## Vocabulary -/

/-- Argument word `i`. -/
@[reducible] def arg (a : List Nat) (i : Nat) : Nat := a.getD i 0

/-- The string `(p, n)` is readable and below `2^48`. -/
def StrIn (m : Memory) (p n : Nat) : Prop :=
  p + n ≤ 2 ^ 48 ∧ (0 < n → m.accessible p n false = true)

/-- A `*tmpBuf` (`n` bytes) argument: nil, or writable below `2^48`. -/
def BufOK (m : Memory) (buf n : Nat) : Prop :=
  buf = 0 ∨ (buf + n ≤ 2 ^ 48 ∧ m.accessible buf n true = true)

/-- What a function with a `*tmpBuf` argument may write in the caller's frame: the buffer. -/
def bufWrites (buf n : Nat) : List (Nat × Nat) := if buf = 0 then [] else [(buf, buf + n)]

/-- The string result `(p, n)` holds the bytes `bs` (and is readable). -/
def StrOut (m : Memory) (p n : Nat) (bs : List Nat) : Prop :=
  n = bs.length ∧ p + n ≤ 2 ^ 48 ∧ (0 < n → m.accessible p n false = true) ∧ strBytes m p n = bs

/-- The slice `(p, len, cap)` is writable and holds `bs` in its first `len` bytes, zero after. -/
def BytesHold (m : Memory) (p len cap : Nat) (bs : List Nat) : Prop :=
  len ≤ cap ∧ p + cap ≤ 2 ^ 48 ∧ m.accessible p cap true = true ∧ strBytes m p len = bs ∧
    ZeroBytes m (p + len) (cap - len)

/-- The 32-bit words (`rune`s, as `uint32`) of the `n`-element array at `p`. -/
def runeWords (m : Memory) (p n : Nat) : List Nat := (List.range n).map fun i => m.readLE (p + 4 * i) 4

/-- The `[]rune` `(p, len, cap)` is writable and holds `rs` in its first `len` elements, zero
after. -/
def RunesHold (m : Memory) (p len cap : Nat) (rs : List Nat) : Prop :=
  len ≤ cap ∧ p + 4 * cap ≤ 2 ^ 48 ∧ m.accessible p (4 * cap) true = true ∧ runeWords m p len = rs ∧
    ZeroBytes m (p + 4 * len) (4 * cap - 4 * len)

/-- The string operands `(ptr, len)` of `concatstringN` in words `i, i+1, …`. -/
def strPairs (a : List Nat) : Nat → Nat → List (Nat × Nat)
  | _, 0 => []
  | i, k + 1 => (arg a i, arg a (i + 1)) :: strPairs a (i + 2) k

attribute [janus_exec, janus_post, janus64_exec, janus64_post] strPairs

/-- The string headers of a `[]string` `(p, n)`. -/
def strHdrs (m : Memory) (p n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun i => (m.readLE (p + 16 * i) 8, m.readLE (p + 16 * i + 8) 8)

/-- The operands are readable and, when the caller passed a buffer, apart from it. -/
def StrsIn (m : Memory) (buf : Nat) (xs : List (Nat × Nat)) : Prop :=
  ∀ x ∈ xs, StrIn m x.1 x.2 ∧ (buf ≠ 0 → Disjoint x.1 x.2 buf 32)

/-- The bytes of the concatenation of `xs`. -/
def catBytes (m : Memory) (xs : List (Nat × Nat)) : List Nat := (xs.map fun x => strBytes m x.1 x.2).flatten

/-- The result of `concatbytes(buf, a)` for the bytes `bs` (`string.go`): `[]byte{}` for no
bytes; the caller's buffer, zeroed, if one was passed and `len ≤ 32`; otherwise
`rawbyteslice(len)`: a block of `roundupsize len` bytes inside `rt`, zero past `len`. -/
def CatBytesOut (rt : List (Nat × Nat)) (buf : Nat) (bs : List Nat) (m : Memory) (r0 r1 r2 : Nat) :
    Prop :=
  r1 = bs.length ∧ (bs.length = 0 → r2 = 0) ∧
    (0 < bs.length → buf ≠ 0 → bs.length ≤ 32 → r0 = buf ∧ r2 = 32) ∧
    (0 < bs.length → (buf = 0 ∨ 32 < bs.length) → r2 = roundupsize bs.length true ∧ InRanges r0 r2 rt) ∧
    (0 < bs.length → BytesHold m r0 r1 r2 bs)

/-- The result of `stringtoslicebyte(buf, s)` (`string.go`): the caller's buffer, zeroed, when one
was passed and `len(s) ≤ 32` (also for `len(s) = 0`); otherwise `rawbyteslice(len(s))`. -/
def ToBytesOut (rt : List (Nat × Nat)) (buf : Nat) (bs : List Nat) (m : Memory) (r0 r1 r2 : Nat) :
    Prop :=
  r1 = bs.length ∧
    (buf ≠ 0 → bs.length ≤ 32 → r0 = buf ∧ r2 = 32 ∧ BytesHold m r0 r1 r2 bs) ∧
    ((buf = 0 ∨ 32 < bs.length) → r2 = roundupsize bs.length true ∧
      (0 < r2 → InRanges r0 r2 rt ∧ BytesHold m r0 r1 r2 bs))

/-! ## Concatenation -/

/-- **`runtime.concatstringK(buf, a0, …, a(K-1))`** (`K = 2 … 5`; `concatstrings(buf,
[]string{a0, …})`): the bytes of `a0 + a1 + …`. Words: `buf`, then `(ptr, len)` per operand. -/
def concatstringSpec (k : Nat) : RtSpec where
  nargs := 1 + 2 * k
  pre a m := BufOK m (arg a 0) 32 ∧ StrsIn m (arg a 0) (strPairs a 1 k)
  writes a _ := bufWrites (arg a 0) 32
  reads a _ := strPairs a 1 k
  post _ a m0 r0 r1 _ m := StrOut m r0 r1 (catBytes m0 (strPairs a 1 k))

/-- **`runtime.concatstrings(buf, a []string)`**: the bytes of the concatenation of the strings
of `a`. Words: `buf, a.ptr, a.len, a.cap`. -/
def concatstringsSpec : RtSpec where
  nargs := 4
  pre a m := BufOK m (arg a 0) 32 ∧ arg a 1 + 16 * arg a 2 ≤ 2 ^ 48 ∧
    (0 < arg a 2 → m.accessible (arg a 1) (16 * arg a 2) false = true) ∧
    StrsIn m (arg a 0) (strHdrs m (arg a 1) (arg a 2)) ∧
    Disjoint (arg a 1) (16 * arg a 2) (arg a 0) (if arg a 0 = 0 then 0 else 32)
  writes a _ := bufWrites (arg a 0) 32
  reads a m := (arg a 1, 16 * arg a 2) :: strHdrs m (arg a 1) (arg a 2)
  post _ a m0 r0 r1 _ m := StrOut m r0 r1 (catBytes m0 (strHdrs m0 (arg a 1) (arg a 2)))

/-- **`runtime.concatbyteK(buf, a0, …)`** (`K = 2 … 5`, `[]byte(a0 + …)`): a new `[]byte`
holding the bytes of the concatenation (`CatBytesOut`). -/
def concatbyteSpec (k : Nat) : RtSpec where
  nargs := 1 + 2 * k
  pre a m := BufOK m (arg a 0) 32 ∧ StrsIn m (arg a 0) (strPairs a 1 k)
  writes a _ := bufWrites (arg a 0) 32
  reads a _ := strPairs a 1 k
  post rt a m0 r0 r1 r2 m := CatBytesOut rt (arg a 0) (catBytes m0 (strPairs a 1 k)) m r0 r1 r2

/-- **`runtime.concatbytes(buf, a []string)`**: as `concatbyteSpec`, for the strings of `a`. -/
def concatbytesSpec : RtSpec where
  nargs := 4
  pre a m := BufOK m (arg a 0) 32 ∧ arg a 1 + 16 * arg a 2 ≤ 2 ^ 48 ∧
    (0 < arg a 2 → m.accessible (arg a 1) (16 * arg a 2) false = true) ∧
    StrsIn m (arg a 0) (strHdrs m (arg a 1) (arg a 2)) ∧
    Disjoint (arg a 1) (16 * arg a 2) (arg a 0) (if arg a 0 = 0 then 0 else 32)
  writes a _ := bufWrites (arg a 0) 32
  reads a m := (arg a 1, 16 * arg a 2) :: strHdrs m (arg a 1) (arg a 2)
  post rt a m0 r0 r1 r2 m :=
    CatBytesOut rt (arg a 0) (catBytes m0 (strHdrs m0 (arg a 1) (arg a 2))) m r0 r1 r2

/-! ## Conversions -/

/-- **`runtime.slicebytetostring(buf, ptr, n)`** (`string(b)`): a string holding the `n` bytes at
`ptr`. (For `n = 1` Go returns a pointer into `runtime.staticuint64s`; for `n ≥ 2` the caller's
buffer if one was passed and `n ≤ 32`, else a new block; only the bytes are promised.) Words:
`buf, ptr, n`. -/
def slicebytetostringSpec : RtSpec where
  nargs := 3
  pre a m := BufOK m (arg a 0) 32 ∧ StrIn m (arg a 1) (arg a 2) ∧
    (arg a 0 ≠ 0 → Disjoint (arg a 1) (arg a 2) (arg a 0) 32)
  writes a _ := bufWrites (arg a 0) 32
  reads a _ := [(arg a 1, arg a 2)]
  post _ a m0 r0 r1 _ m := StrOut m r0 r1 (strBytes m0 (arg a 1) (arg a 2))

/-- **`runtime.slicebytetostringtmp(ptr, n)`**: the string `(ptr, n)` itself, nothing written.
Words: `ptr, n`. -/
def slicebytetostringtmpSpec : RtSpec where
  nargs := 2
  pre a m := StrIn m (arg a 0) (arg a 1)
  reads a _ := [(arg a 0, arg a 1)]
  post _ a m0 r0 r1 _ m := r0 = arg a 0 ∧ r1 = arg a 1 ∧ StrOut m r0 r1 (strBytes m0 (arg a 0) (arg a 1))

/-- **`runtime.stringtoslicebyte(buf, s)`** (`[]byte(s)`): a new `[]byte` holding the bytes of
`s` (`ToBytesOut`). Words: `buf, s.ptr, s.len`. -/
def stringtoslicebyteSpec : RtSpec where
  nargs := 3
  pre a m := BufOK m (arg a 0) 32 ∧ StrIn m (arg a 1) (arg a 2) ∧
    (arg a 0 ≠ 0 → Disjoint (arg a 1) (arg a 2) (arg a 0) 32)
  writes a _ := bufWrites (arg a 0) 32
  reads a _ := [(arg a 1, arg a 2)]
  post rt a m0 r0 r1 r2 m := ToBytesOut rt (arg a 0) (strBytes m0 (arg a 1) (arg a 2)) m r0 r1 r2

/-- **`runtime.stringtoslicerune(buf, s)`** (`[]rune(s)`, `buf *[32]rune`): a new `[]rune` holding
the runes `for range s` produces (`runes`: invalid UTF-8 gives U+FFFD): the caller's buffer
(128 bytes, zeroed) when one was passed and there are at most 32 runes, otherwise
`rawruneslice(n)`: `roundupsize (4n)` bytes inside `rt`, capacity `roundupsize (4n) / 4`, zero
past the runes. Words: `buf, s.ptr, s.len`. -/
def stringtosliceruneSpec : RtSpec where
  nargs := 3
  pre a m := BufOK m (arg a 0) 128 ∧ StrIn m (arg a 1) (arg a 2) ∧ arg a 2 ≤ 2 ^ 46 ∧
    (arg a 0 ≠ 0 → Disjoint (arg a 1) (arg a 2) (arg a 0) 128)
  writes a _ := bufWrites (arg a 0) 128
  reads a _ := [(arg a 1, arg a 2)]
  post rt a m0 r0 r1 r2 m :=
    let rs := runes (strBytes m0 (arg a 1) (arg a 2))
    r1 = rs.length ∧
    (arg a 0 ≠ 0 → rs.length ≤ 32 → r0 = arg a 0 ∧ r2 = 32 ∧ RunesHold m r0 r1 r2 rs) ∧
    ((arg a 0 = 0 ∨ 32 < rs.length) → r2 = roundupsize (4 * rs.length) true / 4 ∧
      (0 < r2 → InRanges r0 (roundupsize (4 * rs.length) true) rt ∧ RunesHold m r0 r1 r2 rs))

/-- **`runtime.slicerunetostring(buf, a)`** (`string(rs)`): the UTF-8 encoding of the runes of
`a` (each element as `uint32`, `encodeRune`: invalid code points give U+FFFD). Words:
`buf, a.ptr, a.len, a.cap`. -/
def slicerunetostringSpec : RtSpec where
  nargs := 4
  pre a m := BufOK m (arg a 0) 32 ∧ StrIn m (arg a 1) (4 * arg a 2) ∧
    (arg a 0 ≠ 0 → Disjoint (arg a 1) (4 * arg a 2) (arg a 0) 32)
  writes a _ := bufWrites (arg a 0) 32
  reads a _ := [(arg a 1, 4 * arg a 2)]
  post _ a m0 r0 r1 _ m := StrOut m r0 r1 (encodeRunes (runeWords m0 (arg a 1) (arg a 2)))

/-- **`runtime.intstring(buf, v)`** (`string(rune(v))` for an `int64 v`, `buf *[4]byte`): the
UTF-8 encoding of `intRune v` (U+FFFD unless `v` is a valid code point). Words: `buf, v`. -/
def intstringSpec : RtSpec where
  nargs := 2
  pre a m := BufOK m (arg a 0) 4
  writes a _ := bufWrites (arg a 0) 4
  post _ a _ r0 r1 _ m := StrOut m r0 r1 (encodeRune (intRune (BitVec.ofNat 64 (arg a 1))))

/-! ## UTF-8 decoding -/

/-- **`runtime.decoderune(s, k)`**: `(r, pos) = decodeRune (bytes of s) k`, `r` in the low 32
bits of the first result register (a `rune`; the upper half is unspecified, the caller
sign-extends). Writes only its stack window. Needs only its stack check to fall through, not `H`. Words: `s.ptr, s.len, k`
(`k < 2^63`, a non-negative `int`). -/
def decoderuneSpec : RtSpec where
  nargs := 3
  pre a m := StrIn m (arg a 0) (arg a 1) ∧ arg a 2 < 2 ^ 63
  guard := some 0
  ready := false
  rtWrites := false
  reads a _ := [(arg a 0, arg a 1)]
  post _ a m0 r0 r1 _ _ :=
    r0 % 2 ^ 32 = (decodeRune (strBytes m0 (arg a 0) (arg a 1)) (arg a 2)).1 ∧
      r1 = (decodeRune (strBytes m0 (arg a 0) (arg a 1)) (arg a 2)).2

/-- **`runtime.countrunes(s)`** (`len([]rune(s))`): the number of runes `for range s` produces.
Needs its stack check (and that of the `decoderune` it calls) to fall through. Words:
`s.ptr, s.len`. -/
def countrunesSpec : RtSpec where
  nargs := 2
  pre a m := StrIn m (arg a 0) (arg a 1)
  guard := some 64
  ready := false
  rtWrites := false
  reads a _ := [(arg a 0, arg a 1)]
  post _ a m0 r0 _ _ _ := r0 = countRunes (strBytes m0 (arg a 0) (arg a 1))

/-! ## C strings and bytes (cgo, syscalls) -/

/-- The NUL-terminated C string at `p` has `l` bytes before its NUL, all readable. -/
def CStr (m : Memory) (p l : Nat) : Prop :=
  p + l + 1 ≤ 2 ^ 48 ∧ m.accessible p (l + 1) false = true ∧
    (∀ i, i < l → (m.bytes (p + i)).toNat ≠ 0) ∧ (m.bytes (p + l)).toNat = 0

/-- The length of the C string at `p` (0 if there is none). -/
noncomputable def cstrLen (m : Memory) (p : Nat) : Nat :=
  open Classical in if h : ∃ l, CStr m p l then Classical.choose h else 0

/-- **`runtime.gostring(p)`**: a Go string holding the bytes of the C string at `p` (up to its
NUL). Words: `p`. -/
noncomputable def gostringSpec : RtSpec where
  nargs := 1
  pre a m := ∃ l, CStr m (arg a 0) l
  reads a m := [(arg a 0, cstrLen m (arg a 0) + 1)]
  post _ a m0 r0 r1 _ m := ∀ l, CStr m0 (arg a 0) l → StrOut m r0 r1 (strBytes m0 (arg a 0) l)

/-- **`runtime.gostringn(p, l)`**: a Go string holding the `l` bytes at `p`. Words: `p, l`. -/
def gostringnSpec : RtSpec where
  nargs := 2
  pre a m := StrIn m (arg a 0) (arg a 1)
  reads a _ := [(arg a 0, arg a 1)]
  post _ a m0 r0 r1 _ m := StrOut m r0 r1 (strBytes m0 (arg a 0) (arg a 1))

/-- **`runtime.gobytes(p, n)`**: a new `[]byte` of length and capacity `n` holding the `n` bytes
at `p` (inside `rt`); `make([]byte, 0)` for `n = 0`. The panic for `n > maxAlloc` is excluded.
Words: `p, n`. -/
def gobytesSpec : RtSpec where
  nargs := 2
  pre a m := StrIn m (arg a 0) (arg a 1) ∧ arg a 1 ≤ maxAlloc
  reads a _ := [(arg a 0, arg a 1)]
  post rt a m0 r0 r1 r2 m := r1 = arg a 1 ∧ r2 = arg a 1 ∧
    (0 < arg a 1 → InRanges r0 (arg a 1) rt ∧ BytesHold m r0 r1 r2 (strBytes m0 (arg a 0) (arg a 1)))

/-- Bytes outside a frame's ranges keep their values. -/
theorem strBytes_of_frame {m0 m : Memory} {rs : List (Nat × Nat)} (hf : MemFrame m0 m rs) {p n : Nat}
    (ho : Outside p n rs) : strBytes m p n = strBytes m0 p n := by
  apply strBytes_congr
  intro i hi
  have := hf.readLE (p + i) 1 (Outside.of_sub ho (by omega) (by omega))
  rw [Memory.readLE_one, Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

theorem catBytes_nil (m : Memory) : catBytes m [] = [] := rfl
theorem catBytes_cons (m : Memory) (x : Nat × Nat) (xs : List (Nat × Nat)) :
    catBytes m (x :: xs) = strBytes m x.1 x.2 ++ catBytes m xs := rfl

attribute [janus_exec, janus_post, janus64_exec, janus64_post] arg bufWrites StrIn BufOK StrsIn StrOut
  catBytes_nil catBytes_cons strBytes_writeLE List.append_nil

end Janus.Contracts
