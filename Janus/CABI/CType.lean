/-!
# C types and their LP64 memory layout (shared by the AAPCS64 and System V models)

The argument and result classifications of `Janus.CABI` (AAPCS64) and `Janus.Amd64.CABI`
(System V) are functions of a C type. This module defines the types they classify and the
memory layout both LP64 ABIs give them (AAPCS64 §5, System V psABI §3.1.2): sizes, alignments,
and the offsets of struct members, which the compilers lay out in declaration order, each at the
next multiple of its alignment, the whole rounded up to the largest member alignment.

`CType` covers what a C prototype can name without attributes:

* `int n signed`: the integer types of `n` bytes (`_Bool`, `char`, `short`, `int`, `long`,
  `long long`, `__int128` for `n = 1, 2, 4, 8, 16`; signedness only matters for the value a
  proof assigns to the bytes);
* `ptr`: every data and function pointer (8 bytes);
* `half` (`_Float16` / `__fp16`), `float`, `double`, `ldouble` (`long double`: IEEE binary128
  on AAPCS64, the x87 80-bit format in a 16-byte slot on System V — both 16 bytes, aligned to 16);
* `complex b`: `_Complex b` for a floating type `b` (two `b`, real part first);
* `vec n`: a short vector of `n = 8` or `16` bytes (`int32x4_t`, `float64x2_t`, `__m64`,
  `__m128`, `__m128d`, `__m128i`), aligned to its size;
* `struct fs`, `union fs`, `array t n`.

Not covered (no constructor): bit-fields, flexible and zero-length arrays, empty structs (a GNU
extension of size 0), `__attribute__((packed))`/`aligned(n)`, and 32/64-byte vectors (`__m256`,
`__m512`: their passing depends on `-mavx`). A prototype using them is outside the model.

The layout functions are plain structural recursion; `#eval`/`decide` evaluate them on concrete
types, and the probe (`JanusTests/CABIProbe.lean`, `scripts/cabi-probe.sh`) checks them against
gcc and clang (`sizeof`, `_Alignof`, `offsetof`).
-/

namespace Janus.C

/-- A C object type (see the module documentation for what is covered). -/
inductive CType where
  | int (bytes : Nat) (signed : Bool)
  | ptr
  | half
  | float
  | double
  | ldouble
  | complex (base : CType)
  | vec (bytes : Nat)
  | struct (fields : List CType)
  | union (fields : List CType)
  | array (elem : CType) (n : Nat)
deriving Repr, Inhabited

namespace CType

/-- `n` rounded up to a multiple of `a` (`a = 0` leaves `n`). -/
def roundUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

mutual
/-- The alignment (`_Alignof`). -/
def align : CType → Nat
  | int n _ => n
  | ptr => 8
  | half => 2
  | float => 4
  | double => 8
  | ldouble => 16
  | complex b => align b
  | vec n => n
  | struct fs => alignList fs
  | union fs => alignList fs
  | array t _ => align t

/-- The largest alignment of a member list (at least 1). -/
def alignList : List CType → Nat
  | [] => 1
  | t :: ts => max (align t) (alignList ts)
end

mutual
/-- The size (`sizeof`). -/
def size : CType → Nat
  | int n _ => n
  | ptr => 8
  | half => 2
  | float => 4
  | double => 8
  | ldouble => 16
  | complex b => 2 * size b
  | vec n => n
  | struct fs => roundUp (structEnd 0 fs) (alignList fs)
  | union fs => roundUp (maxSize fs) (alignList fs)
  | array t n => n * size t

/-- The end offset of the members `fs` laid out from offset `off`. -/
def structEnd (off : Nat) : List CType → Nat
  | [] => off
  | t :: ts => structEnd (roundUp off (align t) + size t) ts

/-- The largest member size. -/
def maxSize : List CType → Nat
  | [] => 0
  | t :: ts => max (size t) (maxSize ts)
end

/-- The offsets of the members of a struct whose first member is at `off`. -/
def offsets (off : Nat) : List CType → List Nat
  | [] => []
  | t :: ts => roundUp off (align t) :: offsets (roundUp off (align t) + size t) ts

/-- Aggregates (`struct`, `union`, arrays) and complex types are *composite* for AAPCS64
(§5.9); the System V classification treats complex types as two scalars. -/
def isAggregate : CType → Bool
  | struct _ | union _ | array _ _ => true
  | _ => false

/-- The floating-point and vector *base types* an AAPCS64 homogeneous aggregate is made of
(§5.9.5: `half`, `float`, `double`, quad, and the 8- and 16-byte short vectors). -/
inductive Base where
  | h | s | d | q | v8 | v16
deriving Repr, DecidableEq, Inhabited

/-- The size of a base type. -/
def Base.size : Base → Nat
  | .h => 2 | .s => 4 | .d => 8 | .q => 16 | .v8 => 8 | .v16 => 16

/-- The leaves of a type for the System V classification: every scalar at its byte offset,
with what it is. -/
inductive Leaf where
  /-- An integer or pointer of `n` bytes (`n = 16` is `__int128`: two INTEGER eightbytes). -/
  | int (n : Nat)
  /-- A `half`/`float`/`double` or an 8-byte vector: SSE. -/
  | sse (n : Nat)
  /-- A 16-byte vector: SSE then SSEUP. -/
  | vec16
  /-- `long double`: X87 then X87UP. -/
  | x87
deriving Repr, DecidableEq, Inhabited

mutual
/-- The scalars of `t` placed at `off`, in increasing offset order within each member. -/
def leaves (off : Nat) : CType → List (Nat × Leaf)
  | int n _ => [(off, .int n)]
  | ptr => [(off, .int 8)]
  | half => [(off, .sse 2)]
  | float => [(off, .sse 4)]
  | double => [(off, .sse 8)]
  | ldouble => [(off, .x87)]
  | complex b => leaves off b ++ leaves (off + size b) b
  | vec n => if n = 16 then [(off, .vec16)] else [(off, .sse n)]
  | struct fs => leavesStruct off fs
  | union fs => leavesUnion off fs
  | array t n => (List.range n).flatMap fun i => leaves (off + i * size t) t

def leavesStruct (off : Nat) : List CType → List (Nat × Leaf)
  | [] => []
  | t :: ts => leaves (roundUp off (align t)) t ++ leavesStruct (roundUp off (align t) + size t) ts

def leavesUnion (off : Nat) : List CType → List (Nat × Leaf)
  | [] => []
  | t :: ts => leaves off t ++ leavesUnion off ts
end

mutual
/-- The homogeneous-aggregate candidate of `t` (AAPCS64 §5.9.5, as gcc's
`aapcs_vfp_sub_candidate` computes it): `some (b, k)` when `t` is made of `k` members of the
single base type `b` with no padding, `none` otherwise. A scalar floating-point or vector type
is its own candidate with `k = 1`; a complex type has `k = 2`; a union takes the largest member
count; an array multiplies. -/
def hfaCand : CType → Option (Base × Nat)
  | half => some (.h, 1)
  | float => some (.s, 1)
  | double => some (.d, 1)
  | ldouble => some (.q, 1)
  | complex b => (hfaCand b).bind fun (x, k) => if k = 1 then some (x, 2) else none
  | vec n => if n = 8 then some (.v8, 1) else if n = 16 then some (.v16, 1) else none
  | struct fs => (hfaFields fs).bind fun (x, k) =>
      if k * x.size = size (struct fs) then some (x, k) else none
  | union fs => (hfaUnion fs).bind fun (x, k) =>
      if k * x.size = size (union fs) then some (x, k) else none
  | array t n => (hfaCand t).bind fun (x, k) => if n = 0 then none else some (x, n * k)
  | _ => none

/-- Struct members: the same base type everywhere, the counts added. -/
def hfaFields : List CType → Option (Base × Nat)
  | [] => none
  | [t] => hfaCand t
  | t :: ts => match hfaCand t, hfaFields ts with
    | some (x, k), some (y, l) => if x = y then some (x, k + l) else none
    | _, _ => none

/-- Union members: the same base type everywhere, the largest count. -/
def hfaUnion : List CType → Option (Base × Nat)
  | [] => none
  | [t] => hfaCand t
  | t :: ts => match hfaCand t, hfaUnion ts with
    | some (x, k), some (y, l) => if x = y then some (x, max k l) else none
    | _, _ => none
end

/-- `t` is a homogeneous floating-point aggregate (HFA) or short-vector aggregate (HVA), or a
floating-point / vector / complex scalar, of `k ∈ [1, 4]` members of base type `b`: the types
AAPCS64 passes in SIMD&FP registers (rules C.1, C.2). -/
def hfa (t : CType) : Option (Base × Nat) :=
  (hfaCand t).bind fun (x, k) => if 1 ≤ k ∧ k ≤ 4 then some (x, k) else none


end CType

/-! ## Where a value is passed

Both classifications produce, for every argument, a `Passing`: either the value's bytes split
into `Piece`s, each in the low bytes of a register or at an offset of the outgoing argument
area, or a pointer (in a register or a stack slot) to a copy of the value in memory. -/

/-- A place an argument or result byte range is passed in. -/
inductive Loc where
  /-- The low bytes of general register `r`, by its hardware number (AAPCS64: `Xr`; x86-64:
  the encoding number, `0 RAX, 1 RCX, 2 RDX, 3 RBX, 6 RSI, 7 RDI, 8–15 R8–R15`). -/
  | gpr (r : Nat)
  /-- Bytes `byteOff ..` of SIMD&FP register `Vr` / `XMMr` (`byteOff = 8` is the upper half of
  an `XMM` register, for a System V SSEUP eightbyte). -/
  | vec (r : Nat) (byteOff : Nat)
  /-- The argument area: offset `off` from the stack pointer at the call (`SP` on AAPCS64,
  `RSP + 8` — the first byte above the return address — on System V). -/
  | stack (off : Nat)
  /-- The x87 register `ST(i)` (System V `long double` and `_Complex long double` results). -/
  | x87 (i : Nat)
deriving Repr, DecidableEq, Inhabited

/-- Bytes `[src, src + len)` of the value are at `loc`. -/
structure Piece where
  src : Nat
  len : Nat
  loc : Loc
deriving Repr, DecidableEq, Inhabited

/-- How one argument (or result) is passed. -/
inductive Passing where
  /-- The value's bytes, in pieces. -/
  | direct (pieces : List Piece)
  /-- A pointer to a copy of the value in memory, at `loc` (8 bytes): AAPCS64 rule B.4 for a
  composite larger than 16 bytes (the caller makes the copy); for a result, the caller-provided
  result buffer (`X8`, System V's hidden first argument). -/
  | indirect (loc : Loc)
deriving Repr, DecidableEq, Inhabited

namespace CType

/-! ## Sanity checks of the layout (the probe checks them against the compilers) -/

example : size (struct [double, int 4 true]) = 16 := rfl
example : align (struct [int 1 false, ldouble]) = 16 := rfl
example : size (struct [int 1 false, ldouble]) = 32 := rfl
example : offsets 0 [int 1 false, int 4 true, int 2 true, double] = [0, 4, 8, 16] := rfl
example : size (union [int 1 false, array (int 2 true) 3]) = 6 := rfl
example : hfa (struct [float, float, float, float]) = some (.s, 4) := rfl
example : hfa (struct [double, double, double, double, double]) = none := rfl
example : hfa (struct [float, double]) = none := rfl
example : hfa (struct [array double 2, complex double]) = some (.d, 4) := rfl
example : hfa (complex float) = some (.s, 2) := rfl
example : hfa (struct [vec 16, vec 16]) = some (.v16, 2) := rfl

end CType

end Janus.C
