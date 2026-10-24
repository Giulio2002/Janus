import Janus.CABI.CType

/-!
# System V AMD64 argument and result classification (pure)

The classification of the *System V Application Binary Interface, AMD64 Architecture Processor
Supplement* (§3.2.3 "Parameter Passing", §3.5.7 "Variable Argument Lists"), as gcc and clang
implement it on Linux. It is a function of the C types only, checked against both compilers by
the differential probe (`scripts/cabi-probe.sh`, docs/FFI.md § 1.3).

**Classification** (`classify`, `cls`). Every eightbyte (8-byte chunk) of a type gets a class
(`Cls`). Scalars: integers and pointers are INTEGER (`__int128`: two INTEGER eightbytes),
`_Float16`/`float`/`double` and 8-byte vectors SSE, 16-byte vectors SSE then SSEUP, `long
double` X87 then X87UP, `_Complex long double` COMPLEX_X87. An aggregate larger than 64 bytes is
MEMORY. Otherwise its eightbytes start as NO_CLASS and the classes of its members, each
classified recursively, are merged in (`merge`, step 4 of §3.2.3: equal classes stay; NO_CLASS
yields to the other; MEMORY wins; then INTEGER; an x87 class against any other gives MEMORY;
otherwise SSE). The post-merger cleanup (step 5, `cleanup`) then makes the aggregate MEMORY if
it is larger than 16 bytes and is not one SSE eightbyte followed only by SSEUP ones, if any
eightbyte is MEMORY, or if an X87UP does not follow an X87; an SSEUP that does not follow
SSE/SSEUP becomes SSE. The cleanup applies to every nested aggregate, and a nested MEMORY makes
the whole object MEMORY (see `cls`).

**Arguments** (`assign`). An argument whose classes are all INTEGER/SSE/SSEUP takes, if
enough are left *for the whole argument*, the next integer argument registers
(`RDI RSI RDX RCX R8 R9`) for its INTEGER eightbytes and the next vector registers
(`XMM0`–`XMM7`) for its SSE eightbytes (an SSEUP eightbyte is the upper half of the preceding
SSE one's register). Otherwise — and for MEMORY and the x87 classes — the argument is copied to
the argument area (`RSP + 8` at entry), at the next offset aligned to `max 8 align`, taking its
size rounded up to 8.

**Results** (`result`). MEMORY: the caller passes the address of a result buffer as a hidden
first argument (in `RDI`, so the arguments start at `RSI`) and the callee returns that address
in `RAX`. Otherwise INTEGER eightbytes come back in `RAX`, `RDX`, SSE ones in `XMM0`, `XMM1`
(SSEUP in the upper half), X87 in `ST0`, COMPLEX_X87 in `ST0` (real) and `ST1` (imaginary).

**Variadic calls**: the arguments are passed exactly as for a prototype that names them, and
`AL` holds an upper bound (≤ 8) on the number of vector registers used (`Sig.vecRegs`). The
callee's `va_list` is `VaList` (`vaStart`, `vaArg`).
-/

namespace Janus.C.SysV

open CType

/-- The classes of §3.2.3. -/
inductive Cls where
  | none | integer | sse | sseup | x87 | x87up | complexX87 | memory
deriving Repr, DecidableEq, Inhabited

/-- Step 4 of the classification: the class of an eightbyte holding scalars of classes `a` and
`b`. -/
def merge (a b : Cls) : Cls :=
  if a = b then a
  else if a = .none then b
  else if b = .none then a
  else if a = .memory ∨ b = .memory then .memory
  else if a = .integer ∨ b = .integer then .integer
  else if a = .x87 ∨ a = .x87up ∨ a = .complexX87 ∨ b = .x87 ∨ b = .x87up ∨ b = .complexX87 then
    .memory
  else .sse

/-- Merge class `c` into eightbyte `i` of `cls`. -/
def mergeAt (cls : List Cls) (i : Nat) (c : Cls) : List Cls :=
  cls.modify i (merge · c)

/-- The classes a scalar at offset `o` contributes. -/
def addLeaf (cls : List Cls) : Nat × Leaf → List Cls
  | (o, .int n) =>
    if n = 16 then mergeAt (mergeAt cls (o / 8) .integer) (o / 8 + 1) .integer
    else mergeAt cls (o / 8) .integer
  | (o, .sse _) => mergeAt cls (o / 8) .sse
  | (o, .vec16) => mergeAt (mergeAt cls (o / 8) .sse) (o / 8 + 1) .sseup
  | (o, .x87) => mergeAt (mergeAt cls (o / 8) .x87) (o / 8 + 1) .x87up

/-- The cleanup loop of step 5 over the classes of one aggregate (`acc` holds the classes
already seen, reversed): a MEMORY eightbyte makes the aggregate MEMORY (`none`); an X87UP not
right after X87 too; an SSEUP not right after SSE/SSEUP becomes SSE. -/
def postStep : List Cls → List Cls → Option (List Cls)
  | acc, [] => some acc.reverse
  | acc, c :: cs =>
    match c with
    | .memory => none
    | .x87up => if acc.head? = some .x87 then postStep (c :: acc) cs else none
    | .sseup =>
      if acc.head? = some .sse ∨ acc.head? = some .sseup then postStep (c :: acc) cs
      else postStep (.sse :: acc) cs
    | _ => postStep (c :: acc) cs

/-- Step 5 for one aggregate: an aggregate of more than two eightbytes is MEMORY unless it is
one SSE eightbyte followed only by SSEUP ones; then the cleanup loop. -/
def cleanup (cls : List Cls) : Option (List Cls) :=
  if 2 < cls.length ∧ (cls.head? ≠ some .sse ∨ (cls.drop 1).any (· ≠ .sseup)) then none
  else postStep [] cls

/-- Merge the classes `sub` of a member into `cls` from eightbyte `pos` on. -/
def mergeFrom (cls sub : List Cls) (pos : Nat) : List Cls :=
  (List.range cls.length).map fun i =>
    if pos ≤ i ∧ i - pos < sub.length then merge (cls.getD i .none) (sub.getD (i - pos) .none)
    else cls.getD i .none

/-- The classes of a scalar at byte offset `o` within its eightbyte (`o < 8`), over the
eightbytes it covers. -/
def scalarCls (o : Nat) (t : CType) : List Cls :=
  (leaves o t).foldl addLeaf (List.replicate ((o + size t + 7) / 8) .none)

mutual
/-- The classes of `t` placed at byte offset `o` within an eightbyte (`o < 8`; a member at
offset `fo` of an aggregate at `o` is at `(o + fo) % 8`, and its classes merge from eightbyte
`(o + fo) / 8` on), or `none` for MEMORY. Every aggregate — also a nested one — is classified
on its own and cleaned up (`cleanup`) before it is merged into the enclosing one, and a nested
MEMORY makes the whole object MEMORY; an array merges its element's classes into each of its
eightbytes in turn. This is the recursion of gcc's `classify_argument` (and clang's
`X86_64ABIInfo::classify`), which the psABI's "each field is classified recursively" leaves
implicit: the differential probe distinguishes it from merging all scalars at once (a struct
containing a `union { long double; int; }` is MEMORY, not two INTEGER eightbytes). -/
def cls (o : Nat) : CType → Option (List Cls)
  | .struct fs =>
    if 64 < size (.struct fs) then none
    else (clsFields o 0 fs (List.replicate ((o + size (.struct fs) + 7) / 8) .none)).bind cleanup
  | .union fs =>
    if 64 < size (.union fs) then none
    else (clsUnion o fs (List.replicate ((o + size (.union fs) + 7) / 8) .none)).bind cleanup
  | .array t n =>
    if 64 < n * size t then none
    else (cls o t).bind fun sub =>
      if sub.isEmpty then none
      else cleanup ((List.range ((o + n * size t + 7) / 8)).map fun i =>
        sub.getD (i % sub.length) .none)
  | .complex .ldouble => some [.complexX87]
  | t => some (scalarCls o t)

/-- The members of a struct, from offset `off`. -/
def clsFields (o : Nat) (off : Nat) : List CType → List Cls → Option (List Cls)
  | [], acc => some acc
  | f :: fs, acc =>
    (cls ((o + roundUp off (align f)) % 8) f).bind fun sub =>
      clsFields o (roundUp off (align f) + size f) fs
        (mergeFrom acc sub ((o + roundUp off (align f)) / 8))

/-- The members of a union, all at offset 0. -/
def clsUnion (o : Nat) : List CType → List Cls → Option (List Cls)
  | [], acc => some acc
  | f :: fs, acc => (cls o f).bind fun sub => clsUnion o fs (mergeFrom acc sub (o / 8))
end

/-- The classes of the eightbytes of `t`, or `[.memory]`. -/
def classify (t : CType) : List Cls :=
  (cls 0 t).getD [.memory]

/-- `t` is passed in memory whatever registers are left (MEMORY or an x87 class). -/
def inMemory (cls : List Cls) : Bool :=
  cls.any fun c => c = .memory ∨ c = .x87 ∨ c = .x87up ∨ c = .complexX87

/-- The integer argument registers `RDI RSI RDX RCX R8 R9`, by hardware number. -/
def intArgRegs : List Nat := [7, 6, 2, 1, 8, 9]

/-- The state of the assignment: integer argument registers used, vector registers used, and
the next offset in the argument area. -/
structure Next where
  gp : Nat := 0
  sse : Nat := 0
  stack : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- The register pieces of an argument whose classes fit: eightbyte `i` is `8i ..` of the
value. -/
def regPieces (sz : Nat) : Nat → Nat → Nat → List Cls → List Piece
  | _, _, _, [] => []
  | i, gp, sse, c :: cs =>
    let len := min 8 (sz - 8 * i)
    match c with
    | .integer => ⟨8 * i, len, .gpr (intArgRegs.getD gp 0)⟩ :: regPieces sz (i + 1) (gp + 1) sse cs
    | .sse => ⟨8 * i, len, .vec sse 0⟩ :: regPieces sz (i + 1) gp (sse + 1) cs
    | .sseup => ⟨8 * i, len, .vec (sse - 1) 8⟩ :: regPieces sz (i + 1) gp sse cs
    | _ => regPieces sz (i + 1) gp sse cs

/-- The argument area: copied at the next offset aligned to `max 8 align`. -/
def toStack (st : Next) (t : CType) : Passing × Next :=
  let off := roundUp st.stack (max 8 (align t))
  (.direct [⟨0, size t, .stack off⟩], { st with stack := off + roundUp (size t) 8 })

/-- One argument. -/
def assign (st : Next) (t : CType) : Passing × Next :=
  let cls := classify t
  let ngp := cls.count .integer
  let nsse := cls.count .sse
  if inMemory cls ∨ 6 < st.gp + ngp ∨ 8 < st.sse + nsse then toStack st t
  else (.direct (regPieces (size t) 0 st.gp st.sse cls), { st with gp := st.gp + ngp, sse := st.sse + nsse })

/-- All arguments, in order, from state `st`. -/
def assignAll (st : Next) : List CType → List Passing × Next
  | [] => ([], st)
  | t :: ts =>
    let r := assign st t
    let rs := assignAll r.2 ts
    (r.1 :: rs.1, rs.2)

/-- The result registers of a class sequence: INTEGER in `RAX`, `RDX`; SSE in `XMM0`, `XMM1`;
SSEUP the upper half of the preceding one. -/
def resPieces (sz : Nat) : Nat → Nat → Nat → List Cls → List Piece
  | _, _, _, [] => []
  | i, gp, sse, c :: cs =>
    let len := min 8 (sz - 8 * i)
    match c with
    | .integer => ⟨8 * i, len, .gpr ([0, 2].getD gp 0)⟩ :: resPieces sz (i + 1) (gp + 1) sse cs
    | .sse => ⟨8 * i, len, .vec sse 0⟩ :: resPieces sz (i + 1) gp (sse + 1) cs
    | .sseup => ⟨8 * i, len, .vec (sse - 1) 8⟩ :: resPieces sz (i + 1) gp sse cs
    | _ => resPieces sz (i + 1) gp sse cs

/-- The result of type `t`. A MEMORY result is `indirect (.gpr 7)`: its buffer address is
passed in `RDI` and returned in `RAX`. An x87 `long double` is the 10 significant bytes in
`ST0`. -/
def result (t : CType) : Passing :=
  match classify t with
  | [.complexX87] => .direct [⟨0, 10, .x87 0⟩, ⟨16, 10, .x87 1⟩]
  | [.x87, .x87up] => .direct [⟨0, 10, .x87 0⟩]
  | cls => if inMemory cls then .indirect (.gpr 7) else .direct (resPieces (size t) 0 0 0 cls)

/-- A prototype (as `Janus.C.AAPCS64.Sig`). -/
structure Sig where
  ret : Option CType := none
  args : List CType
  named : Option Nat := none
deriving Repr, Inhabited

/-- A MEMORY result takes `RDI`. -/
def Sig.start (sig : Sig) : Next :=
  match sig.ret.map result with
  | some (.indirect _) => { gp := 1 }
  | _ => {}

def Sig.passing (sig : Sig) : List Passing := (assignAll sig.start sig.args).1
def Sig.stackSize (sig : Sig) : Nat := (assignAll sig.start sig.args).2.stack
def Sig.resultPassing (sig : Sig) : Option Passing := sig.ret.map result
/-- The number of vector registers the call uses: `AL` must be at least this (and at most 8)
for a variadic callee. -/
def Sig.vecRegs (sig : Sig) : Nat := (assignAll sig.start sig.args).2.sse

/-! ## `va_list` (§3.5.7)

```c
typedef struct {
    unsigned int gp_offset;   // offset in reg_save_area of the next integer register
    unsigned int fp_offset;   // offset in reg_save_area of the next vector register
    void *overflow_arg_area;  // next argument passed in memory
    void *reg_save_area;      // RDI RSI RDX RCX R8 R9 at 0..47, XMM0..XMM7 at 48..175
} va_list[1];                 // 24 bytes, 8-aligned
``` -/

structure VaList where
  gpOffset : Nat
  fpOffset : Nat
  overflow : Nat
  regSave : Nat
deriving Repr, DecidableEq, Inhabited

def vaListOffsets : List Nat := [0, 4, 8, 16]

/-- `va_start`: `named` is the state after the named parameters (and the hidden result
pointer), `argArea` the first byte above the return address at entry (`RSP + 8`). -/
def vaStart (named : Next) (argArea regSave : Nat) : VaList :=
  ⟨8 * named.gp, 48 + 16 * named.sse, argArea + named.stack, regSave⟩

/-- `va_arg` from the overflow area (§3.5.7 step 7–11). -/
def fromOverflow (rd : Nat → Nat → Nat) (l : VaList) (t : CType) : Nat × VaList :=
  let a := if 8 < align t then roundUp l.overflow 16 else l.overflow
  (rd a (size t), { l with overflow := a + roundUp (size t) 8 })

/-- The value of an argument fetched from the register save area, eightbyte by eightbyte. -/
def fromRegs (rd : Nat → Nat → Nat) (base sz : Nat) : Nat → Nat → Nat → List Cls → Nat
  | _, _, _, [] => 0
  | i, gp, fp, c :: cs =>
    let len := min 8 (sz - 8 * i)
    let rest (gp' fp' : Nat) := fromRegs rd base sz (i + 1) gp' fp' cs
    match c with
    | .integer => rd (base + gp) len * 2 ^ (64 * i) + rest (gp + 8) fp
    | .sse => rd (base + fp) len * 2 ^ (64 * i) + rest gp (fp + 16)
    | .sseup => rd (base + fp - 16 + 8) len * 2 ^ (64 * i) + rest gp fp
    | _ => rest gp fp

/-- `va_arg(ap, t)` (§3.5.7): the value and the updated `va_list`. -/
def vaArg (rd : Nat → Nat → Nat) (l : VaList) (t : CType) : Nat × VaList :=
  let cls := classify t
  let ngp := cls.count .integer
  let nfp := cls.count .sse
  if inMemory cls ∨ 48 < l.gpOffset + 8 * ngp ∨ 176 < l.fpOffset + 16 * nfp then
    fromOverflow rd l t
  else
    (fromRegs rd l.regSave (size t) 0 l.gpOffset l.fpOffset cls,
      { l with gpOffset := l.gpOffset + 8 * ngp, fpOffset := l.fpOffset + 16 * nfp })

def vaArgs (rd : Nat → Nat → Nat) : VaList → List CType → List Nat × VaList
  | l, [] => ([], l)
  | l, t :: ts =>
    let r := vaArg rd l t
    let rs := vaArgs rd r.2 ts
    (r.1 :: rs.1, rs.2)

/-! ## Checks -/

section
open CType
example : classify (struct [double, int 4 true]) = [.sse, .integer] := by decide
example : classify (struct [float, float, float, float]) = [.sse, .sse] := by decide
example : classify (struct [int 8 true, int 8 true, int 8 true]) = [.memory] := by decide
example : classify ldouble = [.x87, .x87up] := by decide
example : classify (union [ldouble, int 8 true]) = [.memory] := by decide
/-- The nested cleanup: a union of `long double` and `int` inside a union is MEMORY although
merging its scalars with the `long`s would give two INTEGER eightbytes. -/
example : classify (union [array (int 1 true) 2, array (int 8 true) 2,
    union [ldouble, int 1 false]]) = [.memory] := by decide
example : classify (struct [vec 16]) = [.sse, .sseup] := by decide
example : classify (struct [vec 16, vec 16]) = [.memory] := by decide
/-- Ten integers: six in registers, four in the argument area. -/
example : (Sig.passing ⟨none, List.replicate 10 (int 8 true), none⟩).drop 5 =
    [.direct [⟨0, 8, .gpr 9⟩], .direct [⟨0, 8, .stack 0⟩], .direct [⟨0, 8, .stack 8⟩],
     .direct [⟨0, 8, .stack 16⟩], .direct [⟨0, 8, .stack 24⟩]] := by decide
/-- A MEMORY result takes `RDI`. -/
example : Sig.passing ⟨some (struct [int 8 true, int 8 true, int 8 true]), [int 8 true], none⟩ =
    [.direct [⟨0, 8, .gpr 6⟩]] := by decide
/-- A mixed struct: an SSE and an INTEGER eightbyte, `XMM0` and `RDI`. -/
example : Sig.passing ⟨none, [struct [double, int 8 true]], none⟩ =
    [.direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .gpr 7⟩]] := by decide
/-- All or nothing: a two-register struct when one register is left goes on the stack, and the
register is still used by the next argument. -/
example : (Sig.passing ⟨none, List.replicate 5 (int 8 true) ++
    [struct [int 8 true, int 8 true], int 8 true], none⟩).drop 5 =
    [.direct [⟨0, 16, .stack 0⟩], .direct [⟨0, 8, .gpr 9⟩]] := by decide
example : result (struct [double, int 8 true]) = .direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .gpr 0⟩] := by
  decide
example : result (complex ldouble) = .direct [⟨0, 10, .x87 0⟩, ⟨16, 10, .x87 1⟩] := by decide
end

end Janus.C.SysV
