import Janus.CABI.CType

/-!
# AAPCS64 argument and result classification (pure)

The parameter-passing algorithm of the *Procedure Call Standard for the Arm 64-bit
Architecture* (AAPCS64, Arm IHI 0055, §6.8.2 "Parameter passing rules" and §6.9 "Result
return"), for GNU/Linux (`aarch64-linux-gnu`: variadic arguments follow the same rules as named
ones, and a stacked argument smaller than 8 bytes takes an 8-byte slot). It is a function of the
C types only, computed by `assign`/`assignAll`, and checked against gcc and clang by the
differential probe (`scripts/cabi-probe.sh`, docs/FFI.md § 1.3).

Stage A: `NGRN = NSRN = NSAA = 0` (`Next`). Then for each argument (stage C, after the stage B
rewrites):

* **C.1–C.6, SIMD&FP.** A floating-point, short-vector or complex scalar, or a homogeneous
  floating-point / short-vector aggregate (HFA / HVA, `CType.hfa`: 1–4 members of one base
  type) of `k` members goes in `V[NSRN] … V[NSRN+k-1]`, one member in the low bytes of each,
  if `NSRN + k ≤ 8`; otherwise `NSRN := 8` and it is stored at `NSAA` rounded up to
  `max 8 align`, taking its size rounded up to 8.
* **B.4.** Any other composite larger than 16 bytes is replaced by a pointer to a copy the
  caller makes (`Passing.indirect`), which is then passed like a pointer.
* **C.7–C.15, general registers.** An integer, pointer or (B.5: size rounded up to 8)
  composite of `n` doublewords goes in `X[NGRN] … X[NGRN+n-1]` (C.8: `NGRN` first rounded up to
  even when the type is 16-byte aligned) if they fit below `X8`; otherwise `NGRN := 8` and it
  is stored at `NSAA` rounded up to `max 8 align`, taking its size rounded up to 8.

Results (§6.9): a type that `void f(T)` would pass in registers is returned in the same
registers; otherwise the caller passes the address of a result buffer in `X8`
(`Passing.indirect (.gpr 8)`), which the callee need not preserve or return.

`va_list` (§ "Appendix B: C Variadic Functions"): `VaList`, `vaStart`, `vaArg`.
-/

namespace Janus.C.AAPCS64

open CType

/-- The state of the algorithm: the next general register (`NGRN`), the next SIMD&FP register
(`NSRN`) and the next stacked-argument offset (`NSAA`, from `SP` at the call). -/
structure Next where
  ngrn : Nat := 0
  nsrn : Nat := 0
  nsaa : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- Rules C.7–C.15 for a value of `sz` bytes and alignment `al`: general registers, or the
stack. -/
def gprOrStack (st : Next) (sz al : Nat) : List Piece × Next :=
  let ngrn := if al = 16 then roundUp st.ngrn 2 else st.ngrn
  let nregs := (sz + 7) / 8
  if ngrn + nregs ≤ 8 then
    ((List.range nregs).map fun i => ⟨8 * i, min 8 (sz - 8 * i), .gpr (ngrn + i)⟩,
      { st with ngrn := ngrn + nregs })
  else
    let off := roundUp st.nsaa (max 8 al)
    ([⟨0, sz, .stack off⟩], { st with ngrn := 8, nsaa := off + roundUp sz 8 })

/-- Rules C.1–C.6 for an HFA/HVA (or FP/vector scalar) of `k` members of base `b`. -/
def vecOrStack (st : Next) (t : CType) (b : Base) (k : Nat) : List Piece × Next :=
  if st.nsrn + k ≤ 8 then
    ((List.range k).map fun i => ⟨i * b.size, b.size, .vec (st.nsrn + i) 0⟩,
      { st with nsrn := st.nsrn + k })
  else
    let off := roundUp st.nsaa (max 8 (align t))
    ([⟨0, size t, .stack off⟩], { st with nsrn := 8, nsaa := off + roundUp (size t) 8 })

/-- B.4: composites larger than 16 bytes that are not HFA/HVA are passed by reference. -/
def byRef (t : CType) : Bool := (hfa t).isNone && isAggregate t && decide (16 < size t)

/-- One argument. -/
def assign (st : Next) (t : CType) : Passing × Next :=
  match hfa t with
  | some (b, k) => let r := vecOrStack st t b k; (.direct r.1, r.2)
  | none =>
    if byRef t then
      let r := gprOrStack st 8 8
      (.indirect ((r.1.head?.map Piece.loc).getD (.gpr 0)), r.2)
    else
      let r := gprOrStack st (size t) (align t)
      (.direct r.1, r.2)

/-- All arguments, in order, from state `st`. -/
def assignAll (st : Next) : List CType → List Passing × Next
  | [] => ([], st)
  | t :: ts =>
    let r := assign st t
    let rs := assignAll r.2 ts
    (r.1 :: rs.1, rs.2)

/-- A piece passed in a register (not on the stack). -/
def Piece.inReg (p : Piece) : Bool :=
  match p.loc with
  | .stack _ => false
  | _ => true

/-- The result of type `t` (§6.9): in the registers `void f(T)` would use, or through the
buffer whose address the caller passes in `X8`. -/
def result (t : CType) : Passing :=
  match (assign {} t).1 with
  | .direct ps => if ps.all Piece.inReg then .direct ps else .indirect (.gpr 8)
  | .indirect _ => .indirect (.gpr 8)

/-- A prototype: the result type (`none` = `void`), the parameter types, and for a variadic
function the number of named parameters (`named = some k`: `args.take k` are named, the rest
are the variadic arguments of this call, after the default argument promotions). -/
structure Sig where
  ret : Option CType := none
  args : List CType
  named : Option Nat := none
deriving Repr, Inhabited

/-- Where every argument of a call is passed (Linux: variadic arguments like named ones). -/
def Sig.passing (sig : Sig) : List Passing := (assignAll {} sig.args).1

/-- The size of the stacked-argument area the call needs (`NSAA` at the end). -/
def Sig.stackSize (sig : Sig) : Nat := (assignAll {} sig.args).2.nsaa

/-- Where the result is returned (`none` for `void`). -/
def Sig.resultPassing (sig : Sig) : Option Passing := sig.ret.map result

/-! ## `va_list` (AAPCS64 Appendix B)

```c
typedef struct va_list {
    void *__stack;   // next stacked argument
    void *__gr_top;  // end of the general-register save area
    void *__vr_top;  // end of the SIMD&FP-register save area
    int   __gr_offs; // offset from __gr_top of the next saved general register (≤ 0)
    int   __vr_offs; // offset from __vr_top of the next saved SIMD&FP register (≤ 0)
} va_list;           // 32 bytes, 8-aligned
```

`va_start` sets `__gr_offs = -8·(8 - NGRN)` and `__vr_offs = -16·(8 - NSRN)` for the state
after the named parameters; the prologue of a variadic function saves `X[NGRN] … X7` at
`__gr_top - 8·(8 - NGRN) …` and `Q[NSRN] … Q7` at `__vr_top - 16·(8 - NSRN) …` (16 bytes per
register). -/

/-- The fields of a `va_list`. -/
structure VaList where
  stack : Nat
  grTop : Nat
  vrTop : Nat
  grOffs : Int
  vrOffs : Int
deriving Repr, DecidableEq, Inhabited

/-- Byte offsets of the fields in the 32-byte `va_list` object. -/
def vaListOffsets : List Nat := [0, 8, 16, 24, 28]

/-- `va_start(ap, last)`: `named` is the state after the named parameters, `sp` the stack
pointer at the call (the stacked arguments start there), `grTop`/`vrTop` where the function's
prologue put its save areas. -/
def vaStart (named : Next) (sp grTop vrTop : Nat) : VaList :=
  ⟨sp + named.nsaa, grTop, vrTop, -(8 * (8 - (min named.ngrn 8) : Nat) : Int),
    -(16 * (8 - (min named.nsrn 8) : Nat) : Int)⟩

/-- The address the save-area offset `offs` (≤ 0) designates. -/
def atOffs (top : Nat) (offs : Int) : Nat := (top + offs).toNat

/-- `va_arg` from the stacked arguments: an argument of size `sz` and alignment `al`. -/
def fromStack (rd : Nat → Nat → Nat) (l : VaList) (sz al : Nat) : Nat × VaList :=
  let a := if 8 < al then roundUp l.stack 16 else l.stack
  (rd a sz, { l with stack := a + roundUp sz 8 })

/-- `va_arg(ap, t)`, where `rd a n` reads `n` bytes at `a` (little-endian): the value and the
updated `va_list` (Appendix B.4, as gcc and clang expand it; a register class that does not fit
any more moves its offset past 0 and takes the argument from the stack). -/
def vaArg (rd : Nat → Nat → Nat) (l : VaList) (t : CType) : Nat × VaList :=
  match hfa t with
  | some (b, k) =>
    if 0 ≤ l.vrOffs then fromStack rd l (size t) (align t)
    else
      let nr := l.vrOffs + 16 * k
      if 0 < nr then fromStack rd { l with vrOffs := nr } (size t) (align t)
      else
        ((List.range k).foldr (fun (i : Nat) acc =>
          rd (atOffs l.vrTop (l.vrOffs + 16 * (i : Int))) b.size + 2 ^ (8 * b.size) * acc) 0,
          { l with vrOffs := nr })
  | none =>
    let byref := byRef t
    let sz := if byref then 8 else size t
    let al := if byref then 8 else align t
    let finish : Nat × VaList → Nat × VaList := fun (v, l') =>
      if byref then (rd v (size t), l') else (v, l')
    if 0 ≤ l.grOffs then finish (fromStack rd l sz al)
    else
      let offs : Int := if al = 16 then (l.grOffs + 15) / 16 * 16 else l.grOffs
      let nr := offs + 8 * ((sz + 7) / 8 : Nat)
      if 0 < nr then finish (fromStack rd { l with grOffs := nr } sz al)
      else finish (rd (atOffs l.grTop offs) sz, { l with grOffs := nr })

/-- `va_arg` for each type in turn. -/
def vaArgs (rd : Nat → Nat → Nat) : VaList → List CType → List Nat × VaList
  | l, [] => ([], l)
  | l, t :: ts =>
    let r := vaArg rd l t
    let rs := vaArgs rd r.2 ts
    (r.1 :: rs.1, rs.2)

/-! ## Checks -/

section
open CType
example : Sig.passing ⟨none, [int 8 true, double, float, int 4 true], none⟩ =
    [.direct [⟨0, 8, .gpr 0⟩], .direct [⟨0, 8, .vec 0 0⟩], .direct [⟨0, 4, .vec 1 0⟩],
     .direct [⟨0, 4, .gpr 1⟩]] := by decide
/-- Ten integers: eight in `X0–X7`, two on the stack. -/
example : (Sig.passing ⟨none, List.replicate 9 (int 8 true) ++ [int 4 true], none⟩).drop 8 =
    [.direct [⟨0, 8, .stack 0⟩], .direct [⟨0, 4, .stack 8⟩]] := by decide
/-- An HFA of two doubles in two `D` registers; a 32-byte struct by reference. -/
example : Sig.passing ⟨none, [struct [double, double], struct [int 8 true, int 8 true,
    int 8 true, int 8 true]], none⟩ =
    [.direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .vec 1 0⟩], .indirect (.gpr 0)] := by decide
/-- `__int128` after one integer: `X2`, `X3` (C.8). -/
example : Sig.passing ⟨none, [int 8 true, int 16 false], none⟩ =
    [.direct [⟨0, 8, .gpr 0⟩], .direct [⟨0, 8, .gpr 2⟩, ⟨8, 8, .gpr 3⟩]] := by decide
example : result (struct [int 8 true, int 8 true, int 8 true, int 8 true]) = .indirect (.gpr 8) := by
  decide
example : result (complex double) = .direct [⟨0, 8, .vec 0 0⟩, ⟨8, 8, .vec 1 0⟩] := by decide
example : result ldouble = .direct [⟨0, 16, .vec 0 0⟩] := by decide
end

end Janus.C.AAPCS64
