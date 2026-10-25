import Janus.Float.Core
import Janus.Amd64.Float

/-!
# The x87 floating-point unit (trusted)

The x87 FPU of x86-64 as C compilers use it for `long double` (gcc and clang, System V: an
80-bit double-extended value, 16 bytes in memory). Written from the Intel SDM Vol. 1 ch. 8
("Programming with the x87 FPU") and §4.2.2, §4.8, §4.9, and the Vol. 2 `Operation`,
"FPU Flags Affected" and "Floating-Point Exceptions" sections of each instruction; the corner
cases below were checked on the oracle host (Intel Sapphire Rapids, `docs/ORACLE-AMD64.md`).
This file is pure: formats, the operations on 80-bit encodings, the register-stack state and
the instruction AST. `Janus.Amd64.X87Exec` executes the AST on `State`.

## The double-extended format

An encoding is a natural number `< 2^80`: sign (bit 79), a 15-bit biased exponent (bits 78:64,
bias 16383) and a 64-bit significand **with an explicit integer bit `J`** (bit 63) and a 63-bit
fraction. Classes (SDM Vol. 1 §8.2.2, Table 8-3):

| exponent | `J` | fraction | class | here |
|---|---|---|---|---|
| 0 | 0 | 0 | zero | |
| 0 | 0 | ≠ 0 | denormal | `DE` as an operand |
| 0 | 1 | any | pseudo-denormal | read as its value `1.f × 2^-16382`, `DE` as an operand |
| 1..7FFE | 1 | any | normal | |
| 1..7FFE | 0 | any | unnormal | **unsupported** |
| 7FFF | 1 | 0 | infinity | |
| 7FFF | 1 | `1x…` | quiet NaN | |
| 7FFF | 1 | `0x…`, ≠ 0 | signalling NaN | |
| 7FFF | 0 | any | pseudo-infinity / pseudo-NaN | **unsupported** |

An unsupported operand of an arithmetic, comparison or conversion instruction is an invalid
operation (`IE`, result the QNaN indefinite), with priority over NaN operands (checked on the
host). A supported encoding is read through `std`, the standard IEEE format `ext` = (15, 63)
of the core (`Janus.Float`), whose classes and values coincide with Table 8-3 (a
pseudo-denormal becomes the normal number of the same value). Results are produced by the
core's `round` and written back with `J` explicit (`widen`); the x87 never produces a
pseudo-denormal or an unsupported encoding.

## Precision and rounding control

The control word's `PC` field (bits 9:8) rounds the significand of `FADD FSUB FMUL FDIV FSQRT`
(and their `P`/`R`/`I` forms) to 24 (`00`), 53 (`10`) or 64 (`11`) bits; the exponent range
stays the extended one (so `PC = 24` results are the binary interchange format (15, 23), with
denormals at the extended `emin` and 24 significand bits measured from `J`: checked on the host).
`PC = 01` is reserved: such an instruction faults (`undefinedResult`; the host behaves as `11`).
Loads, stores and conversions ignore `PC`. `RC` (bits 11:10) is the rounding direction of every
rounding operation. Tininess is detected **after rounding** (with the unbounded exponent at the
target precision), as for SSE (host-checked: a product `2^-16382 × (1 − 2^-66)` raises only
`PE`).

## NaNs (SDM Vol. 1 Table 4-7, x87 column)

One NaN operand: that NaN, quieted. A signalling and a quiet NaN: the quiet one. Two of the
same kind: the one with the larger significand, quieted; equal significands: the positive one
unless both are negative (host-checked). Any signalling NaN raises `IE`. Invalid operations
(`∞ − ∞`, `0 × ∞`, `0/0`, `∞/∞`, `√` of a negative non-zero, unsupported operands) deliver the
QNaN indefinite `FFFF C000000000000000`.

## Exceptions

Priority as in §4.9.2: unsupported or signalling-NaN operand (`IE`), quiet-NaN operand, other
invalid operations and division by zero (`ZE`), denormal operand (`DE`), then overflow
(`OE PE`) or underflow (masked: `UE PE` for a tiny **inexact** result) and inexact (`PE`). An
operation returns an `XR`: the result and the flags of the masked response, `traps` (the
exceptions that make it trap when unmasked: an unmasked underflow traps for every tiny result),
and `c1`, the "rounded up" bit (`|result| > |exact|`) that the instructions copy into `C1`.

The **unmasked** response of the x87 is not modelled: the hardware completes the instruction
(storing, for overflow and underflow, a re-biased result), sets `ES`, and raises `#MF` at the
next waiting x87 instruction. The model instead faults (`Fault.fpuException`) at the
instruction that raised the exception. That stops earlier than the hardware, so every
non-faulting run of the model is a run of the hardware.
-/

namespace Janus.Amd64.X87

open Janus.Float
open Janus.Amd64.FP (IE DE ZE OE UE PE)

/-! ## Formats and encodings -/

/-- The standard IEEE format with the x87 exponent range and a 64-bit significand: the view of
a supported double-extended encoding with its integer bit dropped. -/
def ext : Fmt := ⟨15, 63⟩

/-- The format results are rounded to under precision `p` (24, 53 or 64 significand bits): the
extended exponent range, `p - 1` fraction bits. -/
def fmtP (p : Nat) : Fmt := ⟨15, p - 1⟩

def signOf80 (x : Nat) : Bool := x / 2 ^ 79 % 2 = 1
def expOf80 (x : Nat) : Nat := x / 2 ^ 64 % 2 ^ 15
/-- The 64-bit significand, integer bit included. -/
def sigOf80 (x : Nat) : Nat := x % 2 ^ 64
/-- The explicit integer bit `J` (bit 63). -/
def jOf80 (x : Nat) : Bool := x / 2 ^ 63 % 2 = 1

/-- The encoding `sign : exponent : significand`. -/
def pack80 (s : Bool) (e sig : Nat) : Nat := (if s then 2 ^ 79 else 0) + e * 2 ^ 64 + sig

def zero80 (s : Bool) : Nat := pack80 s 0 0
def inf80 (s : Bool) : Nat := pack80 s 0x7FFF (2 ^ 63)
/-- The QNaN floating-point indefinite. -/
def indefinite80 : Nat := pack80 true 0x7FFF 0xC000000000000000
/-- `+1.0` (`FLD1`). -/
def one80 : Nat := pack80 false 16383 (2 ^ 63)

/-- Unnormals, pseudo-infinities and pseudo-NaNs: a non-zero exponent with `J = 0`. -/
def unsupported (x : Nat) : Bool := expOf80 x != 0 && !jOf80 x

/-- A denormal or pseudo-denormal encoding (`DE` when it is an operand). -/
def isDenormal (x : Nat) : Bool := expOf80 x == 0 && sigOf80 x != 0

/-- The `ext` encoding of a supported double-extended encoding: `J` dropped; a pseudo-denormal
becomes the normal number with biased exponent 1 and the same fraction (the same value). -/
def std (x : Nat) : Nat :=
  pack ext (signOf80 x) (if expOf80 x = 0 ∧ jOf80 x then 1 else expOf80 x) (sigOf80 x % 2 ^ 63)

/-- The double-extended encoding of a result rounded to `fmtP p` (`J` explicit, the fraction
left-aligned in the 63 fraction bits). -/
def widen (p : Nat) (y : Nat) : Nat :=
  let f := fmtP p
  pack80 (signOf f y) (expOf f y)
    ((if expOf f y = 0 then 0 else 2 ^ 63) + fracOf f y * 2 ^ (64 - p))

/-- The double-extended encoding of an `ext` encoding. -/
def ofStd (y : Nat) : Nat := widen 64 y

/-- The class of a **supported** encoding. -/
def kind (x : Nat) : Kind := classify ext (std x)

def isNaN80 (x : Nat) : Bool := !unsupported x && isNaN ext (std x)
def isSNaN80 (x : Nat) : Bool := !unsupported x && isSNaN ext (std x)

/-- `x` with its quiet bit (bit 62) set. -/
def quiet80 (x : Nat) : Nat := x ||| 2 ^ 62

/-! ## Results -/

/-- The outcome of an operation: the result, the flags of the masked response, the
exceptions that trap when unmasked, and whether the result was rounded up in magnitude (`C1`). -/
structure XR where
  res : Nat
  flags : Nat
  traps : Nat
  c1 : Bool
deriving DecidableEq, Repr, Inhabited

/-- An exact result with flags `fl` (which are also the trapping ones). -/
def done (r fl : Nat) : XR := ⟨r, fl, fl, false⟩

/-- Round the exact non-zero value `(-1)^neg * m * 2^e` to `f` by `rm` and encode it with
`out`, with the flags `pre` already raised (`DE`): overflow (`OE PE`), underflow (tininess
after rounding; masked: `UE PE` when inexact; unmasked: traps on every tiny result), inexact
(`PE`), and `C1` = the magnitude was rounded up. -/
def roundP (f : Fmt) (out : Nat → Nat) (rm : RM) (pre : Nat) (neg : Bool) (m : Nat) (e : Int) :
    XR :=
  let r := round f rm neg m e
  let up := r.inexact && r.bits != (round f .rz neg m e).bits
  let v := out r.bits
  if r.overflow then ⟨v, pre ||| OE ||| PE, pre ||| OE ||| PE, up⟩
  else if r.tinyAfter then
    if r.inexact then ⟨v, pre ||| UE ||| PE, pre ||| UE ||| PE, up⟩ else ⟨v, pre, pre ||| UE, false⟩
  else if r.inexact then ⟨v, pre ||| PE, pre ||| PE, up⟩
  else ⟨v, pre, pre, false⟩

/-- The NaN result of an operation with a NaN operand (neither unsupported), and `IE` for a
signalling one. -/
def nanPick (a b : Nat) : Nat × Nat :=
  let fl := if isSNaN80 a || isSNaN80 b then IE else 0
  let r :=
    if isNaN80 a && isNaN80 b then
      if isSNaN80 a && !isSNaN80 b then b
      else if isSNaN80 b && !isSNaN80 a then a
      else if sigOf80 a > sigOf80 b then a
      else if sigOf80 b > sigOf80 a then b
      else if signOf80 a then b else a
    else if isNaN80 a then a else b
  (quiet80 r, fl)

/-! ## Arithmetic -/

/-- `FADD`/`FSUB`/`FMUL`/`FDIV` (operand order as computed: `a op b`). -/
inductive BinOp where
  | add | sub | mul | div
deriving DecidableEq, Repr, Inhabited

/-- The `DE` flag of an operation on `a` and `b` (`bDen`: the second operand came from a
denormal single/double-precision memory operand; converted exactly, it is normal in
double-extended, but the instruction still raises `DE`). -/
def deOf (a b : Nat) (bDen : Bool) : Nat := if isDenormal a || isDenormal b || bDen then DE else 0

/-- `-v`. -/
def Val.neg : Val → Val
  | .num n e => .num (-n) e
  | .inf s => .inf (!s)

/-- The sum of two non-NaN operands of classes `ka`, `kb`, signs `sa`, `sb` and values `va`,
`vb` (for a subtraction, `sb` and `vb` are those of the negated subtrahend). -/
def addCore (p : Nat) (rm : RM) (ka kb : Kind) (sa sb : Bool) (va vb : Val) (de : Nat) : XR :=
  if ka = .inf && kb = .inf && sa != sb then done indefinite80 IE
  else if ka = .inf then done (inf80 sa) de
  else if kb = .inf then done (inf80 sb) de
  else if ka = .zero && kb = .zero then done (zero80 (if sa == sb then sa else rm = .rmi)) de
  else
    match addExact va.n va.e vb.n vb.e with
    | none => done (zero80 (rm = .rmi)) de
    | some (neg, m, e) => roundP (fmtP p) (widen p) rm de neg m e

/-- The product of two non-NaN operands. -/
def mulCore (p : Nat) (rm : RM) (ka kb : Kind) (sa sb : Bool) (va vb : Val) (de : Nat) : XR :=
  if (ka = .inf && kb = .zero) || (ka = .zero && kb = .inf) then done indefinite80 IE
  else if ka = .inf || kb = .inf then done (inf80 (sa != sb)) de
  else if ka = .zero || kb = .zero then done (zero80 (sa != sb)) de
  else
    match mulExact va.n va.e vb.n vb.e with
    | none => done (zero80 (sa != sb)) de
    | some (neg, m, e) => roundP (fmtP p) (widen p) rm de neg m e

/-- The quotient of two non-NaN operands (`ZE` for a finite non-zero or zero dividend over a
zero divisor, except `0/0`). -/
def divCore (p : Nat) (rm : RM) (ka kb : Kind) (sa sb : Bool) (va vb : Val) (de : Nat) : XR :=
  if (ka = .inf && kb = .inf) || (ka = .zero && kb = .zero) then done indefinite80 IE
  else if kb = .zero && ka != .inf then done (inf80 (sa != sb)) ZE
  else if ka = .inf then done (inf80 (sa != sb)) de
  else if kb = .inf || ka = .zero then done (zero80 (sa != sb)) de
  else
    match va.mag, vb.mag with
    | (m1, e1), (m2, e2) =>
      match divOdd (fmtP p).fbits m1 e1 m2 e2 with
      | (m, e) => roundP (fmtP p) (widen p) rm de (sa != sb) m e

/-- `a op b` rounded to precision `p` by `rm` (`bDen`: see `deOf`). -/
def binop (op : BinOp) (p : Nat) (rm : RM) (a b : Nat) (bDen : Bool := false) : XR :=
  if unsupported a || unsupported b then done indefinite80 IE
  else if isNaN80 a || isNaN80 b then done (nanPick a b).1 (nanPick a b).2
  else
    match op with
    | .add => addCore p rm (kind a) (kind b) (signOf80 a) (signOf80 b) (valueOf ext (std a))
        (valueOf ext (std b)) (deOf a b bDen)
    | .sub => addCore p rm (kind a) (kind b) (signOf80 a) (!signOf80 b) (valueOf ext (std a))
        (Val.neg (valueOf ext (std b))) (deOf a b bDen)
    | .mul => mulCore p rm (kind a) (kind b) (signOf80 a) (signOf80 b) (valueOf ext (std a))
        (valueOf ext (std b)) (deOf a b bDen)
    | .div => divCore p rm (kind a) (kind b) (signOf80 a) (signOf80 b) (valueOf ext (std a))
        (valueOf ext (std b)) (deOf a b bDen)

/-- `FSQRT` of `x` at precision `p`. -/
def sqrt (p : Nat) (rm : RM) (x : Nat) : XR :=
  if unsupported x then done indefinite80 IE else
  if isNaN80 x then done (quiet80 x) (if isSNaN80 x then IE else 0) else
  match kind x with
  | .zero => done x 0
  | k =>
    if signOf80 x then done indefinite80 IE
    else if k = .inf then done x 0
    else
      let de := if isDenormal x then DE else 0
      let (m, e) := (valueOf ext (std x)).mag
      let (m', e') := sqrtOdd (fmtP p).fbits m e
      roundP (fmtP p) (widen p) rm de false m' e'

/-! ## Comparisons -/

/-- The relation of `a` and `b` (`none` = unordered, else `-1`, `0`, `1`) and the flags:
`IE` for an unsupported operand, a signalling NaN, or (`signal`: `FCOM`, `FCOMI`, `FTST`) any
NaN; `DE` for a denormal operand of an ordered comparison. -/
def compare (signal : Bool) (a b : Nat) (bDen : Bool := false) : Option Int × Nat :=
  if unsupported a || unsupported b then (none, IE)
  else if isNaN80 a || isNaN80 b then
    (none, if signal || isSNaN80 a || isSNaN80 b then IE else 0)
  else
    let de := if isDenormal a || isDenormal b || bDen then DE else 0
    let va := valueOf ext (std a)
    let vb := valueOf ext (std b)
    (some (if Val.eq va vb then 0 else if Val.lt va vb then -1 else 1), de)

/-- `C3 C2 C0` (as bits 2, 1, 0) of `FCOM`/`FUCOM`/`FTST`, and `ZF PF CF` of `FCOMI`/`FUCOMI`
in the same positions: unordered `111`, greater `000`, less `001`, equal `100`. -/
def relBits : Option Int → Nat
  | none => 0b111
  | some r => if r = 0 then 0b100 else if r < 0 then 0b001 else 0b000

/-- `FXAM`'s class code `C3 C2 C0` (bits 2, 1, 0) of a non-empty register. -/
def xamCode (x : Nat) : Nat :=
  if unsupported x then 0b000 else
  -- a pseudo-denormal reads as a normal value but is classified as a denormal (host-checked)
  if isDenormal x then 0b110 else
  match kind x with
  | .qnan | .snan => 0b001
  | .normal => 0b010
  | .inf => 0b011
  | .zero => 0b100
  | .subnormal => 0b110

/-! ## Conversions -/

/-- `FLD m32fp`/`m64fp` (and the memory operand of `FADD m32fp`, ...): the binary32/64
encoding `x` of `f` as double-extended. Exact; a NaN keeps its sign and (left-aligned) payload
and is quieted with `IE` if signalling; a subnormal raises `DE`. -/
def fromFmt (f : Fmt) (x : Nat) : XR :=
  let s := signOf f x
  match classify f x with
  | .qnan | .snan =>
    done (pack80 s 0x7FFF (2 ^ 63 + (fracOf f x ||| f.quietBit) * 2 ^ (63 - f.fbits)))
      (if isSNaN f x then IE else 0)
  | .inf => done (inf80 s) 0
  | .zero => done (zero80 s) 0
  | k =>
    let (m, e) := (valueOf f x).mag
    roundP ext ofStd .rne (if k = .subnormal then DE else 0) s m e

/-- The memory operand of `FADD m32fp`, ... as double-extended, **without** quieting a
signalling NaN (the operation's NaN rules see it as signalling), with whether it was a
subnormal (`DE`). -/
def extend (f : Fmt) (x : Nat) : Nat × Bool :=
  let s := signOf f x
  match classify f x with
  | .qnan | .snan => (pack80 s 0x7FFF (2 ^ 63 + fracOf f x * 2 ^ (63 - f.fbits)), false)
  | k => ((fromFmt f x).res, k = .subnormal)

/-- `FST`/`FSTP m32fp`/`m64fp`: `x` rounded to `g` by `rm`. An unsupported value stores `g`'s
indefinite with `IE`; a NaN keeps its sign and the top fraction bits, quieted (`IE` if
signalling); no `DE` (host-checked). -/
def toFmt (g : Fmt) (rm : RM) (x : Nat) : XR :=
  if unsupported x then done (FP.indefinite g) IE else
  let s := signOf80 x
  match kind x with
  | .qnan | .snan =>
    done (pack g s g.expMax (g.quietBit ||| (sigOf80 x % 2 ^ 63) / 2 ^ (63 - g.fbits)))
      (if isSNaN80 x then IE else 0)
  | .inf => done (inf g s) 0
  | .zero => done (zero g s) 0
  | _ =>
    let (m, e) := (valueOf ext (std x)).mag
    roundP g id rm 0 s m e

/-- `FILD`: the `w`-bit two's-complement integer `v` as double-extended (exact). -/
def ofInt (w v : Nat) : Nat :=
  let i : Int := if v % 2 ^ w < 2 ^ (w - 1) then v % 2 ^ w else ((v % 2 ^ w : Nat) : Int) - 2 ^ w
  if i = 0 then zero80 false else (roundP ext ofStd .rne 0 (decide (i < 0)) i.natAbs 0).res

/-- `FIST`/`FISTP` (`rm` = `RC`) and `FISTTP` (`rm = .rz`) to a `w`-bit integer: a NaN, an
infinity, an unsupported value or one out of range gives the integer indefinite `2^(w-1)`
with `IE`; an inexact result raises `PE` and sets `C1` when rounded up in magnitude. No `DE`
(host-checked). -/
def toInt (w : Nat) (rm : RM) (x : Nat) : XR :=
  let indef := 2 ^ (w - 1)
  if unsupported x || isNaN80 x then done indef IE else
  match kind x with
  | .inf => done indef IE
  | .zero => done 0 0
  | _ =>
    let s := signOf80 x
    let (m, e) := (valueOf ext (std x)).mag
    let (i, inexact) := roundToInt rm s m e
    let (t, _) := roundToInt .rz s m e
    if i < -(2 ^ (w - 1) : Int) || i ≥ 2 ^ (w - 1) then done indef IE
    else
      let fl := if inexact then PE else 0
      ⟨(i % (2 ^ w : Int)).toNat, fl, fl, inexact && decide (i.natAbs > t.natAbs)⟩

/-! ## The control and status words -/

/-- What `FLDCW` keeps of the 16-bit value it loads (`FNSTCW` reads back bits 12:8 and 5:0,
with the reserved bit 6 set and bits 15:13 and 7 clear; host-checked: `0 ↦ 0x0040`,
`0xFFFF ↦ 0x1F7F`). -/
def normCW (v : Nat) : Nat := v % 2 ^ 16 &&& 0x1F3F ||| 0x40

/-- The precision of `PC` (bits 9:8): `none` for the reserved `01`. -/
def precision (cw : Nat) : Option Nat :=
  let pc := cw / 256 % 4
  if pc = 0 then some 24 else if pc = 2 then some 53 else if pc = 3 then some 64 else none

/-- The rounding direction of `RC` (bits 11:10). -/
def rounding (cw : Nat) : RM := FP.decodeRC (cw / 1024 % 4)

/-- The exceptions that are unmasked (`NOT CW<5:0>`, aligned with the flags). -/
def unmasked (cw : Nat) : Nat := 0x3F - cw % 64

/-! ## State -/

/-- The x87 FPU state: the eight physical data registers `R0`–`R7` (80-bit encodings), `TOP`
(`ST(i)` is `R[(TOP + i) mod 8]`), the abridged tag word (`tags i` iff `Ri` is in use; the
full tag is a function of the contents), the control word, the status word's exception and
summary bits and the condition codes `C0`–`C3`. A condition code the SDM leaves undefined after
an instruction is `none`; `FNSTSW` faults (`undefinedFlag`) rather than store it.

The status word field `sw` holds bits 7:0 (`IE DE ZE OE UE PE SF ES`) and bit 15 (`B`); its
`TOP` and condition-code bits live in `top` and `c0`–`c3`. The instruction and data pointers
and the last opcode are not modelled (no supported instruction reads them). The defaults are
the state after `FNINIT` (Linux gives every new process this state). -/
structure St where
  regs : Nat → Nat := fun _ => 0
  top : Nat := 0
  tags : Nat → Bool := fun _ => false
  sw : Nat := 0
  c0 : Option Bool := some false
  c1 : Option Bool := some false
  c2 : Option Bool := some false
  c3 : Option Bool := some false

instance : Inhabited St := ⟨{}⟩

/-- A pending unmasked exception (`ES` set, or a raised flag whose mask is clear in the
control word `cw`): a waiting x87 instruction takes `#MF` before executing. -/
def St.pending (t : St) (cw : Nat) : Bool := t.sw / 128 % 2 = 1 || t.sw % 64 &&& unmasked cw != 0

/-- The physical register of `ST(i)`. -/
def St.phys (t : St) (i : Nat) : Nat := (t.top + i) % 8

def St.used (t : St) (r : Nat) : Bool := t.tags r

/-- `ST(i)`, or `none` if that register is empty (a stack underflow). -/
def St.get (t : St) (i : Nat) : Option Nat :=
  if t.used (t.phys i) then some (t.regs (t.phys i)) else none

/-- `ST(i) ← v` (the register becomes in use). -/
def St.set (t : St) (i v : Nat) : St :=
  let r := t.phys i
  { t with regs := fun j => if j = r then v else t.regs j, tags := fun j => if j = r then true else t.tags j }

/-- Push `v`, or `none` if `ST(7)` is in use (a stack overflow). -/
def St.push (t : St) (v : Nat) : Option St :=
  let r := (t.top + 7) % 8
  if t.used r then none
  else some { t with top := r, regs := fun j => if j = r then v else t.regs j,
                     tags := fun j => if j = r then true else t.tags j }

/-- Pop: `ST(0)` becomes empty, `TOP + 1`. -/
def St.pop (t : St) : St :=
  { t with tags := fun j => if j = t.top then false else t.tags j, top := (t.top + 1) % 8 }

/-- Raise the flags `fl` (bits 5:0). -/
def St.raise (t : St) (fl : Nat) : St := { t with sw := t.sw ||| fl % 64 }

/-- The condition codes after an instruction that sets `C1` to `c1` and leaves `C0 C2 C3`
undefined. -/
def St.ccC1 (t : St) (c1 : Option Bool) : St := { t with c0 := none, c1 := c1, c2 := none, c3 := none }

/-- The status word as `FNSTSW` stores it, or `none` if a condition code is undefined. -/
def St.statusWord (t : St) : Option Nat :=
  match t.c0, t.c1, t.c2, t.c3 with
  | some c0, some c1, some c2, some c3 =>
    some (t.sw % 256 + (if c0 then 0x100 else 0) + (if c1 then 0x200 else 0) +
      (if c2 then 0x400 else 0) + t.top % 8 * 0x800 + (if c3 then 0x4000 else 0) +
      (if t.sw / 0x8000 % 2 = 1 then 0x8000 else 0))
  | _, _, _, _ => none

/-! ## Instructions -/

/-- The six arithmetic operations of `D8`/`DC`/`DE` (`subr`: `src − dst`; `divr`: `src / dst`). -/
inductive Arith where
  | add | mul | sub | subr | div | divr
deriving DecidableEq, Repr, Inhabited

/-- Memory operand formats: binary32/64, double-extended, 16/32/64-bit integers. -/
inductive MemFmt where
  | f32 | f64 | f80 | i16 | i32 | i64
deriving DecidableEq, Repr, Inhabited

/-- The size in bytes of a memory operand. -/
def MemFmt.size : MemFmt → Nat
  | .f32 => 4 | .f64 => 8 | .f80 => 10 | .i16 => 2 | .i32 => 4 | .i64 => 8

/-- An x87 operand: `ST(i)`, or the instruction's memory operand in a format. -/
inductive Src where
  | st (i : Nat)
  | mem (k : MemFmt)
deriving DecidableEq, Repr, Inhabited

/-- The supported x87 instructions. `i < 8` throughout. -/
inductive Op where
  /-- `FADD/FMUL/FSUB/FSUBR/FDIV/FDIVR ST(0), src` with `src` = `ST(i)`, `m32fp`, `m64fp`, and
  `FIADD/...` with `m16int`/`m32int`: `ST(0) ← ST(0) op src`. -/
  | arith (op : Arith) (src : Src)
  /-- `FADD/... ST(i), ST(0)` and the popping `FADDP/FMULP/FSUBP/FSUBRP/FDIVP/FDIVRP`:
  `ST(i) ← ST(i) op ST(0)` (`subr`: `ST(0) − ST(i)`, `divr`: `ST(0) / ST(i)`), then pop. -/
  | arithTo (op : Arith) (i : Nat) (pop : Bool)
  /-- `FCOM/FCOMP/FCOMPP` (`unordered = false`), `FUCOM/FUCOMP/FUCOMPP`, `FICOM/FICOMP`:
  `C3 C2 C0` from comparing `ST(0)` with `src`, then pop `pops` times. -/
  | com (unordered : Bool) (src : Src) (pops : Nat)
  /-- `FCOMI/FCOMIP` (`unordered = false`), `FUCOMI/FUCOMIP ST(0), ST(i)`: `ZF PF CF`. -/
  | comi (unordered : Bool) (i : Nat) (pop : Bool)
  /-- `FTST`: compare `ST(0)` with `+0.0`. -/
  | tst
  /-- `FXAM`: classify `ST(0)` (also when empty). -/
  | xam
  /-- `FLD m32fp/m64fp/m80fp/ST(i)`, `FILD m16int/m32int/m64int`: push. -/
  | ld (src : Src)
  /-- `FLD1`, `FLDZ`: push the double-extended constant `v`. -/
  | ldConst (v : Nat)
  /-- `FST/FSTP m32fp/m64fp/ST(i)`, `FSTP m80fp`: store `ST(0)`, then pop if `pop`. -/
  | st (dst : Src) (pop : Bool)
  /-- `FIST/FISTP` (`trunc = false`) and `FISTTP` to `m16int/m32int/m64int`. -/
  | ist (k : MemFmt) (trunc : Bool) (pop : Bool)
  /-- `FXCH ST(i)`. -/
  | xch (i : Nat)
  /-- `FCHS`. -/
  | chs
  /-- `FABS`. -/
  | abs
  /-- `FSQRT`. -/
  | sqrt
  /-- `FCMOVcc ST(0), ST(i)`; `cc` is the `Jcc` condition number (`B` 2, `NB` 3, `E` 4,
  `NE` 5, `BE` 6, `NBE` 7, `U` 10, `NU` 11). -/
  | cmov (cc : Nat) (i : Nat)
  /-- `FLDCW m16`. -/
  | ldcw
  /-- `FNSTCW m16`. -/
  | nstcw
  /-- `FNSTSW AX` (`ax`) / `FNSTSW m16`. -/
  | nstsw (ax : Bool)
  /-- `FWAIT`. -/
  | wait
  /-- `FNCLEX`. -/
  | nclex
  /-- `FNINIT`. -/
  | ninit
  /-- `FNOP`. -/
  | nop
deriving DecidableEq, Repr, Inhabited

end Janus.Amd64.X87
