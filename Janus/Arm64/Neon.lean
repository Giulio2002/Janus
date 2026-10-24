import Janus.Arm64.Vector
import Janus.Arm64.Float

/-!
# Advanced SIMD integer operations (trusted)

The `Operation` pseudocode of the Advanced SIMD integer classes that `Janus.Arm64.Vector` does
not cover, transcribed from the Arm ASL (Armv9.4-A, as translated in sail-arm's `instrs64.sail`
and `v8_base.sail`), statement by statement, with the element helpers of `Vector`
(`elem` = `Elem[x, e, esize]`, `ofElems` = the element loop, `sint` = `SInt`, `intOf u` =
`asl_Int(·, u)`, `truncInt` = `int<esize-1:0>`).

Element-size and arrangement generic: every function takes `esize` (8, 16, 32 or 64) and the
element count, or the `size`/`datasize` fields from which the decode pseudocode computes them,
so one definition covers every arrangement (`8B`, `16B`, `4H`, `8H`, `2S`, `4S`, `1D`, `2D`) and
the scalar forms (`elements = 1`, `datasize = esize`).

Saturation. The saturating instructions set `FPSR.QC` (bit 27) when an element saturates
(`if sat then FPSR.QC = '1'`); the functions return the saturation as a `Bool` next to the result
(`Res`), and the executor ORs it into `FPSR`.

Only `Nat`/`Int` arithmetic and structural recursion are used, so everything evaluates in the
kernel on literals.
-/

namespace Janus.Arm64.Neon

open Janus.Arm64

/-- A result of an integer vector operation: the value and whether any element saturated. -/
abbrev Res := Nat × Bool

/-- `∃ i < n, p i` as a Boolean fold (`sat` accumulated over the element loop). -/
def anyLane (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => anyLane p k || p k

/-- The element loop of a saturating operation: element `i` of the result is `(f i).1`, and the
operation saturated if some `(f i).2` is true. -/
def satLanes (esize n : Nat) (f : Nat → Nat × Bool) : Res :=
  (ofElems esize n fun i => (f i).1, anyLane (fun i => (f i).2) n)

/-- `SatQ(i, N, unsigned)` (`Janus.Arm64.FP.satQ`). -/
abbrev satQ := FP.satQ

/-- `RShr(value, shift, round)` (`shift > 0` in every call of the ASL; `shift = 0` is the
identity here): `(value + (1 << (shift-1))) >> shift` when rounding, else `value >> shift`,
with `>>` the arithmetic (flooring) shift of an integer. -/
def rshr (v : Int) (shift : Nat) (round : Bool) : Int :=
  if shift = 0 then v
  else if round then Int.fdiv (v + 2 ^ (shift - 1)) (2 ^ shift) else Int.fdiv v (2 ^ shift)

/-- `PolynomialMult(op1, op2)` of two `M`-bit values: carry-less multiplication. -/
def polyMul : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => polyMul k a b ^^^ (if a / 2 ^ k % 2 = 1 then b * 2 ^ k else 0)

/-- The element size `8 << UInt(size)`. -/
def esizeOf (size : Nat) : Nat := 8 * 2 ^ size

/-- `Abs(x)` of an integer. -/
def iabs (x : Int) : Int := if x < 0 then -x else x

/-! ## Three same -/

/-- Advanced SIMD three same, integer opcodes not in `threeSameOp` (`opcode = w<15:11>`), on
`datasize` bits (`datasize = esize` for the scalar forms), with `x = V[n]`, `y = V[m]`,
`d = V[d]` (read by the accumulating forms only):

* `00000` SHADD/UHADD, `00100` SHSUB/UHSUB, `00010` SRHADD/URHADD (`add_halving_*`, `sub_int`);
* `00001` SQADD/UQADD, `00101` SQSUB/UQSUB (`add_saturating`, `sub_saturating`);
* `01000` SSHL/USHL, `01001` SQSHL/UQSHL, `01010` SRSHL/URSHL, `01011` SQRSHL/UQRSHL
  (`shift_sisd`: `R = opcode<1>`, `S = opcode<0>`);
* `01110` SABD/UABD, `01111` SABA/UABA (`diff`);
* `10010` MLA/MLS (`mul_int_accum`), `10011` MUL/PMUL (`mul_int_product`);
* `10110` SQDMULH/SQRDMULH (`mul_int_doubling`);

and every opcode of `threeSameOp` (logical, ADD/SUB, compares, MAX/MIN, pairwise, ADDP). -/
def threeSameInt (U : Bool) (size opcode datasize : Nat) (x y d : Nat) : Res :=
  let e := esizeOf size
  let n := datasize / e
  let a (i : Nat) : Int := intOf U e (elem x e i)
  let b (i : Nat) : Int := intOf U e (elem y e i)
  if opcode = 0b00000 then
    (ofElems e n fun i => truncInt e (Int.fdiv (a i + b i) 2), false)
  else if opcode = 0b00010 then
    (ofElems e n fun i => truncInt e (Int.fdiv (a i + b i + 1) 2), false)
  else if opcode = 0b00100 then
    (ofElems e n fun i => truncInt e (Int.fdiv (a i - b i) 2), false)
  else if opcode = 0b00001 then satLanes e n fun i => satQ e U (a i + b i)
  else if opcode = 0b00101 then satLanes e n fun i => satQ e U (a i - b i)
  else if opcode / 4 = 0b010 then
    -- SSHL/USHL family: `shift = SInt(Elem[operand2, e, esize]<7:0>)`
    let rounding := opcode / 2 % 2 = 1
    let saturating := opcode % 2 = 1
    satLanes e n fun i =>
      let sh := sint 8 (elem y e i % 256)
      let v : Int := if sh ≥ 0 then a i * 2 ^ sh.toNat else rshr (a i) (-sh).toNat rounding
      if saturating then satQ e U v else (truncInt e v, false)
  else if opcode = 0b01110 then (ofElems e n fun i => truncInt e (iabs (a i - b i)), false)
  else if opcode = 0b01111 then
    (ofElems e n fun i => (elem d e i + truncInt e (iabs (a i - b i))) % 2 ^ e, false)
  else if opcode = 0b10010 then
    -- MLA (`U = 0`) / MLS: `product = (UInt(element1) * UInt(element2))<esize-1:0>`
    (ofElems e n fun i =>
      let p := elem x e i * elem y e i % 2 ^ e
      if U then (elem d e i + 2 ^ e - p) % 2 ^ e else (elem d e i + p) % 2 ^ e, false)
  else if opcode = 0b10011 then
    (ofElems e n fun i =>
      if U then polyMul e (elem x e i) (elem y e i) % 2 ^ e else elem x e i * elem y e i, false)
  else if opcode = 0b10110 then
    -- `product = RShr(2 * element1 * element2, esize, rounding)`, `SignedSatQ`
    satLanes e n fun i =>
      satQ e false (rshr (2 * sint e (elem x e i) * sint e (elem y e i)) e U)
  else (threeSameOp U size opcode datasize x y d, false)

/-! ## Three different -/

/-- Advanced SIMD three different (`opcode = w<15:12>`), vector (`datasize = 64`, `part` = `Q`)
and scalar (`elements = 1`). `x = V[n, 128]`, `y = V[m, 128]`, `d = V[d, 128]`; the narrow
operands are `Vpart[n, part]` / `Vpart[m, part]` (the low or high 64 bits), the wide ones the
whole register. The result is `2 * datasize` bits (`V[d, 2*datasize] = result`), except for
ADDHN/SUBHN/RADDHN/RSUBHN, whose 64-bit result is written with `Vpart[d, part]`.

`0000` SADDL/UADDL, `0001` SADDW/UADDW, `0010` SSUBL/USUBL, `0011` SSUBW/USUBW,
`0100` ADDHN/RADDHN, `0101` SABAL/UABAL, `0110` SUBHN/RSUBHN, `0111` SABDL/UABDL,
`1000` SMLAL/UMLAL, `1001` SQDMLAL, `1010` SMLSL/UMLSL, `1011` SQDMLSL, `1100` SMULL/UMULL,
`1101` SQDMULL. `n` is the element count (`64 / esize`, or 1 for the scalar forms). -/
def threeDiffOp (U : Bool) (esize n opcode part x y d : Nat) : Res :=
  let e := esize
  let lo (v : Nat) : Nat := if part = 1 then v / 2 ^ 64 else v % 2 ^ 64
  let x1 := lo x
  let y1 := lo y
  let a (i : Nat) : Int := intOf U e (elem x1 e i)
  let b (i : Nat) : Int := intOf U e (elem y1 e i)
  let wide (i : Nat) : Int := intOf U (2 * e) (elem x (2 * e) i)
  if opcode = 0b0000 then (ofElems (2 * e) n fun i => truncInt (2 * e) (a i + b i), false)
  else if opcode = 0b0001 then (ofElems (2 * e) n fun i => truncInt (2 * e) (wide i + b i), false)
  else if opcode = 0b0010 then (ofElems (2 * e) n fun i => truncInt (2 * e) (a i - b i), false)
  else if opcode = 0b0011 then (ofElems (2 * e) n fun i => truncInt (2 * e) (wide i - b i), false)
  else if opcode = 0b0100 || opcode = 0b0110 then
    -- ADDHN/SUBHN: `UInt` of the wide elements, `RShr(sum, esize, round)`, round = U
    (ofElems e n fun i =>
      let s : Int := if opcode = 0b0100 then (elem x (2 * e) i : Int) + elem y (2 * e) i
        else (elem x (2 * e) i : Int) - elem y (2 * e) i
      truncInt e (rshr s e U), false)
  else if opcode = 0b0101 then
    (ofElems (2 * e) n fun i => (elem d (2 * e) i + truncInt (2 * e) (iabs (a i - b i))) % 2 ^ (2 * e),
     false)
  else if opcode = 0b0111 then
    (ofElems (2 * e) n fun i => truncInt (2 * e) (iabs (a i - b i)), false)
  else if opcode = 0b1000 || opcode = 0b1010 then
    (ofElems (2 * e) n fun i =>
      let p := truncInt (2 * e) (a i * b i)
      if opcode = 0b1010 then (elem d (2 * e) i + 2 ^ (2 * e) - p) % 2 ^ (2 * e)
      else (elem d (2 * e) i + p) % 2 ^ (2 * e), false)
  else if opcode = 0b1100 then (ofElems (2 * e) n fun i => truncInt (2 * e) (a i * b i), false)
  else
    -- SQDMLAL (`1001`), SQDMLSL (`1011`), SQDMULL (`1101`): signed elements
    let sa (i : Nat) : Int := sint e (elem x1 e i)
    let sb (i : Nat) : Int := sint e (elem y1 e i)
    satLanes (2 * e) n fun i =>
      let (p, sat1) := satQ (2 * e) false (2 * sa i * sb i)
      if opcode = 0b1101 then (p, sat1)
      else
        let acc : Int := if opcode = 0b1011 then sint (2 * e) (elem d (2 * e) i) - sint (2 * e) p
          else sint (2 * e) (elem d (2 * e) i) + sint (2 * e) p
        let (r, sat2) := satQ (2 * e) false acc
        (r, sat1 || sat2)

/-! ## Two-register miscellaneous -/

/-- `CountLeadingSignBits(x) = CountLeadingZeroBits(x<N-1:1> EOR x<N-2:0>)` of an `n`-bit value
(`clzNat` is `CountLeadingZeroBits`). -/
def clsN (n x : Nat) : Nat :=
  let v := x % 2 ^ n
  clzNat (n - 1) ((v / 2) ^^^ (v % 2 ^ (n - 1)))

/-- Advanced SIMD two-register miscellaneous, integer opcodes not in `twoMiscOp`
(`opcode = w<16:12>`), on `datasize` bits, `x = V[n, datasize]`, `d = V[d, datasize]`:

* `00010` SADDLP/UADDLP, `00110` SADALP/UADALP (`add_pairwise`: `esize`-bit pairs summed into
  `2*esize`-bit elements, accumulated for `op = opcode<2>`);
* `00011` SUQADD/USQADD (`add_saturating`: `SUQADD` adds the unsigned operand to the signed
  accumulator, `USQADD` the signed operand to the unsigned one);
* `00100` CLS/CLZ (`clsz`);
* `00111` SQABS/SQNEG (`diff_neg_sat`).

and every opcode of `twoMiscOp` (REV, CNT/NOT/RBIT, compares with zero, ABS/NEG). -/
def twoMiscInt (U : Bool) (size opcode datasize x d : Nat) : Res :=
  let e := esizeOf size
  let n := datasize / e
  if opcode = 0b00010 || opcode = 0b00110 then
    let acc := opcode = 0b00110
    (ofElems (2 * e) (n / 2) fun i =>
      let s : Int := intOf U e (elem x e (2 * i)) + intOf U e (elem x e (2 * i + 1))
      let r := truncInt (2 * e) s
      if acc then (elem d (2 * e) i + r) % 2 ^ (2 * e) else r, false)
  else if opcode = 0b00011 then
    satLanes e n fun i =>
      -- `element = Int(Elem[operand], !unsigned); op2 = Int(Elem[operand2], unsigned)`
      let op1 : Int := intOf (!U) e (elem x e i)
      let op2 : Int := intOf U e (elem d e i)
      satQ e U (op1 + op2)
  else if opcode = 0b00100 then
    (ofElems e n fun i => if U then clzNat e (elem x e i) else clsN e (elem x e i), false)
  else if opcode = 0b00111 then
    satLanes e n fun i =>
      let v := sint e (elem x e i)
      satQ e false (if U then -v else iabs v)
  else (twoMiscOp U size opcode datasize x, false)

/-- The narrowing two-register forms (`datasize = 64` vector, `part = Q`; or scalar with
`elements = 1`): `opcode = 10010` is XTN (`U = 0`) / SQXTUN (`U = 1`), `opcode = 10100` SQXTN
(`U = 0`) / UQXTN (`U = 1`). `x = V[n, 128]` (the `2*esize`-bit elements); the result has `n` elements of
`esize` bits. -/
def narrowOp (U : Bool) (esize n opcode x : Nat) : Res :=
  let e := esize
  if opcode = 0b10010 then
    if !U then (ofElems e n fun i => elem x (2 * e) i, false)
    else satLanes e n fun i => satQ e true (sint (2 * e) (elem x (2 * e) i))
  else satLanes e n fun i => satQ e U (intOf U (2 * e) (elem x (2 * e) i))

/-- SHLL/SHLL2: `Elem[result, e, 2*esize] = (UInt(Elem[operand, e, esize]) << esize)`, `x` the
64-bit `Vpart[n, part]`. -/
def shllNOp (esize x : Nat) : Nat :=
  ofElems (2 * esize) (64 / esize) fun i => elem x esize i * 2 ^ esize % 2 ^ (2 * esize)

/-! ## Across lanes and scalar pairwise -/

/-- `Reduce(ReduceOp_ADD, input, esize)` over `n` elements: the wrapping sum (the ASL's
halving tree; addition modulo `2^esize` is associative, so it equals the linear sum). -/
def reduceAdd (esize x n : Nat) : Nat := truncInt esize (sumElems true esize x n)

/-! ## Permute -/

/-- Advanced SIMD permute (`opcode = w<14:12>`): `001` UZP1, `010` TRN1, `011` ZIP1, `101` UZP2,
`110` TRN2, `111` ZIP2; `part = opcode<2>`. `x = V[n]`, `y = V[m]` (`datasize` bits). -/
def permOp (esize datasize opcode x y : Nat) : Nat :=
  let n := datasize / esize
  let part := opcode / 4
  let op := opcode % 4
  if op = 1 then
    -- UZP: `zipped = operandh:operandl; Elem[result, e] = Elem[zipped, 2*e+part]`
    ofElems esize n fun i => pairElem x y esize n (2 * i + part)
  else if op = 2 then
    -- TRN: `Elem[result, 2p] = Elem[op1, 2p+part]; Elem[result, 2p+1] = Elem[op2, 2p+part]`
    ofElems esize n fun i => if i % 2 = 0 then elem x esize (i + part) else elem y esize (i - 1 + part)
  else
    -- ZIP: `base = part * pairs; Elem[result, 2p] = Elem[op1, base+p]; Elem[result, 2p+1] = Elem[op2, base+p]`
    let base := part * (n / 2)
    ofElems esize n fun i => if i % 2 = 0 then elem x esize (base + i / 2) else elem y esize (base + i / 2)

/-! ## Shift by immediate -/

/-- Advanced SIMD shift by immediate, the opcodes not in `shiftImmOp` (`opcode = w<15:11>`), on
`datasize` bits with `esize` from `immh` and `immhb = UInt(immh:immb)`:

* `00100` SRSHR/URSHR, `00110` SRSRA/URSRA (`shift_right`: `round = opcode<2>`,
  `accumulate = opcode<1>`; `shift = 2*esize - immhb`);
* `01100` SQSHLU (`U = 1`), `01110` SQSHL/UQSHL (immediate) (`shift_left_sat`:
  `shift = immhb - esize`; source signed unless UQSHL, destination unsigned unless SQSHL);

and every opcode of `shiftImmOp` (SSHR/USHR, SSRA/USRA, SHL, SLI, SRI). `x = V[n]`, `d = V[d]`. -/
def shiftImmInt (U : Bool) (esize opcode datasize immhb : Nat) (x d : Nat) : Res :=
  let n := datasize / esize
  if opcode = 0b00100 || opcode = 0b00110 then
    let acc := opcode = 0b00110
    let sh := 2 * esize - immhb
    (ofElems esize n fun i =>
      truncInt esize ((if acc then (elem d esize i : Int) else 0) +
        rshr (intOf U esize (elem x esize i)) sh true), false)
  else if opcode = 0b01100 || opcode = 0b01110 then
    let sh := immhb - esize
    -- `op:U` = 01 SQSHLU (signed -> unsigned), 10 SQSHL (signed), 11 UQSHL (unsigned)
    let srcU := opcode = 0b01110 && U
    let dstU := U
    satLanes esize n fun i => satQ esize dstU (intOf srcU esize (elem x esize i) * 2 ^ sh)
  else (shiftImmOp U esize opcode datasize immhb x d, false)

/-- The narrowing shifts by immediate (`shift = 2*esize - immhb`; operand `2*esize`-bit
elements of `x = V[n, 128]`, `n` result elements of `esize` bits):

* `10000` SHRN (`U = 0`) / SQSHRUN (`U = 1`), `10001` RSHRN / SQRSHRUN (`round = opcode<0>`);
* `10010` SQSHRN/UQSHRN, `10011` SQRSHRN/UQRSHRN.

SHRN/RSHRN use `UInt` elements and truncate; SQSHRUN/SQRSHRUN `SInt` elements saturated to
unsigned; SQ/UQ(R)SHRN `asl_Int(·, U)` saturated to the same signedness. -/
def shiftNarrowOp (U : Bool) (esize n opcode shift x : Nat) : Res :=
  let round := opcode % 2 = 1
  if opcode / 2 = 0b1000 then
    if !U then
      (ofElems esize n fun i => truncInt esize (rshr (elem x (2 * esize) i) shift round), false)
    else satLanes esize n fun i =>
      satQ esize true (rshr (sint (2 * esize) (elem x (2 * esize) i)) shift round)
  else satLanes esize n fun i =>
    satQ esize U (rshr (intOf U (2 * esize) (elem x (2 * esize) i)) shift round)

/-! ## Vector x indexed element (integer) -/

/-- Advanced SIMD (scalar) x indexed element, integer opcodes (`opcode = w<15:12>`), with the
element `el = Elem[V[m], index, esize]`, `x = V[n, 128]`, `d = V[d, 128]`, `n` elements:

* same-width (`datasize` bits): `1000` MUL, `0000` MLA (`U = 1`), `0100` MLS (`U = 1`),
  `1100` SQDMULH, `1101` SQRDMULH;
* long (`Vpart[n, part]`, `2*esize`-bit results): `1010` SMULL/UMULL, `0010` SMLAL/UMLAL,
  `0110` SMLSL/UMLSL, `1011` SQDMULL, `0011` SQDMLAL, `0111` SQDMLSL. -/
def byElemInt (U : Bool) (esize n opcode part x d el : Nat) : Res :=
  let e := esize
  if opcode = 0b1000 || opcode = 0b0000 || opcode = 0b0100 then
    (ofElems e n fun i =>
      let p := elem x e i * el % 2 ^ e
      if opcode = 0b1000 then p
      else if opcode = 0b0100 then (elem d e i + 2 ^ e - p) % 2 ^ e
      else (elem d e i + p) % 2 ^ e, false)
  else if opcode = 0b1100 || opcode = 0b1101 then
    satLanes e n fun i => satQ e false (rshr (2 * sint e (elem x e i) * sint e el) e (opcode = 0b1101))
  else
    let x1 := if part = 1 then x / 2 ^ 64 else x % 2 ^ 64
    if opcode = 0b1010 || opcode = 0b0010 || opcode = 0b0110 then
      (ofElems (2 * e) n fun i =>
        let p := truncInt (2 * e) (intOf U e (elem x1 e i) * intOf U e el)
        if opcode = 0b1010 then p
        else if opcode = 0b0110 then (elem d (2 * e) i + 2 ^ (2 * e) - p) % 2 ^ (2 * e)
        else (elem d (2 * e) i + p) % 2 ^ (2 * e), false)
    else
      satLanes (2 * e) n fun i =>
        let (p, sat1) := satQ (2 * e) false (2 * sint e (elem x1 e i) * sint e el)
        if opcode = 0b1011 then (p, sat1)
        else
          let acc : Int := if opcode = 0b0111 then sint (2 * e) (elem d (2 * e) i) - sint (2 * e) p
            else sint (2 * e) (elem d (2 * e) i) + sint (2 * e) p
          let (r, sat2) := satQ (2 * e) false acc
          (r, sat1 || sat2)

/-! ## Loads and stores of interleaved structures -/

/-- The register value of register `j` (`0 ≤ j < selem`) of LD2/LD3/LD4 (multiple structures)
from the `selem * datasize / 8` bytes `blk` read at the address (little-endian, as one number):
`Elem[V[t+j], e, esize] = Mem[address + (e * selem + j) * ebytes, ebytes]`. -/
def deinterleave (esize datasize selem blk j : Nat) : Nat :=
  ofElems esize (datasize / esize) fun e => elem blk esize (e * selem + j)

/-- The memory block written by ST2/ST3/ST4 (multiple structures): structure element `k` of the
block is `Elem[V[t + k MOD selem], k / selem, esize]`, `regs j` being the value of
`V[(t + j) MOD 32, datasize]`. -/
def interleave (esize datasize selem : Nat) (regs : Nat → Nat) : Nat :=
  ofElems esize (selem * (datasize / esize)) fun k => elem (regs (k % selem)) esize (k / selem)

end Janus.Arm64.Neon
