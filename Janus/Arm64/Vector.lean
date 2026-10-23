import Janus.Arm64.State
import Janus.Arm64.Bits

/-!
# Advanced SIMD helpers (trusted)

Pseudocode library for the integer and move instructions of Advanced SIMD (see `Exec`).
A vector operand is handled as the natural number `V[n, datasize]` (`< 2 ^ datasize`),
and its elements with the ARM ARM accessor `Elem[x, e, esize]`:

* `elem x esize e = x<(e+1)*esize-1 : e*esize>` as a natural number;
* `ofElems esize n f` is the `n * esize`-bit vector whose element `e` is `f e` truncated to
  `esize` bits (element 0 in the low bits), i.e. `Elem[result, e, esize] = f e` for `e < n`;
* `sint esize v` is `SInt` of an `esize`-bit element.

Every operation is a direct transcription of the `Operation` pseudocode of the instruction
(loops over elements become `ofElems`). Only `Nat`/`Int` arithmetic and structural recursion
are used, so the kernel can evaluate everything on literals.
-/

namespace Janus.Arm64

/-- `Elem[x, e, esize]`. -/
def elem (x esize e : Nat) : Nat := x / 2 ^ (esize * e) % 2 ^ esize

/-- The vector of `n` elements of `esize` bits whose element `e` is `f e` (mod `2 ^ esize`). -/
def ofElems (esize : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => ofElems esize n f + 2 ^ (esize * n) * (f n % 2 ^ esize)

/-- `SInt` of an `esize`-bit value `v < 2 ^ esize`. -/
def sint (esize v : Nat) : Int := if v < 2 ^ (esize - 1) then (v : Int) else (v : Int) - 2 ^ esize

/-- An integer result truncated to `esize` bits (`int<esize-1:0>`). -/
def truncInt (esize : Nat) (i : Int) : Nat := (i % (2 ^ esize : Int)).toNat

/-- `Ones(n)`. -/
def onesN (n : Nat) : Nat := 2 ^ n - 1

/-- Population count of the low `n` bits of `x` (`BitCount`). -/
def popcountNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + popcountNat n (x / 2)

/-- Element `j` of the `2n`-element concatenation `y : x` (`x` in the low half), as read by the
pairwise instructions: `concat = operand2:operand1; Elem[concat, j, esize]`. -/
def pairElem (x y esize n j : Nat) : Nat := if j < n then elem x esize j else elem y esize (j - n)

/-- Unsigned or signed value of an element (`asl_Int(x, unsigned)`). -/
def intOf (unsigned : Bool) (esize v : Nat) : Int := if unsigned then (v : Int) else sint esize v

/-- `Max`/`Min` of two elements under `asl_Int`, truncated back to `esize` bits. -/
def maxMinElem (unsigned minimum : Bool) (esize a b : Nat) : Nat :=
  let x := intOf unsigned esize a
  let y := intOf unsigned esize b
  truncInt esize (if minimum then min x y else max x y)

/-- Fold of `Max`/`Min` over elements `0 .. n-1` (the across-lanes reductions):
`maxmin = Int(Elem[0]); for e = 1 to n-1: maxmin = Max/Min(maxmin, Int(Elem[e]))`. -/
def foldMaxMin (unsigned minimum : Bool) (esize x : Nat) : Nat → Int
  | 0 => intOf unsigned esize (elem x esize 0)
  | k + 1 =>
    let acc := foldMaxMin unsigned minimum esize x k
    let v := intOf unsigned esize (elem x esize (k + 1))
    if minimum then min acc v else max acc v

/-- `Σ_{e < n} Int(Elem[x, e, esize])`. -/
def sumElems (unsigned : Bool) (esize x : Nat) : Nat → Int
  | 0 => 0
  | k + 1 => sumElems unsigned esize x k + intOf unsigned esize (elem x esize k)

/-! ## Instruction-class operations

Each takes the operands as natural numbers (already read as `V[n, datasize]`) and returns the
result value (before `V[d, ...] = result`). -/

/-- Advanced SIMD three same (integer subset), `opcode = w<15:11>`, for `datasize` bits:
logical (`00011`, selected by `U:size`), ADD/SUB (`10000`), CMTST/CMEQ (`10001`),
CMGT/CMHI (`00110`), CMGE/CMHS (`00111`), SMAX/UMAX (`01100`), SMIN/UMIN (`01101`),
SMAXP/UMAXP (`10100`), SMINP/UMINP (`10101`), ADDP (`10111`). `x = V[n]`, `y = V[m]`,
`d = V[d]` (read by BSL/BIT/BIF only). -/
def threeSameOp (U : Bool) (size opcode datasize : Nat) (x y d : Nat) : Nat :=
  let e := 8 * 2 ^ size
  let n := datasize / e
  let mask := onesN datasize
  if opcode = 0b00011 then
    -- AND/BIC/ORR/ORN; EOR/BSL/BIT/BIF: `EOR(operand1, EOR(operand2, operand4) AND operand3)`
    if !U then
      if size = 0 then x &&& y
      else if size = 1 then x &&& (y ^^^ mask)
      else if size = 2 then x ||| y
      else x ||| (y ^^^ mask)
    else
      if size = 0 then x ^^^ y
      else if size = 1 then y ^^^ ((y ^^^ x) &&& d)
      else if size = 2 then d ^^^ ((d ^^^ x) &&& y)
      else d ^^^ ((d ^^^ x) &&& (y ^^^ mask))
  else if opcode = 0b10000 then
    ofElems e n fun i => if U then elem x e i + 2 ^ e - elem y e i else elem x e i + elem y e i
  else if opcode = 0b10001 then
    ofElems e n fun i =>
      if (if U then decide (elem x e i = elem y e i) else decide (elem x e i &&& elem y e i ≠ 0))
      then onesN e else 0
  else if opcode = 0b00110 then
    ofElems e n fun i =>
      if (if U then decide (elem x e i > elem y e i)
          else decide (sint e (elem x e i) > sint e (elem y e i))) then onesN e else 0
  else if opcode = 0b00111 then
    ofElems e n fun i =>
      if (if U then decide (elem x e i ≥ elem y e i)
          else decide (sint e (elem x e i) ≥ sint e (elem y e i))) then onesN e else 0
  else if opcode = 0b01100 then ofElems e n fun i => maxMinElem U false e (elem x e i) (elem y e i)
  else if opcode = 0b01101 then ofElems e n fun i => maxMinElem U true e (elem x e i) (elem y e i)
  else if opcode = 0b10100 then
    ofElems e n fun i => maxMinElem U false e (pairElem x y e n (2 * i)) (pairElem x y e n (2 * i + 1))
  else if opcode = 0b10101 then
    ofElems e n fun i => maxMinElem U true e (pairElem x y e n (2 * i)) (pairElem x y e n (2 * i + 1))
  else
    -- ADDP (vector)
    ofElems e n fun i => pairElem x y e n (2 * i) + pairElem x y e n (2 * i + 1)

/-- Advanced SIMD across lanes: SADDLV/UADDLV (`00011`), SMAXV/UMAXV (`01010`),
SMINV/UMINV (`11010`), ADDV (`11011`). Returns `(result, width of the result)`. -/
def acrossOp (U : Bool) (size opcode datasize x : Nat) : Nat × Nat :=
  let e := 8 * 2 ^ size
  let n := datasize / e
  if opcode = 0b00011 then (truncInt (2 * e) (sumElems U e x n), 2 * e)
  else if opcode = 0b01010 then (truncInt e (foldMaxMin U false e x (n - 1)), e)
  else if opcode = 0b11010 then (truncInt e (foldMaxMin U true e x (n - 1)), e)
  else (truncInt e (sumElems true e x n), e)

/-- Element `i` of the result of REV16/REV32/REV64 (`csize`-bit containers of `esize`-bit
elements): the element at the mirrored position inside the same container. -/
def revIndex (csize esize i : Nat) : Nat :=
  let k := csize / esize
  i / k * k + (k - 1 - i % k)

/-- Advanced SIMD two-register miscellaneous (integer subset) for `datasize` bits:
REV64/REV32 (`00000`), REV16 (`00001`), CNT/NOT/RBIT (`00101`), CMGT/CMGE #0 (`01000`),
CMEQ/CMLE #0 (`01001`), CMLT #0 (`01010`), ABS/NEG (`01011`). (XTN is `xtnOp`.) -/
def twoMiscOp (U : Bool) (size opcode datasize x : Nat) : Nat :=
  let e := 8 * 2 ^ size
  let n := datasize / e
  let cmp (p : Int → Bool) : Nat := ofElems e n fun i => if p (sint e (elem x e i)) then onesN e else 0
  if opcode = 0b00000 then
    ofElems e n fun i => elem x e (revIndex (if U then 32 else 64) e i)
  else if opcode = 0b00001 then ofElems e n fun i => elem x e (revIndex 16 e i)
  else if opcode = 0b00101 then
    if !U then ofElems 8 (datasize / 8) fun i => popcountNat 8 (elem x 8 i)
    else if size = 0 then x ^^^ onesN datasize
    else ofElems 8 (datasize / 8) fun i => rbitNat 8 (elem x 8 i)
  else if opcode = 0b01000 then (if U then cmp (fun v => decide (v ≥ 0)) else cmp (fun v => decide (v > 0)))
  else if opcode = 0b01001 then (if U then cmp (fun v => decide (v ≤ 0)) else cmp (fun v => decide (v = 0)))
  else if opcode = 0b01010 then cmp (fun v => decide (v < 0))
  else
    ofElems e n fun i =>
      let v := sint e (elem x e i)
      truncInt e (if U then -v else if v < 0 then -v else v)

/-- XTN: the low halves of the `2 * esize`-bit elements of `x` (64-bit result). -/
def xtnOp (size x : Nat) : Nat :=
  let e := 8 * 2 ^ size
  ofElems e (64 / e) fun i => elem x (2 * e) i

/-- Advanced SIMD shift by immediate (no rounding, no saturation), for `datasize` bits:
SSHR/USHR (`00000`), SSRA/USRA (`00010`), SHL (`01010`, `U = 0`), SLI (`01010`, `U = 1`),
SRI (`01000`). `esize` from `immh`; `x = V[n]`, `d = V[d]`. -/
def shiftImmOp (U : Bool) (esize opcode datasize immhb : Nat) (x d : Nat) : Nat :=
  let n := datasize / esize
  let rshift := 2 * esize - immhb
  let lshift := immhb - esize
  if opcode = 0b00000 || opcode = 0b00010 then
    let acc := opcode = 0b00010
    ofElems esize n fun i =>
      truncInt esize ((if acc then (elem d esize i : Int) else 0) +
        Int.fdiv (intOf U esize (elem x esize i)) (2 ^ rshift))
  else if opcode = 0b01010 then
    if !U then ofElems esize n fun i => elem x esize i * 2 ^ lshift
    else
      let mask := onesN esize * 2 ^ lshift % 2 ^ esize
      ofElems esize n fun i =>
        (elem d esize i &&& (mask ^^^ onesN esize)) ||| (elem x esize i * 2 ^ lshift % 2 ^ esize)
  else
    -- SRI
    let mask := onesN esize / 2 ^ rshift
    ofElems esize n fun i =>
      (elem d esize i &&& (mask ^^^ onesN esize)) ||| (elem x esize i / 2 ^ rshift)

/-- SHRN: `Elem[result, e, esize] = (UInt(Elem[operand, e, 2*esize]) >> shift)<esize-1:0>` over
the 128-bit operand; a 64-bit result. -/
def shrnOp (esize shift x : Nat) : Nat :=
  ofElems esize (64 / esize) fun i => elem x (2 * esize) i / 2 ^ shift

/-- SSHLL/USHLL over the 64-bit operand `x` (`Vpart[n, part]`): a 128-bit result. -/
def shllOp (U : Bool) (esize shift x : Nat) : Nat :=
  ofElems (2 * esize) (64 / esize) fun i => truncInt (2 * esize) (intOf U esize (elem x esize i) * 2 ^ shift)

/-- `AdvSIMDExpandImm(op, cmode, imm8)`. -/
def advSimdExpandImm (op : Bool) (cmode imm8 : Nat) : Nat :=
  let rep2 (v : Nat) : Nat := v + 2 ^ 32 * v
  let rep4 (v : Nat) : Nat := v + 2 ^ 16 * v + 2 ^ 32 * v + 2 ^ 48 * v
  let c := cmode / 2
  if c = 0 then rep2 imm8
  else if c = 1 then rep2 (imm8 * 2 ^ 8)
  else if c = 2 then rep2 (imm8 * 2 ^ 16)
  else if c = 3 then rep2 (imm8 * 2 ^ 24)
  else if c = 4 then rep4 imm8
  else if c = 5 then rep4 (imm8 * 2 ^ 8)
  else if c = 6 then
    if cmode % 2 = 0 then rep2 (imm8 * 2 ^ 8 + 0xFF) else rep2 (imm8 * 2 ^ 16 + 0xFFFF)
  else
    let b7 := imm8 / 128 % 2
    let b6 := imm8 / 64 % 2
    if cmode % 2 = 0 then
      if !op then replicateNat imm8 8 8
      else ofElems 8 8 fun i => if imm8 / 2 ^ i % 2 = 1 then 0xFF else 0
    else if !op then
      -- imm8<7>:NOT(imm8<6>):Replicate(imm8<6>,5):imm8<5:0>:Zeros(19)
      rep2 ((b7 * 2 ^ 12 + (1 - b6) * 2 ^ 11 + b6 * 0x7C0 + imm8 % 64) * 2 ^ 19)
    else
      -- imm8<7>:NOT(imm8<6>):Replicate(imm8<6>,8):imm8<5:0>:Zeros(48)
      (b7 * 2 ^ 15 + (1 - b6) * 2 ^ 14 + b6 * 0x3FC0 + imm8 % 64) * 2 ^ 48

/-- Advanced SIMD modified immediate: MOVI/MVNI/ORR/BIC/FMOV (vector, immediate) on `datasize`
bits, `d = V[d]`. The operation is selected by `cmode:op` as in the decode pseudocode. -/
def modImmOp (op : Bool) (cmode imm8 datasize d : Nat) : Nat :=
  let imm64 := advSimdExpandImm op cmode imm8
  let imm := if datasize = 128 then imm64 + 2 ^ 64 * imm64 else imm64
  let mask := onesN datasize
  -- cmode 0xx1 and 10x1 are ORR (op = 0) / BIC (op = 1); 0xx0, 10x0, 110x are MOVI/MVNI;
  -- 1110 and 1111 are MOVI/FMOV regardless of op.
  let logical := cmode % 2 = 1 && cmode < 12
  if cmode ≥ 14 then imm
  else if logical then (if op then d &&& (imm ^^^ mask) else d ||| imm)
  else if op then imm ^^^ mask else imm

/-- EXT: `concat = V[m]:V[n]; result = concat<position+datasize-1:position>`. -/
def extOp (datasize imm4 x y : Nat) : Nat := (y * 2 ^ datasize + x) / 2 ^ (8 * imm4) % 2 ^ datasize

/-- TBL/TBX: `table` is the concatenation of the `regs` table registers (first in the low
bits), `idx = V[m]`, `d = V[d]`. -/
def tblOp (tbx : Bool) (regs datasize table idx d : Nat) : Nat :=
  ofElems 8 (datasize / 8) fun i =>
    let j := elem idx 8 i
    if j < 16 * regs then elem table 8 j else if tbx then elem d 8 i else 0

/-- The `n`-register table of TBL/TBX starting at `V[r]` (register numbers modulo 32). -/
def tableOf (v : Nat → BitVec 128) (r : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tableOf v r k + 2 ^ (128 * k) * (v ((r + k) % 32)).toNat


/-! ## AES (FEAT_AES)

Transcribed from the ASL: the S-boxes are the `GF2`/`GF2_inv` constants of `AESSubBytes` /
`AESInvSubBytes` (byte `x` of the table is `Slice(GF2, 8 * x, 8)`), the row shifts are the
byte permutations of `AESShiftRows` / `AESInvShiftRows`, and `AESMixColumns` /
`AESInvMixColumns` multiply each column (bytes `4c .. 4c+3`) in GF(2^8). -/

/-- `AESSubBytes`'s table. -/
def aesSbox : List Nat := [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

/-- `AESInvSubBytes`'s table. -/
def aesInvSbox : List Nat := [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d]

/-- `AESShiftRows`: byte `i` of the result is byte `aesShiftRowsPerm[i]` of the operand. -/
def aesShiftRowsPerm : List Nat := [0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11]

/-- `AESInvShiftRows`, as `aesShiftRowsPerm`. -/
def aesInvShiftRowsPerm : List Nat := [0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3]

/-- Multiplication by `x` in GF(2^8) modulo `x^8 + x^4 + x^3 + x + 1`, of a byte. -/
def xtime (b : Nat) : Nat := if b < 128 then 2 * b else (2 * b) ^^^ 0x11B

/-- `FFmul02 .. FFmul0E`: multiplication of the byte `b` by `k ∈ {2, 3, 9, 11, 13, 14}`
(sums of `xtime` powers; checked against the ASL tables in `JanusTests/Vector.lean`). -/
def gfMul (k b : Nat) : Nat :=
  let b2 := xtime b
  let b4 := xtime b2
  let b8 := xtime b4
  (if k % 2 = 1 then b else 0) ^^^ (if k / 2 % 2 = 1 then b2 else 0) ^^^
    (if k / 4 % 2 = 1 then b4 else 0) ^^^ (if k / 8 % 2 = 1 then b8 else 0)

/-- `AESShiftRows` / `AESInvShiftRows` of the 128-bit `x`. -/
def aesShiftRows (inv : Bool) (x : Nat) : Nat :=
  ofElems 8 16 fun i => elem x 8 ((if inv then aesInvShiftRowsPerm else aesShiftRowsPerm).getD i 0)

/-- `AESSubBytes` / `AESInvSubBytes`. -/
def aesSubBytes (inv : Bool) (x : Nat) : Nat :=
  ofElems 8 16 fun i => (if inv then aesInvSbox else aesSbox).getD (elem x 8 i) 0

/-- `AESMixColumns` (`k = [2, 3, 1, 1]`) / `AESInvMixColumns` (`k = [14, 11, 13, 9]`): row `r` of
column `c` is `Σ_j k[j] · in[(r + j) mod 4][c]` (XOR sum), where `in[r][c]` is byte `4c + r`. -/
def aesMixColumns (inv : Bool) (x : Nat) : Nat :=
  let k : List Nat := if inv then [14, 11, 13, 9] else [2, 3, 1, 1]
  ofElems 8 16 fun i =>
    let c := i / 4
    let r := i % 4
    let b (j : Nat) : Nat := elem x 8 (4 * c + (r + j) % 4)
    gfMul (k.getD 0 0) (b 0) ^^^ gfMul (k.getD 1 0) (b 1) ^^^ gfMul (k.getD 2 0) (b 2) ^^^
      gfMul (k.getD 3 0) (b 3)

/-- AESE (`opcode = 00100`), AESD (`00101`), AESMC (`00110`), AESIMC (`00111`), with `d = V[d]`
and `n = V[n]`: `AESE: SubBytes(ShiftRows(d EOR n))`, `AESD: InvSubBytes(InvShiftRows(d EOR n))`,
`AESMC: MixColumns(n)`, `AESIMC: InvMixColumns(n)`. -/
def aesOp (opcode d n : Nat) : Nat :=
  if opcode = 0b00100 then aesSubBytes false (aesShiftRows false (d ^^^ n))
  else if opcode = 0b00101 then aesSubBytes true (aesShiftRows true (d ^^^ n))
  else if opcode = 0b00110 then aesMixColumns false n
  else aesMixColumns true n

namespace State

/-- `V[n, width]` as a natural number. -/
def getV (s : State) (n width : Nat) : Nat := (s.vregs n).toNat % 2 ^ width

/-- `V[d, width] = value`: the register is zero-extended above `width` bits. -/
def setV (s : State) (d width value : Nat) : State :=
  { s with vregs := fun i => if i = d then BitVec.ofNat 128 (value % 2 ^ width) else s.vregs i }

end State

end Janus.Arm64
