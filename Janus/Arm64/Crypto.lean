import Janus.Arm64.Vector

/-!
# Cryptographic extension, CRC32 and permute helpers (trusted)

Pseudocode library for the instructions of `Janus.Arm64.CryptoInstr`, transcribed statement by
statement from the Arm ASL (Armv9.4-A, as translated into Sail by rems-project/sail-arm
`f5bf6c3`: `instrs64.sail` for the `execute_*` functions, `v8_base.sail` for the shared
functions `SHAchoose`, `SHAparity`, `SHAmajority`, `SHAhashSIGMA0/1`, `SHA256hash`, `ROL`,
`PolynomialMult`, `BitReverse`, `Poly32Mod2`; `builtins.sail` for `ROR`). The AES helpers
(`AESSubBytes`, `AESShiftRows`, `AESMixColumns` and their inverses) predate this file and live in
`Janus.Arm64.Vector` (`aesOp`).

Conventions are those of `Janus.Arm64.Vector`: a `k`-bit ASL bitvector is a natural number
`< 2 ^ k`, `x[hi .. lo]` of an element-aligned slice is `elem x esize e`, `Elem[x, e, esize] = v`
is `setElem x esize e v`, ASL `+` on `bits(32)` / `bits(64)` is `+` modulo `2 ^ 32` / `2 ^ 64`,
`EOR`/`AND`/`OR` are `^^^`/`&&&`/`|||`, `NOT` on `k` bits is `^^^ onesN k`, and `x @ y` with
`y : bits(k)` is `x * 2 ^ k + y`. ASL `foreach` loops become structural recursion over the loop
counter (iteration `e = 0` innermost), so the kernel evaluates everything on literals.

Every operation takes its operands already read (`V[n, 128]`, `X[n, 32]`, ...) and returns the
value written by `V[d, width] = result` / `X[d, 32] = result`; the reads and writes are in
`Janus.Arm64.execCrypto`.
-/

namespace Janus.Arm64

/-! ## Bit-level helpers -/

/-- ASL `ROL(x, shift)` on `N` bits (`0 ≤ shift ≤ N`):
`if shift == 0 then return x; return ROR(x, N - shift)`. -/
def rolNat (N x shift : Nat) : Nat := if shift = 0 then x else rorNat N x (N - shift)

/-- `Elem[x, e, esize] = v`: `x` with element `e` replaced by `v` (truncated to `esize` bits). -/
def setElem (x esize e v : Nat) : Nat :=
  x - elem x esize e * 2 ^ (esize * e) + (v % 2 ^ esize) * 2 ^ (esize * e)

/-- 32-bit addition (`bits(32) + bits(32)`). -/
def add32 (a b : Nat) : Nat := (a + b) % 2 ^ 32

/-- 64-bit addition (`bits(64) + bits(64)`). -/
def add64 (a b : Nat) : Nat := (a + b) % 2 ^ 64

/-- `NOT(x)` on 64 bits. -/
def not64 (x : Nat) : Nat := x ^^^ onesN 64

/-! ## SHA-1 and SHA-256 -/

/-- `SHAchoose(x, y, z) = EOR(EOR(y, z) AND x, z)`. -/
def shaChoose (x y z : Nat) : Nat := ((y ^^^ z) &&& x) ^^^ z

/-- `SHAparity(x, y, z) = EOR(EOR(x, y), z)`. -/
def shaParity (x y z : Nat) : Nat := (x ^^^ y) ^^^ z

/-- `SHAmajority(x, y, z) = (x AND y) OR ((x OR y) AND z)`. -/
def shaMajority (x y z : Nat) : Nat := (x &&& y) ||| ((x ||| y) &&& z)

/-- `SHAhashSIGMA0(x) = EOR(EOR(ROR(x, 2), ROR(x, 13)), ROR(x, 22))`. -/
def shaHashSigma0 (x : Nat) : Nat := (rorNat 32 x 2 ^^^ rorNat 32 x 13) ^^^ rorNat 32 x 22

/-- `SHAhashSIGMA1(x) = EOR(EOR(ROR(x, 6), ROR(x, 11)), ROR(x, 25))`. -/
def shaHashSigma1 (x : Nat) : Nat := (rorNat 32 x 6 ^^^ rorNat 32 x 11) ^^^ rorNat 32 x 25

/-- One iteration `e` of the loop of SHA1C / SHA1P / SHA1M (`f` is `SHAchoose`, `SHAparity` or
`SHAmajority`), on `(x : bits(128), y : bits(32))`:
```
t = f(x[63..32], x[95..64], x[127..96]);
y = y + ROL(x[31..0], 5) + t + Elem[w, e, 32];
x[63..32] = ROL(x[63..32], 30);
(y @ x) = ROL(y @ x, 32);
``` -/
def sha1Iter (f : Nat → Nat → Nat → Nat) (w e : Nat) (xy : Nat × Nat) : Nat × Nat :=
  let x := xy.1
  let y := xy.2
  let t := f (elem x 32 1) (elem x 32 2) (elem x 32 3)
  let y := add32 (add32 (add32 y (rolNat 32 (elem x 32 0) 5)) t) (elem w 32 e)
  let x := setElem x 32 1 (rolNat 32 (elem x 32 1) 30)
  let yx := rolNat 160 (y * 2 ^ 128 + x) 32
  (yx % 2 ^ 128, yx / 2 ^ 128)

/-- `foreach (e from 0 to k-1)` of `sha1Iter`. -/
def sha1Loop (f : Nat → Nat → Nat → Nat) (w : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, xy => xy
  | k + 1, xy => sha1Iter f w k (sha1Loop f w k xy)

/-- SHA1C / SHA1P / SHA1M: `x = V[d, 128]; y = V[n, 32]; w = V[m, 128]`, four iterations, then
`V[d, 128] = x`. -/
def sha1HashOp (f : Nat → Nat → Nat → Nat) (x y w : Nat) : Nat := (sha1Loop f w 4 (x, y)).1

/-- SHA1SU0: `result = operand2[63..0] @ operand1[127..64];
result = EOR(EOR(result, operand1), operand3)` (`operand1 = V[d]`, `operand2 = V[n]`,
`operand3 = V[m]`). -/
def sha1Su0Op (op1 op2 op3 : Nat) : Nat :=
  let result := elem op2 64 0 * 2 ^ 64 + elem op1 64 1
  (result ^^^ op1) ^^^ op3

/-- SHA1SU1 (`operand1 = V[d]`, `operand2 = V[n]`):
```
T = EOR(operand1, LSR(operand2, 32));
result[31..0] = ROL(T[31..0], 1);  result[63..32] = ROL(T[63..32], 1);
result[95..64] = ROL(T[95..64], 1);
result[127..96] = EOR(ROL(T[127..96], 1), ROL(T[31..0], 2));
``` -/
def sha1Su1Op (op1 op2 : Nat) : Nat :=
  let T := op1 ^^^ (op2 / 2 ^ 32)
  ofElems 32 4 fun e =>
    if e = 3 then rolNat 32 (elem T 32 3) 1 ^^^ rolNat 32 (elem T 32 0) 2
    else rolNat 32 (elem T 32 e) 1

/-- SHA1H: `V[d, 32] = ROL(V[n, 32], 30)`. -/
def sha1HOp (op : Nat) : Nat := rolNat 32 op 30

/-- One iteration `e` of the loop of `SHA256hash`, on `(x, y : bits(128))`:
```
chs = SHAchoose(y[31..0], y[63..32], y[95..64]);
maj = SHAmajority(x[31..0], x[63..32], x[95..64]);
t = y[127..96] + SHAhashSIGMA1(y[31..0]) + chs + Elem[w, e, 32];
x[127..96] = t + x[127..96];
y[127..96] = t + SHAhashSIGMA0(x[31..0]) + maj;
(y @ x) = ROL(y @ x, 32);
``` -/
def sha256Iter (w e : Nat) (xy : Nat × Nat) : Nat × Nat :=
  let x := xy.1
  let y := xy.2
  let chs := shaChoose (elem y 32 0) (elem y 32 1) (elem y 32 2)
  let maj := shaMajority (elem x 32 0) (elem x 32 1) (elem x 32 2)
  let t := add32 (add32 (add32 (elem y 32 3) (shaHashSigma1 (elem y 32 0))) chs) (elem w 32 e)
  let x := setElem x 32 3 (add32 t (elem x 32 3))
  let y := setElem y 32 3 (add32 (add32 t (shaHashSigma0 (elem x 32 0))) maj)
  let yx := rolNat 256 (y * 2 ^ 128 + x) 32
  (yx % 2 ^ 128, yx / 2 ^ 128)

/-- `foreach (e from 0 to k-1)` of `sha256Iter`. -/
def sha256Loop (w : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, xy => xy
  | k + 1, xy => sha256Iter w k (sha256Loop w k xy)

/-- `SHA256hash(x, y, w, part1)`: four iterations, then `if part1 then x else y`. -/
def sha256Hash (x y w : Nat) (part1 : Bool) : Nat :=
  let r := sha256Loop w 4 (x, y)
  if part1 then r.1 else r.2

/-- SHA256SU0 (`operand1 = V[d]`, `operand2 = V[n]`):
```
T = operand2[31..0] @ operand1[127..32];
foreach (e from 0 to 3)
  elt = Elem[T, e, 32];
  elt = EOR(EOR(ROR(elt, 7), ROR(elt, 18)), LSR(elt, 3));
  Elem[result, e, 32] = elt + Elem[operand1, e, 32];
``` -/
def sha256Su0Op (op1 op2 : Nat) : Nat :=
  let T := elem op2 32 0 * 2 ^ 96 + op1 / 2 ^ 32
  ofElems 32 4 fun e =>
    let elt := elem T 32 e
    let elt := (rorNat 32 elt 7 ^^^ rorNat 32 elt 18) ^^^ elt / 2 ^ 3
    add32 elt (elem op1 32 e)

/-- The `elt` update of SHA256SU1: `EOR(EOR(ROR(elt, 17), ROR(elt, 19)), LSR(elt, 10))`. -/
def sha256Su1Sigma (elt : Nat) : Nat := (rorNat 32 elt 17 ^^^ rorNat 32 elt 19) ^^^ elt / 2 ^ 10

/-- SHA256SU1 (`operand1 = V[d]`, `operand2 = V[n]`, `operand3 = V[m]`):
```
T0 = operand3[31..0] @ operand2[127..32];
T1 = operand3[127..64];
foreach (e from 0 to 1)
  elt = Elem[T1, e, 32]; elt = EOR(EOR(ROR(elt, 17), ROR(elt, 19)), LSR(elt, 10));
  elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32]; Elem[result, e, 32] = elt;
T1 = result[63..0];
foreach (e from 2 to 3)
  elt = Elem[T1, e - 2, 32]; elt = EOR(EOR(ROR(elt, 17), ROR(elt, 19)), LSR(elt, 10));
  elt = elt + Elem[operand1, e, 32] + Elem[T0, e, 32]; Elem[result, e, 32] = elt;
```
(`result` starts UNKNOWN; all four elements are written.) -/
def sha256Su1Op (op1 op2 op3 : Nat) : Nat :=
  let T0 := elem op3 32 0 * 2 ^ 96 + op2 / 2 ^ 32
  let T1 := elem op3 64 1
  let lo := ofElems 32 2 fun e =>
    add32 (add32 (sha256Su1Sigma (elem T1 32 e)) (elem op1 32 e)) (elem T0 32 e)
  let T1 := lo
  let hi := ofElems 32 2 fun e' =>
    add32 (add32 (sha256Su1Sigma (elem T1 32 e')) (elem op1 32 (e' + 2))) (elem T0 32 (e' + 2))
  hi * 2 ^ 64 + lo

/-! ## SHA-512 and SHA-3 -/

/-- SHA512H (`x = V[n]`, `y = V[m]`, `w = V[d]`):
```
MSigma1 = EOR(EOR(ROR(y[127..64], 14), ROR(y[127..64], 18)), ROR(y[127..64], 41));
Vtmp[127..64] = EOR(y[127..64] AND x[63..0], NOT(y[127..64]) AND x[127..64]);
Vtmp[127..64] = Vtmp[127..64] + MSigma1 + w[127..64];
tmp = Vtmp[127..64] + y[63..0];
MSigma1 = EOR(EOR(ROR(tmp, 14), ROR(tmp, 18)), ROR(tmp, 41));
Vtmp[63..0] = EOR(tmp AND y[127..64], NOT(tmp) AND x[63..0]);
Vtmp[63..0] = Vtmp[63..0] + MSigma1 + w[63..0];
``` -/
def sha512HOp (x y w : Nat) : Nat :=
  let yh := elem y 64 1
  let msigma1 := (rorNat 64 yh 14 ^^^ rorNat 64 yh 18) ^^^ rorNat 64 yh 41
  let vhi := (yh &&& elem x 64 0) ^^^ (not64 yh &&& elem x 64 1)
  let vhi := add64 (add64 vhi msigma1) (elem w 64 1)
  let tmp := add64 vhi (elem y 64 0)
  let msigma1 := (rorNat 64 tmp 14 ^^^ rorNat 64 tmp 18) ^^^ rorNat 64 tmp 41
  let vlo := (tmp &&& yh) ^^^ (not64 tmp &&& elem x 64 0)
  let vlo := add64 (add64 vlo msigma1) (elem w 64 0)
  vhi * 2 ^ 64 + vlo

/-- SHA512H2 (`x = V[n]`, `y = V[m]`, `w = V[d]`):
```
NSigma0 = EOR(EOR(ROR(y[63..0], 28), ROR(y[63..0], 34)), ROR(y[63..0], 39));
Vtmp[127..64] = EOR(EOR(x[63..0] AND y[127..64], x[63..0] AND y[63..0]), y[127..64] AND y[63..0]);
Vtmp[127..64] = Vtmp[127..64] + NSigma0 + w[127..64];
NSigma0 = EOR(EOR(ROR(Vtmp[127..64], 28), ROR(Vtmp[127..64], 34)), ROR(Vtmp[127..64], 39));
Vtmp[63..0] = EOR(EOR(Vtmp[127..64] AND y[63..0], Vtmp[127..64] AND y[127..64]), y[127..64] AND y[63..0]);
Vtmp[63..0] = Vtmp[63..0] + NSigma0 + w[63..0];
``` -/
def sha512H2Op (x y w : Nat) : Nat :=
  let yl := elem y 64 0
  let yh := elem y 64 1
  let xl := elem x 64 0
  let nsigma0 := (rorNat 64 yl 28 ^^^ rorNat 64 yl 34) ^^^ rorNat 64 yl 39
  let vhi := ((xl &&& yh) ^^^ (xl &&& yl)) ^^^ (yh &&& yl)
  let vhi := add64 (add64 vhi nsigma0) (elem w 64 1)
  let nsigma0 := (rorNat 64 vhi 28 ^^^ rorNat 64 vhi 34) ^^^ rorNat 64 vhi 39
  let vlo := ((vhi &&& yl) ^^^ (vhi &&& yh)) ^^^ (yh &&& yl)
  let vlo := add64 (add64 vlo nsigma0) (elem w 64 0)
  vhi * 2 ^ 64 + vlo

/-- SHA512SU0 (`x = V[n]`, `w = V[d]`):
```
sig0 = EOR(EOR(ROR(w[127..64], 1), ROR(w[127..64], 8)), '0000000':w[127..71]);
Vtmp[63..0] = w[63..0] + sig0;
sig0 = EOR(EOR(ROR(x[63..0], 1), ROR(x[63..0], 8)), '0000000':x[63..7]);
Vtmp[127..64] = w[127..64] + sig0;
``` -/
def sha512Su0Op (x w : Nat) : Nat :=
  let wh := elem w 64 1
  let sig0 := (rorNat 64 wh 1 ^^^ rorNat 64 wh 8) ^^^ wh / 2 ^ 7
  let vlo := add64 (elem w 64 0) sig0
  let xl := elem x 64 0
  let sig0 := (rorNat 64 xl 1 ^^^ rorNat 64 xl 8) ^^^ xl / 2 ^ 7
  let vhi := add64 wh sig0
  vhi * 2 ^ 64 + vlo

/-- SHA512SU1 (`x = V[n]`, `y = V[m]`, `w = V[d]`):
```
sig1 = EOR(EOR(ROR(x[127..64], 19), ROR(x[127..64], 61)), '000000':x[127..70]);
Vtmp[127..64] = w[127..64] + sig1 + y[127..64];
sig1 = EOR(EOR(ROR(x[63..0], 19), ROR(x[63..0], 61)), '000000':x[63..6]);
Vtmp[63..0] = w[63..0] + sig1 + y[63..0];
``` -/
def sha512Su1Op (x y w : Nat) : Nat :=
  let xh := elem x 64 1
  let sig1 := (rorNat 64 xh 19 ^^^ rorNat 64 xh 61) ^^^ xh / 2 ^ 6
  let vhi := add64 (add64 (elem w 64 1) sig1) (elem y 64 1)
  let xl := elem x 64 0
  let sig1 := (rorNat 64 xl 19 ^^^ rorNat 64 xl 61) ^^^ xl / 2 ^ 6
  let vlo := add64 (add64 (elem w 64 0) sig1) (elem y 64 0)
  vhi * 2 ^ 64 + vlo

/-- RAX1: `V[d] = EOR(Vn, ROL(Vm[127..64], 1) : ROL(Vm[63..0], 1))`. -/
def rax1Op (vn vm : Nat) : Nat :=
  vn ^^^ (rolNat 64 (elem vm 64 1) 1 * 2 ^ 64 + rolNat 64 (elem vm 64 0) 1)

/-- EOR3: `V[d] = EOR(EOR(Vn, Vm), Va)`. -/
def eor3Op (vn vm va : Nat) : Nat := (vn ^^^ vm) ^^^ va

/-- BCAX: `V[d] = EOR(Vn, Vm AND NOT(Va))` (128 bits). -/
def bcaxOp (vn vm va : Nat) : Nat := vn ^^^ (vm &&& (va ^^^ onesN 128))

/-- XAR: `tmp = EOR(Vn, Vm); V[d] = ROR(tmp[127..64], UInt(imm6)) : ROR(tmp[63..0], UInt(imm6))`
(`imm6 < 64`). -/
def xarOp (vn vm imm6 : Nat) : Nat :=
  let tmp := vn ^^^ vm
  rorNat 64 (elem tmp 64 1) imm6 * 2 ^ 64 + rorNat 64 (elem tmp 64 0) imm6

/-! ## Polynomial multiply -/

/-- The loop of `PolynomialMult(op1, op2)` (`op1 : bits(M)`, `op2 : bits(N)`) after `k`
iterations: `foreach (i from 0 to k-1) if op1<i> == '1' then result = EOR(result,
LSL(ZeroExtend(op2, M+N), i))`. The shifted `op2 < 2 ^ N` stays below `2 ^ (M+N)` for `i < M`,
so the `M+N`-bit `LSL` never truncates. -/
def polyMult : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, op1, op2 => polyMult k op1 op2 ^^^ (if op1.testBit k then op2 * 2 ^ k else 0)

/-- PMULL/PMULL2 for `esize ∈ {8, 64}` (`datasize = 64`, `elements = 64 / esize`):
```
operand1 = Vpart[n, part]; operand2 = Vpart[m, part];
foreach (e from 0 to elements-1)
  Elem[result, e, 2*esize] = PolynomialMult(Elem[operand1, e, esize], Elem[operand2, e, esize]);
V[d, 128] = result;
```
`x = V[n, 128]`, `y = V[m, 128]`; `Vpart[_, 1]` is the upper 64 bits. -/
def pmullOp (esize : Nat) (part : Bool) (x y : Nat) : Nat :=
  let op1 := if part then elem x 64 1 else elem x 64 0
  let op2 := if part then elem y 64 1 else elem y 64 0
  ofElems (2 * esize) (64 / esize) fun e => polyMult esize (elem op1 esize e) (elem op2 esize e)

/-! ## CRC32 -/

/-- The loop of `Poly32Mod2(data, poly)` over `i = 31 + k .. 32` (downwards):
`if data<i> == '1' then data<i-1:0> = EOR(data<i-1:0>, poly : Zeros(i-32))`. The XOR term is
below `2 ^ i`, so XORing it into the whole of `data` changes exactly `data<i-1:0>`. -/
def poly32Mod2Loop (poly : Nat) : Nat → Nat → Nat
  | 0, data => data
  | k + 1, data =>
    let i := 32 + k
    poly32Mod2Loop poly k (if data.testBit i then data ^^^ poly * 2 ^ (i - 32) else data)

/-- `Poly32Mod2(data, poly)` for a `32 + size`-bit `data`: the loop for `i` from `N - 1` down to
`32`, then `data<31:0>`. -/
def poly32Mod2 (size data poly : Nat) : Nat := poly32Mod2Loop poly size data % 2 ^ 32

/-- CRC32 / CRC32C (`acc = X[n, 32]`, `val = X[m, size]`):
```
poly = (if crc32c then 0x1EDC6F41 else 0x04C11DB7)<31:0>;
tempacc = BitReverse(acc) : Zeros(size);
tempval = BitReverse(val) : Zeros(32);
X[d, 32] = BitReverse(Poly32Mod2(tempacc EOR tempval, poly));
``` -/
def crc32Op (crc32c : Bool) (size acc val : Nat) : Nat :=
  let poly := if crc32c then 0x1EDC6F41 else 0x04C11DB7
  let tempacc := rbitNat 32 acc * 2 ^ size
  let tempval := rbitNat size val * 2 ^ 32
  rbitNat 32 (poly32Mod2 size (tempacc ^^^ tempval) poly)

/-! ## Permutes and scalar DUP -/

/-- UZP1/UZP2 (`part = 0/1`): `zipped = operandh : operandl;
foreach (e) Elem[result, e, esize] = Elem[zipped, 2*e+part, esize]` (`operandl = V[n]`,
`operandh = V[m]`). -/
def uzpOp (esize datasize part x y : Nat) : Nat :=
  let zipped := y * 2 ^ datasize + x
  ofElems esize (datasize / esize) fun e => elem zipped esize (2 * e + part)

/-- TRN1/TRN2: `foreach (p) Elem[result, 2p, esize] = Elem[operand1, 2p+part, esize];
Elem[result, 2p+1, esize] = Elem[operand2, 2p+part, esize]` (`operand1 = V[n]`,
`operand2 = V[m]`). Element `i` of the result comes from `operand1` for even `i`, from
`operand2` for odd `i`, at index `2 * (i / 2) + part`. -/
def trnOp (esize datasize part x y : Nat) : Nat :=
  ofElems esize (datasize / esize) fun i =>
    if i % 2 = 0 then elem x esize (2 * (i / 2) + part) else elem y esize (2 * (i / 2) + part)

/-- ZIP1/ZIP2: `base = part * pairs; foreach (p) Elem[result, 2p, esize] =
Elem[operand1, base+p, esize]; Elem[result, 2p+1, esize] = Elem[operand2, base+p, esize]`
(`pairs = elements / 2`). -/
def zipOp (esize datasize part x y : Nat) : Nat :=
  let pairs := datasize / esize / 2
  let base := part * pairs
  ofElems esize (datasize / esize) fun i =>
    if i % 2 = 0 then elem x esize (base + i / 2) else elem y esize (base + i / 2)

/-- Advanced SIMD permute, `opcode = w<14:12>` (`op = opcode<2>` is `part`): UZP (`x01`),
TRN (`x10`), ZIP (`x11`); `x = V[n]`, `y = V[m]` (`datasize` bits each). -/
def permuteOp (size opcode datasize x y : Nat) : Nat :=
  let esize := 8 * 2 ^ size
  let part := opcode / 4
  let k := opcode % 4
  if k = 1 then uzpOp esize datasize part x y
  else if k = 2 then trnOp esize datasize part x y
  else zipOp esize datasize part x y

end Janus.Arm64
