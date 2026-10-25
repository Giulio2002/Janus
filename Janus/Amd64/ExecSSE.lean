import Janus.Amd64.State
import Janus.Amd64.Instr
import Janus.Amd64.Float
import Janus.Arm64.Vector

/-!
# Semantics of the legacy-SSE packed instructions (WP-D, trusted)

`ExecSSE.exec` executes an `SseI` (decoded by `Janus.Amd64.DecodeSSE`); `Janus.Amd64.exec`
dispatches `Instr.sse` here, passing the linear address of each memory operand (`ea`, the same
`Janus.Amd64.ea` every other instruction uses). Each operation is the `Operation` section of the
Intel SDM Vol. 2 for the instruction, written over element accessors:

* vector values are naturals `< 2^128`; `elem x e i` (`Janus.Arm64.elem`, shared with the arm64
  Advanced SIMD model) is element `i` of width `e`, `ofElems e n f` the vector whose element `i`
  is `f i mod 2^e`, `sint e v` the signed value of an `e`-bit element and `truncInt e` the low
  `e` bits of an integer (two's complement);
* the saturating operations clamp the exact integer result (`satS`, `satU`);
* the floating-point operations apply the scalar operation of `Janus.Amd64.FP` (the IEEE core
  with the x86 NaN, `DAZ`/`FTZ`, exception and rounding rules) to every element. The exception
  flags of all elements are ORed (`lanesFP`): if any element raises an exception that is
  unmasked in `MXCSR`, the instruction faults with `simdFPException` and writes nothing
  (`#XM`; SDM Vol. 1 §11.5.2: an unmasked exception leaves the destination unchanged);
  otherwise the result is written and the flags of all elements are ORed into `MXCSR`.

Legacy SSE writes only bits 127:0 of its `XMM` destination (`ymmHi` is preserved). A 128-bit
memory operand must be 16-byte aligned (`misaligned`) except for `PCMPESTRI`/`PCMPESTRM`/
`PCMPISTRI`/`PCMPISTRM`; narrower operands are never checked. The state updates are written as
structure updates; `Janus.Amd64.ExecSSELemmas` proves them equal to the `State.setXmm`/
`State.setReg`/... of `Janus.Amd64.Exec`, so the proof automation sees one normal form.
-/

namespace Janus.Amd64.ExecSSE

open Janus.Arm64 (elem ofElems sint truncInt)
open Janus.Float (Fmt binary32 binary64)

/-! ## Element helpers -/

/-- The 128-bit vector of `e`-bit elements `f i`. -/
@[reducible] def lanes (e : Nat) (f : Nat → Nat) : Nat := ofElems e (128 / e) f

/-- Signed saturation of `i` to `e` bits (as an `e`-bit pattern). -/
def satS (e : Nat) (i : Int) : Nat :=
  truncInt e (max (-(2 ^ (e - 1) : Int)) (min i (2 ^ (e - 1) - 1)))

/-- Unsigned saturation of `i` to `e` bits. -/
def satU (e : Nat) (i : Int) : Nat := (max 0 (min i (2 ^ e - 1))).toNat

/-- The signed element `i` of `x`. -/
@[reducible] def sel (x e i : Nat) : Int := sint e (elem x e i)

/-- `Σ_{j < k} f j`. -/
def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => sumN k f + f k

/-- `|a - b|` of naturals. -/
@[reducible] def absDiff (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- Whether `p j` holds for some `j < k`. -/
def anyN : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | k + 1, p => anyN k p || p k

/-- Whether `p j` holds for every `j < k`. -/
def allN : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | k + 1, p => allN k p && p k

/-- The `k`-bit mask whose bit `j` is `p j`. -/
@[reducible] def maskN (k : Nat) (p : Nat → Bool) : Nat := ofElems 1 k fun j => (p j).toNat

/-- The lowest `j < k` with bit `j` of `x` set (`k` if none). -/
def lowSet : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => if x % 2 = 1 then 0 else 1 + lowSet k (x / 2)

/-- The highest `j < k` with bit `j` of `x` set (`k` if none). -/
def highSet : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => if x / 2 ^ k % 2 = 1 then k else highSet k x

/-- The lowest `j < k` with `elem x e j = 0` (`k` if none): the implicit string length. -/
def firstZero (e x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if firstZero e x k < k then firstZero e x k else if elem x e k = 0 then k else k + 1

/-! ## Packed integer operations -/

/-- `op(a, b)` on 128-bit `a` (the destination) and `b` (the source). -/
def pintOp (op : PIntOp) (a b : Nat) : Nat :=
  match op with
  | .add e => lanes e fun i => elem a e i + elem b e i
  | .sub e => lanes e fun i => elem a e i + 2 ^ e - elem b e i
  | .adds e => lanes e fun i => satS e (sel a e i + sel b e i)
  | .addus e => lanes e fun i => min (elem a e i + elem b e i) (2 ^ e - 1)
  | .subs e => lanes e fun i => satS e (sel a e i - sel b e i)
  | .subus e => lanes e fun i => elem a e i - elem b e i
  | .mull e => lanes e fun i => elem a e i * elem b e i
  | .mulh u =>
    lanes 16 fun i =>
      if u then elem a 16 i * elem b 16 i / 2 ^ 16
      else truncInt 16 (Int.fdiv (sel a 16 i * sel b 16 i) (2 ^ 16))
  | .muldq sg =>
    lanes 64 fun i =>
      if sg then truncInt 64 (sel a 32 (2 * i) * sel b 32 (2 * i))
      else elem a 32 (2 * i) * elem b 32 (2 * i)
  | .maddwd =>
    lanes 32 fun i =>
      truncInt 32 (sel a 16 (2 * i) * sel b 16 (2 * i) + sel a 16 (2 * i + 1) * sel b 16 (2 * i + 1))
  | .maddubsw =>
    lanes 16 fun i =>
      satS 16 ((elem a 8 (2 * i) : Int) * sel b 8 (2 * i) +
        (elem a 8 (2 * i + 1) : Int) * sel b 8 (2 * i + 1))
  | .mulhrsw =>
    lanes 16 fun i => truncInt 16 (Int.fdiv (Int.fdiv (sel a 16 i * sel b 16 i) (2 ^ 14) + 1) 2)
  | .cmpeq e => lanes e fun i => if elem a e i = elem b e i then 2 ^ e - 1 else 0
  | .cmpgt e => lanes e fun i => if sel a e i > sel b e i then 2 ^ e - 1 else 0
  | .andn => (a ^^^ (2 ^ 128 - 1)) &&& b
  | .unpckl e => lanes e fun j => if j % 2 = 0 then elem a e (j / 2) else elem b e (j / 2)
  | .unpckh e =>
    lanes e fun j => if j % 2 = 0 then elem a e (64 / e + j / 2) else elem b e (64 / e + j / 2)
  | .packss e =>
    lanes (e / 2) fun j => if j < 128 / e then satS (e / 2) (sel a e j) else satS (e / 2) (sel b e (j - 128 / e))
  | .packus e =>
    lanes (e / 2) fun j => if j < 128 / e then satU (e / 2) (sel a e j) else satU (e / 2) (sel b e (j - 128 / e))
  | .minu e => lanes e fun i => min (elem a e i) (elem b e i)
  | .mins e => lanes e fun i => truncInt e (min (sel a e i) (sel b e i))
  | .maxu e => lanes e fun i => max (elem a e i) (elem b e i)
  | .maxs e => lanes e fun i => truncInt e (max (sel a e i) (sel b e i))
  | .sadbw => lanes 64 fun k => sumN 8 fun j => absDiff (elem a 8 (8 * k + j)) (elem b 8 (8 * k + j))
  | .avg e => lanes e fun i => (elem a e i + elem b e i + 1) / 2
  | .sll e =>
    let c := b % 2 ^ 64
    lanes e fun i => if c ≥ e then 0 else elem a e i * 2 ^ c
  | .srl e =>
    let c := b % 2 ^ 64
    lanes e fun i => if c ≥ e then 0 else elem a e i / 2 ^ c
  | .sra e =>
    let c := min (b % 2 ^ 64) (e - 1)
    lanes e fun i => truncInt e (Int.fdiv (sel a e i) (2 ^ c))
  | .hadd e =>
    let h := 64 / e
    lanes e fun j =>
      if j < h then elem a e (2 * j) + elem a e (2 * j + 1)
      else elem b e (2 * (j - h)) + elem b e (2 * (j - h) + 1)
  | .hsub e =>
    let h := 64 / e
    lanes e fun j =>
      if j < h then elem a e (2 * j) + 2 ^ e - elem a e (2 * j + 1)
      else elem b e (2 * (j - h)) + 2 ^ e - elem b e (2 * (j - h) + 1)
  | .hadds =>
    lanes 16 fun j =>
      if j < 4 then satS 16 (sel a 16 (2 * j) + sel a 16 (2 * j + 1))
      else satS 16 (sel b 16 (2 * (j - 4)) + sel b 16 (2 * (j - 4) + 1))
  | .hsubs =>
    lanes 16 fun j =>
      if j < 4 then satS 16 (sel a 16 (2 * j) - sel a 16 (2 * j + 1))
      else satS 16 (sel b 16 (2 * (j - 4)) - sel b 16 (2 * (j - 4) + 1))
  | .sign e =>
    lanes e fun i =>
      if elem b e i = 0 then 0 else if sel b e i < 0 then truncInt e (-(sel a e i)) else elem a e i
  | .abs e => lanes e fun i => (sel b e i).natAbs
  | .movhl => a / 2 ^ 64 * 2 ^ 64 + b / 2 ^ 64

/-- `PSLL/PSRL/PSRA xmm, imm8` (element width `e`) and `PSLLDQ`/`PSRLDQ` on `a`. -/
def pshiftOp (op : PShiftOp) (e : Nat) (a imm : Nat) : Nat :=
  match op with
  | .sll => lanes e fun i => if imm ≥ e then 0 else elem a e i * 2 ^ imm
  | .srl => lanes e fun i => if imm ≥ e then 0 else elem a e i / 2 ^ imm
  | .sra => lanes e fun i => truncInt e (Int.fdiv (sel a e i) (2 ^ (min imm (e - 1))))
  | .slldq => if imm > 15 then 0 else a * 2 ^ (8 * imm) % 2 ^ 128
  | .srldq => if imm > 15 then 0 else a / 2 ^ (8 * imm)

/-- `XMM` value `a` with dword `imm8<5:4>` replaced by `v`, then the dwords of `imm8<3:0>`
zeroed (`INSERTPS`). -/
def insertDword (a v imm : Nat) : Nat :=
  lanes 32 fun i => if imm / 2 ^ i % 2 = 1 then 0 else if i = imm / 16 % 4 then v else elem a 32 i

/-- `op(a, b, imm8)`. -/
def pimmOp (op : PImmOp) (a b imm : Nat) : Nat :=
  match op with
  | .shufps => lanes 32 fun i => if i < 2 then elem a 32 (imm / 4 ^ i % 4) else elem b 32 (imm / 4 ^ i % 4)
  | .shufpd => lanes 64 fun i => if i = 0 then elem a 64 (imm % 2) else elem b 64 (imm / 2 % 2)
  | .palignr => if imm ≥ 32 then 0 else (a * 2 ^ 128 + b) / 2 ^ (8 * imm) % 2 ^ 128
  | .pblendw => lanes 16 fun i => if imm / 2 ^ i % 2 = 1 then elem b 16 i else elem a 16 i
  | .blendps => lanes 32 fun i => if imm / 2 ^ i % 2 = 1 then elem b 32 i else elem a 32 i
  | .blendpd => lanes 64 fun i => if imm / 2 ^ i % 2 = 1 then elem b 64 i else elem a 64 i
  | .pshufhw => lanes 16 fun i => if i < 4 then elem b 16 i else elem b 16 (4 + imm / 4 ^ (i - 4) % 4)
  | .mpsadbw =>
    let ao := imm / 4 % 2 * 4
    let bo := imm % 4 * 4
    lanes 16 fun i => sumN 4 fun j => absDiff (elem a 8 (ao + i + j)) (elem b 8 (bo + j))
  | .insertps => insertDword a (elem b 32 (imm / 64)) imm

/-- `PHMINPOSUW`: the minimum of the first `k` words of `x` and the lowest index holding it. -/
def minPos (x : Nat) : Nat → Nat × Nat
  | 0 => (elem x 16 0, 0)
  | k + 1 =>
    let (m, i) := minPos x k
    if elem x 16 (k + 1) < m then (elem x 16 (k + 1), k + 1) else (m, i)

/-- `CRC32`: the CRC-32C register `crc` (32 bits) updated with the `n` bits of `d`, lowest bit
first (the bit-reflected division by `11EDC6F41H` of SDM Vol. 2 `CRC32`: each step shifts the
reflected register right and adds the reflected polynomial `82F63B78H` when the bit shifted
out, XORed with the data bit, is set). -/
def crc32c : Nat → Nat → Nat → Nat
  | 0, crc, _ => crc
  | n + 1, crc, d =>
    let c := crc ^^^ (d % 2)
    crc32c n (if c % 2 = 1 then (c / 2) ^^^ 0x82F63B78 else c / 2) (d / 2)

/-! ## SSE4.2 string comparison (`PCMPESTRI` ...)

`imm8<1:0>`: element format (unsigned bytes, unsigned words, signed bytes, signed words);
`imm8<3:2>`: aggregation (equal any, ranges, equal each, equal ordered); `imm8<5:4>`: polarity;
`imm8<6>`: the most significant index / the expanded mask. `a` is the first operand (the set,
the ranges, the needle), `b` the second (the string), `la`/`lb` their lengths (elements
`≥ la`/`≥ lb` are invalid). SDM Vol. 2 §4.1 (Imm8 Control Byte Operation). -/

/-- Number of elements (16 bytes or 8 words). -/
@[reducible] def strN (imm : Nat) : Nat := if imm % 2 = 0 then 16 else 8

/-- Element width in bits. -/
@[reducible] def strE (imm : Nat) : Nat := if imm % 2 = 0 then 8 else 16

/-- Element `i` of `x` under the format of `imm8`. -/
def strVal (imm x i : Nat) : Int :=
  if imm / 2 % 2 = 1 then sint (strE imm) (elem x (strE imm) i) else elem x (strE imm) i

/-- `IntRes1` (bit `j` per element of the string, or per position). -/
def intRes1 (imm a b la lb : Nat) : Nat :=
  let n := strN imm
  let av := strVal imm a
  let bv := strVal imm b
  match imm / 4 % 4 with
  | 0 => maskN n fun j => decide (j < lb) && anyN la fun i => decide (av i = bv j)
  | 1 =>
    maskN n fun j => decide (j < lb) && anyN (n / 2) fun k =>
      decide (2 * k + 1 < la) && decide (av (2 * k) ≤ bv j) && decide (bv j ≤ av (2 * k + 1))
  | 2 =>
    maskN n fun i =>
      if i < la ∧ i < lb then decide (av i = bv i) else decide (la ≤ i ∧ lb ≤ i)
  | _ =>
    maskN n fun j => allN (n - j) fun i =>
      if la ≤ i then true else if lb ≤ j + i then false else decide (av i = bv (j + i))

/-- `IntRes2`: `IntRes1` after the polarity of `imm8<5:4>`. -/
def intRes2 (imm a b la lb : Nat) : Nat :=
  let r := intRes1 imm a b la lb
  match imm / 16 % 4 with
  | 1 => r ^^^ (2 ^ strN imm - 1)
  | 3 => r ^^^ (2 ^ lb - 1)
  | _ => r

/-- The status flags of a string comparison: `CF = IntRes2 ≠ 0`, `ZF = (lb < n)`,
`SF = (la < n)`, `OF = IntRes2<0>`, `AF PF` cleared. -/
def strFlags (imm r la lb : Nat) : Flags :=
  { cf := some (decide (r ≠ 0)), pf := some false, af := some false,
    zf := some (decide (lb < strN imm)), sf := some (decide (la < strN imm)),
    ovf := some (decide (r % 2 = 1)) }

/-- The index result (`PCMPxSTRI`). -/
def strIndex (imm r : Nat) : Nat :=
  if r = 0 then strN imm else if imm / 64 % 2 = 0 then lowSet (strN imm) r else highSet (strN imm) r

/-- The mask result (`PCMPxSTRM`). -/
def strMask (imm r : Nat) : Nat :=
  if imm / 64 % 2 = 0 then r
  else ofElems (strE imm) (strN imm) fun i => if r / 2 ^ i % 2 = 1 then 2 ^ strE imm - 1 else 0

/-- An explicit length: the absolute value of the signed `w`-bit register value `v`, saturated
to `n`. -/
def explLen (w n v : Nat) : Nat := min (sint w (v % 2 ^ w)).natAbs n

/-! ## Packed floating point -/

/-- The format of `w`-bit elements. -/
@[reducible] def fmt (w : Nat) : Fmt := if w = 32 then binary32 else binary64

/-- `OR` of `f j` for `j < k`. -/
def orN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => orN k f ||| f k

/-- The `n` element results `f i` (each of width `w`) as one vector, with the flags and traps of
all of them. -/
def lanesFP (n w : Nat) (f : Nat → FP.XR) : FP.XR :=
  ⟨ofElems w n fun i => (f i).res, orN n fun i => (f i).flags, orN n fun i => (f i).traps⟩

/-- The scalar operation of a packed arithmetic instruction on `a` (destination element) and
`b` (source element). -/
def fpLane (op : PFOp) (f : Fmt) (c : FP.Ctl) (a b : Nat) : FP.XR :=
  match op with
  | .add => FP.binop .add f c a b
  | .sub => FP.binop .sub f c a b
  | .mul => FP.binop .mul f c a b
  | .div => FP.binop .div f c a b
  | .min => FP.minmax false f c a b
  | .max => FP.minmax true f c a b
  | .sqrt => FP.sqrt f c b

/-- The packed conversions on the source `b` (`m128` or `m64` as the form reads it). -/
def cvtOp (op : CvtOp) (c : FP.Ctl) (b : Nat) : FP.XR :=
  match op with
  | .dq2ps => lanesFP 4 32 fun i => FP.ofInt binary32 c 32 (elem b 32 i)
  | .ps2dq t => lanesFP 4 32 fun i => FP.toInt binary32 c (if t then .rz else c.rc) 32 (elem b 32 i)
  | .dq2pd => lanesFP 2 64 fun i => FP.ofInt binary64 c 32 (elem b 32 i)
  | .pd2dq t => lanesFP 2 32 fun i => FP.toInt binary64 c (if t then .rz else c.rc) 32 (elem b 64 i)
  | .ps2pd => lanesFP 2 64 fun i => FP.convert binary32 binary64 c (elem b 32 i)
  | .pd2ps => lanesFP 2 32 fun i => FP.convert binary64 binary32 c (elem b 64 i)

/-- The conversions with an `m64` source (no alignment requirement). -/
def cvtNarrow : CvtOp → Bool
  | .dq2pd | .ps2pd => true
  | _ => false

/-! ## State access -/

/-- `XMMn ← v` (bits 127:0; `ymmHi` preserved). -/
def setXmm (s : State) (n : Nat) (v : W128) : State :=
  { s with xmm := fun i => if i = n then v else s.xmm i }

/-- The 64-bit register `r ← v`. -/
def setReg (s : State) (r : Nat) (v : W64) : State :=
  { s with regs := fun i => if i = r then v else s.regs i }

/-- `MXCSR` with the flags `fl` raised. -/
def raiseMx (s : State) (fl : Nat) : State :=
  { s with mxcsr := BitVec.ofNat 32 (s.mxcsr.toNat ||| (fl &&& 0x3F)) }

/-- The low `8k` bits of an `XMM` operand, or `k` bytes of memory (`al`: a 16-byte operand must
be 16-byte aligned). -/
def readN (s : State) (ea : Addr → Nat) (al : Bool) (k : Nat) : XLoc → Except Fault Nat
  | .xmm n => .ok ((s.xmm n).toNat % 2 ^ (8 * k))
  | .mem a =>
    if al ∧ k = 16 ∧ ea a % 16 ≠ 0 then .error (.misaligned (ea a)) else load s.mem (ea a) k

/-- The low `w` bits of a general operand (register, `AH`..`BH`, or `w/8` bytes of memory). -/
def readG (s : State) (ea : Addr → Nat) (w : Nat) : Loc → Except Fault Nat
  | .reg r => .ok ((s.regs r).toNat % 2 ^ w)
  | .high r => .ok ((s.regs r).toNat / 256 % 256)
  | .mem a => load s.mem (ea a) (w / 8)

/-- Commit an `XMM[d]` result: `RIP` advanced. -/
def doneX (s : State) (next : W64) (d v : Nat) : Except Fault State :=
  .ok { setXmm s d (BitVec.ofNat 128 v) with rip := next }

/-- Commit a floating-point result to `XMM[d]`: `#XM` if an unmasked exception was raised,
else the result written and the flags ORed into `MXCSR`. -/
def doneFP (s : State) (pc : Nat) (next : W64) (d : Nat) (o : FP.XR) : Except Fault State :=
  if o.trap s.mxcsr.toNat then .error (.simdFPException pc)
  else .ok { raiseMx (setXmm s d (BitVec.ofNat 128 o.res)) o.flags with rip := next }

/-! ## The executor -/

/-- Execute `i` at `pc` (next instruction at `next`), with `ea` the linear address of a memory
operand. -/
def exec (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : SseI XLoc Loc Addr) :
    Except Fault State :=
  let ctl := FP.ctl s.mxcsr.toNat
  let x (n : Nat) : Nat := (s.xmm n).toNat
  match i with
  | .pint op d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (pintOp op (x d) b)
  | .pshift op e d imm => doneX s next d (pshiftOp op e (x d) imm)
  | .pimm op d src imm =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneX s next d (pimmOp op (x d) b imm)
  | .insertpsM d a imm =>
    match load s.mem (ea a) 4 with
    | .error e => .error e
    | .ok v => doneX s next d (insertDword (x d) v imm)
  | .blendv e d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b =>
      doneX s next d (lanes e fun i => if elem (x 0) e i / 2 ^ (e - 1) % 2 = 1 then elem b e i else elem (x d) e i)
  | .pmovx sg f t d src =>
    match readN s ea false (16 * f / t) src with
    | .error e => .error e
    | .ok b => doneX s next d (lanes t fun i => if sg then truncInt t (sint f (elem b f i)) else elem b f i)
  | .pinsr e d src imm =>
    match readG s ea e src with
    | .error e => .error e
    | .ok v => doneX s next d (lanes e fun i => if i = imm % (128 / e) then v else elem (x d) e i)
  | .pextr e dst src imm =>
    let v := elem (x src) e (imm % (128 / e))
    match dst with
    | .reg r => .ok { setReg s r (BitVec.ofNat 64 v) with rip := next }
    | .mem a =>
      match store s.mem (ea a) (e / 8) v with
      | .error e => .error e
      | .ok m => .ok { s with mem := m, rip := next }
    | .high _ => .error (.undecodable pc [])
  | .movmsk e d src =>
    .ok { setReg s d (BitVec.ofNat 64 (maskN (128 / e) fun i => decide (elem (x src) e i / 2 ^ (e - 1) % 2 = 1))) with rip := next }
  | .ptest a src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b =>
      let f : Flags := ⟨some (decide (b &&& (x a ^^^ (2 ^ 128 - 1)) = 0)), some false, some false,
        some (decide (x a &&& b = 0)), some false, some false⟩
      .ok { s with flags := f, rip := next }
  | .movHalf hi ld r a =>
    if ld then
      match load s.mem (ea a) 8 with
      | .error e => .error e
      | .ok v => doneX s next r (if hi then x r % 2 ^ 64 + v * 2 ^ 64 else x r / 2 ^ 64 * 2 ^ 64 + v)
    else
      match store s.mem (ea a) 8 (if hi then x r / 2 ^ 64 else x r % 2 ^ 64) with
      | .error e => .error e
      | .ok m => .ok { s with mem := m, rip := next }
  | .movdup op d src =>
    match op with
    | .ddup =>
      match readN s ea false 8 src with
      | .error e => .error e
      | .ok b => doneX s next d (b + b * 2 ^ 64)
    | .sldup =>
      match readN s ea true 16 src with
      | .error e => .error e
      | .ok b => doneX s next d (lanes 32 fun i => elem b 32 (i / 2 * 2))
    | .shdup =>
      match readN s ea true 16 src with
      | .error e => .error e
      | .ok b => doneX s next d (lanes 32 fun i => elem b 32 (i / 2 * 2 + 1))
  | .movnti w a r =>
    match store s.mem (ea a) (w / 8) ((s.regs r).toNat % 2 ^ w) with
    | .error e => .error e
    | .ok m => .ok { s with mem := m, rip := next }
  | .phminposuw d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => let (m, j) := minPos b 7; doneX s next d (m + 2 ^ 16 * j)
  | .crc32 w d src =>
    match readG s ea w src with
    | .error e => .error e
    | .ok v => .ok { setReg s d (BitVec.ofNat 64 (crc32c w ((s.regs d).toNat % 2 ^ 32) v)) with rip := next }
  | .pcmpstr expl index w64 a src imm =>
    match readN s ea false 16 src with
    | .error e => .error e
    | .ok b =>
      let n := strN imm
      let rw := if w64 then 64 else 32
      let la := if expl then explLen rw n (s.regs 0).toNat else firstZero (strE imm) (x a) n
      let lb := if expl then explLen rw n (s.regs 2).toNat else firstZero (strE imm) b n
      let r := intRes2 imm (x a) b la lb
      let s1 := { s with flags := strFlags imm r la lb }
      if index then .ok { setReg s1 1 (BitVec.ofNat 64 (strIndex imm r)) with rip := next }
      else .ok { setXmm s1 0 (BitVec.ofNat 128 (strMask imm r)) with rip := next }
  | .fpArith op w d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneFP s pc next d (lanesFP (128 / w) w fun i => fpLane op (fmt w) ctl (elem (x d) w i) (elem b w i))
  | .fpCmp w d src pred =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneFP s pc next d (lanesFP (128 / w) w fun i => FP.cmp (fmt w) ctl pred (elem (x d) w i) (elem b w i))
  | .fpRound w d src imm =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b => doneFP s pc next d (lanesFP (128 / w) w fun i => FP.roundInt (fmt w) ctl imm (elem b w i))
  | .fpHorz sub w d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b =>
      let h := 64 / w
      let o : FP.BinOp := if sub then .sub else .add
      doneFP s pc next d (lanesFP (128 / w) w fun j =>
        if j < h then FP.binop o (fmt w) ctl (elem (x d) w (2 * j)) (elem (x d) w (2 * j + 1))
        else FP.binop o (fmt w) ctl (elem b w (2 * (j - h))) (elem b w (2 * (j - h) + 1)))
  | .fpAddsub w d src =>
    match readN s ea true 16 src with
    | .error e => .error e
    | .ok b =>
      doneFP s pc next d (lanesFP (128 / w) w fun i =>
        FP.binop (if i % 2 = 0 then .sub else .add) (fmt w) ctl (elem (x d) w i) (elem b w i))
  | .cvt op d src =>
    match readN s ea (!cvtNarrow op) (if cvtNarrow op then 8 else 16) src with
    | .error e => .error e
    | .ok b => doneFP s pc next d (cvtOp op ctl b)

end Janus.Amd64.ExecSSE
