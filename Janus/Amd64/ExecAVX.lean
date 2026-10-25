import Janus.Amd64.State
import Janus.Amd64.Instr
import Janus.Amd64.Float
import Janus.Amd64.ExecSSE

/-!
# Semantics of the AVX / AVX2 / FMA3 instructions (WP-F, trusted)

`ExecAVX.exec` executes an `AvxI` (decoded by `Janus.Amd64.DecodeAVX`); `Janus.Amd64.exec`
dispatches `Instr.avx` here with the linear address of each memory operand (`ea`, the same
`Janus.Amd64.ea` as every other instruction). Each operation is the `Operation` section of the
Intel SDM Vol. 2 for the VEX form of the instruction.

**Width.** The packed operations are WP-D's (`Janus.Amd64.ExecSSE`) with the vector width as a
parameter rather than a second copy:

* the in-lane instructions (every AVX2 integer, pack/unpack, horizontal and byte-shuffle
  instruction, `VSHUFPS/PD`, `VPALIGNR`, `VPBLENDW`, `VMPSADBW`, ...) apply WP-D's 128-bit
  operation to each 128-bit lane (`perLane`; at `l = 128` it *is* WP-D's operation, so a VEX.128
  instruction produces exactly the term of its legacy-SSE form and the WP-D lemmas apply);
* the element-wise floating-point operations are WP-D's lane formulas over `l / w` elements
  instead of `128 / w` (`lanesFP (l / w) w ...`);
* the cross-lane instructions (`VPERMD`, `VPERMQ`, `VPERM2I128`, `VINSERTI128`, ...,
  `VPMOVSX/ZX`, the widening and narrowing conversions, broadcasts) are written directly over
  `l`-bit values; `cvtV 128 = ExecSSE.cvtOp` (`ExecAVXLemmas`).

**VEX.128 zero-upper.** Every register result is written by `setV`: bits 127:0 from the result,
bits 255:128 from it at `l = 256` and **zeroed** at `l = 128` (SDM Vol. 1 §14.1.3; the legacy-SSE
instructions of `ExecSSE` write only `xmm` and preserve `ymmHi`). The AVX-512 state above bit 255
is not modelled (no modelled instruction reads it).

**Floating point.** As in WP-D: the flags of all elements are ORed; an unmasked exception in any
element is `#XM` (`simdFPException`) and nothing is written. The 32 VEX comparison predicates are
`vcmp` (`= FP.cmp` for the eight legacy ones). Packed FMA is `FP.fma` per element (single
rounding); an element whose result the manuals leave to the implementation (`FP.fma = none`)
makes the whole instruction `undefinedResult`.

**Memory.** VEX memory operands are unaligned (the aligned moves are `Instr.vmov`). The masked
moves and gathers access only the selected elements (`maskmov`, `gather`):

* `VMASKMOV`/`VPMASKMOV`: an element whose mask bit is clear is not accessed and cannot fault
  (SDM Vol. 2 `VMASKMOV`: "Faults occur only due to mask-bit required memory accesses"); a
  selected element must be readable (load) or writable (store). Conservatively the model also
  faults unless the whole operand lies below `2^47` (the canonical lower half: the SDM's `#GP`
  for a non-canonical operand is stated for the instruction, not per element).
* `VPGATHER*`/`VGATHER*`: the elements are loaded in order from element 0; the SDM's partial
  completion (on a fault the completed elements are written and their mask bits cleared, so that
  the instruction can be restarted) is only visible to a signal handler, and a fault ends a Janus
  execution, so the model faults with nothing written. Without a fault the destination's selected
  elements are replaced, the others kept, the elements past `n` and bits 255:`n·e` zeroed, and the
  whole mask register zeroed. Equal destination, index and mask registers are `#UD` (rejected by
  the decoder).
-/

namespace Janus.Amd64.ExecAVX

open Janus.Arm64 (elem ofElems sint truncInt)
open Janus.Float (Fmt binary32 binary64)
open ExecSSE (lanes maskN lanesFP fpLane fmt allN)

/-! ## State access -/

/-- Bits `l-1:0` of `YMMn` (`l ∈ {128, 256}`). -/
def getV (s : State) (l n : Nat) : Nat := if l = 256 then s.ymm n else (s.xmm n).toNat

/-- The VEX write of the `l`-bit value `v` to `YMMn`: bits 127:0 from `v`, bits 255:128 from `v`
at `l = 256` and zeroed at `l = 128`. -/
def setV (s : State) (l n v : Nat) : State :=
  { s with
    xmm := fun i => if i = n then BitVec.ofNat 128 v else s.xmm i
    ymmHi := fun i => if i = n then (if l = 256 then BitVec.ofNat 128 (v / 2 ^ 128) else 0) else s.ymmHi i }

/-- `k` bytes of a vector operand: the low `8k` bits of a register (all 256 for `k = 32`), or `k`
bytes of memory (no alignment requirement). -/
def rd (s : State) (ea : Addr → Nat) (k : Nat) : XLoc → Except Fault Nat
  | .xmm n => .ok (if k = 32 then s.ymm n else if k = 16 then (s.xmm n).toNat else (s.xmm n).toNat % 2 ^ (8 * k))
  | .mem a => load s.mem (ea a) k

/-- Commit an `l`-bit result to `YMM[d]` (`setV`): `RIP` advanced. -/
def doneV (s : State) (next : W64) (l d v : Nat) : Except Fault State :=
  .ok { setV s l d v with rip := next }

/-- Commit a packed floating-point result: `#XM` if an unmasked exception was raised, else the
`l`-bit result written and the flags ORed into `MXCSR`. -/
def doneFPV (s : State) (pc : Nat) (next : W64) (l d : Nat) (o : FP.XR) : Except Fault State :=
  if o.trap s.mxcsr.toNat then .error (.simdFPException pc)
  else .ok { ExecSSE.raiseMx (setV s l d o.res) o.flags with rip := next }

/-- Commit a scalar floating-point result: `XMM[d] ← hi` with its low `w` bits replaced by the
result, bits 255:128 zeroed. -/
def doneS (s : State) (pc : Nat) (next : W64) (d hi w : Nat) (o : FP.XR) : Except Fault State :=
  if o.trap s.mxcsr.toNat then .error (.simdFPException pc)
  else .ok { ExecSSE.raiseMx (setV s 128 d (hi / 2 ^ w * 2 ^ w + o.res % 2 ^ w)) o.flags with rip := next }

/-! ## Lanes -/

/-- The 128-bit lane operation `f j a b` (`j` the lane) on each 128-bit lane of `l`-bit `a` and
`b`; at `l = 128` just `f 0 a b`. -/
def perLane (l : Nat) (f : Nat → Nat → Nat → Nat) (a b : Nat) : Nat :=
  if l = 256 then ofElems 128 2 fun j => f j (elem a 128 j) (elem b 128 j) else f 0 a b

/-- The shifts by a vector count (`VPSLLW xmm/ymm, xmm, xmm/m128`, ...): their count operand is
128 bits wide at both lengths and applies to every lane. -/
def countOp : PIntOp → Bool
  | .sll _ | .srl _ | .sra _ => true
  | _ => false

/-- `VPADDB ...`: WP-D's `pintOp` per lane (`b` the 128-bit count for `countOp`). -/
def pintV (op : PIntOp) (l a b : Nat) : Nat :=
  if countOp op then perLane l (fun _ x _ => ExecSSE.pintOp op x b) a 0
  else perLane l (fun _ x y => ExecSSE.pintOp op x y) a b

/-- `VPSLLW ..., imm8` per lane. -/
def pshiftV (op : PShiftOp) (e l a imm : Nat) : Nat :=
  perLane l (fun _ x _ => ExecSSE.pshiftOp op e x imm) a 0

/-- The immediate bits lane `j` of a 256-bit `pimm` instruction reads. -/
def laneImm (op : PImmOp) (j imm : Nat) : Nat :=
  if j = 0 then imm else
  match op with
  | .shufpd | .blendpd => imm / 4
  | .blendps => imm / 16
  | .mpsadbw => imm / 8
  | _ => imm

/-- `VSHUFPS ...`: WP-D's `pimmOp` per lane. -/
def pimmV (op : PImmOp) (l a b imm : Nat) : Nat :=
  perLane l (fun j x y => ExecSSE.pimmOp op x y (laneImm op j imm)) a b

/-- One lane `j` (value `b`) of a two-operand shuffle. -/
def shufLane (op : VShufOp) (j b imm : Nat) : Nat :=
  match op with
  | .pshufd | .permilps => lanes 32 fun i => elem b 32 (imm / 4 ^ i % 4)
  | .pshuflw => lanes 16 fun i => if i < 4 then elem b 16 (imm / 4 ^ i % 4) else elem b 16 i
  | .pshufhw => ExecSSE.pimmOp .pshufhw 0 b imm
  | .permilpd => lanes 64 fun i => elem b 64 (imm / 4 ^ j / 2 ^ i % 2)

/-- `VPSHUFD ...` per lane. -/
def shufV (op : VShufOp) (l b imm : Nat) : Nat := perLane l (fun j x _ => shufLane op j x imm) b 0

/-- `VPBLENDVB`/`VBLENDVPS`/`VBLENDVPD`. -/
def blendvV (e l a b m : Nat) : Nat :=
  ofElems e (l / e) fun i => if elem m e i / 2 ^ (e - 1) % 2 = 1 then elem b e i else elem a e i

/-- `VPMOVSX`/`VPMOVZX` from `f` to `t` bits at width `l`. -/
def pmovxV (signed : Bool) (f t l b : Nat) : Nat :=
  ofElems t (l / t) fun i => if signed then truncInt t (sint f (elem b f i)) else elem b f i

/-- `VMOVMSKPS/PD`: bit `i` is the sign of element `i`. -/
def movmskV (e l x : Nat) : Nat := maskN (l / e) fun i => decide (elem x e i / 2 ^ (e - 1) % 2 = 1)

/-- Whether no `e`-bit element of the `l`-bit `v` has its sign bit set. -/
def noSign (e l v : Nat) : Bool := allN (l / e) fun i => decide (elem v e i / 2 ^ (e - 1) % 2 = 0)

/-- `VTESTPS/PD a, b`. -/
def vtestFlags (e l a b : Nat) : Flags :=
  { cf := some (noSign e l (b &&& (a ^^^ (2 ^ l - 1)))), pf := some false, af := some false,
    zf := some (noSign e l (a &&& b)), sf := some false, ovf := some false }

/-- `VMOVDDUP` (each lane's low quadword twice), `VMOVSLDUP`, `VMOVSHDUP` at width `l`. -/
def movdupV (op : DupOp) (l b : Nat) : Nat :=
  match op with
  | .ddup => perLane l (fun _ x _ => x % 2 ^ 64 + x % 2 ^ 64 * 2 ^ 64) b 0
  | .sldup => ofElems 32 (l / 32) fun i => elem b 32 (i / 2 * 2)
  | .shdup => ofElems 32 (l / 32) fun i => elem b 32 (i / 2 * 2 + 1)

/-! ## Floating point -/

/-- `VCMPPS/PD/SS/SD` with the 32 VEX predicates: `p<2:0>` the relation of the eight legacy
predicates, `p<3>` inverts the unordered result (`EQ_UQ NGE_US NGT_US FALSE_OQ NEQ_OQ GE_OS GT_OS
TRUE_UQ`), `p<4>` swaps signalling and quiet (SDM Vol. 2 `CMPPD`, table 3-1). -/
def vcmp (f : Fmt) (c : FP.Ctl) (p : Nat) (a b : Nat) : FP.XR :=
  let q := p % 16
  let base := q % 8
  let signal := (q % 4 = 1 || q % 4 = 2) != (p / 16 % 2 = 1)
  let rel := FP.relation f c a b
  let holds : Bool := match rel with
    | none => (base = 3 || base = 4 || base = 5 || base = 6) != (q ≥ 8)
    | some r =>
      if base = 0 then r = 0 else if base = 1 then r < 0 else if base = 2 then r ≤ 0
      else if base = 3 then false else if base = 4 then r ≠ 0 else if base = 5 then ¬ r < 0
      else if base = 6 then ¬ r ≤ 0 else true
  let ones := 2 ^ f.width - 1
  match rel with
  | none => FP.check (if holds then ones else 0)
      (if Janus.Float.isSNaN f a || Janus.Float.isSNaN f b || signal then FP.IE else 0)
  | some _ =>
    let de := if FP.kindOf f c a = .subnormal || FP.kindOf f c b = .subnormal then FP.DE else 0
    FP.check (if holds then ones else 0) de

/-- `VHADDPS/PD`, `VHSUBPS/PD` at width `l`: in each 128-bit lane, the adjacent pairs of `a`, then
of `b`. -/
def fpHorzV (sub : Bool) (w l : Nat) (c : FP.Ctl) (a b : Nat) : FP.XR :=
  let k := 128 / w
  let h := 64 / w
  let o : FP.BinOp := if sub then .sub else .add
  lanesFP (l / w) w fun i =>
    let base := i / k * k
    let p := i % k
    if p < h then FP.binop o (fmt w) c (elem a w (base + 2 * p)) (elem a w (base + 2 * p + 1))
    else FP.binop o (fmt w) c (elem b w (base + 2 * (p - h))) (elem b w (base + 2 * (p - h) + 1))

/-- The conversions whose result is half as wide as the source (written as a 128-bit result). -/
def cvtHalf : CvtOp → Bool
  | .pd2dq _ | .pd2ps => true
  | _ => false

/-- The packed conversions at width `l` (`ExecSSE.cvtOp` at `l = 128`). -/
def cvtV (op : CvtOp) (l : Nat) (c : FP.Ctl) (b : Nat) : FP.XR :=
  match op with
  | .dq2ps => lanesFP (l / 32) 32 fun i => FP.ofInt binary32 c 32 (elem b 32 i)
  | .ps2dq t => lanesFP (l / 32) 32 fun i => FP.toInt binary32 c (if t then .rz else c.rc) 32 (elem b 32 i)
  | .dq2pd => lanesFP (l / 64) 64 fun i => FP.ofInt binary64 c 32 (elem b 32 i)
  | .pd2dq t => lanesFP (l / 64) 32 fun i => FP.toInt binary64 c (if t then .rz else c.rc) 32 (elem b 64 i)
  | .ps2pd => lanesFP (l / 64) 64 fun i => FP.convert binary32 binary64 c (elem b 32 i)
  | .pd2ps => lanesFP (l / 64) 32 fun i => FP.convert binary64 binary32 c (elem b 64 i)

/-- Packed FMA on `d` (destination), `y` (`src2`) and `z` (`src3`), element by element as the
scalar `Instr.vfmas`; `none` if any element is implementation-defined. -/
def fmaV (form : Nat) (negP negC : Bool) (alt w l : Nat) (c : FP.Ctl) (d y z : Nat) : Option FP.XR :=
  let f (i : Nat) : Option FP.XR :=
    let di := elem d w i
    let yi := elem y w i
    let zi := elem z w i
    let abc : Nat × Nat × Nat :=
      if form = 132 then (di, zi, yi) else if form = 213 then (yi, di, zi) else (yi, zi, di)
    let nc : Bool := if alt = 0 then negC else if alt = 1 then i % 2 = 0 else i % 2 = 1
    FP.fma (fmt w) c negP nc abc.1 abc.2.1 abc.2.2
  if allN (l / w) (fun i => (f i).isSome) then some (lanesFP (l / w) w fun i => (f i).getD default)
  else none

/-- IEEE binary16 (the F16C half-precision format). -/
def binary16 : Fmt := ⟨5, 10⟩

/-- `VCVTPH2PS`, one element: exact (every binary16 value is a binary32 value), `MXCSR.DAZ` and
`FTZ` not applied, no `DE`; a signalling NaN is quieted with `IE` (SDM Vol. 2 `VCVTPH2PS`). -/
def h2s (c : FP.Ctl) (h : Nat) : FP.XR :=
  let o := FP.convert binary16 binary32 { c with daz := false, ftz := false } h
  ⟨o.res, o.flags &&& (0x3F - FP.DE), o.traps &&& (0x3F - FP.DE)⟩

/-- `VCVTPS2PH`, one element: rounded by `imm8<1:0>`, or `MXCSR.RC` if `imm8<2>`; `MXCSR.FTZ` is
not applied (tiny results become binary16 subnormals), `DAZ` is. -/
def s2h (c : FP.Ctl) (imm x : Nat) : FP.XR :=
  let rm := if imm / 4 % 2 = 1 then c.rc else FP.decodeRC (imm % 4)
  FP.convert binary32 binary16 { c with rc := rm, ftz := false } x

/-! ## AVX2 permutes and variable shifts -/

/-- `VPERM2I128`/`VPERM2F128`. -/
def perm2V (a b imm : Nat) : Nat :=
  ofElems 128 2 fun j =>
    let sel := imm / 16 ^ j % 16
    if sel / 8 % 2 = 1 then 0 else elem (if sel % 4 < 2 then a else b) 128 (sel % 2)

/-- `VPERMILPS`/`VPERMILPD` with a control vector. -/
def permilvV (e l a ctl : Nat) : Nat :=
  if e = 32 then ofElems 32 (l / 32) fun i => elem a 32 (i / 4 * 4 + elem ctl 32 i % 4)
  else ofElems 64 (l / 64) fun i => elem a 64 (i / 2 * 2 + elem ctl 64 i / 2 % 2)

/-- `VPSLLV`/`VPSRLV`/`VPSRAV`. -/
def shiftvV (op : VShiftOp) (e l a b : Nat) : Nat :=
  ofElems e (l / e) fun i =>
    let c := elem b e i
    match op with
    | .sll => if c ≥ e then 0 else elem a e i * 2 ^ c
    | .srl => if c ≥ e then 0 else elem a e i / 2 ^ c
    | .sra => truncInt e (Int.fdiv (sint e (elem a e i)) (2 ^ (min c (e - 1))))

/-! ## Masked moves and gathers -/

/-- Memory `m` with element `i < k` of `v` (`sz` bytes at `addr + i·sz`) written where `p i`. -/
def writeMasked (m : Memory) (addr sz : Nat) (p : Nat → Bool) (v : Nat) : Nat → Memory
  | 0 => m
  | k + 1 =>
    let m' := writeMasked m addr sz p v k
    if p k then m'.writeLE (addr + k * sz) sz (elem v (8 * sz) k) else m'

/-- The top bit of element `i` of `v`. -/
@[reducible] def msb (v e i : Nat) : Bool := elem v e i / 2 ^ (e - 1) % 2 = 1

/-- `VMASKMOV`/`VPMASKMOV` (see the module doc). -/
def maskmovExec (s : State) (next : W64) (e l : Nat) (ld : Bool) (x mask addr : Nat) : Except Fault State :=
  let n := l / e
  let sz := e / 8
  let mv := getV s l mask
  if addr + l / 8 > 2 ^ 47 then .error (.outsideAllocation addr (l / 8)) else
  if !(allN n fun i => !msb mv e i || s.mem.accessible (addr + i * sz) sz false) then
    .error (.outsideAllocation addr (l / 8))
  else if ld then
    doneV s next l x (ofElems e n fun i => if msb mv e i then s.mem.readLE (addr + i * sz) sz else 0)
  else if !(allN n fun i => !msb mv e i || s.mem.accessible (addr + i * sz) sz true) then
    .error (.readOnly addr (l / 8))
  else .ok { s with mem := writeMasked s.mem addr sz (fun i => msb mv e i) (getV s l x) n, rip := next }

/-- The address of gather element `j`: `base + sext(index[j]) · 2^scale + disp (mod 2^64)`. -/
def gatherAddr (s : State) (ie : Nat) (a : Addr) (iv j : Nat) : Nat :=
  let base := match a.base with
    | some b => (s.regs b).toNat
    | none => 0
  let x := elem iv ie j
  let sx := if x ≥ 2 ^ (ie - 1) then x + 2 ^ 64 - 2 ^ ie else x
  (base + sx * 2 ^ a.scale + a.disp) % 2 ^ 64

/-- `VPGATHER*`/`VGATHER*` (see the module doc). -/
def gatherExec (s : State) (next : W64) (e ie l d mask : Nat) (a : Addr) : Except Fault State :=
  let n := l / max e ie
  let sz := e / 8
  let iv := getV s 256 (match a.index with | some i => i | none => 0)
  let mv := getV s 256 mask
  let dv := getV s 256 d
  let addr := gatherAddr s ie a iv
  if !(allN n fun j => !msb mv e j || s.mem.accessible (addr j) sz false) then
    .error (.outsideAllocation (addr 0) sz)
  else
    let r := ofElems e n fun j => if msb mv e j then s.mem.readLE (addr j) sz else elem dv e j
    .ok { setV (setV s (if n * e = 256 then 256 else 128) d r) 256 mask 0 with rip := next }

/-! ## The executor -/

/-- Execute `i` at `pc` (next instruction at `next`), with `ea` the linear address of a memory
operand. -/
def exec (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : AvxI XLoc Loc Addr) :
    Except Fault State :=
  let ctl := FP.ctl s.mxcsr.toNat
  let x (n : Nat) : Nat := (s.xmm n).toNat
  match i with
  | .pint op l d s1 src =>
    match rd s ea (if countOp op then 16 else l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (pintV op l (getV s l s1) b)
  | .pshift op e l d src imm => doneV s next l d (pshiftV op e l (getV s l src) imm)
  | .pimm op l d s1 src imm =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (pimmV op l (getV s l s1) b imm)
  | .shuf op l d src imm =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (shufV op l b imm)
  | .insertpsM d s1 a imm =>
    match load s.mem (ea a) 4 with
    | .error e => .error e
    | .ok v => doneV s next 128 d (ExecSSE.insertDword (x s1) v imm)
  | .blendv e l d s1 src m =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (blendvV e l (getV s l s1) b (getV s l m))
  | .pmovx sg f t l d src =>
    match rd s ea (l / 8 * f / t) src with
    | .error e => .error e
    | .ok b => doneV s next l d (pmovxV sg f t l b)
  | .pinsr e d s1 src imm =>
    match ExecSSE.readG s ea e src with
    | .error e => .error e
    | .ok v => doneV s next 128 d (lanes e fun i => if i = imm % (128 / e) then v else elem (x s1) e i)
  | .movmsk e l d src =>
    .ok { ExecSSE.setReg s d (BitVec.ofNat 64 (movmskV e l (getV s l src))) with rip := next }
  | .vtest e l a src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => .ok { s with flags := vtestFlags e l (getV s l a) b, rip := next }
  | .movHalfL hi d s1 a =>
    match load s.mem (ea a) 8 with
    | .error e => .error e
    | .ok v => doneV s next 128 d (if hi then x s1 % 2 ^ 64 + v * 2 ^ 64 else x s1 / 2 ^ 64 * 2 ^ 64 + v)
  | .movdup op l d src =>
    match rd s ea (if op = .ddup ∧ l = 128 then 8 else l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (movdupV op l b)
  | .phminposuw d src =>
    match rd s ea 16 src with
    | .error e => .error e
    | .ok b => let (m, j) := ExecSSE.minPos b 7; doneV s next 128 d (m + 2 ^ 16 * j)
  | .pcmpstrm expl w64 a src imm =>
    match rd s ea 16 src with
    | .error e => .error e
    | .ok b =>
      let n := ExecSSE.strN imm
      let rw := if w64 then 64 else 32
      let la := if expl then ExecSSE.explLen rw n (s.regs 0).toNat else ExecSSE.firstZero (ExecSSE.strE imm) (x a) n
      let lb := if expl then ExecSSE.explLen rw n (s.regs 2).toNat else ExecSSE.firstZero (ExecSSE.strE imm) b n
      let r := ExecSSE.intRes2 imm (x a) b la lb
      doneV { s with flags := ExecSSE.strFlags imm r la lb } next 128 0 (ExecSSE.strMask imm r)
  | .fpArith op w l d s1 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b =>
      doneFPV s pc next l d (lanesFP (l / w) w fun i => fpLane op (fmt w) ctl (elem (getV s l s1) w i) (elem b w i))
  | .fpCmp w l d s1 src p =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneFPV s pc next l d (lanesFP (l / w) w fun i => vcmp (fmt w) ctl p (elem (getV s l s1) w i) (elem b w i))
  | .fpRound w l d src imm =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneFPV s pc next l d (lanesFP (l / w) w fun i => FP.roundInt (fmt w) ctl imm (elem b w i))
  | .fpHorz sub w l d s1 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneFPV s pc next l d (fpHorzV sub w l ctl (getV s l s1) b)
  | .fpAddsub w l d s1 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b =>
      doneFPV s pc next l d (lanesFP (l / w) w fun i =>
        FP.binop (if i % 2 = 0 then .sub else .add) (fmt w) ctl (elem (getV s l s1) w i) (elem b w i))
  | .cvt op l d src =>
    match rd s ea (if ExecSSE.cvtNarrow op then l / 16 else l / 8) src with
    | .error e => .error e
    | .ok b => doneFPV s pc next (if cvtHalf op then 128 else l) d (cvtV op l ctl b)
  | .fma form negP negC alt w l d s2 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok z =>
      match fmaV form negP negC alt w l ctl (getV s l d) (getV s l s2) z with
      | none => .error (.undefinedResult pc)
      | some o => doneFPV s pc next l d o
  | .sArith op w d s1 src =>
    match rd s ea (w / 8) src with
    | .error e => .error e
    | .ok b => doneS s pc next d (x s1) w (fpLane op (fmt w) ctl (x s1 % 2 ^ w) b)
  | .sCmp w d s1 src p =>
    match rd s ea (w / 8) src with
    | .error e => .error e
    | .ok b => doneS s pc next d (x s1) w (vcmp (fmt w) ctl p (x s1 % 2 ^ w) b)
  | .cvtsi2f w iw d s1 src =>
    match ExecSSE.readG s ea iw src with
    | .error e => .error e
    | .ok v => doneS s pc next d (x s1) w (FP.ofInt (fmt w) ctl iw v)
  | .cvtff w d s1 src =>
    match rd s ea (w / 8) src with
    | .error e => .error e
    | .ok b =>
      let w' := if w = 64 then 32 else 64
      doneS s pc next d (x s1) w' (FP.convert (fmt w) (fmt w') ctl b)
  | .sRound w d s1 src imm =>
    match rd s ea (w / 8) src with
    | .error e => .error e
    | .ok b => doneS s pc next d (x s1) w (FP.roundInt (fmt w) ctl imm b)
  | .movsRR w d s1 s2 => doneV s next 128 d (x s1 / 2 ^ w * 2 ^ w + x s2 % 2 ^ w)
  | .vload k d src =>
    match rd s ea k src with
    | .error e => .error e
    | .ok b => doneV s next 128 d b
  | .movdG w d src =>
    match ExecSSE.readG s ea w src with
    | .error e => .error e
    | .ok v => doneV s next 128 d v
  | .perm2 d s1 src imm =>
    match rd s ea 32 src with
    | .error e => .error e
    | .ok b => doneV s next 256 d (perm2V (getV s 256 s1) b imm)
  | .permd d idx src =>
    match rd s ea 32 src with
    | .error e => .error e
    | .ok b => doneV s next 256 d (ofElems 32 8 fun i => elem b 32 (elem (getV s 256 idx) 32 i % 8))
  | .permq d src imm =>
    match rd s ea 32 src with
    | .error e => .error e
    | .ok b => doneV s next 256 d (ofElems 64 4 fun i => elem b 64 (imm / 4 ^ i % 4))
  | .permilv e l d s1 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok c => doneV s next l d (permilvV e l (getV s l s1) c)
  | .insert128 d s1 src imm =>
    match rd s ea 16 src with
    | .error e => .error e
    | .ok b => doneV s next 256 d (ofElems 128 2 fun j => if j = imm % 2 then b else elem (getV s 256 s1) 128 j)
  | .extract128 dst src imm =>
    let v := elem (getV s 256 src) 128 (imm % 2)
    match dst with
    | .xmm r => doneV s next 128 r v
    | .mem a =>
      match store s.mem (ea a) 16 v with
      | .error e => .error e
      | .ok m => .ok { s with mem := m, rip := next }
  | .bcast e l d src =>
    match rd s ea (e / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (ofElems e (l / e) fun _ => b)
  | .maskmov e l ld xr m a => maskmovExec s next e l ld xr m (ea a)
  | .shiftv op e l d s1 src =>
    match rd s ea (l / 8) src with
    | .error e => .error e
    | .ok b => doneV s next l d (shiftvV op e l (getV s l s1) b)
  | .gather e ie l d m a => gatherExec s next e ie l d m a
  | .cvtph2ps l d src =>
    match rd s ea (l / 16) src with
    | .error e => .error e
    | .ok b => doneFPV s pc next l d (lanesFP (l / 32) 32 fun i => h2s ctl (elem b 16 i))
  | .cvtps2ph l dst src imm =>
    let o := lanesFP (l / 32) 16 fun i => s2h ctl imm (elem (getV s l src) 32 i)
    if o.trap s.mxcsr.toNat then .error (.simdFPException pc) else
    match dst with
    | .xmm r => .ok { ExecSSE.raiseMx (setV s 128 r o.res) o.flags with rip := next }
    | .mem a =>
      match store s.mem (ea a) (l / 16) o.res with
      | .error e => .error e
      | .ok m => .ok { ExecSSE.raiseMx { s with mem := m } o.flags with rip := next }
  | .vzeroall => .ok { s with xmm := fun _ => 0, ymmHi := fun _ => 0, rip := next }

end Janus.Amd64.ExecAVX
