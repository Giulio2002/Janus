import Janus.Amd64.State
import Janus.Amd64.Instr
import Janus.Amd64.Float
import Janus.Amd64.ExecSSE
import Janus.Amd64.ExecAVX

/-!
# Semantics of the AVX-512 instructions (WP-G, trusted)

`ExecEVEX.exec` executes an `EvexI` (decoded by `Janus.Amd64.DecodeEVEX`); `Janus.Amd64.exec`
dispatches `Instr.evex` here with the linear address of each memory operand (`ea`, the same
`Janus.Amd64.ea` as every other instruction). Each operation is the `Operation` section of the
Intel SDM Vol. 2 for the EVEX form of the instruction (and, for `KMOV*` and friends, the VEX
form).

**State.** `ZMMn` is `zmmHi n ++ ymmHi n ++ xmm n` (`State.zmm`); `getZ s l n` is its low `l`
bits. Every vector register result is written by `setZ`: bits `l-1:0` from the result and bits
511:`l` **zeroed** (the EVEX zero-upper rule; at `l = 128` and `256` `setZ` is the VEX write
`ExecAVX.setV`, `ExecEVEXLemmas`). The opmask registers are `State.kreg`; a mask register
written with a `w`-bit value is zero-extended to 64 bits.

**Masking.** A write mask `k ≠ 0` selects element `i` (of `e` bits) of the destination iff bit
`i` of `K[k]` is set (`kb`). A selected element gets the result; a masked-off one is zeroed
(`z`, zeroing-masking) or keeps the destination's old value (merging-masking) (`merge`). `k = 0`
writes the whole result. Floating-point exceptions of masked-off elements are not raised.

**Width.** The packed operations are WP-D's and WP-F's with the vector width as a parameter:
the in-lane instructions apply WP-D's 128-bit operation to each of the `l/128` lanes
(`ExecAVX.perLane`, generalised to four lanes for `l = 512`), the element-wise ones run over `l/e`
elements.

**Memory and fault suppression.** EVEX memory operands are unaligned except for the aligned moves
(`l/8`-byte alignment, checked whatever the mask, `misaligned`). A broadcast (`{1toN}`) reads one
element. A full-width operand of an element-wise instruction with a write mask (`EOp.suppress`,
the compares, `VPBLENDM*`, the moves and the floating-point arithmetic: SDM exception classes
`E1`, `E2`, `E4`) accesses only its selected elements: a masked-off element is not read or
written and cannot fault (`rdMasked`, `stMasked`); as for WP-F's `VMASKMOV`, the model also
requires the whole operand below `2^47` (conservative). Every other memory operand (classes
`E4NF`, `E6NF`, ...: the permutes and shuffles, GFNI, `VPCLMULQDQ`, inserts, extracts, broadcasts,
`VPMOVSX/ZX`) is accessed in full, as is a broadcast element. `VPCOMPRESS*` to memory writes only
the packed elements, `VPEXPAND*` from memory reads only as many elements as are selected.

**Floating point.** As in WP-D/WP-F (`ExecSSE.fpLane`, `ExecAVX.vcmp`), with embedded rounding
(`{er}`: the `EVEX.L'L` rounding control replaces `MXCSR.RC`) and `{sae}`: both suppress every
exception (no `MXCSR` flags, no `#XM`); `DAZ`/`FTZ` still apply.
-/

namespace Janus.Amd64.ExecEVEX

open Janus.Arm64 (elem ofElems sint truncInt)
open Janus.Float (Fmt binary32 binary64)
open ExecSSE (lanes maskN lanesFP fpLane fmt allN orN)

/-! ## State access -/

/-- Bits `l-1:0` of `ZMMn` (`l ∈ {128, 256, 512}`). -/
def getZ (s : State) (l n : Nat) : Nat :=
  if l = 512 then s.zmm n else if l = 256 then s.ymm n else (s.xmm n).toNat

/-- The EVEX write of the `l`-bit value `v` to `ZMMn`: bits `l-1:0` from `v`, bits 511:`l`
zeroed. -/
def setZ (s : State) (l n v : Nat) : State :=
  { s with
    xmm := fun i => if i = n then BitVec.ofNat 128 v else s.xmm i
    ymmHi := fun i => if i = n then (if l = 128 then 0 else BitVec.ofNat 128 (v / 2 ^ 128)) else s.ymmHi i
    zmmHi := fun i => if i = n then (if l = 512 then BitVec.ofNat 256 (v / 2 ^ 256) else 0) else s.zmmHi i }

/-- Bit `i` of the opmask register `K[k]`. -/
def kb (s : State) (k i : Nat) : Bool := (s.kreg k).toNat / 2 ^ i % 2 = 1

/-- Whether element `i` is selected by the write mask `k` (`k = 0`: every element). -/
def selected (s : State) (k i : Nat) : Bool := k == 0 || kb s k i

/-- The masked `l`-bit value written to `ZMM[d]`: element `i` (of `e` bits) of the result `r`
where selected, otherwise `0` (`z`) or element `i` of the old destination. -/
def merge (s : State) (e l d k : Nat) (z : Bool) (r : Nat) : Nat :=
  if k = 0 then r else
  ofElems e (l / e) fun i => if kb s k i then elem r e i else if z then 0 else elem (getZ s l d) e i

/-- Commit a masked `l`-bit result to `ZMM[d]` (bits 511:`l` zeroed), `RIP` advanced. -/
def done (s : State) (next : W64) (e l d k : Nat) (z : Bool) (r : Nat) : Except Fault State :=
  .ok { setZ s l d (merge s e l d k z r) with rip := next }

/-- `K[n] ← v` (the 64-bit register; callers pass a value already zero-extended). -/
def setK (s : State) (n v : Nat) : State :=
  { s with kreg := fun i => if i = n then BitVec.ofNat 64 v else s.kreg i }

/-- The low `c` bits of `v` repeated over `l` bits. -/
def repl (c l v : Nat) : Nat := ofElems c (l / c) fun _ => v

/-! ## Memory operands -/

/-- The `l`-bit memory operand at `addr` with only the elements selected by `k` accessed (fault
suppression; masked-off elements read as 0). -/
def rdMasked (s : State) (addr l e k : Nat) : Except Fault Nat :=
  let n := l / e
  let sz := e / 8
  if addr + l / 8 > 2 ^ 47 then .error (.outsideAllocation addr (l / 8))
  else if !(allN n fun i => !kb s k i || s.mem.accessible (addr + i * sz) sz false) then
    .error (.outsideAllocation addr (l / 8))
  else .ok (ofElems e n fun i => if kb s k i then s.mem.readLE (addr + i * sz) sz else 0)

/-- A vector source operand of `l` bits with `e`-bit elements: a register, a broadcast element
(`bc ≠ 0`, `bc/8` bytes replicated), or `l/8` bytes of memory, of which only the elements
selected by `k` are accessed when `sup` (fault suppression). -/
def rdV (s : State) (ea : Addr → Nat) (l e bc k : Nat) (sup : Bool) : XLoc → Except Fault Nat
  | .xmm n => .ok (getZ s l n)
  | .mem a =>
    if bc ≠ 0 then
      match load s.mem (ea a) (bc / 8) with
      | .ok v => .ok (repl bc l v)
      | .error f => .error f
    else if sup ∧ k ≠ 0 then rdMasked s (ea a) l e k
    else load s.mem (ea a) (l / 8)

/-- The low `b` bits of a vector register, or `b/8` bytes of memory (no fault suppression). -/
def rdLow (s : State) (ea : Addr → Nat) (b : Nat) : XLoc → Except Fault Nat
  | .xmm n => .ok (s.zmm n % 2 ^ b)
  | .mem a => load s.mem (ea a) (b / 8)

/-- Store the `l`-bit `v` at `addr` with only the elements selected by `k` written (`k ≠ 0`):
with `sup` only those elements are accessed (fault suppression), otherwise the whole operand
must be writable. -/
def stMasked (s : State) (addr l e k v : Nat) (sup : Bool) : Except Fault Memory :=
  let n := l / e
  let sz := e / 8
  if k = 0 then store s.mem addr (l / 8) v
  else if addr + l / 8 > 2 ^ 47 then .error (.outsideAllocation addr (l / 8))
  else if sup then
    if !(allN n fun i => !kb s k i || s.mem.accessible (addr + i * sz) sz false) then
      .error (.outsideAllocation addr (l / 8))
    else if !(allN n fun i => !kb s k i || s.mem.accessible (addr + i * sz) sz true) then
      .error (.readOnly addr (l / 8))
    else .ok (ExecAVX.writeMasked s.mem addr sz (fun i => kb s k i) v n)
  else if !(s.mem.accessible addr (l / 8) false) then .error (.outsideAllocation addr (l / 8))
  else if !(s.mem.accessible addr (l / 8) true) then .error (.readOnly addr (l / 8))
  else .ok (ExecAVX.writeMasked s.mem addr sz (fun i => kb s k i) v n)

/-- The element-wise WP-D operations: the result element `i` depends only on the source elements
`i` (and the mask granularity is their width), so a masked memory operand is accessed element by
element (SDM exception class `E4`). -/
def pintElementwise : PIntOp → Bool
  | .add _ | .sub _ | .adds _ | .addus _ | .subs _ | .subus _ | .mull _ | .mulh _ | .minu _
  | .mins _ | .maxu _ | .maxs _ | .avg _ | .abs _ => true
  | _ => false

/-- Whether a masked full-width memory operand of `op` is accessed element by element. -/
def EOp.suppress : EOp → Bool
  | .pint op => pintElementwise op
  | .logic _ | .ternlog _ | .popcnt | .shiftv _ | .rotv _ => true
  | _ => false

/-- Whether a masked full-width memory operand of `op` is accessed element by element (the
immediate shifts and rotates, class `E4`). -/
def EUOp.suppress : EUOp → Bool
  | .shift _ | .rot _ => true
  | _ => false

/-- Whether `op` reads a 128-bit count operand (`VPSLLW ..., xmm/m128`). -/
def EOp.count : EOp → Bool
  | .pint op => ExecAVX.countOp op
  | _ => false

/-! ## GF(2⁸) and carry-less multiplication -/

/-- Carry-less product of `a` (its low `k` bits) and `b`. -/
def clmulN : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => (if a % 2 = 1 then b else 0) ^^^ clmulN k (a / 2) (2 * b)

/-- Reduction of a carry-less product of two bytes modulo `x⁸ + x⁴ + x³ + x + 1` (`0x11B`):
bits `j+7 .. 8` cleared from the top. -/
def gfRed : Nat → Nat → Nat
  | 0, x => x % 256
  | j + 1, x => gfRed j (if x / 2 ^ (j + 8) % 2 = 1 then x ^^^ (0x11B * 2 ^ j) else x)

/-- Multiplication in GF(2⁸) (the AES field). -/
def gfMul (a b : Nat) : Nat := gfRed 7 (clmulN 8 a b)

/-- The multiplicative inverse in GF(2⁸), `x²⁵⁴` (`0` for `0`). -/
def gfInv (x : Nat) : Nat :=
  let x2 := gfMul x x
  let x4 := gfMul x2 x2
  let x8 := gfMul x4 x4
  let x16 := gfMul x8 x8
  let x32 := gfMul x16 x16
  let x64 := gfMul x32 x32
  let x128 := gfMul x64 x64
  gfMul (gfMul (gfMul (gfMul (gfMul (gfMul x2 x4) x8) x16) x32) x64) x128

/-- Number of one bits among the low `n` bits of `x` (as `Janus.Amd64.popNat`, which is defined
after this module). -/
def popc : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + popc n (x / 2)

/-- Even parity of the low 8 bits of `x` as `0`/`1` (`1` = odd). -/
def parity8 (x : Nat) : Nat := popc 8 x % 2

/-- `PSHUFB` on one 128-bit lane: byte `i` is `0` if bit 7 of byte `i` of `y` is set, else byte
`y[i] mod 16` of `x`. -/
def shufbLane (x y : Nat) : Nat :=
  ofElems 8 16 fun i => if elem y 8 i ≥ 128 then 0 else elem x 8 (elem y 8 i % 16)

/-- `affine_byte(A, x, imm8)`: bit `i` is the parity of `A.byte[7-i] AND x`, `XOR imm8<i>`. -/
def gfAffine (A x imm : Nat) : Nat :=
  ofElems 1 8 fun i => (parity8 (elem A 8 (7 - i) &&& x) + imm / 2 ^ i) % 2

/-! ## Operations -/

/-- Rotate the `e`-bit `x` left by `c < e`. -/
def rotl (e x c : Nat) : Nat := x * 2 ^ c % 2 ^ e + x / 2 ^ (e - c)

/-- `VPTERNLOGD/Q` on `l`-bit `a` (destination), `b` (`src1`), `c` (`src2`): bit `j` of the result
is bit `4·a_j + 2·b_j + c_j` of `imm8`, as the `OR` of the minterms `imm8` selects. -/
def ternlog (l imm a b c : Nat) : Nat :=
  let m := 2 ^ l - 1
  let pick (bit : Bool) (x : Nat) : Nat := if bit then x % 2 ^ l else x ^^^ m
  orN 8 fun t =>
    if imm / 2 ^ t % 2 = 1 then pick (t / 4 % 2 = 1) a &&& pick (t / 2 % 2 = 1) b &&& pick (t % 2 = 1) c
    else 0

/-- `dst ← op(d, a, b)` at width `l` with `e`-bit elements (`d` the old destination, `a` = `src1`,
`b` = `src2`). -/
def evalOp (o : EOp) (e l d a b : Nat) : Nat :=
  let n := l / e
  match o with
  | .pint op => ExecAVX.pintV op l a b
  | .logic op =>
    match op with
    | .and => a &&& b
    | .andn => (a ^^^ (2 ^ l - 1)) &&& b
    | .or => a ||| b
    | .xor => a ^^^ b
  | .shufb => ExecAVX.perLane l (fun _ x y => shufbLane x y) a b
  | .ternlog imm => ternlog l imm d a b
  | .perm => ofElems e n fun i => elem b e (elem a e i % n)
  | .permi2 =>
    ofElems e n fun i =>
      let j := elem d e i % (2 * n)
      if j < n then elem a e j else elem b e (j - n)
  | .permt2 =>
    ofElems e n fun i =>
      let j := elem a e i % (2 * n)
      if j < n then elem d e j else elem b e (j - n)
  | .gfaffine inv imm =>
    ofElems 8 (l / 8) fun i =>
      gfAffine (elem b 64 (i / 8)) (if inv then gfInv (elem a 8 i) else elem a 8 i) imm
  | .gfmul => ofElems 8 (l / 8) fun i => gfMul (elem a 8 i) (elem b 8 i)
  | .popcnt => ofElems e n fun i => popc e (elem b e i)
  | .shiftv op => ExecAVX.shiftvV op e l a b
  | .rotv left =>
    ofElems e n fun i =>
      let c := elem b e i % e
      rotl e (elem a e i) (if left then c else (e - c) % e)
  | .alignr imm => ExecAVX.pimmV .palignr l a b imm
  | .align imm =>
    ofElems e n fun i =>
      let j := i + imm % n
      if j < n then elem b e j else elem a e (j - n)
  | .shuf128 imm =>
    let m := l / 128
    let bits := if m = 4 then 2 else 1
    ofElems 128 m fun j =>
      elem (if j < m / 2 then a else b) 128 (imm / 2 ^ (bits * j) % 2 ^ bits)
  | .clmul imm =>
    ExecAVX.perLane l (fun _ x y => clmulN 64 (elem x 64 (imm % 2)) (elem y 64 (imm / 16 % 2))) a b

/-- `dst ← op(b, imm8)` at width `l` with `e`-bit elements. -/
def evalUop (o : EUOp) (e l b imm : Nat) : Nat :=
  match o with
  | .shift op => ExecAVX.pshiftV op e l b imm
  | .rot left =>
    ofElems e (l / e) fun i => rotl e (elem b e i) (if left then imm % e else (e - imm % e) % e)
  | .shuf op => ExecAVX.shufV op l b imm
  | .permq => ofElems 64 (l / 64) fun i => elem b 64 (i / 4 * 4 + imm / 4 ^ (i % 4) % 4)

/-- `VPCMP*`'s predicate on `e`-bit `x`, `y`. -/
def icmp (signed : Bool) (pred e x y : Nat) : Bool :=
  let a : Int := if signed then sint e x else x
  let b : Int := if signed then sint e y else y
  match pred % 8 with
  | 0 => a = b
  | 1 => a < b
  | 2 => a ≤ b
  | 3 => false
  | 4 => a ≠ b
  | 5 => ¬ a < b
  | 6 => ¬ a ≤ b
  | _ => true

/-- `VPCOMPRESS*`: the selected elements (`p`) among the first `i` of `src` packed from element 0,
and their number. -/
def compressGo (e src : Nat) (p : Nat → Bool) : Nat → Nat × Nat
  | 0 => (0, 0)
  | i + 1 =>
    let r := compressGo e src p i
    if p i then (r.1 + 2 ^ (e * r.2) * elem src e i, r.2 + 1) else r

/-- `VPEXPAND*`: the first `i` elements of the result (selected ones from consecutive elements of
`src`, the others `old j`), and the number of source elements used. -/
def expandGo (e src : Nat) (p : Nat → Bool) (old : Nat → Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | i + 1 =>
    let r := expandGo e src p old i
    if p i then (r.1 + 2 ^ (e * i) * elem src e r.2, r.2 + 1) else (r.1 + 2 ^ (e * i) * (old i % 2 ^ e), r.2)

/-- The number of elements among the first `n` that `k` selects. -/
def countSel (s : State) (k n : Nat) : Nat := (compressGo 1 0 (selected s k) n).2

/-! ## Floating point -/

/-- The `MXCSR` controls with the embedded rounding `rc` (`1..4`: `RN RD RU RZ`) applied. -/
def ctlOf (s : State) (rc : Nat) : FP.Ctl :=
  let c := FP.ctl s.mxcsr.toNat
  if rc = 0 ∨ rc = 5 then c else { c with rc := FP.decodeRC (rc - 1) }

/-- Commit a masked packed floating-point result (`o.res` already merged): `#XM` if an unmasked
exception was raised, else written and the flags ORed into `MXCSR`. -/
def doneFP (s : State) (pc : Nat) (next : W64) (l d : Nat) (o : FP.XR) : Except Fault State :=
  if o.trap s.mxcsr.toNat then .error (.simdFPException pc)
  else .ok { ExecSSE.raiseMx (setZ s l d o.res) o.flags with rip := next }

/-! ## Opmask operations -/

/-- `KANDB/W/D/Q`... on the low `w` bits. -/
def kop (op : KOp) (w a b : Nat) : Nat :=
  let m := 2 ^ w - 1
  let x := a % 2 ^ w
  let y := b % 2 ^ w
  match op with
  | .and => x &&& y
  | .andn => (x ^^^ m) &&& y
  | .or => x ||| y
  | .xor => x ^^^ y
  | .xnor => (x ^^^ y) ^^^ m
  | .add => (x + y) % 2 ^ w

/-- The status flags of `KORTEST` (`zf`, `cf`): `OF SF AF PF` cleared. -/
def kflags (zf cf : Bool) : Flags :=
  { cf := some cf, pf := some false, af := some false, zf := some zf, sf := some false, ovf := some false }

/-- Read a `KMOV` source operand (`w` bits). -/
def rdK (s : State) (ea : Addr → Nat) (w : Nat) : KLoc Addr → Except Fault Nat
  | .k n => .ok ((s.kreg n).toNat % 2 ^ w)
  | .gpr r => .ok ((s.regs r).toNat % 2 ^ w)
  | .mem a => load s.mem (ea a) (w / 8)

/-! ## The executor -/

/-- Execute `i` at `pc` (next instruction at `next`), with `ea` the linear address of a memory
operand. -/
def exec (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : EvexI XLoc Loc Addr) :
    Except Fault State :=
  match i with
  | .mov e l al dst src k z =>
    match dst, src with
    | .xmm d, .xmm r => done s next e l d k z (getZ s l r)
    | .xmm d, .mem a =>
      if al ∧ ea a % (l / 8) ≠ 0 then .error (.misaligned (ea a)) else
      match rdV s ea l e 0 k true (.mem a) with
      | .error f => .error f
      | .ok v => done s next e l d k z v
    | .mem a, .xmm r =>
      if al ∧ ea a % (l / 8) ≠ 0 then .error (.misaligned (ea a)) else
      match stMasked s (ea a) l e k (getZ s l r) true with
      | .error f => .error f
      | .ok m => .ok { s with mem := m, rip := next }
    | .mem _, .mem _ => .error (.undecodable pc [])
  | .op o e l d s1 src bc k z =>
    match rdV s ea (if EOp.count o then 128 else l) e bc k (EOp.suppress o) src with
    | .error f => .error f
    | .ok b => done s next e l d k z (evalOp o e l (getZ s l d) (getZ s l s1) b)
  | .uop o e l d src bc imm k z =>
    match rdV s ea l e bc k (EUOp.suppress o) src with
    | .error f => .error f
    | .ok b => done s next e l d k z (evalUop o e l b imm)
  | .blendm e l d s1 src bc k z =>
    match rdV s ea l e bc k true src with
    | .error f => .error f
    | .ok b =>
      let a := getZ s l s1
      .ok { setZ s l d (ofElems e (l / e) fun i =>
              if selected s k i then elem b e i else if z then 0 else elem a e i) with rip := next }
  | .cmp c e l kd s1 src bc k =>
    match rdV s ea l e bc k true src with
    | .error f => .error f
    | .ok b =>
      let a := getZ s l s1
      let n := l / e
      match c with
      | .int sg p =>
        .ok { setK s kd (maskN n fun i => selected s k i && icmp sg p e (elem a e i) (elem b e i)) with rip := next }
      | .test neg =>
        .ok { setK s kd (maskN n fun i => selected s k i && ((elem a e i &&& elem b e i) ≠ 0) != neg) with
                rip := next }
      | .fp p sae =>
        let ctl := FP.ctl s.mxcsr.toNat
        let o := lanesFP n 1 fun i =>
          if selected s k i then
            let r := ExecAVX.vcmp (fmt e) ctl p (elem a e i) (elem b e i)
            ⟨if r.res = 0 then 0 else 1, if sae then 0 else r.flags, if sae then 0 else r.traps⟩
          else ⟨0, 0, 0⟩
        if o.trap s.mxcsr.toNat then .error (.simdFPException pc)
        else .ok { ExecSSE.raiseMx (setK s kd o.res) o.flags with rip := next }
  | .compress e l dst src k z =>
    let n := l / e
    let r := compressGo e (getZ s l src) (selected s k) n
    match dst with
    | .xmm d =>
      let old := getZ s l d
      let rest := if z then 0 else old / 2 ^ (e * r.2) * 2 ^ (e * r.2)
      .ok { setZ s l d (r.1 + rest) with rip := next }
    | .mem a =>
      let addr := ea a
      if addr + l / 8 > 2 ^ 47 then .error (.outsideAllocation addr (l / 8))
      else if r.2 = 0 then .ok { s with rip := next }
      else
        match store s.mem addr (r.2 * (e / 8)) r.1 with
        | .error f => .error f
        | .ok m => .ok { s with mem := m, rip := next }
  | .expand e l d src k z =>
    let n := l / e
    let old := getZ s l d
    let cnt := countSel s k n
    let rd : Except Fault Nat := match src with
      | .xmm r => .ok (getZ s l r)
      | .mem a =>
        if ea a + l / 8 > 2 ^ 47 then .error (.outsideAllocation (ea a) (l / 8))
        else if cnt = 0 then .ok 0 else load s.mem (ea a) (cnt * (e / 8))
    match rd with
    | .error f => .error f
    | .ok v =>
      let r := expandGo e v (selected s k) (fun j => if z then 0 else elem old e j) n
      .ok { setZ s l d r.1 with rip := next }
  | .extract e l c dst src imm k z =>
    let v := elem (getZ s l src) c (imm % (l / c))
    match dst with
    | .xmm d => done s next e c d k z v
    | .mem a =>
      match stMasked s (ea a) c e k v false with
      | .error f => .error f
      | .ok m => .ok { s with mem := m, rip := next }
  | .insert e l c d s1 src imm k z =>
    match rdLow s ea c src with
    | .error f => .error f
    | .ok b =>
      let a := getZ s l s1
      done s next e l d k z (ofElems c (l / c) fun j => if j = imm % (l / c) then b else elem a c j)
  | .bcast e c l d src k z =>
    match rdLow s ea c src with
    | .error f => .error f
    | .ok b => done s next e l d k z (repl c l b)
  | .bcastG e l d src k z => done s next e l d k z (repl e l ((s.regs src).toNat % 2 ^ e))
  | .pmovx sg f t l d src k z =>
    match rdLow s ea (l * f / t) src with
    | .error f => .error f
    | .ok b => done s next t l d k z (ExecAVX.pmovxV sg f t l b)
  | .fp op w l d s1 src bc rc k z =>
    match rdV s ea l w bc k true src with
    | .error f => .error f
    | .ok b =>
      let ctl := ctlOf s rc
      let a := getZ s l s1
      let old := getZ s l d
      let o := lanesFP (l / w) w fun i =>
        if selected s k i then
          let r := fpLane op (fmt w) ctl (elem a w i) (elem b w i)
          if rc = 0 then r else ⟨r.res, 0, 0⟩
        else ⟨if z then 0 else elem old w i, 0, 0⟩
      doneFP s pc next l d o
  | .kmov w dst src =>
    match rdK s ea w src with
    | .error f => .error f
    | .ok v =>
      match dst with
      | .k n => .ok { setK s n v with rip := next }
      | .gpr r => .ok { ExecSSE.setReg s r (BitVec.ofNat 64 v) with rip := next }
      | .mem a =>
        match store s.mem (ea a) (w / 8) v with
        | .error f => .error f
        | .ok m => .ok { s with mem := m, rip := next }
  | .klogic op w kd k1 k2 =>
    .ok { setK s kd (kop op w (s.kreg k1).toNat (s.kreg k2).toNat) with rip := next }
  | .knot w kd ks => .ok { setK s kd ((s.kreg ks).toNat % 2 ^ w ^^^ (2 ^ w - 1)) with rip := next }
  | .kshift left w kd ks imm =>
    let x := (s.kreg ks).toNat % 2 ^ w
    let v := if imm ≥ w then 0 else if left then x * 2 ^ imm % 2 ^ w else x / 2 ^ imm
    .ok { setK s kd v with rip := next }
  | .kortest w k1 k2 =>
    let x := ((s.kreg k1).toNat ||| (s.kreg k2).toNat) % 2 ^ w
    .ok { s with flags := kflags (x = 0) (x = 2 ^ w - 1), rip := next }
  | .ktest w k1 k2 =>
    let a := (s.kreg k1).toNat % 2 ^ w
    let b := (s.kreg k2).toNat % 2 ^ w
    .ok { s with flags := kflags (a &&& b = 0) (((a ^^^ (2 ^ w - 1)) &&& b) = 0), rip := next }
  | .kunpck w kd k1 k2 =>
    .ok { setK s kd ((s.kreg k2).toNat % 2 ^ w + 2 ^ w * ((s.kreg k1).toNat % 2 ^ w)) with rip := next }

end Janus.Amd64.ExecEVEX
