import Janus.Arm64.State
import Janus.Arm64.Instr
import Janus.Arm64.Bits
import Janus.Arm64.Decode

/-!
# AArch64 execution semantics for the supported subset

`step w s` decodes the 32-bit word `w` fetched at `s.pc` and executes it, returning the
successor state (with `pc` advanced by 4 or redirected) or a `Fault`.

Each case follows the ARM ARM `Operation` pseudocode of the instruction. Operations of the
32-bit (`sf = 0`) forms are computed on `BitVec 32` and zero-extended to 64 bits on write,
which is what `X[d, 32] = result` does on AArch64. The executor is written with
non-recursive definitions (plus the structurally recursive `Nat` helpers of `Bits`) so that
`simp` and `decide` can evaluate it; see `JanusTests/Exec.lean`.

Modelling decisions (user mode, Linux):
* Memory accesses go through the checked `load`/`store` of `State`; an access outside the
  caller's allocations is a `Fault`, never a value.
* An access whose base register is SP (`Rn = 31`) faults with `spMisaligned` unless
  `SP % 16 = 0` (Linux sets SCTLR_EL1.SA0). The check precedes the access, as in the
  pseudocode (`if n == 31 then CheckSPAlignment()`).
* BR/BLR/RET to a target that is not a multiple of 4 fault with `pcMisaligned` (on hardware
  this is the PC alignment fault taken at the next fetch). Immediate branches always produce
  4-aligned targets when `pc` is aligned. All address arithmetic wraps modulo 2^64.
* Top-byte-ignore (Linux enables TBI0 for EL0) is not modelled: addresses use all 64 bits,
  so an access through a tagged pointer lies outside every allocation, and an indirect
  branch to a tagged address leaves the tag in `pc`, which matches no loaded code. Both end
  in a fault, so this is conservative (hardware would proceed).
* The model is single-threaded with no caches, so DMB/DSB/ISB and the accepted hints
  (NOP, YIELD, SEV, SEVL, DGH, CSDB, BTI) only advance `pc`.
-/

namespace Janus.Arm64

/-! ## Pseudocode library -/

/-- ARM ARM `AddWithCarry(x, y, carry_in)`:
```
unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
signed_sum   = SInt(x) + SInt(y) + UInt(carry_in);
result = unsigned_sum<N-1:0>;
n = result<N-1>; z = IsZero(result);
c = if UInt(result) == unsigned_sum then '0' else '1';
v = if SInt(result) == signed_sum then '0' else '1';
```
-/
def addWithCarry {N : Nat} (x y : BitVec N) (carry : Bool) : BitVec N × Flags :=
  let unsignedSum : Nat := x.toNat + y.toNat + carry.toNat
  let signedSum : Int := x.toInt + y.toInt + (carry.toNat : Int)
  let result : BitVec N := BitVec.ofNat N unsignedSum
  (result, { n := result.msb, z := decide (result = 0),
             c := decide (result.toNat ≠ unsignedSum), v := decide (result.toInt ≠ signedSum) })

@[simp] theorem addWithCarry_false_fst {N : Nat} (x y : BitVec N) :
    (addWithCarry x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [addWithCarry]

@[simp] theorem addWithCarry_not_true_fst {N : Nat} (x y : BitVec N) :
    (addWithCarry x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, BitVec.toNat_sub,
    Bool.toNat_true]
  have := y.isLt
  have : 0 < 2 ^ N := Nat.two_pow_pos N
  congr 1
  omega

/-- `x + y` (`sub = false`) or `x + NOT(y) + 1` (`sub = true`), with flags, as in the
add/subtract instructions: `if sub_op then operand2 = NOT(operand2); carry_in = '1'`. -/
def addSub {N : Nat} (x y : BitVec N) (sub : Bool) : BitVec N × Flags :=
  if sub then addWithCarry x (~~~y) true else addWithCarry x y false

/-- The result of `addSub` as plain `BitVec` arithmetic. Use this (and do not unfold `addSub`)
when simplifying: `simp` would otherwise first normalise `~~~y` on literals. -/
@[simp] theorem addSub_fst {N : Nat} (x y : BitVec N) (sub : Bool) :
    (addSub x y sub).1 = if sub then x - y else x + y := by
  cases sub <;> simp [addSub]

/-- ARM ARM `ConditionHolds(cond)`. -/
def conditionHolds (cond : Nat) (f : Flags) : Bool :=
  let base :=
    match cond / 2 with
    | 0 => f.z                      -- EQ / NE
    | 1 => f.c                      -- CS / CC
    | 2 => f.n                      -- MI / PL
    | 3 => f.v                      -- VS / VC
    | 4 => f.c && !f.z              -- HI / LS
    | 5 => f.n == f.v               -- GE / LT
    | 6 => f.n == f.v && !f.z       -- GT / LE
    | _ => true                     -- AL
  if cond % 2 = 1 && cond ≠ 15 then !base else base

/-- ARM ARM `ShiftReg(reg, shift_type, amount)` applied to the register value `x`. -/
def shiftReg {N : Nat} (x : BitVec N) (t : ShiftType) (amount : Nat) : BitVec N :=
  match t with
  | .lsl => x <<< amount
  | .lsr => x >>> amount
  | .asr => x.sshiftRight amount
  | .ror => x.rotateRight amount

/-- ARM ARM `ExtendReg(reg, exttype, shift)` at width `N`, for the 64-bit register value `v`:
```
val = X[reg, N]; len = Min(len, N - shift);
return Extend(val<len-1:0> : Zeros(shift), N, unsigned);
```
This equals "extend the low `len` bits of `val` to `N` bits, then shift left by `shift`
(mod 2^N)": bits of the extension above `N - shift` are shifted out either way. -/
def extendReg (N : Nat) (v : W64) (t : ExtendType) (shift : Nat) : BitVec N :=
  let ext : BitVec N :=
    match t with
    | .uxtb => (v.setWidth 8).setWidth N
    | .uxth => (v.setWidth 16).setWidth N
    | .uxtw => (v.setWidth 32).setWidth N
    | .uxtx => v.setWidth N
    | .sxtb => (v.setWidth 8).signExtend N
    | .sxth => (v.setWidth 16).signExtend N
    | .sxtw => (v.setWidth 32).signExtend N
    | .sxtx => v.signExtend N
  ext <<< shift

/-- Flags of the logical flag-setting instructions (ANDS/BICS): `N:Z:00`. -/
def logicFlags {N : Nat} (r : BitVec N) : Flags :=
  { n := r.msb, z := decide (r = 0), c := false, v := false }

/-! ## Register file access at a width -/

namespace State

/-- `X[r, N]`: the low `N` bits of register `r`, 31 = ZR. -/
def getX (s : State) (N r : Nat) : BitVec N := (s.readZR r).setWidth N

/-- `SP`-or-`X[r]` at width `N`, 31 = SP. -/
def getXSP (s : State) (N r : Nat) : BitVec N := (s.readSP r).setWidth N

/-- `X[r] = ZeroExtend(v)`, 31 = ZR. -/
def setX {N : Nat} (s : State) (r : Nat) (v : BitVec N) : State := s.writeZR r (v.setWidth 64)

/-- `X[r]`/`SP` `= ZeroExtend(v)`, 31 = SP. -/
def setXSP {N : Nat} (s : State) (r : Nat) (v : BitVec N) : State := s.writeSP r (v.setWidth 64)

/-- Advance `pc` to the next sequential instruction. -/
def next (s : State) : State := { s with pc := s.pc + 4 }

def setFlags (s : State) (f : Flags) : State := { s with flags := f }

end State

/-! ## Data processing -/

def execAddSubImm (N : Nat) (s : State) (op S sh : Bool) (imm12 rn rd : Nat) : State :=
  let x := s.getXSP N rn
  let imm : BitVec N := BitVec.ofNat N (if sh then imm12 * 2 ^ 12 else imm12)
  let res := addSub x imm op
  if S then (s.setX rd res.1).setFlags res.2 else s.setXSP rd res.1

def execAddSubShifted (N : Nat) (s : State) (op S : Bool) (shift : ShiftType)
    (rm imm6 rn rd : Nat) : State :=
  let x := s.getX N rn
  let y := shiftReg (s.getX N rm) shift imm6
  let res := addSub x y op
  if S then (s.setX rd res.1).setFlags res.2 else s.setX rd res.1

def execAddSubExt (N : Nat) (s : State) (op S : Bool) (rm : Nat) (option : ExtendType)
    (imm3 rn rd : Nat) : State :=
  let x := s.getXSP N rn
  let y := extendReg N (s.readZR rm) option imm3
  let res := addSub x y op
  if S then (s.setX rd res.1).setFlags res.2 else s.setXSP rd res.1

def execAddSubCarry (N : Nat) (s : State) (op S : Bool) (rm rn rd : Nat) : State :=
  let x := s.getX N rn
  let y := s.getX N rm
  let res := addWithCarry x (if op then ~~~y else y) s.flags.c
  if S then (s.setX rd res.1).setFlags res.2 else s.setX rd res.1

/-- The logical operation, for AND/ORR/EOR/ANDS. -/
def logicOp {N : Nat} (opc : LogicOp) (x y : BitVec N) : BitVec N :=
  match opc with
  | .and => x &&& y
  | .orr => x ||| y
  | .eor => x ^^^ y
  | .ands => x &&& y

def execLogicalImm (N : Nat) (s : State) (opc : LogicOp) (Nbit : Bool) (immr imms rn rd : Nat) :
    State :=
  -- `decode` guarantees `DecodeBitMasks` succeeds; `getD` only makes `exec` total.
  let imm : BitVec N := BitVec.ofNat N ((decodeBitMasks Nbit imms immr true N).getD (0, 0)).1
  let r := logicOp opc (s.getX N rn) imm
  match opc with
  | .ands => (s.setX rd r).setFlags (logicFlags r)
  | _ => s.setXSP rd r

def execLogicalShifted (N : Nat) (s : State) (opc : LogicOp) (shift : ShiftType) (invert : Bool)
    (rm imm6 rn rd : Nat) : State :=
  let y := shiftReg (s.getX N rm) shift imm6
  let y := if invert then ~~~y else y
  let r := logicOp opc (s.getX N rn) y
  match opc with
  | .ands => (s.setX rd r).setFlags (logicFlags r)
  | _ => s.setX rd r

def execMoveWide (N : Nat) (s : State) (opc : MoveWideOp) (hw imm16 rd : Nat) : State :=
  let pos := hw * 16
  let field : BitVec N := BitVec.ofNat N imm16 <<< pos
  match opc with
  | .movz => s.setX rd field
  | .movn => s.setX rd (~~~field)
  | .movk => s.setX rd ((s.getX N rd &&& ~~~(BitVec.ofNat N 0xFFFF <<< pos)) ||| field)

/-- SBFM/BFM/UBFM:
```
(wmask, tmask) = DecodeBitMasks(N, imms, immr, FALSE, datasize);
dst = if inzero then Zeros() else X[d]; src = X[n];
bot = (dst AND NOT(wmask)) OR (ROR(src, R) AND wmask);
top = if extend then Replicate(src<S>) else dst;
X[d] = (top AND NOT(tmask)) OR (bot AND tmask);
```
-/
def execBitfield (N : Nat) (s : State) (opc : BitfieldOp) (Nbit : Bool) (immr imms rn rd : Nat) :
    State :=
  let masks := (decodeBitMasks Nbit imms immr false N).getD (0, 0)
  let wmask : BitVec N := BitVec.ofNat N masks.1
  let tmask : BitVec N := BitVec.ofNat N masks.2
  let inzero := match opc with | .bfm => false | _ => true
  let extend := match opc with | .sbfm => true | _ => false
  let src := s.getX N rn
  let dst : BitVec N := if inzero then 0 else s.getX N rd
  let bot := (dst &&& ~~~wmask) ||| (src.rotateRight immr &&& wmask)
  let top : BitVec N := if extend then (if src.getLsbD imms then BitVec.allOnes N else 0) else dst
  s.setX rd ((top &&& ~~~tmask) ||| (bot &&& tmask))

/-- EXTR: `concat = X[n]:X[m]; result = concat<lsb+datasize-1:lsb>`. -/
def execExtr (N : Nat) (s : State) (rm imms rn rd : Nat) : State :=
  s.setX rd ((s.getX N rn ++ s.getX N rm).extractLsb' imms N)

/-- CSEL/CSINC/CSINV/CSNEG:
`result = if ConditionHolds(cond) then X[n] else X[m]` with `else_inv`/`else_inc`. -/
def execCondSel (N : Nat) (s : State) (op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) :
    State :=
  let r : BitVec N :=
    if conditionHolds cond s.flags then s.getX N rn
    else
      let r := s.getX N rm
      let r := if op then ~~~r else r
      if o2 then r + 1 else r
  s.setX rd r

/-- CCMN/CCMP: `if ConditionHolds(cond) then (-, flags) = AddWithCarry(...) else nzcv`. -/
def execCondCmp {N : Nat} (s : State) (op : Bool) (x y : BitVec N) (cond nzcv : Nat) : State :=
  if conditionHolds cond s.flags then s.setFlags (addSub x y op).2
  else s.setFlags { n := bit nzcv 3, z := bit nzcv 2, c := bit nzcv 1, v := bit nzcv 0 }

def execMadd (N : Nat) (s : State) (o0 : Bool) (rm ra rn rd : Nat) : State :=
  let prod := s.getX N rn * s.getX N rm
  s.setX rd (if o0 then s.getX N ra - prod else s.getX N ra + prod)

/-- SMADDL/SMSUBL/UMADDL/UMSUBL:
`result = UInt(X[a]) ± Int(W[n], unsigned) * Int(W[m], unsigned); X[d] = result<63:0>`. -/
def execMaddl (s : State) (U o0 : Bool) (rm ra rn rd : Nat) : State :=
  let a : Int := (s.getX 64 ra).toNat
  let n : Int := if U then (s.getX 32 rn).toNat else (s.getX 32 rn).toInt
  let m : Int := if U then (s.getX 32 rm).toNat else (s.getX 32 rm).toInt
  s.setX rd (BitVec.ofInt 64 (if o0 then a - n * m else a + n * m))

/-- SMULH/UMULH: `result = Int(X[n]) * Int(X[m]); X[d] = result<127:64>`. -/
def execMulh (s : State) (U : Bool) (rm rn rd : Nat) : State :=
  let ext (v : W64) : BitVec 128 := if U then v.setWidth 128 else v.signExtend 128
  s.setX rd ((ext (s.getX 64 rn) * ext (s.getX 64 rm)).extractLsb' 64 64)

/-- UDIV/SDIV: `if IsZero(operand2) then result = 0 else RoundTowardsZero(op1 / op2)`;
`INT_MIN / -1` wraps to `INT_MIN` when truncated to `datasize` bits. -/
def execDiv (N : Nat) (s : State) (signed : Bool) (rm rn rd : Nat) : State :=
  let x := s.getX N rn
  let y := s.getX N rm
  let r : BitVec N :=
    if y = 0 then 0
    else if signed then BitVec.ofInt N (Int.tdiv x.toInt y.toInt)
    else BitVec.ofNat N (x.toNat / y.toNat)
  s.setX rd r

/-- LSLV/LSRV/ASRV/RORV: `ShiftReg(n, shift_type, UInt(X[m]) MOD datasize)`. -/
def execShiftV (N : Nat) (s : State) (t : ShiftType) (rm rn rd : Nat) : State :=
  s.setX rd (shiftReg (s.getX N rn) t ((s.getX N rm).toNat % N))

def execRbit (N : Nat) (s : State) (rn rd : Nat) : State :=
  s.setX rd (BitVec.ofNat N (rbitNat N (s.getX N rn).toNat))

/-- REV16/REV32/REV: `container_size = 8 << opc` bits; reverse bytes in each container. -/
def execRev (N : Nat) (s : State) (opc rn rd : Nat) : State :=
  let cb := 2 ^ opc   -- container size in bytes: opc 1 → 2, 2 → 4, 3 → 8
  s.setX rd (BitVec.ofNat N (revContainersNat cb (N / 8 / cb) (s.getX N rn).toNat))

def execClz (N : Nat) (s : State) (rn rd : Nat) : State :=
  s.setX rd (BitVec.ofNat N (clzNat N (s.getX N rn).toNat))

/-- CLS: `CountLeadingSignBits(x) = CountLeadingZeroBits(x<N-1:1> EOR x<N-2:0>)`. -/
def execCls (N : Nat) (s : State) (rn rd : Nat) : State :=
  let x := (s.getX N rn).toNat
  s.setX rd (BitVec.ofNat N (clzNat (N - 1) ((x / 2) ^^^ (x % 2 ^ (N - 1)))))

/-! ## Branches -/

/-- `SignExtend(imm, 64)` of a `width`-bit field value `imm`. -/
def sext64 (width imm : Nat) : W64 := (BitVec.ofNat width imm).signExtend 64

/-- An indirect branch: fault unless the target is 4-byte aligned. -/
def branchReg (s : State) (target : W64) : Except Fault State :=
  if target.toNat % 4 = 0 then .ok { s with pc := target }
  else .error (.pcMisaligned target.toNat)

/-! ## Loads and stores -/

/-- The base address `X[n]`, or `SP` for `n = 31` after `CheckSPAlignment()`. -/
def baseAddr (s : State) (rn : Nat) : Except Fault W64 :=
  if rn = 31 then
    if s.sp.toNat % 16 = 0 then .ok s.sp else .error (.spMisaligned s.sp.toNat)
  else .ok (s.regs rn)

/-- Sign-extend the `2^size`-byte loaded value `v` to `M` bits (`size ≤ 2`). -/
def signExtendLoad (size : Nat) (M : Nat) (v : Nat) : BitVec M :=
  if size = 0 then (BitVec.ofNat 8 v).signExtend M
  else if size = 1 then (BitVec.ofNat 16 v).signExtend M
  else (BitVec.ofNat 32 v).signExtend M

/-- The single-register access of `2^size` bytes at `addr`, selected by `opc`:
00 store `X[t]` (low bytes), 01 load and zero-extend, 10 load and sign-extend to 64 bits,
11 load, sign-extend to 32 bits and zero-extend to 64 bits. -/
def memSingle (s : State) (size opc rt : Nat) (addr : W64) : Except Fault State :=
  if opc = 0 then
    match store s.mem addr.toNat (2 ^ size) (s.readZR rt).toNat with
    | .ok m => .ok { s with mem := m }
    | .error e => .error e
  else
    match load s.mem addr.toNat (2 ^ size) with
    | .error e => .error e
    | .ok v =>
      let val : W64 :=
        if opc = 1 then BitVec.ofNat 64 v
        else if opc = 2 then signExtendLoad size 64 v
        else (signExtendLoad size 32 v).setWidth 64
      .ok (s.writeZR rt val)

/-- LDP/STP/LDPSW at `addr` and `addr + dbytes`, `dbytes = 4 << opc<1>`. -/
def memPair (s : State) (opc : Nat) (L : Bool) (rt rt2 : Nat) (addr : W64) :
    Except Fault State :=
  let dbytes := 2 ^ (2 + opc / 2)
  let addr2 := addr + BitVec.ofNat 64 dbytes
  if L then
    match load s.mem addr.toNat dbytes with
    | .error e => .error e
    | .ok v1 =>
      match load s.mem addr2.toNat dbytes with
      | .error e => .error e
      | .ok v2 =>
        let ext (v : Nat) : W64 := if opc = 1 then signExtendLoad 2 64 v else BitVec.ofNat 64 v
        .ok ((s.writeZR rt (ext v1)).writeZR rt2 (ext v2))
  else
    match store s.mem addr.toNat dbytes (s.readZR rt).toNat with
    | .error e => .error e
    | .ok m1 =>
      match store m1 addr2.toNat dbytes (s.readZR rt2).toNat with
      | .error e => .error e
      | .ok m2 => .ok { s with mem := m2 }

/-- Shared shape of the immediate-offset forms:
```
if n == 31 then CheckSPAlignment(); address = SP[] else address = X[n];
if !postindex then address = address + offset;
<memory access>;
if wback then if postindex then address = address + offset; X/SP[n] = address;
```
-/
def memIndexed (s : State) (rn : Nat) (offset : W64) (postindex wback : Bool)
    (access : State → W64 → Except Fault State) : Except Fault State :=
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let addr := if postindex then base else base + offset
    match access s addr with
    | .error e => .error e
    | .ok s' => .ok (if wback then s'.writeSP rn (base + offset) else s')

/-! ## The executor -/

/-- Execute a decoded instruction. Only specified on the output of `decode`. -/
def exec (i : Instr) (s : State) : Except Fault State :=
  match i with
  -- Data processing: immediate
  | .adr op immlo immhi rd =>
    if op then
      -- ADRP: `imm = SignExtend(immhi:immlo:Zeros(12), 64); base<11:0> = Zeros(12)`
      let base := s.pc &&& ~~~(0xFFF : W64)
      .ok (s.writeZR rd (base + sext64 33 ((immhi * 4 + immlo) * 2 ^ 12))).next
    else
      .ok (s.writeZR rd (s.pc + sext64 21 (immhi * 4 + immlo))).next
  | .addSubImm sf op S sh imm12 rn rd =>
    .ok (if sf then execAddSubImm 64 s op S sh imm12 rn rd
         else execAddSubImm 32 s op S sh imm12 rn rd).next
  | .logicalImm sf opc N immr imms rn rd =>
    .ok (if sf then execLogicalImm 64 s opc N immr imms rn rd
         else execLogicalImm 32 s opc N immr imms rn rd).next
  | .moveWide sf opc hw imm16 rd =>
    .ok (if sf then execMoveWide 64 s opc hw imm16 rd else execMoveWide 32 s opc hw imm16 rd).next
  | .bitfield sf opc N immr imms rn rd =>
    .ok (if sf then execBitfield 64 s opc N immr imms rn rd
         else execBitfield 32 s opc N immr imms rn rd).next
  | .extr sf _ rm imms rn rd =>
    .ok (if sf then execExtr 64 s rm imms rn rd else execExtr 32 s rm imms rn rd).next
  -- Branches
  | .b op imm26 =>
    let s := if op then s.writeZR 30 (s.pc + 4) else s
    .ok { s with pc := s.pc + sext64 28 (imm26 * 4) }
  | .bcond imm19 cond =>
    if conditionHolds cond s.flags then .ok { s with pc := s.pc + sext64 21 (imm19 * 4) }
    else .ok s.next
  | .cb sf op imm19 rt =>
    let isZero : Bool := if sf then decide (s.getX 64 rt = 0) else decide (s.getX 32 rt = 0)
    if isZero != op then .ok { s with pc := s.pc + sext64 21 (imm19 * 4) }
    else .ok s.next
  | .tb b5 op b40 imm14 rt =>
    let bitPos := b5.toNat * 32 + b40
    if (s.readZR rt).getLsbD bitPos == op then .ok { s with pc := s.pc + sext64 16 (imm14 * 4) }
    else .ok s.next
  | .br rn => branchReg s (s.readZR rn)
  | .blr rn =>
    let target := s.readZR rn
    branchReg (s.writeZR 30 (s.pc + 4)) target
  | .ret rn => branchReg s (s.readZR rn)
  | .hint _ _ => .ok s.next
  | .barrier _ _ => .ok s.next
  -- Loads and stores
  | .ldrLit opc imm19 rt =>
    let addr := s.pc + sext64 21 (imm19 * 4)
    -- opc 00: 4 bytes zero-extended, 01: 8 bytes, 10: LDRSW (4 bytes sign-extended)
    let r := if opc = 0 then memSingle s 2 1 rt addr
             else if opc = 1 then memSingle s 3 1 rt addr
             else memSingle s 2 2 rt addr
    match r with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .ldstUImm size opc imm12 rn rt =>
    match memIndexed s rn (BitVec.ofNat 64 (imm12 * 2 ^ size)) false false
        (fun s a => memSingle s size opc rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .ldstImm9 size opc mode imm9 rn rt =>
    let postindex := match mode with | .post => true | _ => false
    let wback := match mode with | .unscaled => false | _ => true
    match memIndexed s rn (sext64 9 imm9) postindex wback
        (fun s a => memSingle s size opc rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .ldstReg size opc rm option S rn rt =>
    let offset := extendReg 64 (s.readZR rm) option (if S then size else 0)
    match memIndexed s rn offset false false (fun s a => memSingle s size opc rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .ldstPair opc mode L imm7 rt2 rn rt =>
    let postindex := match mode with | .post => true | _ => false
    let wback := match mode with | .offset => false | _ => true
    -- `scale = 2 + UInt(opc<1>); offset = LSL(SignExtend(imm7, 64), scale)`
    let offset := (BitVec.ofNat 7 imm7).signExtend 64 <<< (2 + opc / 2)
    match memIndexed s rn offset postindex wback (fun s a => memPair s opc L rt rt2 a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  -- Data processing: register
  | .logicalShifted sf opc shift N rm imm6 rn rd =>
    .ok (if sf then execLogicalShifted 64 s opc shift N rm imm6 rn rd
         else execLogicalShifted 32 s opc shift N rm imm6 rn rd).next
  | .addSubShifted sf op S shift rm imm6 rn rd =>
    .ok (if sf then execAddSubShifted 64 s op S shift rm imm6 rn rd
         else execAddSubShifted 32 s op S shift rm imm6 rn rd).next
  | .addSubExt sf op S rm option imm3 rn rd =>
    .ok (if sf then execAddSubExt 64 s op S rm option imm3 rn rd
         else execAddSubExt 32 s op S rm option imm3 rn rd).next
  | .addSubCarry sf op S rm rn rd =>
    .ok (if sf then execAddSubCarry 64 s op S rm rn rd
         else execAddSubCarry 32 s op S rm rn rd).next
  | .condCmpReg sf op rm cond rn nzcv =>
    .ok (if sf then execCondCmp s op (s.getX 64 rn) (s.getX 64 rm) cond nzcv
         else execCondCmp s op (s.getX 32 rn) (s.getX 32 rm) cond nzcv).next
  | .condCmpImm sf op imm5 cond rn nzcv =>
    .ok (if sf then execCondCmp s op (s.getX 64 rn) (BitVec.ofNat 64 imm5) cond nzcv
         else execCondCmp s op (s.getX 32 rn) (BitVec.ofNat 32 imm5) cond nzcv).next
  | .condSel sf op rm cond o2 rn rd =>
    .ok (if sf then execCondSel 64 s op rm cond o2 rn rd
         else execCondSel 32 s op rm cond o2 rn rd).next
  | .madd sf o0 rm ra rn rd =>
    .ok (if sf then execMadd 64 s o0 rm ra rn rd else execMadd 32 s o0 rm ra rn rd).next
  | .maddl U o0 rm ra rn rd => .ok (execMaddl s U o0 rm ra rn rd).next
  | .mulh U rm rn rd => .ok (execMulh s U rm rn rd).next
  | .div sf o1 rm rn rd =>
    .ok (if sf then execDiv 64 s o1 rm rn rd else execDiv 32 s o1 rm rn rd).next
  | .shiftV sf t rm rn rd =>
    .ok (if sf then execShiftV 64 s t rm rn rd else execShiftV 32 s t rm rn rd).next
  | .rbit sf rn rd => .ok (if sf then execRbit 64 s rn rd else execRbit 32 s rn rd).next
  | .rev sf opc rn rd =>
    .ok (if sf then execRev 64 s opc rn rd else execRev 32 s opc rn rd).next
  | .clz sf rn rd => .ok (if sf then execClz 64 s rn rd else execClz 32 s rn rd).next
  | .cls sf rn rd => .ok (if sf then execCls 64 s rn rd else execCls 32 s rn rd).next

/-- Decode and execute the word `w` fetched at `s.pc`. -/
def step (w : Nat) (s : State) : Except Fault State :=
  match decode w with
  | some i => exec i s
  | none => .error (.undecodable s.pc.toNat w)

/-- Rewrite `step` once the decoding of a literal word is known (e.g. by `rfl`/`decide`). -/
theorem step_of_decode {w : Nat} {i : Instr} (h : decode w = some i) (s : State) :
    step w s = exec i s := by
  simp [step, h]

end Janus.Arm64
