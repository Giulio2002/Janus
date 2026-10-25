import Janus.Arm64.State
import Janus.Arm64.Instr
import Janus.Arm64.Bits
import Janus.Arm64.Decode
import Janus.Arm64.Vector
import Janus.Arm64.ExecFloat
import Janus.Arm64.ExecCrypto

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
  branch to a target with a non-zero top byte faults (`noCode`) at the branch. Whether
  hardware strips the tag from a branch target depends on TCR_EL1.TBID0 (set by Linux when
  pointer authentication is enabled), so the model refuses both readings. Both are
  conservative: the model faults where hardware might proceed.
* The model is single-threaded with no caches, so DMB/DSB/ISB and the accepted hints
  (NOP, YIELD, SEV, SEVL, DGH, CSDB, BTI) only advance `pc`. So do PRFM/PRFUM (prefetch: never
  faults, no architectural effect) and CLREX (the exclusive monitor is not modelled, because
  no store-exclusive is decoded).
* **Ordering is not modelled.** With one thread and no other observer, a load-acquire
  (LDAR, LDAPR, LDAXR) is an ordinary load and a store-release (STLR) an ordinary store, and the
  A/L (acquire/release) bits of the LSE atomics change nothing. LDXR/LDAXR are plain loads: the
  monitor they would arm is only observable by a store-exclusive, which faults (undecodable).
* **LSE atomics** (LD<op>, SWP, CAS, CASP) are single-instruction read-modify-writes and are
  modelled exactly: read the old value, write the new one, return the old one. Their memory
  access is a write access even when CAS does not store (permission faults are taken
  regardless of the comparison), so read-only memory faults.
* **Alignment.** Ordered, exclusive and atomic accesses must be naturally aligned (CASP: to
  the pair size), otherwise `unaligned`. Hardware without FEAT_LSE2 always faults there; with
  FEAT_LSE2 some misaligned accesses inside 16 bytes succeed. Faulting is the conservative
  choice for both.
* **Feature assumptions.** The model is of a CPU implementing FEAT_LSE (LD<op>, SWP, CAS,
  CASP) and FEAT_LRCPC (LDAPR). On an Armv8.0 CPU these are UNDEFINED. Go only executes LSE
  instructions after testing `internal/cpu.ARM64.HasATOMICS` (or, for `GOARM64=v8.1`, refuses
  to start without it), so a proof through such code assumes that flag (see
  `docs/SOUNDNESS.md`).
* **DCZID_EL0 / DC ZVA.** `MRS Xt, DCZID_EL0` returns `State.dczid`, an implementation-defined
  constant of the state (never a fixed value). DC ZVA zeroes the aligned block of
  `4 << BS` bytes containing `X[t]` (checked as a store of that many bytes), and faults
  (`trapped`) when `DZP = 1`.
* **TPIDR_EL0.** `MRS Xt, TPIDR_EL0` returns `State.tpidr`, a field of the state that no
  supported instruction writes (`MSR TPIDR_EL0` is not decoded).
* **Advanced SIMD and SIMD&FP loads/stores** (`State.vregs`, see `Janus.Arm64.Vector`): only
  integer and move instructions (Advanced SIMD floating point is not decoded). `V[d, n] = x` zero-extends to 128 bits (on an SVE CPU the hardware also zeroes the
  upper bits of `Z[d]`, which the model does not have). SIMD&FP loads and stores need no
  alignment (Linux runs EL0 with SCTLR_EL1.A = 0) except the SP check. A multi-register
  LD1/ST1, LDP/STP or single-structure access is checked per register or element as in the
  pseudocode; an access that faults in the middle faults as a whole (hardware may have written
  part of it, which is irrelevant since the run stops). AES (`AESE`, `AESD`, `AESMC`,
  `AESIMC`) assumes FEAT_AES, which Go tests before using it (`useAeshash`).
* **Scalar floating point** (`Janus.Arm64.ExecFloat`, `Janus.Arm64.Float`, `Janus.Float`): the
  ASL of FADD ... FRINT*, FCMP/FCCMP, FCSEL, FCVT and the integer conversions on single and
  double precision, reading `State.fpcr` (RMode, FZ, DN, FIZ/AH/NEP of FEAT_AFP) and ORing the
  raised exceptions into `State.fpsr`; an exception whose trap is enabled faults
  (`fpTrapped`). Half precision and Advanced SIMD floating point are rejected.
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

/-- An indirect branch: fault unless the target is untagged and 4-byte aligned. -/
def branchReg (s : State) (target : W64) : Except Fault State :=
  if target.toNat ≥ 2 ^ 56 then .error (.noCode target.toNat)
  else if target.toNat % 4 = 0 then .ok { s with pc := target }
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

/-! ## Ordered, exclusive and atomic accesses

The base address is `X[n]` or `SP` (after `CheckSPAlignment()`, `baseAddr`) and must be a
multiple of the access size, otherwise the access faults (`unaligned`). -/

/-- The LSE read-modify-write operations on the old memory value `old` and the register
operand `v` (ARM ARM `MemAtomicOp`). -/
def atomicOp {N : Nat} (op : AtomicOp) (old v : BitVec N) : BitVec N :=
  match op with
  | .add => old + v
  | .clr => old &&& ~~~v
  | .eor => old ^^^ v
  | .set => old ||| v
  | .smax => if old.toInt < v.toInt then v else old
  | .smin => if v.toInt < old.toInt then v else old
  | .umax => if old.toNat < v.toNat then v else old
  | .umin => if v.toNat < old.toNat then v else old
  | .swp => v

/-- LDAR/LDAPR (`L`) or STLR of `2^size` bytes: an ordinary, naturally aligned access. -/
def execOrdered (s : State) (size : Nat) (L : Bool) (rn rt : Nat) : Except Fault State :=
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let n := 2 ^ size
    let a := base.toNat
    if a % n ≠ 0 then .error (.unaligned a n) else
    if L then
      match load s.mem a n with
      | .error e => .error e
      | .ok v => .ok (s.writeZR rt (BitVec.ofNat 64 v)).next
    else
      match store s.mem a n (s.readZR rt).toNat with
      | .error e => .error e
      | .ok m => .ok { s with mem := m }.next

/-- LD<op>/SWP of `2^size` bytes:
```
data = X[s, datasize]; old = Mem[address]; Mem[address] = op(old, data);
if t != 31 then X[t] = ZeroExtend(old)
```
-/
def execAtomic (s : State) (size : Nat) (op : AtomicOp) (rs rn rt : Nat) : Except Fault State :=
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let n := 2 ^ size
    let a := base.toNat
    if a % n ≠ 0 then .error (.unaligned a n) else
    match load s.mem a n with
    | .error e => .error e
    | .ok old =>
      let new := atomicOp op (BitVec.ofNat (8 * n) old) (s.getX (8 * n) rs)
      match store s.mem a n new.toNat with
      | .error e => .error e
      | .ok m => .ok ({ s with mem := m }.writeZR rt (BitVec.ofNat 64 old)).next

/-- CAS of `2^size` bytes: `X[s]` is the expected value, `X[t]` the new one; memory is written
only on equality, but the access needs write permission either way. `X[s]` receives the old
value (zero-extended). -/
def execCas (s : State) (size : Nat) (rs rn rt : Nat) : Except Fault State :=
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let n := 2 ^ size
    let a := base.toNat
    if a % n ≠ 0 then .error (.unaligned a n) else
    match load s.mem a n with
    | .error e => .error e
    | .ok old =>
      if old = (s.getX (8 * n) rs).toNat then
        match store s.mem a n (s.readZR rt).toNat with
        | .error e => .error e
        | .ok m => .ok ({ s with mem := m }.writeZR rs (BitVec.ofNat 64 old)).next
      else if s.mem.accessible a n true then .ok (s.writeZR rs (BitVec.ofNat 64 old)).next
      else .error (.readOnly a n)

/-- CASP with `eb`-byte halves (`eb = 4` or `8`), little-endian: the expected value is
`X[s+1]:X[s]`, the new one `X[t+1]:X[t]`; afterwards `X[s] = old<8eb-1:0>`,
`X[s+1] = old<16eb-1:8eb>`. -/
def execCasp (s : State) (eb : Nat) (rs rn rt : Nat) : Except Fault State :=
  let pair (r : Nat) : Nat := (s.getX (8 * eb) r).toNat + 2 ^ (8 * eb) * (s.getX (8 * eb) (r + 1)).toNat
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let a := base.toNat
    if a % (2 * eb) ≠ 0 then .error (.unaligned a (2 * eb)) else
    match load s.mem a (2 * eb) with
    | .error e => .error e
    | .ok old =>
      let res (s' : State) : State :=
        ((s'.writeZR rs (BitVec.ofNat 64 (old % 2 ^ (8 * eb)))).writeZR (rs + 1)
          (BitVec.ofNat 64 (old / 2 ^ (8 * eb)))).next
      if old = pair rs then
        match store s.mem a (2 * eb) (pair rt) with
        | .error e => .error e
        | .ok m => .ok (res { s with mem := m })
      else if s.mem.accessible a (2 * eb) true then .ok (res s)
      else .error (.readOnly a (2 * eb))

/-- DC ZVA: zero the `4 << BS`-byte block containing `X[t]`, unless `DZP` prohibits it. -/
def execDcZva (s : State) (rt : Nat) : Except Fault State :=
  if s.dczid.getLsbD 4 then .error (.trapped s.pc.toNat) else
  let bs := 4 * 2 ^ (s.dczid.toNat % 16)
  let a := (s.readZR rt).toNat / bs * bs
  match store s.mem a bs 0 with
  | .error e => .error e
  | .ok m => .ok { s with mem := m }.next

/-! ## Advanced SIMD and SIMD&FP loads and stores

The operations are in `Janus.Arm64.Vector`. Here: operand reads (`V[n, datasize]`), result
writes (`V[d, datasize] = result`, which zero-extends) and the memory accesses. -/

/-- `datasize` of a vector operation: 128 bits for `Q = 1`, else 64. -/
def qsize (Q : Bool) : Nat := if Q then 128 else 64

/-- Three same: `V[d] = op(V[n], V[m])`; only BSL/BIT/BIF (`U = 1`, logical) also read `V[d]`
(passed as 0 otherwise, where `threeSameOp` ignores it). -/
def execVThreeSame (s : State) (Q U : Bool) (size rm opcode rn rd : Nat) : State :=
  let ds := qsize Q
  let d := if U && opcode = 0b00011 then s.getV rd ds else 0
  s.setV rd ds (threeSameOp U size opcode ds (s.getV rn ds) (s.getV rm ds) d)

/-- `Vpart[d, 1] = r` for a 64-bit `r`: the upper half is written, the lower half kept. -/
def setVHigh (s : State) (d r : Nat) : State := s.setV d 128 (s.getV d 64 + 2 ^ 64 * (r % 2 ^ 64))

/-- DUP/INS/SMOV/UMOV (`Instr.vCopy`). `size = LowestSetBit(imm5)`,
`index = UInt(imm5<4:size+1>)`. -/
def execVCopy (s : State) (Q op : Bool) (imm5 imm4 rn rd : Nat) : State :=
  let sz := lowestSetBit5 imm5
  let e := 8 * 2 ^ sz
  let idx := imm5 / 2 ^ (sz + 1)
  let ds := qsize Q
  let src := elem (s.getV rn 128) e idx
  if op then
    -- INS (element): Elem[V[d], index, esize] = Elem[V[n], imm4<3:size>, esize]
    let el := elem (s.getV rn 128) e (imm4 / 2 ^ sz)
    s.setV rd 128 (ofElems e (128 / e) fun i => if i = idx then el else elem (s.getV rd 128) e i)
  else if imm4 = 0 then s.setV rd ds (ofElems e (ds / e) fun _ => src)               -- DUP (element)
  else if imm4 = 1 then s.setV rd ds (ofElems e (ds / e) fun _ => (s.readZR rn).toNat)  -- DUP (general)
  else if imm4 = 3 then                                                              -- INS (general)
    s.setV rd 128 (ofElems e (128 / e) fun i => if i = idx then (s.readZR rn).toNat else elem (s.getV rd 128) e i)
  else if imm4 = 5 then s.writeZR rd (BitVec.ofNat 64 (truncInt (qsize Q / 2) (sint e src)))  -- SMOV
  else s.writeZR rd (BitVec.ofNat 64 src)                                                -- UMOV

def execVAcross (s : State) (Q U : Bool) (size opcode rn rd : Nat) : State :=
  let r := acrossOp U size opcode (qsize Q) (s.getV rn (qsize Q))
  s.setV rd r.2 r.1

def execVTwoMisc (s : State) (Q U : Bool) (size opcode rn rd : Nat) : State :=
  if opcode = 0b10010 then
    -- XTN{2}: Vpart[d, part] = result
    let r := xtnOp size (s.getV rn 128)
    if Q then setVHigh s rd r else s.setV rd 64 r
  else s.setV rd (qsize Q) (twoMiscOp U size opcode (qsize Q) (s.getV rn (qsize Q)))

def execVShiftImm (s : State) (Q U : Bool) (immh immb opcode rn rd : Nat) : State :=
  let esize := 8 * 2 ^ highestSetBit4 immh
  let immhb := immh * 8 + immb
  if opcode = 0b10000 then
    -- SHRN{2}: shift = 2 * esize - UInt(immh:immb); Vpart[d, part] = result
    let r := shrnOp esize (2 * esize - immhb) (s.getV rn 128)
    if Q then setVHigh s rd r else s.setV rd 64 r
  else if opcode = 0b10100 then
    -- SSHLL{2}/USHLL{2}: operand = Vpart[n, part]; shift = UInt(immh:immb) - esize
    let x := if Q then s.getV rn 128 / 2 ^ 64 else s.getV rn 64
    s.setV rd 128 (shllOp U esize (immhb - esize) x)
  else
    let ds := qsize Q
    s.setV rd ds (shiftImmOp U esize opcode ds immhb (s.getV rn ds) (s.getV rd ds))

/-- FMOV between general and SIMD&FP registers. `opcode = 110`: `X[d] = V[n]` (`rmode = 01`:
`V[n]<127:64>`); `111`: `V[d] = X[n]` (`rmode = 01`: only `V[d]<127:64>` is written). -/
def execFmovGen (s : State) (sf : Bool) (rmode opcode rn rd : Nat) : State :=
  let w := if sf then 64 else 32
  if opcode = 6 then
    s.writeZR rd (BitVec.ofNat 64 (if rmode = 1 then s.getV rn 128 / 2 ^ 64 else s.getV rn w))
  else if rmode = 1 then setVHigh s rd (s.readZR rn).toNat
  else s.setV rd w (s.readZR rn).toNat

/-- A SIMD&FP single-register access of `nbytes` bytes at `addr` (`L` = load):
`V[t] = ZeroExtend(Mem[address, nbytes])`, or `Mem[address, nbytes] = V[t, 8 * nbytes]`. -/
def memV (s : State) (L : Bool) (nbytes rt : Nat) (addr : W64) : Except Fault State :=
  if L then
    match load s.mem addr.toNat nbytes with
    | .error e => .error e
    | .ok v => .ok (s.setV rt (8 * nbytes) v)
  else
    match store s.mem addr.toNat nbytes (s.getV rt (8 * nbytes)) with
    | .error e => .error e
    | .ok m => .ok { s with mem := m }

/-- LDP/STP of SIMD&FP registers at `addr` and `addr + nbytes`. -/
def memVPair (s : State) (L : Bool) (nbytes rt rt2 : Nat) (addr : W64) : Except Fault State :=
  let addr2 := addr + BitVec.ofNat 64 nbytes
  if L then
    match load s.mem addr.toNat nbytes with
    | .error e => .error e
    | .ok v1 =>
      match load s.mem addr2.toNat nbytes with
      | .error e => .error e
      | .ok v2 => .ok ((s.setV rt (8 * nbytes) v1).setV rt2 (8 * nbytes) v2)
  else
    match store s.mem addr.toNat nbytes (s.getV rt (8 * nbytes)) with
    | .error e => .error e
    | .ok m1 =>
      match store m1 addr2.toNat nbytes (s.getV rt2 (8 * nbytes)) with
      | .error e => .error e
      | .ok m2 => .ok { s with mem := m2 }

/-- LD1 (multiple structures) of `k` registers: register `V[(t + r) MOD 32]` is loaded from the
`rbytes` bytes at `addr + r * rbytes`. -/
def ldMulti (s : State) (rt rbytes : Nat) (addr : W64) : Nat → Except Fault State
  | 0 => .ok s
  | k + 1 =>
    match ldMulti s rt rbytes addr k with
    | .error e => .error e
    | .ok s' =>
      match load s.mem (addr + BitVec.ofNat 64 (rbytes * k)).toNat rbytes with
      | .error e => .error e
      | .ok v => .ok (s'.setV ((rt + k) % 32) (8 * rbytes) v)

/-- ST1 (multiple structures) of `k` registers, in register order. -/
def stMulti (s : State) (rt rbytes : Nat) (addr : W64) : Nat → Except Fault State
  | 0 => .ok s
  | k + 1 =>
    match stMulti s rt rbytes addr k with
    | .error e => .error e
    | .ok s' =>
      match store s'.mem (addr + BitVec.ofNat 64 (rbytes * k)).toNat rbytes
          (s.getV ((rt + k) % 32) (8 * rbytes)) with
      | .error e => .error e
      | .ok m => .ok { s' with mem := m }

/-- LD1–LD4 (single structure) / LD1R–LD4R of `k` registers: register `V[(t + j) MOD 32]` gets
the `eb`-byte element at `addr + j * eb`, replicated (`V[t, datasize] = Replicate(element)`) or
into lane `idx` (the rest of the 128-bit register is kept). -/
def ldSingle (s : State) (rt eb idx : Nat) (rep : Bool) (ds : Nat) (addr : W64) :
    Nat → Except Fault State
  | 0 => .ok s
  | k + 1 =>
    match ldSingle s rt eb idx rep ds addr k with
    | .error e => .error e
    | .ok s' =>
      match load s.mem (addr + BitVec.ofNat 64 (eb * k)).toNat eb with
      | .error e => .error e
      | .ok v =>
        let r := (rt + k) % 32
        .ok (if rep then s'.setV r ds (ofElems (8 * eb) (ds / (8 * eb)) fun _ => v)
             else s'.setV r 128 (ofElems (8 * eb) (16 / eb) fun i =>
               if i = idx then v else elem (s'.getV r 128) (8 * eb) i))

/-- ST1–ST4 (single structure): lane `idx` of `V[(t + j) MOD 32]` to `addr + j * eb`. -/
def stSingle (s : State) (rt eb idx : Nat) (addr : W64) : Nat → Except Fault State
  | 0 => .ok s
  | k + 1 =>
    match stSingle s rt eb idx addr k with
    | .error e => .error e
    | .ok s' =>
      match store s'.mem (addr + BitVec.ofNat 64 (eb * k)).toNat eb
          (elem (s.getV ((rt + k) % 32) 128) (8 * eb) idx) with
      | .error e => .error e
      | .ok m => .ok { s' with mem := m }

/-- LD1–LD4/ST1–ST4 (single structure) and LD1R–LD4R; `selem = opcode<0>:R + 1` registers. -/
def execVLdStSingle (s : State) (Q L R : Bool) (opcode : Nat) (S : Bool) (size : Nat) (post : Bool)
    (rm rn rt : Nat) :
    Except Fault State :=
  let selem := opcode % 2 * 2 + R.toNat + 1
  let (eb, idx, rep) := (vSingleLayout Q opcode S size L).getD (1, 0, false)
  let offset : W64 := if rm = 31 then BitVec.ofNat 64 (selem * eb) else s.regs rm
  memIndexed s rn offset true post fun s a =>
    if L then ldSingle s rt eb idx rep (qsize Q) a selem else stSingle s rt eb idx a selem

/-- The number of registers of LD1/ST1 (multiple structures) by `opcode`. -/
def multiRegs (opcode : Nat) : Nat :=
  if opcode = 0b0111 then 1 else if opcode = 0b1010 then 2 else if opcode = 0b0110 then 3 else 4

/-- LD1/ST1 (multiple structures). The post-index offset is `X[m]`, or the number of bytes
transferred for `m = 31`. -/
def execVLdStMulti (s : State) (Q L : Bool) (opcode : Nat) (post : Bool) (rm rn rt : Nat) :
    Except Fault State :=
  let rbytes := qsize Q / 8
  let k := multiRegs opcode
  let offset : W64 := if rm = 31 then BitVec.ofNat 64 (k * rbytes) else s.regs rm
  memIndexed s rn offset true post fun s a => if L then ldMulti s rt rbytes a k else stMulti s rt rbytes a k

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
  | .clrex _ => .ok s.next
  | .mrsDczid rt => .ok (s.writeZR rt (s.dczid.setWidth 64)).next
  | .mrsTpidr rt => .ok (s.writeZR rt s.tpidr).next
  | .dcZva rt => execDcZva s rt
  | .prefetch _ => .ok s.next
  | .ldstOrdered size L _ rn rt => execOrdered s size L rn rt
  | .ldExcl size _ rn rt => execOrdered s size true rn rt
  | .atomic size _ _ rs op rn rt => execAtomic s size op rs rn rt
  | .cas size _ _ rs rn rt => execCas s size rs rn rt
  | .casp sz _ _ rs rn rt => execCasp s (if sz then 8 else 4) rs rn rt
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
  -- SIMD&FP loads and stores
  | .vldstMulti Q L opcode _ post rm rn rt =>
    match execVLdStMulti s Q L opcode post rm rn rt with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldstSingle Q L R opcode S size post rm rn rt =>
    match execVLdStSingle s Q L R opcode S size post rm rn rt with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldrLit opc imm19 rt =>
    match memV s true (4 * 2 ^ opc) rt (s.pc + sext64 21 (imm19 * 4)) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldstUImm size opc imm12 rn rt =>
    let scale := opc / 2 * 4 + size
    match memIndexed s rn (BitVec.ofNat 64 (imm12 * 2 ^ scale)) false false
        (fun s a => memV s (opc % 2 = 1) (2 ^ scale) rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldstImm9 size opc mode imm9 rn rt =>
    let scale := opc / 2 * 4 + size
    let postindex := match mode with | .post => true | _ => false
    let wback := match mode with | .unscaled => false | _ => true
    match memIndexed s rn (sext64 9 imm9) postindex wback
        (fun s a => memV s (opc % 2 = 1) (2 ^ scale) rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldstReg size opc rm option S rn rt =>
    let scale := opc / 2 * 4 + size
    let offset := extendReg 64 (s.readZR rm) option (if S then scale else 0)
    match memIndexed s rn offset false false (fun s a => memV s (opc % 2 = 1) (2 ^ scale) rt a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .vldstPair opc mode L imm7 rt2 rn rt =>
    let postindex := match mode with | .post => true | _ => false
    let wback := match mode with | .offset => false | _ => true
    -- `scale = 2 + UInt(opc); offset = LSL(SignExtend(imm7, 64), scale)`
    let offset := (BitVec.ofNat 7 imm7).signExtend 64 <<< (2 + opc)
    match memIndexed s rn offset postindex wback (fun s a => memVPair s L (4 * 2 ^ opc) rt rt2 a) with
    | .error e => .error e
    | .ok s' => .ok s'.next
  -- Advanced SIMD data processing
  | .vThreeSame Q U size rm opcode rn rd => .ok (execVThreeSame s Q U size rm opcode rn rd).next
  | .vScalarThreeSame U size rm opcode rn rd =>
    .ok (s.setV rd 64 (threeSameOp U size opcode 64 (s.getV rn 64) (s.getV rm 64) (s.getV rd 64))).next
  | .vCopy Q op imm5 imm4 rn rd => .ok (execVCopy s Q op imm5 imm4 rn rd).next
  | .vAcross Q U size opcode rn rd => .ok (execVAcross s Q U size opcode rn rd).next
  | .vTwoMisc Q U size opcode rn rd => .ok (execVTwoMisc s Q U size opcode rn rd).next
  | .vShiftImm Q U immh immb opcode rn rd => .ok (execVShiftImm s Q U immh immb opcode rn rd).next
  | .vModImm Q op cmode imm8 rd =>
    .ok (s.setV rd (qsize Q) (modImmOp op cmode imm8 (qsize Q) (s.getV rd (qsize Q)))).next
  | .vExt Q rm imm4 rn rd =>
    .ok (s.setV rd (qsize Q) (extOp (qsize Q) imm4 (s.getV rn (qsize Q)) (s.getV rm (qsize Q)))).next
  | .vTbl Q rm len op rn rd =>
    .ok (s.setV rd (qsize Q) (tblOp op (len + 1) (qsize Q) (tableOf s.vregs rn (len + 1))
      (s.getV rm (qsize Q)) (s.getV rd (qsize Q)))).next
  | .vAes opcode rn rd => .ok (s.setV rd 128 (aesOp opcode (s.getV rd 128) (s.getV rn 128))).next
  | .crypto c => .ok (execCrypto s c).next  -- `Janus.Arm64.ExecCrypto`
  | .fmovGen sf _ rmode opcode rn rd => .ok (execFmovGen s sf rmode opcode rn rd).next
  -- Scalar floating point (`Janus.Arm64.ExecFloat`)
  | .fpDP1 ftype opcode rn rd =>
    match execFpDP1 s ftype opcode rn rd with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .fpDP2 ftype rm opcode rn rd =>
    match execFpDP2 s ftype rm opcode rn rd with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .fpDP3 ftype o1 rm o0 ra rn rd =>
    match execFpDP3 s ftype o1 rm o0 ra rn rd with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .fpCmp ftype rm opc rn =>
    match execFpCmp s ftype rm opc rn with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .fpCcmp ftype rm cond signal rn nzcv =>
    match execFpCcmp s ftype rm (conditionHolds cond s.flags) signal rn nzcv with
    | .error e => .error e
    | .ok s' => .ok s'.next
  | .fpCsel ftype rm cond rn rd => .ok (execFpCsel s ftype rm (conditionHolds cond s.flags) rn rd).next
  | .fpImm ftype imm8 rd => .ok (execFpImm s ftype imm8 rd).next
  | .fpCvtInt sf ftype rmode opcode rn rd =>
    match execFpCvtInt s sf ftype rmode opcode rn rd with
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
