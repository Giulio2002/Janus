import Janus.Amd64.State
import Janus.Amd64.Instr
import Janus.Amd64.Decode
import Janus.Arm64.Bits
import Janus.Amd64.TacticAttr
import Janus.Amd64.Float
import Janus.Amd64.ExecSSE
import Janus.Amd64.ExecCrypto

/-!
# x86-64 execution semantics for the supported subset

`step bytes s` decodes the instruction at the start of `bytes` (the code at `s.rip`) and
executes it, returning the successor state (with `rip` advanced past the instruction or
redirected) or a `Fault`.

Each case follows the Intel SDM Vol. 2 `Operation` and `Flags Affected` sections:

* Register writes: a 32-bit result is zero-extended into the 64-bit register; 8- and 16-bit
  results leave the other bits unchanged (SDM Vol. 1 §3.4.1.1). `AH`…`BH` are bits 15:8.
* Flags that the SDM lists as *undefined* become `none`; reading one faults
  (`undefinedFlag`). Flags listed as *unaffected* keep their value (and definedness).
  Where Intel and AMD document different behaviour, the flag is undefined (e.g. `ZF` after
  `BT`: unaffected on Intel).
* Architecturally undefined *results* fault (`undefinedResult`): 16-bit `SHLD`/`SHRD` with a
  count above 16, and `BSF`/`BSR` of zero for 16/32-bit operands. For 64-bit `BSF`/`BSR` of
  zero the destination is unchanged (documented by AMD; the Intel behaviour Linux relies on,
  and checked by the oracle on Intel hardware).
* Memory goes through the checked `load`/`store`/`loadRW` of `State`. A read-modify-write
  destination must be writable before it is read. Effective addresses wrap modulo `2^64`.
  RIP-relative addresses are relative to the next instruction.
* `#DE` (division by zero, quotient overflow) faults with `divideError`; a 16-byte SSE memory
  operand that must be aligned (`MOVAPS`, `MOVDQA`, legacy-SSE `XORPS`/`PXOR`) faults with
  `misaligned` when it is not.
* Branch targets must be canonical user addresses `< 2^47`; otherwise the branch faults
  (`badTarget`). On hardware a non-canonical target is `#GP` at the branch and an upper-half
  target faults at the fetch, so this is conservative.
* Vector registers (`State.xmm` = bits 127:0, `State.ymmHi` = bits 255:128): a legacy-SSE
  instruction writes only `xmm` (bits 255:128 preserved, SDM Vol. 1 §14.1.3); a VEX.128
  instruction writes `xmm` and zeroes `ymmHi` of its destination register; a VEX.256 one writes
  both (`State.setV`). VEX memory operands need no alignment except for `VMOVDQA`/`VMOVNTDQ`
  (`l/8` bytes, else `misaligned`). Vector values are naturals `< 2^l`, little-endian, so byte
  `i` is `v / 256^i % 256`.
* An `FS`-relative memory operand is at `fsBase + ea` (mod `2^64`).
-/

namespace Janus.Amd64

open Janus.Arm64 (clzNat revBytesNat)

/-! ## Bit helpers (structural recursion only) -/

/-- Even parity of the low `k` bits of `x` (`true` = even number of ones). -/
def parityBits : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, x => if x % 2 = 1 then !parityBits k (x / 2) else parityBits k (x / 2)

/-- `PF`: set iff the least-significant byte has an even number of ones. -/
def parity (x : Nat) : Bool := parityBits 8 x

/-- Number of trailing zero bits of the `n`-bit value `x` (`n` if `x = 0`). -/
def ctzNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => if x % 2 = 1 then 0 else 1 + ctzNat n (x / 2)

/-- Number of one bits among the low `n` bits of `x`. -/
def popNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + popNat n (x / 2)

/-! ## Register file -/

namespace State

/-- Replace the full 64-bit register `r`. -/
def setReg (s : State) (r : Nat) (v : W64) : State :=
  { s with regs := fun i => if i = r then v else s.regs i }

def setXmm (s : State) (n : Nat) (v : W128) : State :=
  { s with xmm := fun i => if i = n then v else s.xmm i }

def setYmmHi (s : State) (n : Nat) (v : W128) : State :=
  { s with ymmHi := fun i => if i = n then v else s.ymmHi i }

/-- Bits `l-1:0` of `YMMn` (`l ∈ {128, 256}`) as a natural number. -/
def getV (s : State) (l n : Nat) : Nat := if l = 256 then s.ymm n else (s.xmm n).toNat

/-- A VEX write of the `l`-bit value `v` to `YMMn`: bits 127:0 from `v`, bits 255:128 from `v`
for `l = 256`, zeroed for `l = 128`. -/
def setV (s : State) (l n v : Nat) : State :=
  (s.setXmm n (BitVec.ofNat 128 v)).setYmmHi n (if l = 256 then BitVec.ofNat 128 (v / 2 ^ 128) else 0)

/-- The low `w` bits of register `r`. -/
def getReg (s : State) (w r : Nat) : BitVec w := (s.regs r).setWidth w

/-- Bits 15:8 of register `r` (`AH`, `CH`, `DH`, `BH`). -/
def getHigh (s : State) (r : Nat) : BitVec 8 := (s.regs r).extractLsb' 8 8

/-- Write a `w`-bit result to register `r`: 64 and 32 bits replace the whole register
(zero-extension), 8 and 16 bits merge into the low bits. -/
def putReg (s : State) (w r : Nat) (v : BitVec w) : State :=
  if w = 64 ∨ w = 32 then s.setReg r (v.setWidth 64)
  else s.setReg r ((s.regs r &&& ~~~(BitVec.allOnes w).setWidth 64) ||| v.setWidth 64)

def putHigh (s : State) (r : Nat) (v : BitVec 8) : State :=
  s.setReg r ((s.regs r &&& ~~~(0xFF00 : W64)) ||| (v.setWidth 64 <<< 8))

def setFlags (s : State) (f : Flags) : State := { s with flags := f }

def setRip (s : State) (v : W64) : State := { s with rip := v }

end State

/-! ## Operands -/

/-- The effective address of `a` within its segment; `next` is the address of the next
instruction. (In the `janus64_exec` simp set, as `ea` is.) -/
@[janus64_exec] def eaOff (s : State) (next : W64) (a : Addr) : W64 :=
  if a.rip then BitVec.ofNat 64 ((next.toNat + a.disp) % 2 ^ 64) else
  let base : W64 := match a.base with
    | some b => s.regs b
    | none => 0
  let idx : W64 := match a.index with
    | some i => s.regs i <<< a.scale
    | none => 0
  base + idx + BitVec.ofNat 64 a.disp

/-- The linear address of `a`: `eaOff`, plus the `FS` base for an `FS`-relative operand. -/
def ea (s : State) (next : W64) (a : Addr) : W64 :=
  if a.fs then s.fsBase + eaOff s next a else eaOff s next a

def readLoc (s : State) (next : W64) (w : Nat) : Loc → Except Fault (BitVec w)
  | .reg r => .ok (s.getReg w r)
  | .high r => .ok ((s.getHigh r).setWidth w)
  | .mem a =>
    match load s.mem (ea s next a).toNat (w / 8) with
    | .ok v => .ok (BitVec.ofNat w v)
    | .error e => .error e

/-- Read the destination of a read-modify-write: memory must be writable. -/
def readLocRW (s : State) (next : W64) (w : Nat) : Loc → Except Fault (BitVec w)
  | .reg r => .ok (s.getReg w r)
  | .high r => .ok ((s.getHigh r).setWidth w)
  | .mem a =>
    match loadRW s.mem (ea s next a).toNat (w / 8) with
    | .ok v => .ok (BitVec.ofNat w v)
    | .error e => .error e

def readSrc (s : State) (next : W64) (w : Nat) : Src → Except Fault (BitVec w)
  | .loc l => readLoc s next w l
  | .imm v => .ok (BitVec.ofNat w v)

def writeLoc (s : State) (next : W64) (w : Nat) (l : Loc) (v : BitVec w) : Except Fault State :=
  match l with
  | .reg r => .ok (s.putReg w r v)
  | .high r => .ok (s.putHigh r (v.setWidth 8))
  | .mem a =>
    match store s.mem (ea s next a).toNat (w / 8) v.toNat with
    | .ok m => .ok { s with mem := m }
    | .error e => .error e

/-- Read a 128-bit SSE operand (`aligned`: a memory operand must be 16-byte aligned). -/
def readX (s : State) (next : W64) (aligned : Bool) : XLoc → Except Fault W128
  | .xmm n => .ok (s.xmm n)
  | .mem a =>
    let addr := (ea s next a).toNat
    if aligned ∧ addr % 16 ≠ 0 then .error (.misaligned addr) else
    match load s.mem addr 16 with
    | .ok v => .ok (BitVec.ofNat 128 v)
    | .error e => .error e

def writeX (s : State) (next : W64) (aligned : Bool) (l : XLoc) (v : W128) : Except Fault State :=
  match l with
  | .xmm n => .ok (s.setXmm n v)
  | .mem a =>
    let addr := (ea s next a).toNat
    if aligned ∧ addr % 16 ≠ 0 then .error (.misaligned addr) else
    match store s.mem addr 16 v.toNat with
    | .ok m => .ok { s with mem := m }
    | .error e => .error e

/-- Read an `l`-bit vector operand as a natural number (`aligned`: a memory operand must be
`l/8`-byte aligned). -/
def readV (s : State) (next : W64) (l : Nat) (aligned : Bool) : XLoc → Except Fault Nat
  | .xmm n => .ok (s.getV l n)
  | .mem a =>
    let addr := (ea s next a).toNat
    if aligned ∧ addr % (l / 8) ≠ 0 then .error (.misaligned addr) else
    load s.mem addr (l / 8)

/-- Write an `l`-bit vector result `v` (`< 2^l`) with VEX semantics (`State.setV`). -/
def writeV (s : State) (next : W64) (l : Nat) (aligned : Bool) (dst : XLoc) (v : Nat) :
    Except Fault State :=
  match dst with
  | .xmm n => .ok (s.setV l n v)
  | .mem a =>
    let addr := (ea s next a).toNat
    if aligned ∧ addr % (l / 8) ≠ 0 then .error (.misaligned addr) else
    match store s.mem addr (l / 8) v with
    | .ok m => .ok { s with mem := m }
    | .error e => .error e

/-! ## Vector lanes

Byte lanes of naturals (byte `i` of `a` is `a / 256^i % 256`), by structural recursion on the
lane count so that the kernel and `simp` evaluate them. -/

/-- `PCMPEQB` on `k` byte lanes: `0xFF` where the bytes are equal, `0` elsewhere. -/
def cmpeqBytes : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => (if a % 256 = b % 256 then 255 else 0) + 256 * cmpeqBytes k (a / 256) (b / 256)

/-- `PMOVMSKB` of `k` byte lanes: bit `i` is bit 7 of byte `i`. -/
def msbBytes : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 256 / 128 + 2 * msbBytes k (a / 256)

/-- `PUNPCKLBW` of the low `k` bytes: `a₀ b₀ a₁ b₁ …`. -/
def unpackLoBytes : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => a % 256 + 256 * (b % 256) + 65536 * unpackLoBytes k (a / 256) (b / 256)

/-- `k` copies of the byte `b` (`< 256`). -/
def replBytes : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, b => b + 256 * replBytes k b

/-- `PSHUFD`: dword `i` of the result is dword `imm[2i+1:2i]` of `a`. -/
def pshufdNat (a imm : Nat) : Nat :=
  let sel (i : Nat) : Nat := a / 2 ^ (32 * (imm / 4 ^ i % 4)) % 2 ^ 32
  sel 0 + 2 ^ 32 * sel 1 + 2 ^ 64 * sel 2 + 2 ^ 96 * sel 3

/-- `PSHUFB` on one 128-bit lane: byte `i` (of `k` remaining) is `0` if bit 7 of byte `i` of
`b` is set, else byte `b[i] & 15` of `a`. -/
def pshufbGo (a : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, b => (if b % 256 ≥ 128 then 0 else a / 256 ^ (b % 16) % 256) + 256 * pshufbGo a k (b / 256)

/-- `PSHUFB` on `k` 128-bit lanes (each lane selects within itself). -/
def pshufbLanes : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b => pshufbGo (a % 2 ^ 128) 16 (b % 2 ^ 128) + 2 ^ 128 * pshufbLanes k (a / 2 ^ 128) (b / 2 ^ 128)

/-- `PSIGNB` on `k` byte lanes: byte `i` of `a` negated (mod 256), zeroed or kept as byte `i`
of `b` is negative, zero or positive. -/
def psignBytes : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, a, b =>
    (if b % 256 = 0 then 0 else if b % 256 ≥ 128 then (256 - a % 256) % 256 else a % 256) +
      256 * psignBytes k (a / 256) (b / 256)

/-- A packed vector operation on `l`-bit values `a` (destination / first source) and `b`. -/
@[janus64_exec] def vecBin (op : SseOp) (l a b : Nat) : Nat :=
  match op with
  | .xor => a ^^^ b
  | .and => a &&& b
  | .or => a ||| b
  | .pcmpeqb => cmpeqBytes (l / 8) a b
  | .punpcklbw => unpackLoBytes (l / 16) a b
  | .pshufb => pshufbLanes (l / 128) a b
  | .psignb => psignBytes (l / 8) a b

/-- The legacy-SSE form on `XMM` values (`xor` stays a `BitVec` operation). -/
@[janus64_exec] def sseBin (op : SseOp) (x v : W128) : W128 :=
  match op with
  | .xor => x ^^^ v
  | .and => BitVec.ofNat 128 (vecBin .and 128 x.toNat v.toNat)
  | .or => BitVec.ofNat 128 (vecBin .or 128 x.toNat v.toNat)
  | .pcmpeqb => BitVec.ofNat 128 (vecBin .pcmpeqb 128 x.toNat v.toNat)
  | .punpcklbw => BitVec.ofNat 128 (vecBin .punpcklbw 128 x.toNat v.toNat)
  | .pshufb => BitVec.ofNat 128 (vecBin .pshufb 128 x.toNat v.toNat)
  | .psignb => BitVec.ofNat 128 (vecBin .psignb 128 x.toNat v.toNat)

/-- `VPTEST a, b` (`l`-bit values): `ZF = (a AND b = 0)`, `CF = (b AND NOT a = 0)`, the
other four status flags cleared. -/
@[janus64_exec] def ptestFlags (l x y : Nat) : Flags :=
  { cf := some (decide (y &&& (x ^^^ (2 ^ l - 1)) = 0)), pf := some false, af := some false,
    zf := some (decide (x &&& y = 0)), sf := some false, ovf := some false }

/-! ## Flags -/

/-- `AF`: carry/borrow out of bit 3, i.e. bit 4 of `x XOR y XOR result`. -/
def auxCarry {w : Nat} (x y r : BitVec w) : Bool := ((x ^^^ y ^^^ r).toNat / 16) % 2 = 1

/-- `ADD`/`ADC`: `x + y + c` with all six flags. -/
def addFlags {w : Nat} (x y : BitVec w) (c : Bool) : BitVec w × Flags :=
  let sum : Nat := x.toNat + y.toNat + c.toNat
  let r : BitVec w := BitVec.ofNat w sum
  (r, { cf := some (decide (sum ≥ 2 ^ w)), pf := some (parity r.toNat),
        af := some (auxCarry x y r), zf := some (decide (r = 0)), sf := some r.msb,
        ovf := some (decide (r.toInt ≠ x.toInt + y.toInt + (c.toNat : Int))) })

/-- `SUB`/`SBB`/`CMP`/`NEG`: `x - y - b` with all six flags. -/
def subFlags {w : Nat} (x y : BitVec w) (b : Bool) : BitVec w × Flags :=
  let r : BitVec w := BitVec.ofNat w (x.toNat + 2 ^ w - y.toNat - b.toNat)
  (r, { cf := some (decide (x.toNat < y.toNat + b.toNat)), pf := some (parity r.toNat),
        af := some (auxCarry x y r), zf := some (decide (r = 0)), sf := some r.msb,
        ovf := some (decide (r.toInt ≠ x.toInt - y.toInt - (b.toNat : Int))) })

@[simp] theorem addFlags_false_fst {w : Nat} (x y : BitVec w) : (addFlags x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq; simp [addFlags]

theorem addFlags_fst {w : Nat} (x y : BitVec w) (c : Bool) :
    (addFlags x y c).1 = x + y + BitVec.ofNat w c.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [addFlags, Nat.add_mod]

@[simp] theorem subFlags_false_fst {w : Nat} (x y : BitVec w) : (subFlags x y false).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [subFlags, BitVec.toNat_ofNat, BitVec.toNat_sub, Bool.toNat_false, Nat.sub_zero]
  have := y.isLt
  congr 1; omega

/-- `AND`/`OR`/`XOR`/`TEST`: `CF = OF = 0`, `SF ZF PF` from the result, `AF` undefined. -/
def logicFlags {w : Nat} (r : BitVec w) : Flags :=
  { cf := some false, pf := some (parity r.toNat), af := none, zf := some (decide (r = 0)),
    sf := some r.msb, ovf := some false }

/-- `cc` (the low nibble of `Jcc`/`SETcc`/`CMOVcc`), or `none` if it reads an undefined flag.
SDM Vol. 1 appendix B: O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G. -/
def condition (cc : Nat) (f : Flags) : Option Bool :=
  let base : Option Bool :=
    match cc / 2 with
    | 0 => f.ovf
    | 1 => f.cf
    | 2 => f.zf
    | 3 => match f.cf, f.zf with
      | some c, some z => some (c || z)
      | _, _ => none
    | 4 => f.sf
    | 5 => f.pf
    | 6 => match f.sf, f.ovf with
      | some a, some b => some (a != b)
      | _, _ => none
    | _ => match f.zf, f.sf, f.ovf with
      | some z, some a, some b => some (z || (a != b))
      | _, _, _ => none
  if cc % 2 = 1 then base.map (!·) else base

/-! ## Instruction families -/

/-- A branch: the target must be a canonical user address. -/
def branchTo (s : State) (target : W64) : Except Fault State :=
  if target.toNat < 2 ^ 47 then .ok (s.setRip target) else .error (.badTarget target.toNat)

def push64 (s : State) (v : W64) : Except Fault State :=
  let sp := s.regs 4 - 8
  match store s.mem sp.toNat 8 v.toNat with
  | .ok m => .ok ({ s with mem := m }.setReg 4 sp)
  | .error e => .error e

def execAlu (s : State) (next : W64) (op : AluOp) (w : Nat) (dst : Loc) (src : Src) :
    Except Fault State :=
  match readSrc s next w src with
  | .error e => .error e
  | .ok y =>
    let rd := match op with | .cmp => readLoc s next w dst | _ => readLocRW s next w dst
    match rd with
    | .error e => .error e
    | .ok x =>
      let res : Option (BitVec w × Flags) :=
        match op with
        | .add => some (addFlags x y false)
        | .adc => s.flags.cf.map fun c => addFlags x y c
        | .sub | .cmp => some (subFlags x y false)
        | .sbb => s.flags.cf.map fun c => subFlags x y c
        | .and => some (x &&& y, logicFlags (x &&& y))
        | .or => some (x ||| y, logicFlags (x ||| y))
        | .xor => some (x ^^^ y, logicFlags (x ^^^ y))
      match res with
      | none => .error (.undefinedFlag s.rip.toNat)
      | some (r, f) =>
        match op with
        | .cmp => .ok ((s.setFlags f).setRip next)
        | _ =>
          match writeLoc s next w dst r with
          | .ok s' => .ok ((s'.setFlags f).setRip next)
          | .error e => .error e

def execUnary (s : State) (next : W64) (op : UnOp) (w : Nat) (dst : Loc) : Except Fault State :=
  match readLocRW s next w dst with
  | .error e => .error e
  | .ok x =>
    let (r, f) : BitVec w × Flags :=
      match op with
      | .inc => let p := addFlags x 1 false; (p.1, { p.2 with cf := s.flags.cf })
      | .dec => let p := subFlags x 1 false; (p.1, { p.2 with cf := s.flags.cf })
      | .not => (~~~x, s.flags)
      | .neg => let p := subFlags 0 x false; (p.1, { p.2 with cf := some (decide (x ≠ 0)) })
    match writeLoc s next w dst r with
    | .ok s' => .ok ((s'.setFlags f).setRip next)
    | .error e => .error e

/-- `MUL`/`IMUL` one-operand: the double-width product into `AX` or `rDX:rAX`. `CF = OF` is
set iff the upper half is significant; `SF ZF AF PF` are undefined. -/
def execMul1 (s : State) (next : W64) (signed : Bool) (w : Nat) (src : Loc) : Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok y =>
    let x := s.getReg w 0
    let (lo, hi, ovf) : BitVec w × BitVec w × Bool :=
      if signed then
        let full : Int := x.toInt * y.toInt
        let lo : BitVec w := BitVec.ofInt w full
        (lo, BitVec.ofInt w (full / (2 ^ w : Nat)), decide (lo.toInt ≠ full))
      else
        let full : Nat := x.toNat * y.toNat
        let hi : BitVec w := BitVec.ofNat w (full / 2 ^ w)
        (BitVec.ofNat w full, hi, decide (hi ≠ 0))
    let f : Flags := { cf := some ovf, ovf := some ovf, sf := none, zf := none, af := none, pf := none }
    let s' := if w = 8 then s.putReg 16 0 (BitVec.ofNat 16 (hi.toNat * 256 + lo.toNat))
      else (s.putReg w 0 lo).putReg w 2 hi
    .ok ((s'.setFlags f).setRip next)

/-- Two/three-operand `IMUL dst, a, b`: truncated product, `CF = OF` = truncation changed the
signed value; `SF ZF AF PF` undefined. -/
def execImul (s : State) (next : W64) (w dst : Nat) (a : Loc) (b : Src) : Except Fault State :=
  match readLoc s next w a with
  | .error e => .error e
  | .ok x =>
    match readSrc s next w b with
    | .error e => .error e
    | .ok y =>
      -- the truncated product is the same for signed and unsigned operands
      let full : Int := x.toInt * y.toInt
      let r : BitVec w := x * y
      let ovf := decide (r.toInt ≠ full)
      let f : Flags := { cf := some ovf, ovf := some ovf, sf := none, zf := none, af := none, pf := none }
      .ok (((s.putReg w dst r).setFlags f).setRip next)

/-- `DIV`/`IDIV`: `#DE` on a zero divisor or a quotient that does not fit; all flags undefined.
`IDIV` truncates towards zero and the remainder has the sign of the dividend. -/
def execDiv (s : State) (next : W64) (signed : Bool) (w : Nat) (src : Loc) : Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok y =>
    let lo : Nat := if w = 8 then (s.getReg 8 0).toNat else (s.getReg w 0).toNat
    let hi : Nat := if w = 8 then (s.getHigh 0).toNat else (s.getReg w 2).toNat
    let dividendU : Nat := hi * 2 ^ w + lo
    let undef : Flags := ⟨none, none, none, none, none, none⟩
    if y = 0 then .error (.divideError s.rip.toNat) else
    let qr : Option (Nat × Nat) :=
      if signed then
        let n : Int := (BitVec.ofNat (2 * w) dividendU).toInt
        let d : Int := y.toInt
        let q := n.tdiv d
        let r := n.tmod d
        if q < -((2 ^ (w - 1) : Nat) : Int) ∨ q ≥ ((2 ^ (w - 1) : Nat) : Int) then none
        else some ((BitVec.ofInt w q).toNat, (BitVec.ofInt w r).toNat)
      else
        let q := dividendU / y.toNat
        if q ≥ 2 ^ w then none else some (q, dividendU % y.toNat)
    match qr with
    | none => .error (.divideError s.rip.toNat)
    | some (q, r) =>
      let s' := if w = 8 then s.putReg 16 0 (BitVec.ofNat 16 (r * 256 + q))
        else (s.putReg w 0 (BitVec.ofNat w q)).putReg w 2 (BitVec.ofNat w r)
      .ok ((s'.setFlags undef).setRip next)

/-- Shifts and rotates (SDM `SAL/SAR/SHL/SHR` and `RCL/RCR/ROL/ROR`). The count is masked to
5 bits (6 for 64-bit operands); a masked count of 0 changes neither the value nor the flags
(but a 32-bit register destination is still written, i.e. zero-extended). -/
def execShift (s : State) (next : W64) (op : ShOp) (w : Nat) (dst : Loc) (count : Src) :
    Except Fault State :=
  match readSrc s next 8 count with
  | .error e => .error e
  | .ok cnt =>
    match readLocRW s next w dst with
    | .error e => .error e
    | .ok x =>
      let c := cnt.toNat % (if w = 64 then 64 else 32)
      -- A masked count of 0 leaves the value and the flags unchanged, but the destination is
      -- still written: a 32-bit register is zero-extended (observed by the oracle). For
      -- rotates the SDM pseudocode makes OF undefined even at count 0 (its prose says the
      -- flags are unaffected), so OF becomes undefined there.
      if c = 0 then
        let f := match op with
          | .rol | .ror => { s.flags with ovf := none }
          | _ => s.flags
        match writeLoc s next w dst x with
        | .ok s' => .ok ((s'.setFlags f).setRip next)
        | .error e => .error e
      else
      let szp (r : BitVec w) (cf of : Option Bool) : Flags :=
        { cf := cf, pf := some (parity r.toNat), af := none, zf := some (decide (r = 0)),
          sf := some r.msb, ovf := of }
      let (r, f) : BitVec w × Flags :=
        match op with
        | .shl =>
          let r := x <<< c
          let cf := if c < w then some (x.getLsbD (w - c)) else none
          (r, szp r cf (if c = 1 then cf.map (r.msb != ·) else none))
        | .shr =>
          let r := x >>> c
          let cf := if c < w then some (x.getLsbD (c - 1)) else none
          (r, szp r cf (if c = 1 then some x.msb else none))
        | .sar =>
          let r := x.sshiftRight c
          -- a count ≥ the width (8/16-bit operands only) leaves CF undefined: the SDM pins it
          -- only implicitly, the ACL2/Sail model leaves it undefined, AMD is undocumented
          let cf := if c < w then some (x.getLsbD (c - 1)) else none
          (r, szp r cf (if c = 1 then some false else none))
        | .rol =>
          let r := x.rotateLeft (c % w)
          let cf := r.getLsbD 0
          (r, { s.flags with cf := some cf, ovf := if c = 1 then some (r.msb != cf) else none })
        | .ror =>
          let r := x.rotateRight (c % w)
          (r, { s.flags with cf := some r.msb,
                             ovf := if c = 1 then some (r.msb != r.getLsbD (w - 2)) else none })
      match writeLoc s next w dst r with
      | .ok s' => .ok ((s'.setFlags f).setRip next)
      | .error e => .error e

/-- `RCL`/`RCR` at `w ∈ {32, 64}`: rotate `CF:dst` (`w + 1` bits) by the masked count. A
masked count of 0 changes nothing but `OF`, which becomes undefined (as for `ROL`/`ROR`: the
SDM pseudocode defines `OF` only for a count of 1) and still writes (zero-extends) a 32-bit
register; otherwise `CF` must be defined (it is rotated in), `CF` is the last bit rotated out,
`OF` is defined only for a count of 1 (`RCL`: `MSB(result) XOR CF'`; `RCR`: `MSB(dst) XOR CF`,
before the rotation) and `SF ZF AF PF` are unaffected. -/
def execRcx (s : State) (next : W64) (left : Bool) (w : Nat) (dst : Loc) (count : Src) :
    Except Fault State :=
  match readSrc s next 8 count with
  | .error e => .error e
  | .ok cnt =>
    match readLocRW s next w dst with
    | .error e => .error e
    | .ok x =>
      let c := cnt.toNat % (if w = 64 then 64 else 32)
      if c = 0 then
        match writeLoc s next w dst x with
        | .ok s' => .ok ((s'.setFlags { s.flags with ovf := none }).setRip next)
        | .error e => .error e
      else
      match s.flags.cf with
      | none => .error (.undefinedFlag s.rip.toNat)
      | some cf =>
        let t := cf.toNat * 2 ^ w + x.toNat
        let t' := if left then t * 2 ^ c % 2 ^ (w + 1) + t / 2 ^ (w + 1 - c)
          else t / 2 ^ c + t * 2 ^ (w + 1 - c) % 2 ^ (w + 1)
        let r : BitVec w := BitVec.ofNat w t'
        let ncf := decide (t' / 2 ^ w % 2 = 1)
        let of : Option Bool := if c = 1 then some (if left then r.msb != ncf else x.msb != cf) else none
        match writeLoc s next w dst r with
        | .ok s' => .ok ((s'.setFlags { s.flags with cf := some ncf, ovf := of }).setRip next)
        | .error e => .error e

/-- `SHLD`/`SHRD dst, src, count`: count masked like shifts (0: as for shifts); a count above
the operand size (16-bit only) has an undefined result. -/
def execShd (s : State) (next : W64) (left : Bool) (w : Nat) (dst : Loc) (src : Nat) (count : Src) :
    Except Fault State :=
  match readSrc s next 8 count with
  | .error e => .error e
  | .ok cnt =>
    match readLocRW s next w dst with
    | .error e => .error e
    | .ok x =>
      let y := s.getReg w src
      let c := cnt.toNat % (if w = 64 then 64 else 32)
      -- A masked count of 0 leaves the value and the flags unchanged, but the destination is
      -- still written: a 32-bit register is zero-extended (observed by the oracle).
      if c = 0 then
        match writeLoc s next w dst x with
        | .ok s' => .ok (s'.setRip next)
        | .error e => .error e
      else
      if c > w then .error (.undefinedResult s.rip.toNat) else
      let r : BitVec w :=
        if left then BitVec.ofNat w ((x.toNat * 2 ^ w + y.toNat) * 2 ^ c / 2 ^ w)
        else BitVec.ofNat w ((y.toNat * 2 ^ w + x.toNat) / 2 ^ c)
      let cf := if left then x.getLsbD (w - c) else x.getLsbD (c - 1)
      let f : Flags :=
        { cf := some cf, pf := some (parity r.toNat), af := none,
          zf := some (decide (r = 0)), sf := some r.msb,
          ovf := if c = 1 then some (r.msb != x.msb) else none }
      match writeLoc s next w dst r with
      | .ok s' => .ok ((s'.setFlags f).setRip next)
      | .error e => .error e

/-- `BT/BTS/BTR/BTC`: `CF` = the selected bit (offset modulo the operand size); `OF SF AF PF`
undefined (SDM), `ZF` undefined (unaffected on Intel, undefined on AMD). -/
def execBit (s : State) (next : W64) (op : BitOp) (w : Nat) (dst : Loc) (off : Src) :
    Except Fault State :=
  match readSrc s next w off with
  | .error e => .error e
  | .ok o =>
    let rd := match op with | .bt => readLoc s next w dst | _ => readLocRW s next w dst
    match rd with
    | .error e => .error e
    | .ok x =>
      let k := o.toNat % w
      let b := x.getLsbD k
      let m : BitVec w := 1 <<< k
      let f : Flags := { cf := some b, pf := none, af := none, zf := none, sf := none, ovf := none }
      let r? : Option (BitVec w) := match op with
        | .bt => none
        | .bts => some (x ||| m)
        | .btr => some (x &&& ~~~m)
        | .btc => some (x ^^^ m)
      match r? with
      | none => .ok ((s.setFlags f).setRip next)
      | some r =>
        match writeLoc s next w dst r with
        | .ok s' => .ok ((s'.setFlags f).setRip next)
        | .error e => .error e

def execCount (s : State) (next : W64) (op : CntOp) (w dst : Nat) (src : Loc) : Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok x =>
    let n := x.toNat
    let fin (r : BitVec w) (f : Flags) : Except Fault State := .ok (((s.putReg w dst r).setFlags f).setRip next)
    match op with
    | .bsf | .bsr =>
      -- the destination is undefined for a zero source (Intel; AMD keeps it), at every width
      if n = 0 then .error (.undefinedResult s.rip.toNat)
      else
        let idx := match op with | .bsf => ctzNat w n | _ => w - 1 - clzNat w n
        fin (BitVec.ofNat w idx) { cf := none, pf := none, af := none, zf := some false, sf := none, ovf := none }
    | .tzcnt | .lzcnt =>
      let r := match op with | .tzcnt => ctzNat w n | _ => clzNat w n
      fin (BitVec.ofNat w r)
        { cf := some (decide (n = 0)), pf := none, af := none, zf := some (decide (r = 0)), sf := none, ovf := none }
    | .popcnt =>
      fin (BitVec.ofNat w (popNat w n))
        { cf := some false, pf := some false, af := some false, zf := some (decide (n = 0)),
          sf := some false, ovf := some false }

/-! ## BMI1, BMI2

The VEX-encoded general-purpose instructions (SDM Vol. 2, `ANDN`, `BLSR`, ..., `PEXT`) at
`w ∈ {32, 64}`; their register destinations are written like every 32/64-bit result
(zero-extended). Memory operands are read only. -/

/-- `SF ZF` from `r`, `CF` given, `OF` cleared, `AF PF` undefined (`ANDN BLSR BLSI BZHI`). -/
@[janus64_exec] def bmiFlags {w : Nat} (r : BitVec w) (cf : Bool) : Flags :=
  { cf := some cf, pf := none, af := none, zf := some (decide (r = 0)), sf := some r.msb,
    ovf := some false }

/-- `PDEP` of the low `k` bits of the mask `m`: the low bits of `x` deposited at the set bits
of `m`, from the bottom. -/
def pdepNat : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, m =>
    if m % 2 = 1 then x % 2 + 2 * pdepNat k (x / 2) (m / 2) else 2 * pdepNat k x (m / 2)

/-- `PEXT` of the low `k` bits: the bits of `x` at the set bits of `m`, packed from the bottom. -/
def pextNat : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, m =>
    if m % 2 = 1 then x % 2 + 2 * pextNat k (x / 2) (m / 2) else pextNat k (x / 2) (m / 2)

/-- `ANDN dst, src1, src2`. -/
@[janus64_exec] def execAndn (s : State) (next : W64) (w dst src1 : Nat) (src2 : Loc) :
    Except Fault State :=
  match readLoc s next w src2 with
  | .error e => .error e
  | .ok y =>
    let r := ~~~(s.getReg w src1) &&& y
    .ok (((s.putReg w dst r).setFlags (bmiFlags r false)).setRip next)

/-- `BLSR` (`op = 1`: `CF` = source is zero), `BLSMSK` (`2`: `CF` = source is zero, `ZF`
cleared), `BLSI` (`3`: `CF` = source is not zero). -/
@[janus64_exec] def execBlsx (s : State) (next : W64) (op w dst : Nat) (src : Loc) :
    Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok x =>
    let rf : BitVec w × Flags :=
      if op = 1 then ((x - 1) &&& x, bmiFlags ((x - 1) &&& x) (decide (x = 0)))
      else if op = 2 then ((x - 1) ^^^ x, { bmiFlags ((x - 1) ^^^ x) (decide (x = 0)) with zf := some false })
      else ((0 - x) &&& x, bmiFlags ((0 - x) &&& x) (decide (x ≠ 0)))
    .ok (((s.putReg w dst rf.1).setFlags rf.2).setRip next)

/-- `BEXTR dst, src, ctl`: `ZF` from the result, `CF OF` cleared, `AF SF PF` undefined. -/
@[janus64_exec] def execBextr (s : State) (next : W64) (w dst : Nat) (src : Loc) (ctl : Nat) :
    Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok x =>
    let c := (s.getReg w ctl).toNat
    let r : BitVec w := BitVec.ofNat w (x.toNat / 2 ^ (c % 256) % 2 ^ (c / 256 % 256))
    let f : Flags :=
      { cf := some false, pf := none, af := none, zf := some (decide (r = 0)), sf := none, ovf := some false }
    .ok (((s.putReg w dst r).setFlags f).setRip next)

/-- `BZHI dst, src, idx`. -/
@[janus64_exec] def execBzhi (s : State) (next : W64) (w dst : Nat) (src : Loc) (idx : Nat) :
    Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok x =>
    let n := (s.getReg w idx).toNat % 256
    let r : BitVec w := if n < w then BitVec.ofNat w (x.toNat % 2 ^ n) else x
    .ok (((s.putReg w dst r).setFlags (bmiFlags r (decide (w ≤ n)))).setRip next)

/-- `SHLX`/`SHRX`/`SARX dst, src, cnt` (flags unaffected). -/
@[janus64_exec] def execShiftx (s : State) (next : W64) (op : ShOp) (w dst : Nat) (src : Loc)
    (cnt : Nat) : Except Fault State :=
  match readLoc s next w src with
  | .error e => .error e
  | .ok x =>
    let c := (s.getReg w cnt).toNat % (if w = 64 then 64 else 32)
    let r : BitVec w := match op with
      | .shl => x <<< c
      | .sar => x.sshiftRight c
      | _ => x >>> c
    .ok ((s.putReg w dst r).setRip next)

/-! ## String instructions

The direction flag is `State.df`, written by `CLD`/`STD` (`POPF`/`IRET` are not modelled). It
is clear at every Go call (Go ABIInternal: "The direction flag (D) is always cleared (set to
the forward direction) at a call"; `GoABI.CallSetup.df`). `MOVS`/`STOS` step forward with
`df = false` and backward with `df = true`. The address size is 64 bits (the `67` prefix is
rejected), so `RSI`, `RDI` and `RCX` are used in full. A `REP` string instruction is the
sequential repetition of its element step, which is also its architectural result on hardware
with fast strings (SDM Vol. 1 §7.3.9.3); a fault in iteration `k` stops the run. -/

/-- `k` element steps of `MOVS` with element size `sz` bytes: load `sz` bytes at `RSI`, store
them at `RDI`, add `sz` to `RSI` and `RDI`. -/
def movsIter (sz : Nat) : Nat → State → Except Fault State
  | 0, s => .ok s
  | k + 1, s =>
    match load s.mem (s.regs 6).toNat sz with
    | .error e => .error e
    | .ok v =>
      match store s.mem (s.regs 7).toNat sz v with
      | .error e => .error e
      | .ok m =>
        movsIter sz k (({ s with mem := m }.setReg 6 (s.regs 6 + BitVec.ofNat 64 sz)).setReg 7
          (s.regs 7 + BitVec.ofNat 64 sz))

/-- `k` element steps of `MOVS` with `DF = 1`: as `movsIter`, but `RSI` and `RDI` step down by
`sz` (SDM Vol. 2, `MOVS`: "the registers are decremented if DF = 1"). -/
def movsIterB (sz : Nat) : Nat → State → Except Fault State
  | 0, s => .ok s
  | k + 1, s =>
    match load s.mem (s.regs 6).toNat sz with
    | .error e => .error e
    | .ok v =>
      match store s.mem (s.regs 7).toNat sz v with
      | .error e => .error e
      | .ok m =>
        movsIterB sz k (({ s with mem := m }.setReg 6 (s.regs 6 - BitVec.ofNat 64 sz)).setReg 7
          (s.regs 7 - BitVec.ofNat 64 sz))

/-- `k` element steps of `STOS` with `DF = 1` (`RDI` steps down). -/
def stosIterB (sz v : Nat) : Nat → State → Except Fault State
  | 0, s => .ok s
  | k + 1, s =>
    match store s.mem (s.regs 7).toNat sz v with
    | .error e => .error e
    | .ok m => stosIterB sz v k ({ s with mem := m }.setReg 7 (s.regs 7 - BitVec.ofNat 64 sz))

/-- `k` element steps of `STOS` with element size `sz` bytes storing `v` (`< 2^(8 sz)`): store
at `RDI`, add `sz` to `RDI`. -/
def stosIter (sz v : Nat) : Nat → State → Except Fault State
  | 0, s => .ok s
  | k + 1, s =>
    match store s.mem (s.regs 7).toNat sz v with
    | .error e => .error e
    | .ok m => stosIter sz v k ({ s with mem := m }.setReg 7 (s.regs 7 + BitVec.ofNat 64 sz))

/-! ## SSE scalar floating point

The operations are `Janus.Amd64.FP` (Intel SDM semantics on the IEEE core). Legacy-SSE
scalar instructions replace the low `w` bits of the destination `XMM` register and preserve
bits 127:`w` (and `YMM` bits 255:128). A scalar memory operand is `w/8` bytes, without an
alignment requirement; the packed bitwise forms read 16 aligned bytes. An exception that is
unmasked in `MXCSR` is `#XM` (`Fault.simdFPException`); otherwise the raised flags are ORed
into `MXCSR`. -/

/-- The low `w` bits of an SSE operand (`XMMn`, or `w/8` bytes of memory). -/
def readXs (s : State) (next : W64) (w : Nat) : XLoc → Except Fault Nat
  | .xmm n => .ok ((s.xmm n).toNat % 2 ^ w)
  | .mem a => load s.mem (ea s next a).toNat (w / 8)

/-- `XMM[d]` with its low `w` bits replaced by `r`. -/
def State.setXmmLow (s : State) (d w r : Nat) : State :=
  s.setXmm d (BitVec.ofNat 128 ((s.xmm d).toNat / 2 ^ w * 2 ^ w + r % 2 ^ w))

/-- `MXCSR` with the flags `fl` (bits 5:0) raised. -/
def State.raiseMx (s : State) (fl : Nat) : State :=
  { s with mxcsr := BitVec.ofNat 32 (s.mxcsr.toNat ||| (fl &&& 0x3F)) }

/-- Commit a floating-point result: `#XM` when the operation trapped, else `k r` with the
flags raised and `RIP` advanced. -/
def fpDone (s : State) (pc : Nat) (next : W64) (o : FP.XR) (k : Nat → State) : Except Fault State :=
  if o.trap s.mxcsr.toNat then .error (.simdFPException pc) else .ok (((k o.res).raiseMx o.flags).setRip next)

/-- The format of an `SS` (`w = 32`) / `SD` (`w = 64`) instruction. -/
def fmtOf (w : Nat) : Janus.Float.Fmt := if w = 32 then Janus.Float.binary32 else Janus.Float.binary64

/-- `ADDSD`, ..., `SQRTSD` and the `SS` forms on `a = XMM[dst]` and `b = src`. -/
def sseArithOp (op : FPArith) (w : Nat) (c : FP.Ctl) (a b : Nat) : FP.XR :=
  let f := fmtOf w
  match op with
  | .add => FP.binop .add f c a b
  | .sub => FP.binop .sub f c a b
  | .mul => FP.binop .mul f c a b
  | .div => FP.binop .div f c a b
  | .min => FP.minmax false f c a b
  | .max => FP.minmax true f c a b
  | .sqrt => FP.sqrt f c b

/-! ## The executor -/

/-- The linear address of a memory operand as a natural (`ea`), as a function of the operand: what
the executors of the extension instructions (`ExecCrypto.exec`) take. A definition of its own
so that the proof automation does not rewrite inside the unapplied function. -/
def eaNat (s : State) (next : W64) (a : Addr) : Nat := (ea s next a).toNat
/-- The `RFLAGS` image `PUSHFQ` pushes (WP-C): `CF` bit 0, `PF` 2, `AF` 4, `ZF` 6, `SF` 7, `DF` 10,
`OF` 11, and the fixed user-mode bits `IF` (9) and bit 1 (`0x202`: Linux starts a process with
exactly these system bits, and user code cannot change `IF`/`IOPL`; `TF`, `NT`, `AC` and `ID`
are never set in the model because `POPFQ` refuses to set them). `none` if a status flag is
undefined. -/
def rflagsImage (f : Flags) (df : Bool) : Option Nat :=
  match f.cf, f.pf, f.af, f.zf, f.sf, f.ovf with
  | some c, some p, some a, some z, some sg, some o =>
    some (0x202 + c.toNat + 4 * p.toNat + 16 * a.toNat + 64 * z.toNat + 128 * sg.toNat +
      1024 * df.toNat + 2048 * o.toNat)
  | _, _, _, _, _, _ => none

/-- Bit `k` of `v`. -/
def bitOf (v k : Nat) : Bool := (v >>> k) % 2 == 1

/-- The status flags of an `RFLAGS` image (`POPFQ`). -/
def flagsOfImage (v : Nat) : Flags :=
  ⟨some (bitOf v 0), some (bitOf v 2), some (bitOf v 4), some (bitOf v 6), some (bitOf v 7),
    some (bitOf v 11)⟩

/-- An `RFLAGS` image `POPFQ` would load with a system flag the model does not track: `TF` (8),
`NT` (14), `AC` (18), `ID` (21). -/
def setsSystemFlag (v : Nat) : Bool := bitOf v 8 || bitOf v 14 || bitOf v 18 || bitOf v 21

/-- Execute a decoded instruction of length `len` at `s.rip`. Only specified on the output
of `decode`. -/
def exec (i : Instr) (len : Nat) (s : State) : Except Fault State :=
  -- `RIP` arithmetic is done on naturals (the same values as `BitVec` addition modulo `2^64`).
  let next : W64 := BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)
  let pc := s.rip.toNat
  match i with
  | .alu op w dst src => execAlu s next op w dst src
  | .test w a b =>
    match readLoc s next w a with
    | .error e => .error e
    | .ok x =>
      match readSrc s next w b with
      | .error e => .error e
      | .ok y => .ok ((s.setFlags (logicFlags (x &&& y))).setRip next)
  | .mov w dst src =>
    match readSrc s next w src with
    | .error e => .error e
    | .ok v =>
      match writeLoc s next w dst v with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .movx signed dw sw dst src =>
    match readLoc s next sw src with
    | .error e => .error e
    | .ok v => .ok ((s.putReg dw dst (if signed then v.signExtend dw else v.setWidth dw)).setRip next)
  | .lea w dst a => .ok ((s.putReg w dst ((ea s next a).setWidth w)).setRip next)
  | .unary op w dst => execUnary s next op w dst
  | .mul1 signed w src => execMul1 s next signed w src
  | .imul w dst a b => execImul s next w dst a b
  | .div signed w src => execDiv s next signed w src
  | .shift op w dst count => execShift s next op w dst count
  | .shd left w dst src count => execShd s next left w dst src count
  | .rcx left w dst count => execRcx s next left w dst count
  | .bit op w dst off => execBit s next op w dst off
  | .count op w dst src => execCount s next op w dst src
  | .bswap w r =>
    .ok ((s.putReg w r (BitVec.ofNat w (revBytesNat (w / 8) (s.getReg w r).toNat))).setRip next)
  | .setcc cc dst =>
    match condition cc s.flags with
    | none => .error (.undefinedFlag pc)
    | some b =>
      match writeLoc s next 8 dst (if b then 1 else 0) with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .cmov cc w dst src =>
    match readLoc s next w src with
    | .error e => .error e
    | .ok v =>
      match condition cc s.flags with
      | none => .error (.undefinedFlag pc)
      | some b =>
        -- a 32-bit CMOV always writes (zero-extends) its destination
        .ok ((s.putReg w dst (if b then v else s.getReg w dst)).setRip next)
  | .jcc cc rel =>
    match condition cc s.flags with
    | none => .error (.undefinedFlag pc)
    | some b => if b then branchTo s (BitVec.ofNat 64 ((next.toNat + rel) % 2 ^ 64)) else .ok (s.setRip next)
  | .jmp rel => branchTo s (BitVec.ofNat 64 ((next.toNat + rel) % 2 ^ 64))
  | .jmpInd src =>
    match readLoc s next 64 src with
    | .error e => .error e
    | .ok t => branchTo s t
  | .call rel =>
    let t := BitVec.ofNat 64 ((next.toNat + rel) % 2 ^ 64)
    if t.toNat < 2 ^ 47 then
      match push64 s next with
      | .ok s' => .ok (s'.setRip t)
      | .error e => .error e
    else .error (.badTarget t.toNat)
  | .callInd src =>
    match readLoc s next 64 src with
    | .error e => .error e
    | .ok t =>
      if t.toNat < 2 ^ 47 then
        match push64 s next with
        | .ok s' => .ok (s'.setRip t)
        | .error e => .error e
      else .error (.badTarget t.toNat)
  | .ret n =>
    match load s.mem (s.regs 4).toNat 8 with
    | .error e => .error e
    | .ok v => branchTo (s.setReg 4 (s.regs 4 + BitVec.ofNat 64 (8 + n))) (BitVec.ofNat 64 v)
  | .push src =>
    match readSrc s next 64 src with
    | .error e => .error e
    | .ok v =>
      match push64 s v with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .pop r =>
    match load s.mem (s.regs 4).toNat 8 with
    | .error e => .error e
    | .ok v => .ok (((s.setReg 4 (s.regs 4 + 8)).setReg r (BitVec.ofNat 64 v)).setRip next)
  | .leave =>
    let bp := s.regs 5
    match load s.mem bp.toNat 8 with
    | .error e => .error e
    | .ok v => .ok (((s.setReg 4 (bp + 8)).setReg 5 (BitVec.ofNat 64 v)).setRip next)
  | .nop => .ok (s.setRip next)
  -- Kernel, trap, environment and flag-image instructions (WP-C, `Janus.Amd64.DecodeSys`)
  | .syscall => .error (.kernel pc)
  | .envRead _ => .error (.kernel pc)
  | .trap sig => .error (.trap pc sig)
  | .pushfq =>
    match rflagsImage s.flags s.df with
    | none => .error (.undefinedFlag pc)
    | some v =>
      match push64 s (BitVec.ofNat 64 v) with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .popfq =>
    match load s.mem (s.regs 4).toNat 8 with
    | .error e => .error e
    | .ok v =>
      if setsSystemFlag v then .error (.systemFlag pc) else
      .ok ({ (s.setReg 4 (s.regs 4 + 8)).setFlags (flagsOfImage v) with df := bitOf v 10 }.setRip next)
  | .xchg w a b =>
    match readLocRW s next w a with
    | .error e => .error e
    | .ok va =>
      match readLoc s next w b with
      | .error e => .error e
      | .ok vb =>
        match writeLoc s next w a vb with
        | .error e => .error e
        | .ok s1 =>
          match writeLoc s1 next w b va with
          | .ok s2 => .ok (s2.setRip next)
          | .error e => .error e
  | .cbw w =>
    .ok ((s.putReg w 0 ((s.getReg (w / 2) 0).signExtend w)).setRip next)
  | .cwd w =>
    let v : BitVec w := if (s.getReg w 0).msb then BitVec.allOnes w else 0
    .ok ((s.putReg w 2 v).setRip next)
  | .flagOp op =>
    match op with
    | .clc => .ok ((s.setFlags { s.flags with cf := some false }).setRip next)
    | .stc => .ok ((s.setFlags { s.flags with cf := some true }).setRip next)
    | .cmc =>
      match s.flags.cf with
      | none => .error (.undefinedFlag pc)
      | some c => .ok ((s.setFlags { s.flags with cf := some (!c) }).setRip next)
  | .sseMov al dst src =>
    match readX s next al src with
    | .error e => .error e
    | .ok v =>
      match writeX s next al dst v with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .sseOp op dst src =>
    match readX s next true src with
    | .error e => .error e
    | .ok v => .ok ((s.setXmm dst (sseBin op (s.xmm dst) v)).setRip next)
  | .pshufd dst src imm =>
    match readX s next true src with
    | .error e => .error e
    | .ok v => .ok ((s.setXmm dst (BitVec.ofNat 128 (pshufdNat v.toNat imm))).setRip next)
  | .pshuflw dst src imm =>
    match readX s next true src with
    | .error e => .error e
    | .ok v =>
      let a := v.toNat
      let sel (i : Nat) : Nat := a / 2 ^ (16 * (imm / 4 ^ i % 4)) % 2 ^ 16
      .ok ((s.setXmm dst (BitVec.ofNat 128 (sel 0 + 2 ^ 16 * sel 1 + 2 ^ 32 * sel 2 + 2 ^ 48 * sel 3 +
        a / 2 ^ 64 * 2 ^ 64))).setRip next)
  | .movsd w dst src =>
    match dst, src with
    | .xmm d, .mem a =>
      match load s.mem (ea s next a).toNat (w / 8) with
      | .error e => .error e
      | .ok v => .ok ((s.setXmm d (BitVec.ofNat 128 v)).setRip next)
    | .xmm d, .xmm r =>
      .ok ((s.setXmm d (BitVec.ofNat 128 ((s.xmm d).toNat / 2 ^ w * 2 ^ w + (s.xmm r).toNat % 2 ^ w))).setRip next)
    | .mem a, .xmm r =>
      match store s.mem (ea s next a).toNat (w / 8) ((s.xmm r).toNat % 2 ^ w) with
      | .error e => .error e
      | .ok m => .ok ({ s with mem := m }.setRip next)
    | .mem _, .mem _ => .error (.undecodable pc [])
  | .pmovmskb l dst src =>
    .ok ((s.setReg dst (BitVec.ofNat 64 (msbBytes (l / 8) (s.getV l src)))).setRip next)
  | .vmov al l dst src =>
    match readV s next l al src with
    | .error e => .error e
    | .ok v =>
      match writeV s next l al dst v with
      | .error e => .error e
      | .ok s' => .ok (s'.setRip next)
  | .vop op l dst src1 src2 =>
    match readV s next l false src2 with
    | .error e => .error e
    | .ok b => .ok ((s.setV l dst (vecBin op l (s.getV l src1) b)).setRip next)
  | .vptest l a b =>
    match readV s next l false b with
    | .error e => .error e
    | .ok y =>
      .ok ((s.setFlags (ptestFlags l (s.getV l a) y)).setRip next)
  | .vpbroadcastb l dst src =>
    let b : Except Fault Nat := match src with
      | .xmm n => .ok ((s.xmm n).toNat % 256)
      | .mem a => load s.mem (ea s next a).toNat 1
    match b with
    | .error e => .error e
    | .ok b => .ok ((s.setV l dst (replBytes (l / 8) b)).setRip next)
  | .vzeroupper => .ok ({ s with ymmHi := fun _ => 0 }.setRip next)
  | .movdq w toX x g =>
    if toX then
      match readLoc s next w g with
      | .error e => .error e
      | .ok v => .ok ((s.setXmm x (v.setWidth 128)).setRip next)
    else
      match writeLoc s next w g ((s.xmm x).setWidth w) with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .movq dst src =>
    let v : Except Fault (BitVec 64) :=
      match src with
      | .xmm n => .ok ((s.xmm n).setWidth 64)
      | .mem a =>
        match load s.mem (ea s next a).toNat 8 with
        | .ok v => .ok (BitVec.ofNat 64 v)
        | .error e => .error e
    match v with
    | .error e => .error e
    | .ok v =>
      match dst with
      | .xmm n => .ok ((s.setXmm n (v.setWidth 128)).setRip next)
      | .mem a =>
        match store s.mem (ea s next a).toNat 8 v.toNat with
        | .ok m => .ok ({ s with mem := m }.setRip next)
        | .error e => .error e

  | .xadd w dst src =>
    -- `TEMP ← SRC + DEST; SRC ← DEST; DEST ← TEMP` (the address is computed once, before)
    match readLocRW s next w dst with
    | .error e => .error e
    | .ok x =>
      match readLoc s next w src with
      | .error e => .error e
      | .ok y =>
        let r := addFlags x y false
        match writeLoc s next w dst r.1 with
        | .error e => .error e
        | .ok s1 =>
          match writeLoc s1 next w src x with
          | .error e => .error e
          | .ok s2 => .ok ((s2.setFlags r.2).setRip next)
  | .cmpxchg w dst src =>
    -- `TEMP ← DEST; IF accumulator = TEMP THEN DEST ← SRC ELSE accumulator ← TEMP;
    -- DEST ← TEMP` (memory `DEST` is always written); flags of `CMP accumulator, TEMP`
    match readLocRW s next w dst with
    | .error e => .error e
    | .ok x =>
      match readLoc s next w src with
      | .error e => .error e
      | .ok y =>
        let acc := s.getReg w 0
        let f := (subFlags acc x false).2
        if acc = x then
          match writeLoc s next w dst y with
          | .error e => .error e
          | .ok s1 => .ok ((s1.setFlags f).setRip next)
        else
          match writeLoc s next w dst x with
          | .error e => .error e
          | .ok s1 => .ok (((s1.putReg w 0 x).setFlags f).setRip next)
  | .cmpxchgDbl w a =>
    let addr := (ea s next a).toNat
    let h := w / 2
    if w = 128 ∧ addr % 16 ≠ 0 then .error (.misaligned addr) else
    match loadRW s.mem addr (w / 8) with
    | .error e => .error e
    | .ok v =>
      let cmp := (s.getReg h 2).toNat * 2 ^ h + (s.getReg h 0).toNat
      if v = cmp then
        match store s.mem addr (w / 8) ((s.getReg h 1).toNat * 2 ^ h + (s.getReg h 3).toNat) with
        | .error e => .error e
        | .ok m => .ok (({ s with mem := m }.setFlags { s.flags with zf := some true }).setRip next)
      else
        match store s.mem addr (w / 8) v with
        | .error e => .error e
        | .ok m =>
          .ok (((({ s with mem := m }.putReg h 0 (BitVec.ofNat h v)).putReg h 2
            (BitVec.ofNat h (v / 2 ^ h))).setFlags { s.flags with zf := some false }).setRip next)
  | .movs rep w =>
    if s.df then
      match movsIterB (w / 8) (if rep then (s.regs 1).toNat else 1) s with
      | .error e => .error e
      | .ok s' => .ok ((if rep then s'.setReg 1 0 else s').setRip next)
    else
    match movsIter (w / 8) (if rep then (s.regs 1).toNat else 1) s with
    | .error e => .error e
    | .ok s' => .ok ((if rep then s'.setReg 1 0 else s').setRip next)
  | .stos rep w =>
    if s.df then
      match stosIterB (w / 8) (s.getReg w 0).toNat (if rep then (s.regs 1).toNat else 1) s with
      | .error e => .error e
      | .ok s' => .ok ((if rep then s'.setReg 1 0 else s').setRip next)
    else
    match stosIter (w / 8) (s.getReg w 0).toNat (if rep then (s.regs 1).toNat else 1) s with
    | .error e => .error e
    | .ok s' => .ok ((if rep then s'.setReg 1 0 else s').setRip next)
  | .setDF b => .ok ({ s with df := b }.setRip next)
  -- SSE scalar floating point
  | .sseArith op w dst src =>
    match readXs s next w src with
    | .error e => .error e
    | .ok b =>
      fpDone s pc next (sseArithOp op w (FP.ctl s.mxcsr.toNat) ((s.xmm dst).toNat % 2 ^ w) b)
        fun r => s.setXmmLow dst w r
  | .sseComi signal w a b =>
    match readXs s next w b with
    | .error e => .error e
    | .ok y =>
      let o := FP.comis signal (fmtOf w) (FP.ctl s.mxcsr.toNat) ((s.xmm a).toNat % 2 ^ w) y
      if o.trap s.mxcsr.toNat then .error (.simdFPException pc) else
      .ok (((s.setFlags ⟨some (o.res % 2 = 1), some (o.res / 2 % 2 = 1), some false,
        some (o.res / 4 % 2 = 1), some false, some false⟩).raiseMx o.flags).setRip next)
  | .sseCmp w dst src pred =>
    match readXs s next w src with
    | .error e => .error e
    | .ok b =>
      fpDone s pc next (FP.cmp (fmtOf w) (FP.ctl s.mxcsr.toNat) pred ((s.xmm dst).toNat % 2 ^ w) b)
        fun r => s.setXmmLow dst w r
  | .cvtsi2f w iw dst src =>
    match readLoc s next iw src with
    | .error e => .error e
    | .ok x => fpDone s pc next (FP.ofInt (fmtOf w) (FP.ctl s.mxcsr.toNat) iw x.toNat) fun r => s.setXmmLow dst w r
  | .cvtf2si trunc w iw dst src =>
    match readXs s next w src with
    | .error e => .error e
    | .ok b =>
      let mx := s.mxcsr.toNat
      fpDone s pc next (FP.toInt (fmtOf w) (FP.ctl mx) (if trunc then .rz else (FP.ctl mx).rc) iw b)
        fun r => s.putReg iw dst (BitVec.ofNat iw r)
  | .cvtff w dst src =>
    match readXs s next w src with
    | .error e => .error e
    | .ok b =>
      let w' := if w = 64 then 32 else 64
      fpDone s pc next (FP.convert (fmtOf w) (fmtOf w') (FP.ctl s.mxcsr.toNat) b) fun r => s.setXmmLow dst w' r
  | .sseRound w dst src imm =>
    match readXs s next w src with
    | .error e => .error e
    | .ok b => fpDone s pc next (FP.roundInt (fmtOf w) (FP.ctl s.mxcsr.toNat) imm b) fun r => s.setXmmLow dst w r
  | .fpLogic op dst src =>
    match readX s next true src with
    | .error e => .error e
    | .ok v =>
      let d := s.xmm dst
      .ok ((s.setXmm dst (if op = 0 then d &&& v else if op = 1 then ~~~d &&& v else d ||| v)).setRip next)
  | .andn w dst src1 src2 => execAndn s next w dst src1 src2
  | .blsx op w dst src => execBlsx s next op w dst src
  | .bextr w dst src ctl => execBextr s next w dst src ctl
  | .bzhi w dst src idx => execBzhi s next w dst src idx
  | .shiftx op w dst src cnt => execShiftx s next op w dst src cnt
  | .rorx w dst src imm =>
    match readLoc s next w src with
    | .error e => .error e
    | .ok x => .ok ((s.putReg w dst (x.rotateRight (imm % w))).setRip next)
  | .mulx w hi lo src =>
    -- `DEST2 ← low half; DEST1 ← high half` (rDX is read before either write)
    match readLoc s next w src with
    | .error e => .error e
    | .ok y =>
      let full := (s.getReg w 2).toNat * y.toNat
      .ok (((s.putReg w lo (BitVec.ofNat w full)).putReg w hi (BitVec.ofNat w (full / 2 ^ w))).setRip next)
  | .pdep w dst src mask =>
    match readLoc s next w mask with
    | .error e => .error e
    | .ok m => .ok ((s.putReg w dst (BitVec.ofNat w (pdepNat w (s.getReg w src).toNat m.toNat))).setRip next)
  | .pext w dst src mask =>
    match readLoc s next w mask with
    | .error e => .error e
    | .ok m => .ok ((s.putReg w dst (BitVec.ofNat w (pextNat w (s.getReg w src).toNat m.toNat))).setRip next)
  | .movbe w dst src =>
    match readLoc s next w src with
    | .error e => .error e
    | .ok v =>
      match writeLoc s next w dst (BitVec.ofNat w (revBytesNat (w / 8) v.toNat)) with
      | .ok s' => .ok (s'.setRip next)
      | .error e => .error e
  | .vfmas w form negP negC dst src2 src3 =>
    match readXs s next w src3 with
    | .error e => .error e
    | .ok z =>
      let d := (s.xmm dst).toNat % 2 ^ w
      let y := (s.xmm src2).toNat % 2 ^ w
      let abc : Nat × Nat × Nat := if form = 132 then (d, z, y) else if form = 213 then (y, d, z) else (y, z, d)
      match FP.fma (fmtOf w) (FP.ctl s.mxcsr.toNat) negP negC abc.1 abc.2.1 abc.2.2 with
      | none => .error (.undefinedResult pc)
      | some o => fpDone s pc next o fun r => (s.setXmmLow dst w r).setYmmHi dst 0
  | .locked i a size =>
    let addr := (ea s next a).toNat
    if addr % size ≠ 0 then .error (.misaligned addr) else exec i len s
  | .sse i => ExecSSE.exec s next pc (eaNat s next) i
  | .crypto i => ExecCrypto.exec s next pc (eaNat s next) i

/-- Decode and execute the instruction at the start of `bytes` (the code at `s.rip`). -/
def step (bytes : List Nat) (s : State) : Except Fault State :=
  match decode bytes with
  | some (i, len) => exec i len s
  | none => .error (.undecodable s.rip.toNat (bytes.take 15))

theorem step_of_decode {bytes : List Nat} {i : Instr} {len : Nat}
    (h : decode bytes = some (i, len)) (s : State) : step bytes s = exec i len s := by
  simp [step, h]

end Janus.Amd64
