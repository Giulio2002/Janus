import Janus.Amd64.State
import Janus.Amd64.Instr
import Janus.Amd64.Decode
import Janus.Arm64.Bits

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

/-- The effective address of `a`; `next` is the address of the next instruction. -/
def ea (s : State) (next : W64) (a : Addr) : W64 :=
  if a.rip then BitVec.ofNat 64 ((next.toNat + a.disp) % 2 ^ 64) else
  let base : W64 := match a.base with
    | some b => s.regs b
    | none => 0
  let idx : W64 := match a.index with
    | some i => s.regs i <<< a.scale
    | none => 0
  base + idx + BitVec.ofNat 64 a.disp

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
      if n = 0 then
        let f : Flags := { cf := none, pf := none, af := none, zf := some true, sf := none, ovf := none }
        if w = 64 then .ok ((s.setFlags f).setRip next) else .error (.undefinedResult s.rip.toNat)
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

/-! ## The executor -/

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
  | .sseOp .xor dst src =>
    match readX s next true src with
    | .error e => .error e
    | .ok v => .ok ((s.setXmm dst (s.xmm dst ^^^ v)).setRip next)
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

/-- Decode and execute the instruction at the start of `bytes` (the code at `s.rip`). -/
def step (bytes : List Nat) (s : State) : Except Fault State :=
  match decode bytes with
  | some (i, len) => exec i len s
  | none => .error (.undecodable s.rip.toNat (bytes.take 15))

theorem step_of_decode {bytes : List Nat} {i : Instr} {len : Nat}
    (h : decode bytes = some (i, len)) (s : State) : step bytes s = exec i len s := by
  simp [step, h]

end Janus.Amd64
