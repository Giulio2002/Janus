import Janus.Arm64.NeonInstr
import Janus.Arm64.Decode
import Janus.Arm64.NeonFP
import Janus.Arm64.ExecFloat

/-!
# Execution of the Advanced SIMD classes of `NeonInstr` (trusted)

`execNeon i s` is `exec (.neon i) s` (`Janus.Arm64.exec` dispatches here). The operations are
in `Janus.Arm64.Neon` (integer) and `Janus.Arm64.NeonFP` (floating point); this file does what
the ASL does around them: operand reads (`V[n, datasize]`, `Vpart[n, part]`), result writes
(`V[d, datasize] = result` zero-extends; `Vpart[d, 1] = result` keeps the low half), the scalar
floating-point merge of FEAT_AFP (`elements == 1 && IsMerging(FPCR)`: the result starts as
`V[src, 128]`, with the source named per instruction), `FPSR.QC` for saturation, the
floating-point exceptions (`fpCommit`: a trap-enabled exception faults, the others are ORed into
`FPSR`), and the memory accesses.

Memory. `LD2`–`LD4`/`ST2`–`ST4` (multiple structures) transfer `selem * datasize / 8`
contiguous bytes; the model checks the whole block as one access, which is never more
permissive than the ASL's element accesses (a block that crosses from one allocation into an
adjacent one faults here). A faulting instruction faults as a whole. `LDNP`/`STNP` are
`LDP`/`STP` (the non-temporal hint has no architectural effect).

The SP-relative base and the indexed-access shape repeat `Exec`'s `baseAddr`/`memIndexed`/
`memVPair` (which `Exec` defines after importing this file); `Janus.Tactic.Neon` proves the
copies equal to the originals.
-/

namespace Janus.Arm64

open Janus.Float Janus.Arm64.FP Janus.Arm64.Neon Janus.Arm64.NeonFP

namespace NeonExec

/-- `datasize` of a vector operation. -/
def dsize (Q : Bool) : Nat := if Q then 128 else 64

/-- `Vpart[n, part]` of a 64-bit part: the low (`part = false`) or high half of `V[n, 128]`. -/
def vpart (s : State) (n : Nat) (part : Bool) : Nat :=
  if part then s.getV n 128 / 2 ^ 64 else s.getV n 64

/-- `Vpart[d, part] = r` for a 64-bit `r`: `V[d, 64] = r` (zero-extended) for part 0; for part 1
the upper half is written and the lower half kept. -/
def setVpart (s : State) (d : Nat) (part : Bool) (r : Nat) : State :=
  if part then s.setV d 128 (s.getV d 64 + 2 ^ 64 * (r % 2 ^ 64)) else s.setV d 64 r

/-- `if sat then FPSR.QC = '1'`. -/
def qcCommit (t : State) (qc : Bool) : State :=
  if qc then { t with fpsr := t.fpsr ||| BitVec.ofNat 32 (2 ^ 27) } else t

/-- An integer result: `.ok` with `FPSR.QC` set on saturation. -/
def intCommit (t : State) (r : Res) (write : State → Nat → State) : Except Fault State :=
  .ok (qcCommit (write t r.1) r.2)

/-- The single-precision estimates under `FPCR.AH = 1` depend on FEAT_RPRES (IMPLEMENTATION
DEFINED): the model faults rather than choose. -/
def rpresUnknown (s : State) (sz : Nat) : Bool := sz = 0 && ah s.fpcr.toNat

/-- Vector `FABS`/`FNEG` under `FPCR.AH = 1` with a NaN lane: the ASL leaves the NaN unchanged
(`FPAbs`/`FPNeg` with FEAT_AFP), which the Sail model confirms, but qemu 10.2.1 flips or clears
its sign bit; the references disagree, so the model faults instead of choosing. -/
def absNegAHNaN (s : State) (sz ds x : Nat) : Bool :=
  let e := fesize sz
  ah s.fpcr.toNat && anyLane (fun i => Janus.Float.isNaN (fmtOf sz) (elem x e i)) (ds / e)

/-! ## Data processing -/

def threeSame (s : State) (Q U : Bool) (size rm opcode rn rd : Nat) : Except Fault State :=
  let ds := dsize Q
  let x := s.getV rn ds
  let y := s.getV rm ds
  let d := s.getV rd ds
  if opcode / 8 = 0b11 then
    let o := threeSameFP U (size / 2 = 1) (size % 2) opcode ds s.fpcr.toNat x y d
    fpCommit s o.2 (s.setV rd ds o.1)
  else intCommit s (threeSameInt U size opcode ds x y d) fun t r => t.setV rd ds r

def sThreeSame (s : State) (U : Bool) (size rm opcode rn rd : Nat) : Except Fault State :=
  if opcode / 8 = 0b11 then
    let sz := size % 2
    let e := fesize sz
    let o := threeSameFP U (size / 2 = 1) sz opcode e s.fpcr.toNat (s.getV rn e) (s.getV rm e)
      (s.getV rd e)
    -- the compares merge into `V[m]`, the others into `V[n]`
    let src := if opcode = 0b11100 || opcode = 0b11101 then rm else rn
    fpCommit s o.2 (s.setScalar rd e (s.mergeBase src) o.1)
  else
    let e := esizeOf size
    intCommit s (threeSameInt U size opcode e (s.getV rn e) (s.getV rm e) (s.getV rd e))
      fun t r => t.setV rd e r

def threeDiff (s : State) (Q U : Bool) (size rm opcode rn rd : Nat) : Except Fault State :=
  let e := esizeOf size
  let r := threeDiffOp U e (64 / e) opcode (if Q then 1 else 0) (s.getV rn 128) (s.getV rm 128)
    (s.getV rd 128)
  if opcode = 0b0100 || opcode = 0b0110 then intCommit s r fun t r => setVpart t rd Q r
  else intCommit s r fun t r => t.setV rd 128 r

def sThreeDiff (s : State) (U : Bool) (size rm opcode rn rd : Nat) : Except Fault State :=
  let e := esizeOf size
  intCommit s (threeDiffOp U e 1 opcode 0 (s.getV rn 128) (s.getV rm 128) (s.getV rd 128))
    fun t r => t.setV rd (2 * e) r

def twoMisc (s : State) (Q U : Bool) (size opcode rn rd : Nat) : Except Fault State :=
  let ds := dsize Q
  let fpcr := s.fpcr.toNat
  let isFP := opcode ≥ 0b01100 && opcode ≠ 0b10010 && opcode ≠ 0b10011 && opcode ≠ 0b10100
  if isFP then
    let a := size / 2 = 1
    let sz := size % 2
    if opcode = 0b10110 then
      let o := fcvtnOp U 2 fpcr (s.getV rn 128)
      fpCommit s o.2 (setVpart s rd Q o.1)
    else if opcode = 0b10111 then
      let o := fcvtlOp fpcr (vpart s rn Q)
      fpCommit s o.2 (s.setV rd 128 o.1)
    else if opcode = 0b11101 && a && rpresUnknown s sz then .error (.trapped s.pc.toNat)
    else if opcode = 0b01111 && absNegAHNaN s sz ds (s.getV rn ds) then .error (.trapped s.pc.toNat)
    else
      let o := twoMiscFP U a sz opcode ds fpcr (s.getV rn ds)
      fpCommit s o.2 (s.setV rd ds o.1)
  else
    let e := esizeOf size
    if opcode = 0b10010 || opcode = 0b10100 then
      intCommit s (narrowOp U e (64 / e) opcode (s.getV rn 128)) fun t r => setVpart t rd Q r
    else if opcode = 0b10011 then .ok (s.setV rd 128 (shllNOp e (vpart s rn Q)))
    else intCommit s (twoMiscInt U size opcode ds (s.getV rn ds) (s.getV rd ds))
      fun t r => t.setV rd ds r

def sTwoMisc (s : State) (U : Bool) (size opcode rn rd : Nat) : Except Fault State :=
  let fpcr := s.fpcr.toNat
  if opcode = 0b00011 || opcode = 0b00111 then
    let e := esizeOf size
    intCommit s (twoMiscInt U size opcode e (s.getV rn e) (s.getV rd e)) fun t r => t.setV rd e r
  else if opcode = 0b01000 || opcode = 0b01001 || opcode = 0b01010 || opcode = 0b01011 then
    intCommit s (twoMiscInt U size opcode 64 (s.getV rn 64) (s.getV rd 64))
      fun t r => t.setV rd 64 r
  else if opcode = 0b10010 || opcode = 0b10100 then
    let e := esizeOf size
    intCommit s (narrowOp U e 1 opcode (s.getV rn 128)) fun t r => t.setV rd e r
  else
    let a := size / 2 = 1
    let sz := size % 2
    let e := fesize sz
    if opcode = 0b10110 then
      -- FCVTXN (scalar): merging `V[d, 128]`, else `Vpart[d, 0] = result<31:0>`
      let o := fpConvertOdd fpcr (s.getV rn 64)
      fpCommit s o.2 (s.setScalar rd 32 (s.mergeBase rd) o.1)
    else if opcode = 0b11101 && a && rpresUnknown s sz then .error (.trapped s.pc.toNat)
    else
      let o := twoMiscFP U a sz opcode e fpcr (s.getV rn e)
      -- the compares with zero do not merge
      let cmp := opcode = 0b01100 || opcode = 0b01101 || opcode = 0b01110
      fpCommit s o.2 (if cmp then s.setV rd e o.1 else s.setScalar rd e (s.mergeBase rd) o.1)

def across (s : State) (Q U : Bool) (size opcode rn rd : Nat) : Except Fault State :=
  if opcode = 0b01100 || opcode = 0b01111 then
    -- F(MAX|MIN)(NM)V .4S: `Reduce(op, V[n, 128], 32)`
    let op := (if opcode = 0b01111 then 2 else 0) + (if size / 2 = 1 then 1 else 0)
    let o := reduce4 op s.fpcr.toNat (s.getV rn 128)
    fpCommit s o.2 (s.setV rd 32 o.1)
  else
    let r := acrossOp U size opcode (dsize Q) (s.getV rn (dsize Q))
    .ok (s.setV rd r.2 r.1)

def sPairwise (s : State) (_U : Bool) (size opcode rn rd : Nat) : Except Fault State :=
  if opcode = 0b11011 then .ok (s.setV rd 64 (reduceAdd 64 (s.getV rn 128) 2))
  else
    let sz := size % 2
    let e := fesize sz
    let op := if opcode = 0b01101 then 4
      else (if opcode = 0b01111 then 2 else 0) + (if size / 2 = 1 then 1 else 0)
    let o := reduce2 op sz s.fpcr.toNat (s.getV rn (2 * e))
    fpCommit s o.2 (s.setV rd e o.1)

/-- The fixed-point conversions by immediate on `n` elements of `x`: SCVTF/UCVTF (`11100`,
rounding from `FPCR`) and FCVTZS/FCVTZU (`11111`, toward zero), `fbits = 2*esize - immh:immb`. -/
def fixedLanes (U : Bool) (esize n opcode fbits fpcr x : Nat) : Nat × Exc :=
  let f := if esize = 32 then binary32 else binary64
  fpLanes esize n fun i =>
    if opcode = 0b11100 then fixedToFPF f fpcr U (roundingMode fpcr) esize fbits (elem x esize i)
    else fpToFixedF f fpcr U .rz esize fbits (elem x esize i)

def shiftImm (s : State) (Q U : Bool) (immh immb opcode rn rd : Nat) : Except Fault State :=
  let esize := 8 * 2 ^ neonHsb4 immh
  let immhb := immh * 8 + immb
  let ds := dsize Q
  if opcode / 4 = 0b100 then
    intCommit s (shiftNarrowOp U esize (64 / esize) opcode (2 * esize - immhb) (s.getV rn 128))
      fun t r => setVpart t rd Q r
  else if opcode = 0b10100 then .ok (s.setV rd 128 (shllOp U esize (immhb - esize) (vpart s rn Q)))
  else if opcode = 0b11100 || opcode = 0b11111 then
    let o := fixedLanes U esize (ds / esize) opcode (2 * esize - immhb) s.fpcr.toNat (s.getV rn ds)
    fpCommit s o.2 (s.setV rd ds o.1)
  else intCommit s (shiftImmInt U esize opcode ds immhb (s.getV rn ds) (s.getV rd ds))
    fun t r => t.setV rd ds r

def sShiftImm (s : State) (U : Bool) (immh immb opcode rn rd : Nat) : Except Fault State :=
  let esize := 8 * 2 ^ neonHsb4 immh
  let immhb := immh * 8 + immb
  if opcode / 4 = 0b100 then
    intCommit s (shiftNarrowOp U esize 1 opcode (2 * esize - immhb) (s.getV rn 128))
      fun t r => t.setV rd esize r
  else if opcode = 0b11100 || opcode = 0b11111 then
    let o := fixedLanes U esize 1 opcode (2 * esize - immhb) s.fpcr.toNat (s.getV rn esize)
    fpCommit s o.2 (s.setScalar rd esize (s.mergeBase rd) o.1)
  else intCommit s (shiftImmInt U esize opcode esize immhb (s.getV rn esize) (s.getV rd esize))
    fun t r => t.setV rd esize r

/-- The element index and register of the integer by-element forms: `size = 01`:
`index = H:L:M`, `m = 0:Rm`; `size = 10`: `index = H:L`, `m = M:Rm`. -/
def intIdx (size : Nat) (L M H : Bool) (rm : Nat) : Nat × Nat :=
  if size = 1 then (H.toNat * 4 + L.toNat * 2 + M.toNat, rm) else (H.toNat * 2 + L.toNat, M.toNat * 16 + rm)

/-- The element index and register of the floating-point by-element forms: `sz = 0`:
`index = H:L`; `sz = 1`: `index = H`; `m = M:Rm`. -/
def fpIdx (sz : Nat) (L M H : Bool) (rm : Nat) : Nat × Nat :=
  (if sz = 0 then H.toNat * 2 + L.toNat else H.toNat, M.toNat * 16 + rm)

def byElem (s : State) (Q U : Bool) (size : Nat) (L M : Bool) (rm opcode : Nat) (H : Bool)
    (rn rd : Nat) : Except Fault State :=
  if opcode = 0b0001 || opcode = 0b0101 || opcode = 0b1001 then
    let sz := size % 2
    let e := fesize sz
    let (idx, m) := fpIdx sz L M H rm
    let ds := dsize Q
    let o := byElemFP U sz opcode ds s.fpcr.toNat (s.getV rn ds) (s.getV rd ds) (elem (s.getV m 128) e idx)
    fpCommit s o.2 (s.setV rd ds o.1)
  else
    let e := esizeOf size
    let (idx, m) := intIdx size L M H rm
    let el := elem (s.getV m 128) e idx
    if opcode = 0b1000 || opcode = 0b0000 || opcode = 0b0100 || opcode = 0b1100 || opcode = 0b1101 then
      let ds := dsize Q
      intCommit s (byElemInt U e (ds / e) opcode 0 (s.getV rn ds) (s.getV rd ds) el)
        fun t r => t.setV rd ds r
    else
      intCommit s (byElemInt U e (64 / e) opcode (if Q then 1 else 0) (s.getV rn 128) (s.getV rd 128) el)
        fun t r => t.setV rd 128 r

def sByElem (s : State) (U : Bool) (size : Nat) (L M : Bool) (rm opcode : Nat) (H : Bool)
    (rn rd : Nat) : Except Fault State :=
  if opcode = 0b0001 || opcode = 0b0101 || opcode = 0b1001 then
    let sz := size % 2
    let e := fesize sz
    let (idx, m) := fpIdx sz L M H rm
    let o := byElemFP U sz opcode e s.fpcr.toNat (s.getV rn e) (s.getV rd e) (elem (s.getV m 128) e idx)
    -- FMLA/FMLS merge into `V[d]`, FMUL/FMULX into `V[n]`
    fpCommit s o.2 (s.setScalar rd e (s.mergeBase (if opcode = 0b1001 then rn else rd)) o.1)
  else
    let e := esizeOf size
    let (idx, m) := intIdx size L M H rm
    let el := elem (s.getV m 128) e idx
    if opcode = 0b1100 || opcode = 0b1101 then
      intCommit s (byElemInt U e 1 opcode 0 (s.getV rn e) (s.getV rd e) el) fun t r => t.setV rd e r
    else
      intCommit s (byElemInt U e 1 opcode 0 (s.getV rn 128) (s.getV rd 128) el)
        fun t r => t.setV rd (2 * e) r

/-- Conversion between floating point and fixed point (scalar, general register):
`fbits = 64 - scale`; SCVTF/UCVTF write `V[d]` (merging under `IsMerging(FPCR)`), FCVTZS/FCVTZU
write `X[d, intsize]`. -/
def fpCvtFixed (s : State) (sf : Bool) (ftype opcode scale rn rd : Nat) : Except Fault State :=
  let f := ftypeFmt ftype
  let N := ftypeSize ftype
  let fpcr := s.fpcr.toNat
  let intsize := if sf then 64 else 32
  let fbits := 64 - scale
  let unsigned := opcode % 2 = 1
  if opcode / 2 = 1 then
    let x := (s.readZR rn).toNat % 2 ^ intsize
    let o := fixedToFPF f fpcr unsigned (roundingMode fpcr) intsize fbits x
    fpCommit s o.2 (s.setScalar rd N (s.mergeBase rd) o.1)
  else
    let o := fpToFixedF f fpcr unsigned .rz intsize fbits (s.getV rn N)
    fpCommit s o.2 (s.writeZR rd (BitVec.ofNat 64 o.1))

/-! ## Loads and stores -/

/-- `Exec.baseAddr`: `X[n]`, or `SP` for `n = 31` after `CheckSPAlignment()`. -/
def baseAddr (s : State) (rn : Nat) : Except Fault W64 :=
  if rn = 31 then
    if s.sp.toNat % 16 = 0 then .ok s.sp else .error (.spMisaligned s.sp.toNat)
  else .ok (s.regs rn)

/-- `Exec.memIndexed`. -/
def memIndexed (s : State) (rn : Nat) (offset : W64) (postindex wback : Bool)
    (access : State → W64 → Except Fault State) : Except Fault State :=
  match baseAddr s rn with
  | .error e => .error e
  | .ok base =>
    let addr := if postindex then base else base + offset
    match access s addr with
    | .error e => .error e
    | .ok s' => .ok (if wback then s'.writeSP rn (base + offset) else s')

/-- `Exec.memVPair`. -/
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

/-- The number of registers (`selem`) of LD2–LD4/ST2–ST4 by `opcode`. -/
def selemOf (opcode : Nat) : Nat := if opcode = 0b0000 then 4 else if opcode = 0b0100 then 3 else 2

/-- Load `selem` interleaved registers of `ds` bits from the block at `addr`. -/
def ldStructRegs (s : State) (rt esize ds blk : Nat) : Nat → Nat → State
  | 0, _ => s
  | k + 1, selem => (ldStructRegs s rt esize ds blk k selem).setV ((rt + k) % 32) ds
      (deinterleave esize ds selem blk k)

def ldstStruct (s : State) (Q L : Bool) (opcode size : Nat) (post : Bool) (rm rn rt : Nat) :
    Except Fault State :=
  let ds := dsize Q
  let e := esizeOf size
  let selem := selemOf opcode
  let total := selem * (ds / 8)
  let offset : W64 := if rm = 31 then BitVec.ofNat 64 total else s.regs rm
  memIndexed s rn offset true post fun s a =>
    if L then
      match load s.mem a.toNat total with
      | .error err => .error err
      | .ok blk => .ok (ldStructRegs s rt e ds blk selem selem)
    else
      match store s.mem a.toNat total (interleave e ds selem fun j => s.getV ((rt + j) % 32) ds) with
      | .error err => .error err
      | .ok m => .ok { s with mem := m }

def ldstNP (s : State) (opc : Nat) (L : Bool) (imm7 rt2 rn rt : Nat) : Except Fault State :=
  -- `scale = 2 + UInt(opc); offset = LSL(SignExtend(imm7, 64), scale)`, no writeback
  let offset := (BitVec.ofNat 7 imm7).signExtend 64 <<< (2 + opc)
  memIndexed s rn offset false false fun s a => memVPair s L (4 * 2 ^ opc) rt rt2 a

end NeonExec

open NeonExec in
/-- Execute a decoded `NeonInstr` (the `exec` of `Instr.neon`); `pc` advances by 4. -/
def execNeon (i : NeonInstr) (s : State) : Except Fault State :=
  let r : Except Fault State :=
    match i with
    | .threeSame Q U size rm opcode rn rd => threeSame s Q U size rm opcode rn rd
    | .sThreeSame U size rm opcode rn rd => sThreeSame s U size rm opcode rn rd
    | .threeDiff Q U size rm opcode rn rd => threeDiff s Q U size rm opcode rn rd
    | .sThreeDiff U size rm opcode rn rd => sThreeDiff s U size rm opcode rn rd
    | .twoMisc Q U size opcode rn rd => twoMisc s Q U size opcode rn rd
    | .sTwoMisc U size opcode rn rd => sTwoMisc s U size opcode rn rd
    | .across Q U size opcode rn rd => across s Q U size opcode rn rd
    | .sPairwise U size opcode rn rd => sPairwise s U size opcode rn rd
    | .shiftImm Q U immh immb opcode rn rd => shiftImm s Q U immh immb opcode rn rd
    | .sShiftImm U immh immb opcode rn rd => sShiftImm s U immh immb opcode rn rd
    | .byElem Q U size L M rm opcode H rn rd => byElem s Q U size L M rm opcode H rn rd
    | .sByElem U size L M rm opcode H rn rd => sByElem s U size L M rm opcode H rn rd
    | .ldstStruct Q L opcode size post rm rn rt => ldstStruct s Q L opcode size post rm rn rt
    | .ldstNP opc L imm7 rt2 rn rt => ldstNP s opc L imm7 rt2 rn rt
    | .fpCvtFixed sf ftype _ opcode scale rn rd => fpCvtFixed s sf ftype opcode scale rn rd
  match r with
  | .error e => .error e
  | .ok s' => .ok { s' with pc := s'.pc + 4 }

end Janus.Arm64
