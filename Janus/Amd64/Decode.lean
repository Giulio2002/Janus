import Janus.Amd64.Instr

/-!
# x86-64 decoder for the supported subset

`decode bytes` reads one instruction from the start of `bytes` (the code at `RIP`) and returns
it with its length, or `none` when the bytes are outside the supported subset **or** are an
encoding the hardware treats differently from what we would model. Rejecting is always safe
(execution stops with `Fault.undecodable`); accepting an encoding with a different meaning
would be unsound. Sources: Intel SDM Vol. 2, chapter 2 (instruction format, REX, ModRM/SIB
tables 2-1..2-3) and the opcode maps of appendix A, cross-checked against
`golang.org/x/arch/x86/x86asm` and the native oracle (`docs/ORACLE-AMD64.md`).

Prefix policy (strict):
* Legacy prefixes `66` (operand size), `F2`/`F3` (only where they select an instruction:
  `PAUSE`, `POPCNT`, `TZCNT`, `LZCNT`, `MOVDQU`, `MOVQ`), and the null segment overrides
  `26`/`2E`/`36`/`3E` (ignored in 64-bit mode; not accepted on branches, where they are hints
  or CET `NOTRACK`). At most one of each group (`66` may repeat).
* `F0` (`LOCK`), `64`/`65` (`FS`/`GS`), `67` (address size) are rejected.
* `REX` (`40`–`4F`) must immediately precede the opcode; a `REX` followed by another prefix
  (which hardware silently ignores) is rejected, as is a second `REX`.
* `VEX`/`EVEX`/`XOP` (`C4`, `C5`, `62`, `8F` with `reg ≠ 0`) are rejected.
* Instructions longer than 15 bytes are rejected (`#GP` on hardware).
* `66` on near branches, `CALL`, `RET`, `PUSH`, `POP`, `LEAVE` is rejected (it changes the
  operand size differently on Intel and AMD).

Everything is plain `Nat` arithmetic, `if`, `match` on lists, and two structurally recursive
helpers (`readLE`, `parsePrefixes`), so `decide`, `rfl` and `simp` evaluate the decoder on
literal bytes.
-/

namespace Janus.Amd64

namespace Decode

/-- Little-endian unsigned value of the first `k` bytes, and the rest. -/
def readLE : Nat → List Nat → Option (Nat × List Nat)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    match readLE k bs with
    | some (v, r) => some (b + 256 * v, r)
    | none => none

/-- Sign-extend the `n`-bit value `v` (`< 2^n`) to `m ≥ n` bits. -/
def sext (n m v : Nat) : Nat := if v ≥ 2 ^ (n - 1) then v + 2 ^ m - 2 ^ n else v

structure Prefixes where
  /-- `66` seen. -/
  opsize : Bool := false
  /-- `0`, or the last of `F2`/`F3`. -/
  rep : Nat := 0
  /-- A null segment override (`26`/`2E`/`36`/`3E`) seen. -/
  seg : Bool := false
  /-- The low nibble `WRXB` of the REX prefix, if any. -/
  rex : Option Nat := none
deriving Repr, DecidableEq, Inhabited

/-- Parse legacy prefixes and REX. Returns the prefixes, the bytes from the opcode on, and
the number of prefix bytes. -/
def parsePrefixes : List Nat → Prefixes → Nat → Option (Prefixes × List Nat × Nat)
  | [], _, _ => none
  | b :: rest, p, n =>
    if b = 0x66 then
      if p.rex.isSome then none else parsePrefixes rest { p with opsize := true } (n + 1)
    else if b = 0xF2 ∨ b = 0xF3 then
      if p.rep ≠ 0 ∨ p.rex.isSome then none else parsePrefixes rest { p with rep := b } (n + 1)
    else if b = 0x26 ∨ b = 0x2E ∨ b = 0x36 ∨ b = 0x3E then
      if p.seg ∨ p.rex.isSome then none else parsePrefixes rest { p with seg := true } (n + 1)
    else if 0x40 ≤ b ∧ b < 0x50 then
      if p.rex.isSome then none else parsePrefixes rest { p with rex := some (b - 0x40) } (n + 1)
    else some (p, b :: rest, n)

/-- The decoded `r/m` operand of a ModRM byte. -/
inductive RM where
  | r (n : Nat)
  | m (a : Addr)
deriving Repr, DecidableEq, Inhabited

/-- `disp8` (`mod = 01`), `disp32` (`mod = 10`) or none (`mod = 00`), sign-extended to 64
bits, with the number of bytes read. -/
def disp (md : Nat) (bs : List Nat) : Option (Nat × List Nat × Nat) :=
  if md = 1 then
    match readLE 1 bs with
    | some (d, r) => some (sext 8 64 d, r, 1)
    | none => none
  else if md = 2 then
    match readLE 4 bs with
    | some (d, r) => some (sext 32 64 d, r, 4)
    | none => none
  else some (0, bs, 0)

structure ModRM where
  md : Nat
  /-- `reg` field with `REX.R`. -/
  reg : Nat
  /-- raw 3-bit `reg` field (opcode extension). -/
  ext : Nat
  rm : RM
deriving Repr, DecidableEq, Inhabited

/-- Decode ModRM (+ SIB + displacement) with the REX bits `rex = WRXB`. Returns the fields,
the remaining bytes and the number of bytes consumed. SDM Vol. 2, tables 2-2 and 2-3, and
§2.2.1.2/§2.2.1.6: in 64-bit mode `mod = 00, r/m = 101` is `[RIP + disp32]` (independently of
`REX.B`); `SIB.base = 101` with `mod = 00` is `[disp32]` without base (also for `REX.B = 1`);
`SIB.index = 100` without `REX.X` means no index. -/
def modrm (rex : Nat) : List Nat → Option (ModRM × List Nat × Nat)
  | [] => none
  | m :: rest =>
    let rexR := (rex / 4) % 2
    let rexX := (rex / 2) % 2
    let rexB := rex % 2
    let md := m / 64
    let ext := (m / 8) % 8
    let reg := ext + 8 * rexR
    let rm := m % 8
    if md = 3 then some (⟨md, reg, ext, .r (rm + 8 * rexB)⟩, rest, 1)
    else if rm = 4 then
      match rest with
      | [] => none
      | sib :: rest2 =>
        let sc := sib / 64
        let idx := (sib / 8) % 8 + 8 * rexX
        let index := if idx = 4 then none else some idx
        let bs := sib % 8
        if bs = 5 ∧ md = 0 then
          match readLE 4 rest2 with
          | some (d, r3) =>
            some (⟨md, reg, ext, .m ⟨none, index, sc, sext 32 64 d, false⟩⟩, r3, 6)
          | none => none
        else
          match disp md rest2 with
          | some (d, r3, k) =>
            some (⟨md, reg, ext, .m ⟨some (bs + 8 * rexB), index, sc, d, false⟩⟩, r3, 2 + k)
          | none => none
    else if rm = 5 ∧ md = 0 then
      match readLE 4 rest with
      | some (d, r3) => some (⟨md, reg, ext, .m ⟨none, none, 0, sext 32 64 d, true⟩⟩, r3, 5)
      | none => none
    else
      match disp md rest with
      | some (d, r3, k) => some (⟨md, reg, ext, .m ⟨some (rm + 8 * rexB), none, 0, d, false⟩⟩, r3, 1 + k)
      | none => none

/-- An 8-bit register operand: without a REX prefix, numbers 4–7 are `AH CH DH BH`. -/
def reg8 (rexPresent : Bool) (n : Nat) : Loc :=
  if !rexPresent && 4 ≤ n && n < 8 then .high (n - 4) else .reg n

/-- The `r/m` operand as a general location at width `w`. -/
def rmLoc (rexPresent : Bool) (w : Nat) : RM → Loc
  | .r n => if w = 8 then reg8 rexPresent n else .reg n
  | .m a => .mem a

/-- The `reg` operand as a general location at width `w`. -/
def regLoc (rexPresent : Bool) (w : Nat) (n : Nat) : Loc :=
  if w = 8 then reg8 rexPresent n else .reg n

def rmX : RM → XLoc
  | .r n => .xmm n
  | .m a => .mem a

/-- Immediate of an instruction with operand size `w`: `imm8` for `w = 8`, `imm16` for 16,
`imm32` for 32, and `imm32` sign-extended to 64 bits for 64 (`Iz`). -/
def immZ (w : Nat) (bs : List Nat) : Option (Nat × List Nat × Nat) :=
  let k := if w = 8 then 1 else if w = 16 then 2 else 4
  match readLE k bs with
  | some (v, r) => some (if w = 64 then sext 32 64 v else v, r, k)
  | none => none

/-- `imm8` sign-extended to the operand size `w` (`Ib` of `83`, `6B`, `6A`). -/
def immB (w : Nat) (bs : List Nat) : Option (Nat × List Nat × Nat) :=
  match readLE 1 bs with
  | some (v, r) => some (sext 8 w v, r, 1)
  | none => none

/-- `imm8` unsigned (shift counts, `BT` offsets, `SHLD`/`SHRD` counts, 8-bit operands). -/
def immU8 (bs : List Nat) : Option (Nat × List Nat × Nat) :=
  match readLE 1 bs with
  | some (v, r) => some (v, r, 1)
  | none => none

/-- Group-1 operation from the 3-bit field. -/
def aluOp (n : Nat) : AluOp :=
  if n = 0 then .add else if n = 1 then .or else if n = 2 then .adc else if n = 3 then .sbb
  else if n = 4 then .and else if n = 5 then .sub else if n = 6 then .xor else .cmp

/-- Group-2 operation from the 3-bit field (`RCL`, `RCR` and the `/6` alias are rejected). -/
def shOp (n : Nat) : Option ShOp :=
  if n = 0 then some .rol else if n = 1 then some .ror else if n = 4 then some .shl
  else if n = 5 then some .shr else if n = 7 then some .sar else none

/-- What a decoded instruction tolerates in its prefixes. -/
inductive PrefixClass where
  /-- ordinary integer instruction: `66` selects 16-bit, null segments ok, no `F2`/`F3`. -/
  | int
  /-- fixed-size or control-transfer instruction: no `66`, no `F2`/`F3`, no segment. -/
  | fixed
  /-- the instruction's own mandatory-prefix rules were already applied. -/
  | own
deriving DecidableEq

/-- Check prefixes and total length (`≤ 15`) and package the result. -/
def finish (p : Prefixes) (cls : PrefixClass) (i : Instr) (len : Nat) : Option (Instr × Nat) :=
  if len > 15 then none else
  match cls with
  | .int => if p.rep = 0 then some (i, len) else none
  | .fixed => if p.rep = 0 ∧ !p.opsize ∧ !p.seg then some (i, len) else none
  | .own => some (i, len)

/-- One-byte opcode map (no `0F` escape). `n` is the number of bytes before the opcode. -/
def oneByte (p : Prefixes) (op : Nat) (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let rex := p.rex.getD 0
  let rexP := p.rex.isSome
  let rexW := rex / 8 = 1
  let rexB := rex % 2
  let osz := if rexW then 64 else if p.opsize then 16 else 32
  -- ModRM-based helper: decode ModRM and continue with `k`.
  let withModRM (k : ModRM → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match modrm rex bs with
    | some (m, r, c) => k m r (n + 1 + c)
    | none => none
  if op < 0x40 ∧ op % 8 < 6 then
    -- ALU: 00-05 ADD, 08 OR, 10 ADC, 18 SBB, 20 AND, 28 SUB, 30 XOR, 38 CMP
    let a := aluOp (op / 8)
    let form := op % 8
    if form = 4 then
      match immU8 bs with
      | some (v, _, c) => finish p .int (.alu a 8 (.reg 0) (.imm v)) (n + 1 + c)
      | none => none
    else if form = 5 then
      match immZ osz bs with
      | some (v, _, c) => finish p .int (.alu a osz (.reg 0) (.imm v)) (n + 1 + c)
      | none => none
    else
      let w := if form % 2 = 0 then 8 else osz
      withModRM fun m _ len =>
        if form < 2 then finish p .int (.alu a w (rmLoc rexP w m.rm) (.loc (regLoc rexP w m.reg))) len
        else finish p .int (.alu a w (regLoc rexP w m.reg) (.loc (rmLoc rexP w m.rm))) len
  else if 0x50 ≤ op ∧ op < 0x58 then
    finish p .fixed (.push (.loc (.reg (op - 0x50 + 8 * rexB)))) (n + 1)
  else if 0x58 ≤ op ∧ op < 0x60 then
    finish p .fixed (.pop (op - 0x58 + 8 * rexB)) (n + 1)
  else if op = 0x63 then
    -- MOVSXD r64, r/m32 (only with REX.W; without it the encoding is a discouraged MOV)
    if !rexW then none else
    withModRM fun m _ len => finish p .int (.movx true 64 32 m.reg (rmLoc rexP 32 m.rm)) len
  else if op = 0x68 then
    match readLE 4 bs with
    | some (v, _) => finish p .fixed (.push (.imm (sext 32 64 v))) (n + 5)
    | none => none
  else if op = 0x6A then
    match readLE 1 bs with
    | some (v, _) => finish p .fixed (.push (.imm (sext 8 64 v))) (n + 2)
    | none => none
  else if op = 0x69 ∨ op = 0x6B then
    withModRM fun m r len =>
      match (if op = 0x69 then immZ osz r else immB osz r) with
      | some (v, _, c) => finish p .int (.imul osz m.reg (rmLoc rexP osz m.rm) (.imm v)) (len + c)
      | none => none
  else if 0x70 ≤ op ∧ op < 0x80 then
    match readLE 1 bs with
    | some (v, _) => finish p .fixed (.jcc (op - 0x70) (sext 8 64 v)) (n + 2)
    | none => none
  else if op = 0x80 ∨ op = 0x81 ∨ op = 0x83 then
    let w := if op = 0x80 then 8 else osz
    withModRM fun m r len =>
      let im := if op = 0x81 then immZ w r else if op = 0x80 then immU8 r else immB w r
      match im with
      | some (v, _, c) => finish p .int (.alu (aluOp m.ext) w (rmLoc rexP w m.rm) (.imm v)) (len + c)
      | none => none
  else if op = 0x84 ∨ op = 0x85 then
    let w := if op = 0x84 then 8 else osz
    withModRM fun m _ len => finish p .int (.test w (rmLoc rexP w m.rm) (.loc (regLoc rexP w m.reg))) len
  else if op = 0x86 ∨ op = 0x87 then
    let w := if op = 0x86 then 8 else osz
    withModRM fun m _ len => finish p .int (.xchg w (rmLoc rexP w m.rm) (regLoc rexP w m.reg)) len
  else if 0x88 ≤ op ∧ op ≤ 0x8B then
    let w := if op % 2 = 0 then 8 else osz
    withModRM fun m _ len =>
      if op < 0x8A then finish p .int (.mov w (rmLoc rexP w m.rm) (.loc (regLoc rexP w m.reg))) len
      else finish p .int (.mov w (regLoc rexP w m.reg) (.loc (rmLoc rexP w m.rm))) len
  else if op = 0x8D then
    withModRM fun m _ len =>
      match m.rm with
      | .m a => finish p .int (.lea osz m.reg a) len
      | .r _ => none
  else if op = 0x8F then
    -- POP r/m64: only the register form (`/0`, mod = 11); `/1..7` is XOP.
    withModRM fun m _ len =>
      match m.rm with
      | .r r => if m.ext = 0 then finish p .fixed (.pop r) len else none
      | .m _ => none
  else if op = 0x90 ∧ rexB = 0 then
    -- NOP (any operand size, including REX.W) / PAUSE (F3 90)
    if p.rep = 0xF2 then none else finish p .own .nop (n + 1)
  else if 0x90 ≤ op ∧ op < 0x98 then
    finish p .int (.xchg osz (.reg 0) (.reg (op - 0x90 + 8 * rexB))) (n + 1)
  else if op = 0x98 then finish p .int (.cbw osz) (n + 1)
  else if op = 0x99 then finish p .int (.cwd osz) (n + 1)
  else if op = 0xA8 then
    match immU8 bs with
    | some (v, _, c) => finish p .int (.test 8 (.reg 0) (.imm v)) (n + 1 + c)
    | none => none
  else if op = 0xA9 then
    match immZ osz bs with
    | some (v, _, c) => finish p .int (.test osz (.reg 0) (.imm v)) (n + 1 + c)
    | none => none
  else if 0xB0 ≤ op ∧ op < 0xB8 then
    match immU8 bs with
    | some (v, _, c) => finish p .int (.mov 8 (reg8 rexP (op - 0xB0 + 8 * rexB)) (.imm v)) (n + 1 + c)
    | none => none
  else if 0xB8 ≤ op ∧ op < 0xC0 then
    let k := if osz = 64 then 8 else if osz = 16 then 2 else 4
    match readLE k bs with
    | some (v, _) => finish p .int (.mov osz (.reg (op - 0xB8 + 8 * rexB)) (.imm v)) (n + 1 + k)
    | none => none
  else if op = 0xC0 ∨ op = 0xC1 ∨ (0xD0 ≤ op ∧ op ≤ 0xD3) then
    let w := if op % 2 = 0 then 8 else osz
    withModRM fun m r len =>
      match shOp m.ext with
      | none => none
      | some s =>
        let dst := rmLoc rexP w m.rm
        if op = 0xC0 ∨ op = 0xC1 then
          match immU8 r with
          | some (v, _, c) => finish p .int (.shift s w dst (.imm v)) (len + c)
          | none => none
        else if op = 0xD0 ∨ op = 0xD1 then finish p .int (.shift s w dst (.imm 1)) len
        else finish p .int (.shift s w dst (.loc (.reg 1))) len
  else if op = 0xC2 then
    match readLE 2 bs with
    | some (v, _) => finish p .fixed (.ret v) (n + 3)
    | none => none
  else if op = 0xC3 then finish p .fixed (.ret 0) (n + 1)
  else if op = 0xC6 ∨ op = 0xC7 then
    let w := if op = 0xC6 then 8 else osz
    withModRM fun m r len =>
      if m.ext ≠ 0 then none else
      match (if w = 8 then immU8 r else immZ w r) with
      | some (v, _, c) => finish p .int (.mov w (rmLoc rexP w m.rm) (.imm v)) (len + c)
      | none => none
  else if op = 0xC9 then finish p .fixed .leave (n + 1)
  else if op = 0xE8 ∨ op = 0xE9 then
    match readLE 4 bs with
    | some (v, _) =>
      finish p .fixed (if op = 0xE8 then .call (sext 32 64 v) else .jmp (sext 32 64 v)) (n + 5)
    | none => none
  else if op = 0xEB then
    match readLE 1 bs with
    | some (v, _) => finish p .fixed (.jmp (sext 8 64 v)) (n + 2)
    | none => none
  else if op = 0xF5 then finish p .int (.flagOp .cmc) (n + 1)
  else if op = 0xF8 then finish p .int (.flagOp .clc) (n + 1)
  else if op = 0xF9 then finish p .int (.flagOp .stc) (n + 1)
  else if op = 0xF6 ∨ op = 0xF7 then
    let w := if op = 0xF6 then 8 else osz
    withModRM fun m r len =>
      let dst := rmLoc rexP w m.rm
      if m.ext = 0 then
        match (if w = 8 then immU8 r else immZ w r) with
        | some (v, _, c) => finish p .int (.test w dst (.imm v)) (len + c)
        | none => none
      else if m.ext = 1 then none
      else if m.ext = 2 then finish p .int (.unary .not w dst) len
      else if m.ext = 3 then finish p .int (.unary .neg w dst) len
      else if m.ext = 4 then finish p .int (.mul1 false w dst) len
      else if m.ext = 5 then finish p .int (.mul1 true w dst) len
      else if m.ext = 6 then finish p .int (.div false w dst) len
      else finish p .int (.div true w dst) len
  else if op = 0xFE then
    withModRM fun m _ len =>
      if m.ext = 0 then finish p .int (.unary .inc 8 (rmLoc rexP 8 m.rm)) len
      else if m.ext = 1 then finish p .int (.unary .dec 8 (rmLoc rexP 8 m.rm)) len
      else none
  else if op = 0xFF then
    withModRM fun m _ len =>
      if m.ext = 0 then finish p .int (.unary .inc osz (rmLoc rexP osz m.rm)) len
      else if m.ext = 1 then finish p .int (.unary .dec osz (rmLoc rexP osz m.rm)) len
      else if m.ext = 2 then finish p .fixed (.callInd (rmLoc rexP 64 m.rm)) len
      else if m.ext = 4 then finish p .fixed (.jmpInd (rmLoc rexP 64 m.rm)) len
      else if m.ext = 6 then finish p .fixed (.push (.loc (rmLoc rexP 64 m.rm))) len
      else none
  else none

/-- Two-byte opcode map (`0F xx`). `n` counts the bytes before `xx`. -/
def twoByte (p : Prefixes) (op : Nat) (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let rex := p.rex.getD 0
  let rexP := p.rex.isSome
  let rexW := rex / 8 = 1
  let rexB := rex % 2
  let osz := if rexW then 64 else if p.opsize then 16 else 32
  let withModRM (k : ModRM → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match modrm rex bs with
    | some (m, r, c) => k m r (n + 1 + c)
    | none => none
  -- mandatory-prefix selector for SSE: 0 none, 1 = 66, 2 = F3, 3 = F2, 4 = invalid mix
  let sel := if p.opsize ∧ p.rep ≠ 0 then 4 else if p.opsize then 1 else if p.rep = 0xF3 then 2
    else if p.rep = 0xF2 then 3 else 0
  let fin (i : Instr) (len : Nat) : Option (Instr × Nat) := finish p .own i len
  if op = 0x10 ∨ op = 0x11 ∨ op = 0x28 ∨ op = 0x29 then
    -- MOVUPS/MOVUPD (10/11), MOVAPS/MOVAPD (28/29)
    if sel > 1 then none else
    withModRM fun m _ len =>
      let al := op = 0x28 ∨ op = 0x29
      if op % 2 = 0 then fin (.sseMov al (.xmm m.reg) (rmX m.rm)) len
      else fin (.sseMov al (rmX m.rm) (.xmm m.reg)) len
  else if op = 0x6F ∨ op = 0x7F then
    -- MOVDQA (66) / MOVDQU (F3); the no-prefix form is MMX
    if sel ≠ 1 ∧ sel ≠ 2 then none else
    withModRM fun m _ len =>
      let al := sel = 1
      if op = 0x6F then fin (.sseMov al (.xmm m.reg) (rmX m.rm)) len
      else fin (.sseMov al (rmX m.rm) (.xmm m.reg)) len
  else if op = 0x57 ∨ op = 0xEF then
    -- XORPS (0F 57), XORPD (66 0F 57), PXOR (66 0F EF; 0F EF is MMX)
    if sel > 1 ∨ (op = 0xEF ∧ sel ≠ 1) then none else
    withModRM fun m _ len => fin (.sseOp .xor m.reg (rmX m.rm)) len
  else if op = 0x6E then
    if sel ≠ 1 then none else
    withModRM fun m _ len => fin (.movdq (if rexW then 64 else 32) true m.reg (rmLoc rexP 64 m.rm)) len
  else if op = 0x7E then
    if sel = 1 then
      withModRM fun m _ len => fin (.movdq (if rexW then 64 else 32) false m.reg (rmLoc rexP 64 m.rm)) len
    else if sel = 2 then
      withModRM fun m _ len => fin (.movq (.xmm m.reg) (rmX m.rm)) len
    else none
  else if op = 0xD6 then
    if sel ≠ 1 then none else
    withModRM fun m _ len => fin (.movq (rmX m.rm) (.xmm m.reg)) len
  else if op = 0x1F then
    -- NOP r/m (`/0`), no memory access
    if sel > 1 then none else
    withModRM fun m _ len => if m.ext = 0 then finish p .int .nop len else none
  else if 0x40 ≤ op ∧ op < 0x50 then
    withModRM fun m _ len => finish p .int (.cmov (op - 0x40) osz m.reg (rmLoc rexP osz m.rm)) len
  else if 0x80 ≤ op ∧ op < 0x90 then
    match readLE 4 bs with
    | some (v, _) => finish p .fixed (.jcc (op - 0x80) (sext 32 64 v)) (n + 5)
    | none => none
  else if 0x90 ≤ op ∧ op < 0xA0 then
    withModRM fun m _ len =>
      if m.ext = 0 then finish p .int (.setcc (op - 0x90) (rmLoc rexP 8 m.rm)) len else none
  else if op = 0xA3 ∨ op = 0xAB ∨ op = 0xB3 ∨ op = 0xBB then
    -- BT/BTS/BTR/BTC r/m, r: register destination only (memory bit strings unsupported)
    let b := if op = 0xA3 then BitOp.bt else if op = 0xAB then .bts else if op = 0xB3 then .btr else .btc
    withModRM fun m _ len =>
      match m.rm with
      | .r r => finish p .int (.bit b osz (.reg r) (.loc (.reg m.reg))) len
      | .m _ => none
  else if op = 0xA4 ∨ op = 0xA5 ∨ op = 0xAC ∨ op = 0xAD then
    let left := op = 0xA4 ∨ op = 0xA5
    withModRM fun m r len =>
      if op % 2 = 0 then
        match immU8 r with
        | some (v, _, c) => finish p .int (.shd left osz (rmLoc rexP osz m.rm) m.reg (.imm v)) (len + c)
        | none => none
      else finish p .int (.shd left osz (rmLoc rexP osz m.rm) m.reg (.loc (.reg 1))) len
  else if op = 0xAF then
    withModRM fun m _ len => finish p .int (.imul osz m.reg (.reg m.reg) (.loc (rmLoc rexP osz m.rm))) len
  else if op = 0xB6 ∨ op = 0xB7 ∨ op = 0xBE ∨ op = 0xBF then
    let sw := if op % 2 = 0 then 8 else 16
    if osz ≤ sw then none else
    withModRM fun m _ len => finish p .int (.movx (op ≥ 0xBE) osz sw m.reg (rmLoc rexP sw m.rm)) len
  else if op = 0xB8 then
    -- POPCNT (F3 0F B8)
    if sel = 2 then withModRM fun m _ len => fin (.count .popcnt osz m.reg (rmLoc rexP osz m.rm)) len
    else none
  else if op = 0xBA then
    withModRM fun m r len =>
      let b := if m.ext = 4 then some BitOp.bt else if m.ext = 5 then some .bts
        else if m.ext = 6 then some .btr else if m.ext = 7 then some .btc else none
      match b, immU8 r with
      | some b, some (v, _, c) => finish p .int (.bit b osz (rmLoc rexP osz m.rm) (.imm v)) (len + c)
      | _, _ => none
  else if op = 0xBC ∨ op = 0xBD then
    let c := if sel = 2 then (if op = 0xBC then some CntOp.tzcnt else some .lzcnt)
      else if sel = 0 ∨ sel = 1 then (if op = 0xBC then some CntOp.bsf else some .bsr) else none
    match c with
    | none => none
    | some c => withModRM fun m _ len => fin (.count c osz m.reg (rmLoc rexP osz m.rm)) len
  else if 0xC8 ≤ op ∧ op < 0xD0 then
    if p.opsize then none else
    finish p .int (.bswap (if rexW then 64 else 32) (op - 0xC8 + 8 * rexB)) (n + 1)
  else none

end Decode

open Decode in
/-- Decode the instruction at the start of `bytes`: the instruction and its length in bytes.
`none` for anything outside the supported subset (see the module documentation). -/
def decode (bytes : List Nat) : Option (Instr × Nat) :=
  match parsePrefixes bytes {} 0 with
  | none => none
  | some (p, ops, n) =>
    match ops with
    | [] => none
    | op :: rest =>
      if op = 0x0F then
        match rest with
        | [] => none
        | op2 :: rest2 => twoByte p op2 rest2 (n + 1)
      else oneByte p op rest n

end Janus.Amd64
