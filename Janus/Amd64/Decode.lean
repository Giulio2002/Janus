import Janus.Amd64.Instr
import Janus.Amd64.DecodeSys
import Janus.Amd64.DecodeSSE
import Janus.Amd64.DecodeCrypto
import Janus.Amd64.DecodeAVX

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
  `PAUSE`, `POPCNT`, `TZCNT`, `LZCNT`, `MOVDQU`, `MOVQ`, `MOVSD`, `MOVSS`, `PSHUFB`, `PSIGNB`,
  the SSE scalar
  floating-point instructions (`Decode.sseFp`), and `F3` = `REP` on `MOVS`/`STOS`), and the null segment overrides `26`/`2E`/`36`/`3E` (ignored in 64-bit mode;
  not accepted on branches, where they are hints or CET `NOTRACK`). At most one of each group
  (`66` may repeat).
* `64` (`FS`) only on the integer forms whose ModRM memory operand it relocates (`MOV`, the
  ALU group, `TEST`, `MOVZX`/`MOVSX`/`MOVSXD`, `CMP`; `Decode.withFS`): their address becomes
  `FS.base + ea`. Everywhere else (`LEA`, which ignores segments, string instructions, whose
  `RDI` operand cannot be overridden, register-only forms, SSE/AVX, branches) it is rejected.
* `F0` (`LOCK`) only on the lockable read-modify-write forms with a memory destination
  (`Decode.lockable`); elsewhere it is `#UD` and rejected. It is in group 1 with `F2`/`F3`,
  so `F0` together with `F2`/`F3` (the HLE hints) is rejected.
* `65` (`GS`) and `67` (address size) are rejected.
* `REX` (`40`–`4F`) must immediately precede the opcode; a `REX` followed by another prefix
  (which hardware silently ignores) is rejected, as is a second `REX`.
* `VEX` (`C4`/`C5`) is decoded for exactly the AVX/AVX2 instructions Go's runtime and
  `internal/bytealg` use (`Decode.vexOp`): `VMOVDQU VMOVDQA VMOVNTDQ VPXOR VPAND VPOR VPCMPEQB
  VPMOVMSKB VPTEST VPBROADCASTB VZEROUPPER`, the BMI1/BMI2 general-purpose instructions (`ANDN
  BLSR BLSMSK BLSI BEXTR BZHI SHLX SHRX SARX RORX MULX PDEP PEXT`, `VEX.L0` only) and the
  scalar FMA3 instructions (`VF{,N}M{ADD,SUB}{132,213,231}{SS,SD}`, `VEX.L0` only), with every
  field the SDM reserves checked
  (`VEX.vvvv = 1111` where it is unused, `VEX.W0` for `VPBROADCASTB`, `VEX.L0` for
  `VZEROUPPER`, the register-only and memory-only forms). A VEX prefix preceded by any other
  prefix (`66 F2 F3 F0` or `REX` are `#UD`; segment overrides are rejected too) is rejected.
  `EVEX` (`62`) and `XOP` (`8F` with `reg ≠ 0`) are rejected.
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
  /-- `F0` (`LOCK`) seen. It shares prefix group 1 with `F2`/`F3`. -/
  lock : Bool := false
  /-- `64` (`FS`) seen. It shares prefix group 2 with the null segment overrides. -/
  fs : Bool := false
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
      if p.rep ≠ 0 ∨ p.lock ∨ p.rex.isSome then none
      else parsePrefixes rest { p with rep := b } (n + 1)
    else if b = 0xF0 then
      if p.rep ≠ 0 ∨ p.lock ∨ p.rex.isSome then none
      else parsePrefixes rest { p with lock := true } (n + 1)
    else if b = 0x26 ∨ b = 0x2E ∨ b = 0x36 ∨ b = 0x3E then
      if p.seg ∨ p.fs ∨ p.rex.isSome then none else parsePrefixes rest { p with seg := true } (n + 1)
    else if b = 0x64 then
      if p.seg ∨ p.fs ∨ p.rex.isSome then none else parsePrefixes rest { p with fs := true } (n + 1)
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
            some (⟨md, reg, ext, .m ⟨none, index, sc, sext 32 64 d, false, false⟩⟩, r3, 6)
          | none => none
        else
          match disp md rest2 with
          | some (d, r3, k) =>
            some (⟨md, reg, ext, .m ⟨some (bs + 8 * rexB), index, sc, d, false, false⟩⟩, r3, 2 + k)
          | none => none
    else if rm = 5 ∧ md = 0 then
      match readLE 4 rest with
      | some (d, r3) => some (⟨md, reg, ext, .m ⟨none, none, 0, sext 32 64 d, true, false⟩⟩, r3, 5)
      | none => none
    else
      match disp md rest with
      | some (d, r3, k) => some (⟨md, reg, ext, .m ⟨some (rm + 8 * rexB), none, 0, d, false, false⟩⟩, r3, 1 + k)
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
  | .fixed => if p.rep = 0 ∧ !p.opsize ∧ !p.seg ∧ !p.fs then some (i, len) else none
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
  else if op = 0xA4 ∨ op = 0xA5 ∨ op = 0xAA ∨ op = 0xAB then
    -- MOVS (A4/A5), STOS (AA/AB); `F3` = REP. `F2` (REPNE, which hardware treats as REP
    -- here) and segment overrides are rejected; the address size is always 64.
    if p.rep = 0xF2 ∨ p.seg then none else
    let w := if op % 2 = 0 then 8 else osz
    let rp := p.rep = 0xF3
    finish p .own (if op < 0xA8 then .movs rp w else .stos rp w) (n + 1)
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
      -- RCL (/2) and RCR (/3) at 32/64 bits
      let rc : Option Bool := if (m.ext = 2 ∨ m.ext = 3) ∧ (w = 32 ∨ w = 64) then some (m.ext = 2) else none
      match rc with
      | some left =>
        let dst := rmLoc rexP w m.rm
        if op = 0xC0 ∨ op = 0xC1 then
          match immU8 r with
          | some (v, _, c) => finish p .int (.rcx left w dst (.imm v)) (len + c)
          | none => none
        else if op = 0xD0 ∨ op = 0xD1 then finish p .int (.rcx left w dst (.imm 1)) len
        else finish p .int (.rcx left w dst (.loc (.reg 1))) len
      | none =>
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
  else if op = 0xFC then finish p .fixed (.setDF false) (n + 1)
  else if op = 0xFD then finish p .fixed (.setDF true) (n + 1)
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

/-- The SSE scalar floating-point encodings of the two-byte map (and `66 0F 3A 0A/0B`,
`ROUNDSS`/`ROUNDSD`), with their mandatory prefix (`sel`: 1 = `66`, 2 = `F3`, 3 = `F2`):
`F2/F3 0F 51 58 59 5C 5D 5E 5F` (`SQRT ADD MUL SUB MIN DIV MAX`), `(66) 0F 2E/2F`
(`UCOMIS`/`COMIS`), `F2/F3 0F 2A` (`CVTSI2SD/SS`, `REX.W` = 64-bit source), `F2/F3 0F 2C/2D`
(`CVTTSD2SI`, `CVTSD2SI`, ..., `REX.W` = 64-bit destination), `F2/F3 0F 5A`
(`CVTSD2SS`/`CVTSS2SD`), `F2/F3 0F C2 ib` (`CMPSD/SS`, predicates 0–7), `(66) 0F 54/55/56`
(`AND(N)PS/PD`, `ORPS/PD`). `REX.W` is rejected where it selects nothing; the packed forms
(no prefix or `66` on the arithmetic opcodes), the MMX conversions and the reserved
immediate bits (`CMPSD` `imm8 ≥ 8`, `ROUNDSD` `imm8 ≥ 16`) are rejected. `n` counts the bytes
before `op`. -/
def sseFp (p : Prefixes) (op : Nat) (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let rex := p.rex.getD 0
  let rexP := p.rex.isSome
  let rexW := rex / 8 = 1
  let withModRM (k : ModRM → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match modrm rex bs with
    | some (m, r, c) => k m r (n + 1 + c)
    | none => none
  let sel := if p.opsize ∧ p.rep ≠ 0 then 4 else if p.opsize then 1 else if p.rep = 0xF3 then 2
    else if p.rep = 0xF2 then 3 else 0
  let fin (i : Instr) (len : Nat) : Option (Instr × Nat) := finish p .own i len
  let scalar := sel = 2 ∨ sel = 3
  let w := if sel = 3 then 64 else 32
  if op = 0x51 ∨ op = 0x58 ∨ op = 0x59 ∨ op = 0x5C ∨ op = 0x5D ∨ op = 0x5E ∨ op = 0x5F then
    if ¬ scalar ∨ rexW then none else
    let a := if op = 0x51 then FPArith.sqrt else if op = 0x58 then .add else if op = 0x59 then .mul
      else if op = 0x5C then .sub else if op = 0x5D then .min else if op = 0x5E then .div else .max
    withModRM fun m _ len => fin (.sseArith a w m.reg (rmX m.rm)) len
  else if op = 0x2E ∨ op = 0x2F then
    if sel > 1 ∨ rexW then none else
    withModRM fun m _ len => fin (.sseComi (op = 0x2F) (if sel = 1 then 64 else 32) m.reg (rmX m.rm)) len
  else if op = 0x2A then
    if ¬ scalar then none else
    let iw := if rexW then 64 else 32
    withModRM fun m _ len => fin (.cvtsi2f w iw m.reg (rmLoc rexP iw m.rm)) len
  else if op = 0x2C ∨ op = 0x2D then
    if ¬ scalar then none else
    withModRM fun m _ len => fin (.cvtf2si (op = 0x2C) w (if rexW then 64 else 32) m.reg (rmX m.rm)) len
  else if op = 0x5A then
    if ¬ scalar ∨ rexW then none else
    withModRM fun m _ len => fin (.cvtff w m.reg (rmX m.rm)) len
  else if op = 0xC2 then
    if ¬ scalar ∨ rexW then none else
    withModRM fun m r len =>
      match immU8 r with
      | some (v, _, c) => if v ≥ 8 then none else fin (.sseCmp w m.reg (rmX m.rm) v) (len + c)
      | none => none
  else if op = 0x54 ∨ op = 0x55 ∨ op = 0x56 then
    if sel > 1 ∨ rexW then none else
    withModRM fun m _ len => fin (.fpLogic (op - 0x54) m.reg (rmX m.rm)) len
  else if op = 0x3A then
    -- 66 0F 3A 0A/0B /r ib: ROUNDSS/ROUNDSD
    match bs with
    | op3 :: rest =>
      if (op3 ≠ 0x0A ∧ op3 ≠ 0x0B) ∨ sel ≠ 1 ∨ rexW then none else
      match modrm rex rest with
      | some (m, r, c) =>
        match immU8 r with
        | some (v, _, ci) =>
          if v ≥ 16 then none
          else fin (.sseRound (if op3 = 0x0B then 64 else 32) m.reg (rmX m.rm) v) (n + 2 + c + ci)
        | none => none
      | none => none
    | [] => none
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
  if (op = 0x10 ∨ op = 0x11) ∧ (sel = 2 ∨ sel = 3) then
    -- MOVSS (F3 0F 10/11), MOVSD (F2 0F 10/11)
    withModRM fun m _ len =>
      let w := if sel = 3 then 64 else 32
      if op = 0x10 then fin (.movsd w (.xmm m.reg) (rmX m.rm)) len
      else fin (.movsd w (rmX m.rm) (.xmm m.reg)) len
  else if op = 0x10 ∨ op = 0x11 ∨ op = 0x28 ∨ op = 0x29 then
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
  else if op = 0xDB ∨ op = 0xEB ∨ op = 0x74 ∨ op = 0x60 then
    -- PAND (66 0F DB), POR (66 0F EB), PCMPEQB (66 0F 74), PUNPCKLBW (66 0F 60); without 66
    -- these are MMX
    if sel ≠ 1 then none else
    let o := if op = 0xDB then SseOp.and else if op = 0xEB then .or else if op = 0x74 then .pcmpeqb
      else .punpcklbw
    withModRM fun m _ len => fin (.sseOp o m.reg (rmX m.rm)) len
  else if op = 0xD7 then
    -- PMOVMSKB r32/r64, xmm (66 0F D7, register source only)
    if sel ≠ 1 then none else
    withModRM fun m _ len =>
      match m.rm with
      | .r r => fin (.pmovmskb 128 m.reg r) len
      | .m _ => none
  else if op = 0x70 then
    -- PSHUFD xmm, xmm/m128, imm8 (66 0F 70), PSHUFLW (F2 0F 70)
    if sel ≠ 1 ∧ sel ≠ 3 then none else
    withModRM fun m r len =>
      match immU8 r with
      | some (v, _, c) =>
        fin (if sel = 1 then .pshufd m.reg (rmX m.rm) v else .pshuflw m.reg (rmX m.rm) v) (len + c)
      | none => none
  else if op = 0x18 then
    -- PREFETCHNTA/T0/T1/T2 m8 (0F 18 /0../3, memory form, no prefix); /4../7 and the
    -- register forms are reserved NOPs, rejected
    if sel ≠ 0 then none else
    withModRM fun m _ len =>
      match m.rm with
      | .m _ => if m.ext < 4 then finish p .int .nop len else none
      | .r _ => none
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
  else if op = 0xB0 ∨ op = 0xB1 ∨ op = 0xC0 ∨ op = 0xC1 then
    -- CMPXCHG (B0/B1) and XADD (C0/C1) with a memory destination (the register forms are
    -- not modelled: Go never emits them)
    let w := if op % 2 = 0 then 8 else osz
    withModRM fun m _ len =>
      match m.rm with
      | .m a =>
        let i := if op < 0xC0 then Instr.cmpxchg w (.mem a) (regLoc rexP w m.reg)
          else .xadd w (.mem a) (regLoc rexP w m.reg)
        finish p .int i len
      | .r _ => none
  else if op = 0xC7 then
    -- CMPXCHG8B / CMPXCHG16B (REX.W) m: `/1`, memory only (`mod = 11` is RDRAND/RDSEED)
    if p.opsize then none else
    withModRM fun m _ len =>
      match m.rm with
      | .m a => if m.ext = 1 then finish p .int (.cmpxchgDbl (if rexW then 128 else 64) a) len else none
      | .r _ => none
  else if op = 0xAE then
    -- LFENCE (E8), MFENCE (F0), SFENCE (F8): exactly these bytes, without any prefix (other
    -- `0F AE` forms, and these with `66`/`F2`/`F3`, are other instructions)
    match bs with
    | m :: _ =>
      if (m = 0xE8 ∨ m = 0xF0 ∨ m = 0xF8) ∧ p = {} then some (.nop, n + 2) else none
    | [] => none
  else if op = 0x1E then
    -- ENDBR64 (`F3 0F 1E FA`), exactly these bytes and no other prefix: the CET indirect-branch
    -- landing pad that C compilers put at every function entry (`-fcf-protection`). Executed,
    -- it is a NOP, with or without CET; the IBT check it satisfies belongs to the indirect
    -- branch that targets it, and Linux does not enable IBT for user space. Every other
    -- `F3 0F 1E` form (`ENDBR32`, `RDSSP`) and every other prefix combination is rejected.
    match bs with
    | m :: _ => if m = 0xFA ∧ p = { rep := 0xF3 } then some (.nop, n + 2) else none
    | [] => none
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
  else if op = 0x38 then
    -- the three-byte map `0F 38`: `PSHUFB` (`66 0F 38 00`), `PSIGNB` (`66 0F 38 08`; without
    -- `66` both are MMX), `MOVBE r, m` (`0F 38 F0`) and `MOVBE m, r` (`0F 38 F1`), memory forms
    -- only (`mod = 11` is `#UD`); `F2 0F 38 F0/F1` is `CRC32` and `F3` is reserved
    match bs with
    | [] => none
    | op3 :: rest =>
      let withModRM3 (k : ModRM → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
        match modrm rex rest with
        | some (m, r, c) => k m r (n + 2 + c)
        | none => none
      if op3 = 0x00 ∨ op3 = 0x08 then
        if sel ≠ 1 then none else
        withModRM3 fun m _ len =>
          fin (.sseOp (if op3 = 0x00 then .pshufb else .psignb) m.reg (rmX m.rm)) len
      else if op3 = 0xF0 ∨ op3 = 0xF1 then
        if p.rep ≠ 0 then none else
        withModRM3 fun m _ len =>
          match m.rm with
          | .m a =>
            finish p .int (if op3 = 0xF0 then .movbe osz (.reg m.reg) (.mem a)
              else .movbe osz (.mem a) (.reg m.reg)) len
          | .r _ => none
      else none
  else sseFp p op bs n  -- SSE scalar floating point

end Decode

namespace Decode

/-- Instructions that accept a `LOCK` prefix (SDM Vol. 2, `LOCK`): the read-modify-write
forms of `ADD ADC AND BTC BTR BTS CMPXCHG CMPXCHG8B/16B DEC INC NEG NOT OR SBB SUB XOR XADD
XCHG` with a memory destination. Anything else with `LOCK` is `#UD`. -/
def lockable : Instr → Bool
  | .alu op _ (.mem _) _ => op != .cmp
  | .unary _ _ (.mem _) => true
  | .bit op _ (.mem _) _ => op != .bt
  | .xchg _ (.mem _) _ => true
  | .xadd _ (.mem _) _ => true
  | .cmpxchg _ (.mem _) _ => true
  | .cmpxchgDbl _ _ => true
  | _ => false

/-- The memory operand (address, size in bytes) of a locked access: the `LOCK`able forms and
`XCHG` with memory. -/
def lockMem : Instr → Option (Addr × Nat)
  | .alu _ w (.mem a) _ => some (a, w / 8)
  | .unary _ w (.mem a) => some (a, w / 8)
  | .bit _ w (.mem a) _ => some (a, w / 8)
  | .xchg w (.mem a) _ => some (a, w / 8)
  | .xadd w (.mem a) _ => some (a, w / 8)
  | .cmpxchg w (.mem a) _ => some (a, w / 8)
  | .cmpxchgDbl w a => some (a, w / 8)
  | _ => none

/-- Wrap a locked access in `Instr.locked` (alignment check at execution). -/
def wrapLocked (i : Instr) : Instr :=
  match lockMem i with
  | some (a, sz) => .locked i a sz
  | none => i

end Decode

namespace Decode

/-- The `FS`-relative form of an instruction decoded after a `64` prefix: its ModRM memory
operand gets `fs := true`. Only the integer forms Go uses with `FS` (the TLS load and store
`MOVQ FS:-8, R14` / `MOVQ R14, FS:-8`, and the ALU/`TEST`/`MOVZX` forms with the same operand
shape) are accepted; anything else (including a register-only form, where `64` would be
ignored) is rejected. -/
def withFS : Instr → Option Instr
  | .mov w (.mem a) src => some (.mov w (.mem { a with fs := true }) src)
  | .mov w dst (.loc (.mem a)) => some (.mov w dst (.loc (.mem { a with fs := true })))
  | .alu op w (.mem a) src => some (.alu op w (.mem { a with fs := true }) src)
  | .alu op w dst (.loc (.mem a)) => some (.alu op w dst (.loc (.mem { a with fs := true })))
  | .test w (.mem a) src => some (.test w (.mem { a with fs := true }) src)
  | .movx sg dw sw d (.mem a) => some (.movx sg dw sw d (.mem { a with fs := true }))
  | _ => none

/-- The VEX-encoded instructions (SDM Vol. 2 §2.3). `rex` holds `W R X B` (already
un-inverted), `v` the un-inverted `VEX.vvvv`, `l` the vector length (128/256), `pp` the
implied prefix (0 none, 1 `66`, 2 `F3`, 3 `F2`), `mp` the opcode map (1 `0F`, 2 `0F38`,
3 `0F3A`), `op` the opcode, `bs` the bytes after it and `n` the bytes before it. Only the
forms listed in the module doc are accepted. -/
def vexOp (rex v l pp mp op : Nat) (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let withModRM (k : ModRM → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match modrm rex bs with
    | some (m, r, c) => k m r (n + 1 + c)
    | none => none
  let fin (i : Instr) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (i, len)
  -- operand size of the BMI/FMA forms: `VEX.W1` = 64 bits (`SD`), `W0` = 32 bits (`SS`)
  let w := if rex / 8 = 1 then 64 else 32
  let gpr : RM → Loc := fun | .r r => .reg r | .m a => .mem a
  if mp = 2 ∧ (op = 0xF2 ∨ op = 0xF3 ∨ op = 0xF5 ∨ op = 0xF6 ∨ op = 0xF7) then
    -- BMI1/BMI2 (`VEX.LZ.0F38`; `VEX.L1` is `#UD`)
    if l ≠ 128 then none
    else if op = 0xF2 then
      -- ANDN r, vvvv, r/m (no implied prefix)
      if pp ≠ 0 then none else
      withModRM fun m _ len => fin (.andn w m.reg v (gpr m.rm)) len
    else if op = 0xF3 then
      -- group 17: BLSR (/1), BLSMSK (/2), BLSI (/3) vvvv, r/m
      if pp ≠ 0 then none else
      withModRM fun m _ len =>
        if m.ext = 1 ∨ m.ext = 2 ∨ m.ext = 3 then fin (.blsx m.ext w v (gpr m.rm)) len else none
    else if op = 0xF5 then
      -- BZHI r, r/m, vvvv (none), PEXT (F3), PDEP r, vvvv, r/m (F2)
      if pp = 0 then withModRM fun m _ len => fin (.bzhi w m.reg (gpr m.rm) v) len
      else if pp = 2 then withModRM fun m _ len => fin (.pext w m.reg v (gpr m.rm)) len
      else if pp = 3 then withModRM fun m _ len => fin (.pdep w m.reg v (gpr m.rm)) len
      else none
    else if op = 0xF6 then
      -- MULX r(hi), vvvv(lo), r/m (F2)
      if pp ≠ 3 then none else
      withModRM fun m _ len => fin (.mulx w m.reg v (gpr m.rm)) len
    else
      -- BEXTR (none), SHLX (66), SARX (F3), SHRX (F2) r, r/m, vvvv
      withModRM fun m _ len =>
        if pp = 0 then fin (.bextr w m.reg (gpr m.rm) v) len
        else fin (.shiftx (if pp = 1 then .shl else if pp = 2 then .sar else .shr) w m.reg (gpr m.rm) v) len
  else if mp = 3 ∧ op = 0xF0 then
    -- RORX r, r/m, imm8 (`VEX.LZ.F2.0F3A`, `VEX.vvvv = 1111`)
    if l ≠ 128 ∨ pp ≠ 3 ∨ v ≠ 0 then none else
    withModRM fun m r len =>
      match immU8 r with
      | some (i, _, c) => fin (.rorx w m.reg (gpr m.rm) i) (len + c)
      | none => none
  else if mp = 2 ∧ pp = 1 ∧ (op / 16 = 9 ∨ op / 16 = 10 ∨ op / 16 = 11) ∧ op % 2 = 1 ∧ op % 16 ≥ 9 then
    -- FMA3 scalar: VF(N)MADD/VF(N)MSUB 132 (9x), 213 (Ax), 231 (Bx) SS/SD (x = 9 B D F):
    -- `VEX.LIG.66.0F38`; only `VEX.L0` (what compilers emit) is accepted
    if l ≠ 128 then none else
    let form := if op / 16 = 9 then 132 else if op / 16 = 10 then 213 else 231
    let k := (op % 16 - 9) / 2
    withModRM fun m _ len => fin (.vfmas w form (k ≥ 2) (k % 2 = 1) m.reg v (rmX m.rm)) len
  else if mp = 1 then
    if (op = 0x6F ∨ op = 0x7F) ∧ (pp = 1 ∨ pp = 2) then
      -- VMOVDQA (66) / VMOVDQU (F3) load (6F) and store (7F)
      if v ≠ 0 then none else
      withModRM fun m _ len =>
        if op = 0x6F then fin (.vmov (pp = 1) l (.xmm m.reg) (rmX m.rm)) len
        else fin (.vmov (pp = 1) l (rmX m.rm) (.xmm m.reg)) len
    else if op = 0xE7 ∧ pp = 1 then
      -- VMOVNTDQ m, xmm/ymm (memory destination only)
      if v ≠ 0 then none else
      withModRM fun m _ len =>
        match m.rm with
        | .m a => fin (.vmov true l (.mem a) (.xmm m.reg)) len
        | .r _ => none
    else if (op = 0xEF ∨ op = 0xDB ∨ op = 0xEB ∨ op = 0x74) ∧ pp = 1 then
      -- VPXOR, VPAND, VPOR, VPCMPEQB
      let o := if op = 0xEF then SseOp.xor else if op = 0xDB then .and else if op = 0xEB then .or
        else .pcmpeqb
      withModRM fun m _ len => fin (.vop o l m.reg v (rmX m.rm)) len
    else if op = 0xD7 ∧ pp = 1 then
      -- VPMOVMSKB r, xmm/ymm (register source only)
      if v ≠ 0 then none else
      withModRM fun m _ len =>
        match m.rm with
        | .r r => fin (.pmovmskb l m.reg r) len
        | .m _ => none
    else if op = 0x77 ∧ pp = 0 ∧ l = 128 ∧ v = 0 then
      -- VZEROUPPER (VEX.L1 is VZEROALL, not modelled); no ModRM
      fin .vzeroupper (n + 1)
    else none
  else if mp = 2 ∧ pp = 1 then
    if op = 0x17 then
      -- VPTEST
      if v ≠ 0 then none else
      withModRM fun m _ len => fin (.vptest l m.reg (rmX m.rm)) len
    else if op = 0x78 then
      -- VPBROADCASTB xmm/ymm, xmm/m8 (VEX.W0)
      if v ≠ 0 ∨ rex / 8 = 1 then none else
      withModRM fun m _ len => fin (.vpbroadcastb l m.reg (rmX m.rm)) len
    else none
  else none

/-- Decode a VEX instruction: `b0 = C5` (2-byte form: `R̄ v̄v̄v̄v̄ L pp`) or `C4` (3-byte form:
`R̄ X̄ B̄ m-mmmm`, `W v̄v̄v̄v̄ L pp`), at the very start of the instruction (no prefix). -/
def vex (b0 : Nat) (bs : List Nat) : Option (Instr × Nat) :=
  if b0 = 0xC5 then
    match bs with
    | b1 :: op :: rest =>
      let r := 1 - b1 / 128
      vexOp (4 * r) (15 - (b1 / 8) % 16) (if (b1 / 4) % 2 = 1 then 256 else 128) (b1 % 4) 1 op rest 2
    | _ => none
  else
    match bs with
    | b1 :: b2 :: op :: rest =>
      let r := 1 - b1 / 128
      let x := 1 - (b1 / 64) % 2
      let b := 1 - (b1 / 32) % 2
      let w := b2 / 128
      vexOp (8 * w + 4 * r + 2 * x + b) (15 - (b2 / 8) % 16) (if (b2 / 4) % 2 = 1 then 256 else 128)
        (b2 % 4) (b1 % 32) op rest 3
    | _ => none

end Decode

open Decode in
/-- Decode a legacy-encoded instruction (prefixes, `REX`, the one- and two-byte maps). A VEX
byte (`C4`/`C5`) after a prefix is not an opcode here and is rejected. -/
def Decode.decodeLegacy (bytes : List Nat) : Option (Instr × Nat) :=
  match parsePrefixes bytes {} 0 with
  | none => none
  | some (p, ops, n) =>
    let r := match ops with
      | [] => none
      | op :: rest =>
        if op = 0x0F then
          match rest with
          | [] => none
          | op2 :: rest2 => ((twoByte p op2 rest2 (n + 1)).orElse fun _ => DecodeSSE.decode p.opsize p.rep p.rex (fun bs => (modrm (p.rex.getD 0) bs).map fun (m, r, c) => (m.reg, m.ext, rmX m.rm, r, c)) op2 rest2 (n + 1)).orElse fun _ => DecodeCrypto.decode p.opsize p.rep p.rex (fun bs => (modrm (p.rex.getD 0) bs).map fun (m, r, c) => (m.reg, m.ext, rmX m.rm, r, c)) op2 rest2 (n + 1)
        else oneByte p op rest n
    -- `LOCK` is accepted exactly on the lockable memory forms; the model is single-threaded,
    -- so a locked instruction has the semantics of the unlocked one.
    -- a locked access (`LOCK`, or `XCHG` with memory, which is always locked) must be
    -- naturally aligned (`Instr.locked`)
    let r := if p.lock then
      match r with
      | some (i, len) => if lockable i then some (wrapLocked i, len) else none
      | none => none
    else
      match r with
      | some (.xchg w (.mem a) b, len) => some (wrapLocked (.xchg w (.mem a) b), len)
      | r => r
    -- `FS` relocates the memory operand of the forms `withFS` accepts
    if p.fs then
      match r with
      | some (i, len) =>
        match withFS i with
        | some i' => some (i', len)
        | none => none
      | none => none
    else r

open Decode in
/-- Decode the instruction at the start of `bytes`: the instruction and its length in bytes.
`none` for anything outside the supported subset (see the module documentation). -/
def decode (bytes : List Nat) : Option (Instr × Nat) :=
  -- `SYSCALL`, `CPUID`, `XGETBV`, `RDTSC(P)`, the traps, `PUSHFQ`/`POPFQ` (`Janus.Amd64.DecodeSys`)
  match decodeSys bytes with
  | some r => some r
  | none =>
  match bytes with
  | b0 :: rest0 =>
    if b0 = 0xC4 ∨ b0 = 0xC5 then (vex b0 rest0).orElse fun _ => DecodeAVX.vex (fun rex bs => (modrm rex bs).map fun (m, r, c) => (m.reg, m.ext, rmX m.rm, r, c)) b0 rest0 else decodeLegacy bytes
  | [] => none

end Janus.Amd64
