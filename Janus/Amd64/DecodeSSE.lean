import Janus.Amd64.Instr

/-!
# Decoder for the legacy-SSE packed instructions (WP-D)

`DecodeSSE.decode` is consulted by `Janus.Amd64.Decode.decodeLegacy` for a two-byte-map
instruction (`0F xx`, including the three-byte maps `0F 38 xx` and `0F 3A xx`) that the main
decoder rejects. It sees the prefixes already parsed (`66`, the last of `F2`/`F3`, `REX`), the
opcode byte after `0F`, the bytes after it, the number of bytes before it, and the main
decoder's ModRM parser (`mrm`: the `reg` field with `REX.R`, the raw 3-bit `reg` field, the
`r/m` operand as an `XLoc` whose register number is the encoding number with `REX.B`, the bytes
after ModRM/SIB/displacement, and how many bytes those took). `LOCK` and `FS` are rejected by
`decodeLegacy` for everything decoded here (`Decode.lockable`, `Decode.withFS`); null segment
overrides are ignored, as in 64-bit mode.

The mandatory prefix selects the instruction (SDM Vol. 2, appendix A): `sel` is 0 (none), 1
(`66`), 2 (`F3`), 3 (`F2`), 4 (`66` together with `F2`/`F3`). Every form not listed is rejected,
in particular: the MMX forms (the packed-integer opcodes without `66`), `66` combined with
`F2`/`F3` (except `66 F2 0F 38 F1`, the 16-bit `CRC32`), the register forms of the memory-only
moves (`MOVLPS m`..., `MOVNTDQ`, `MOVNTDQA`, `LDDQU`, `MOVNTI`) and the memory forms of the
register-only ones (`MOVHLPS`, `MOVLHPS` share their opcodes with `MOVLPS`/`MOVHPS`; the
shift-by-immediate groups, `PEXTRW 0F C5`, `MOVMSKPS/PD`), the reserved group members
(`66 0F 71 /0 /1 /3 /5 /7`, ...), reserved immediate bits (`CMPPS/PD imm8 ≥ 8`,
`ROUNDPS/PD imm8 ≥ 16`, `PCMPxSTRx imm8<7>`), `REX.W` on the 16-bit `CRC32`, and the instructions whose result is implementation-specific
(`RCPPS`, `RSQRTPS`), not modelled (`MASKMOVDQU`, `DPPS`, `DPPD`, `LDMXCSR`) or another work
package's (AES-NI, `PCLMULQDQ`, SHA). `REX.W` is ignored by hardware on the other forms (it
selects nothing; on `PINSRB`/`PINSRW` it widens only the unused part of the register source and
on `PEXTRB`/`PEXTRW` the zero-extended destination) and is accepted there, as is `66` on the
8-bit `CRC32` (`66 F2 0F 38 F0`, where the operand size selects nothing).
-/

namespace Janus.Amd64.DecodeSSE

/-- The main decoder's ModRM parser: `(reg, ext, rm, rest, consumed)` (see the module doc). -/
abbrev MRM := List Nat → Option (Nat × Nat × XLoc × List Nat × Nat)

abbrev I := SseI XLoc Loc Addr

/-- The `r/m` operand as a general location at width `w` (an 8-bit register without `REX` is
`AH`..`BH` for numbers 4–7). -/
def gpr (rexP : Bool) (w : Nat) : XLoc → Loc
  | .xmm n => if w = 8 ∧ !rexP ∧ 4 ≤ n ∧ n < 8 then .high (n - 4) else .reg n
  | .mem a => .mem a

/-- The packed-integer operation of a `66 0F xx` opcode. -/
def pint66 (op : Nat) : Option PIntOp :=
  match op with
  | 0x14 => some (.unpckl 64) | 0x15 => some (.unpckh 64)
  | 0x61 => some (.unpckl 16) | 0x62 => some (.unpckl 32) | 0x63 => some (.packss 16)
  | 0x64 => some (.cmpgt 8) | 0x65 => some (.cmpgt 16) | 0x66 => some (.cmpgt 32)
  | 0x67 => some (.packus 16) | 0x68 => some (.unpckh 8) | 0x69 => some (.unpckh 16)
  | 0x6A => some (.unpckh 32) | 0x6B => some (.packss 32) | 0x6C => some (.unpckl 64)
  | 0x6D => some (.unpckh 64) | 0x75 => some (.cmpeq 16) | 0x76 => some (.cmpeq 32)
  | 0xD1 => some (.srl 16) | 0xD2 => some (.srl 32) | 0xD3 => some (.srl 64)
  | 0xD4 => some (.add 64) | 0xD5 => some (.mull 16) | 0xD8 => some (.subus 8)
  | 0xD9 => some (.subus 16) | 0xDA => some (.minu 8) | 0xDC => some (.addus 8)
  | 0xDD => some (.addus 16) | 0xDE => some (.maxu 8) | 0xDF => some .andn
  | 0xE0 => some (.avg 8) | 0xE1 => some (.sra 16) | 0xE2 => some (.sra 32)
  | 0xE3 => some (.avg 16) | 0xE4 => some (.mulh true) | 0xE5 => some (.mulh false)
  | 0xE8 => some (.subs 8) | 0xE9 => some (.subs 16) | 0xEA => some (.mins 16)
  | 0xEC => some (.adds 8) | 0xED => some (.adds 16) | 0xEE => some (.maxs 16)
  | 0xF1 => some (.sll 16) | 0xF2 => some (.sll 32) | 0xF3 => some (.sll 64)
  | 0xF4 => some (.muldq false) | 0xF5 => some .maddwd | 0xF6 => some .sadbw
  | 0xF8 => some (.sub 8) | 0xF9 => some (.sub 16) | 0xFA => some (.sub 32)
  | 0xFB => some (.sub 64) | 0xFC => some (.add 8) | 0xFD => some (.add 16)
  | 0xFE => some (.add 32)
  | _ => none

/-- The packed-integer operation of a `66 0F 38 xx` opcode (SSSE3, SSE4.1, SSE4.2). -/
def pint38 (op : Nat) : Option PIntOp :=
  match op with
  | 0x01 => some (.hadd 16) | 0x02 => some (.hadd 32) | 0x03 => some .hadds
  | 0x04 => some .maddubsw | 0x05 => some (.hsub 16) | 0x06 => some (.hsub 32)
  | 0x07 => some .hsubs | 0x09 => some (.sign 16) | 0x0A => some (.sign 32)
  | 0x0B => some .mulhrsw | 0x1C => some (.abs 8) | 0x1D => some (.abs 16)
  | 0x1E => some (.abs 32) | 0x28 => some (.muldq true) | 0x29 => some (.cmpeq 64)
  | 0x2B => some (.packus 32) | 0x37 => some (.cmpgt 64) | 0x38 => some (.mins 8)
  | 0x39 => some (.mins 32) | 0x3A => some (.minu 16) | 0x3B => some (.minu 32)
  | 0x3C => some (.maxs 8) | 0x3D => some (.maxs 32) | 0x3E => some (.maxu 16)
  | 0x3F => some (.maxu 32) | 0x40 => some (.mull 32)
  | _ => none

/-- The packed floating-point arithmetic of `0F 51/58/59/5C/5D/5E/5F`. -/
def pfop (op : Nat) : Option PFOp :=
  match op with
  | 0x51 => some .sqrt | 0x58 => some .add | 0x59 => some .mul | 0x5C => some .sub
  | 0x5D => some .min | 0x5E => some .div | 0x5F => some .max
  | _ => none

/-- The shift group `66 0F 71/72/73 /ext ib` (register form only). -/
def shiftGroup (op ext : Nat) : Option (PShiftOp × Nat) :=
  let e := if op = 0x71 then 16 else if op = 0x72 then 32 else 64
  if ext = 2 then some (.srl, e)
  else if ext = 4 ∧ op ≠ 0x73 then some (.sra, e)
  else if ext = 6 then some (.sll, e)
  else if ext = 3 ∧ op = 0x73 then some (.srldq, 128)
  else if ext = 7 ∧ op = 0x73 then some (.slldq, 128)
  else none

/-- `imm8` after ModRM. -/
def imm8 : List Nat → Option Nat
  | b :: _ => some b
  | [] => none

/-- Decode an SSE instruction of the `0F` map (see the module doc). `n` counts the bytes before
`op` (prefixes and `0F`). -/
def decode (opsize : Bool) (rep : Nat) (rex : Option Nat) (mrm : MRM) (op : Nat)
    (bs : List Nat) (n : Nat) : Option (Instr × Nat) :=
  let rexP := rex.isSome
  let rexW := rex.getD 0 / 8 = 1
  let sel := if opsize ∧ rep ≠ 0 then 4 else if opsize then 1 else if rep = 0xF3 then 2
    else if rep = 0xF2 then 3 else 0
  let fin (i : Instr) (len : Nat) : Option (Instr × Nat) := if len > 15 then none else some (i, len)
  let sse (i : I) (len : Nat) : Option (Instr × Nat) := fin (.sse i) len
  -- ModRM directly after `op` (`k` gets reg, ext, rm, rest and the length so far)
  let m2 (k : Nat → Nat → XLoc → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    match mrm bs with
    | some (reg, ext, rm, rest, c) => k reg ext rm rest (n + 1 + c)
    | none => none
  -- ModRM then `imm8`
  let m2i (k : Nat → Nat → XLoc → Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
    m2 fun reg ext rm rest len =>
      match imm8 rest with
      | some v => k reg ext rm v (len + 1)
      | none => none
  if op = 0x38 ∨ op = 0x3A then
    match bs with
    | [] => none
    | op3 :: rest3 =>
      let m3 (k : Nat → Nat → XLoc → List Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
        match mrm rest3 with
        | some (reg, ext, rm, rest, c) => k reg ext rm rest (n + 2 + c)
        | none => none
      let m3i (k : Nat → XLoc → Nat → Nat → Option (Instr × Nat)) : Option (Instr × Nat) :=
        m3 fun reg _ rm rest len =>
          match imm8 rest with
          | some v => k reg rm v (len + 1)
          | none => none
      if op = 0x38 then
        if op3 = 0xF0 ∨ op3 = 0xF1 then
          -- CRC32 r32/r64, r/m8 (`F2 0F 38 F0`) and r/m16/32/64 (`F2 0F 38 F1`; `66 F2` = 16-bit)
          if op3 = 0xF0 then
            if sel ≠ 3 ∧ ¬ (sel = 4 ∧ rep = 0xF2) then none else
            m3 fun reg _ rm _ len => sse (.crc32 8 reg (gpr rexP 8 rm)) len
          else if sel = 3 then
            let w := if rexW then 64 else 32
            m3 fun reg _ rm _ len => sse (.crc32 w reg (gpr rexP w rm)) len
          else if sel = 4 ∧ rep = 0xF2 ∧ !rexW then
            m3 fun reg _ rm _ len => sse (.crc32 16 reg (gpr rexP 16 rm)) len
          else none
        else if sel ≠ 1 then none
        else
        match pint38 op3 with
        | some o => m3 fun reg _ rm _ len => sse (.pint o reg rm) len
        | none =>
          if op3 = 0x10 ∨ op3 = 0x14 ∨ op3 = 0x15 then
            let e := if op3 = 0x10 then 8 else if op3 = 0x14 then 32 else 64
            m3 fun reg _ rm _ len => sse (.blendv e reg rm) len
          else if op3 = 0x17 then m3 fun reg _ rm _ len => sse (.ptest reg rm) len
          else if (0x20 ≤ op3 ∧ op3 ≤ 0x25) ∨ (0x30 ≤ op3 ∧ op3 ≤ 0x35) then
            let k := op3 % 16
            let ft : Nat × Nat := if k = 0 then (8, 16) else if k = 1 then (8, 32)
              else if k = 2 then (8, 64) else if k = 3 then (16, 32) else if k = 4 then (16, 64)
              else (32, 64)
            m3 fun reg _ rm _ len => sse (.pmovx (op3 < 0x30) ft.1 ft.2 reg rm) len
          else if op3 = 0x2A then
            -- MOVNTDQA xmm, m128 (aligned load; memory only)
            m3 fun reg _ rm _ len =>
              match rm with
              | .mem a => fin (.sseMov true (.xmm reg) (.mem a)) len
              | .xmm _ => none
          else if op3 = 0x41 then m3 fun reg _ rm _ len => sse (.phminposuw reg rm) len
          else none
      else
        -- 0F 3A: every form has an imm8 and needs 66
        if sel ≠ 1 then none
        else if op3 = 0x08 ∨ op3 = 0x09 then
          m3i fun reg rm v len =>
            if v ≥ 16 then none else sse (.fpRound (if op3 = 0x08 then 32 else 64) reg rm v) len
        else if op3 = 0x0C ∨ op3 = 0x0D ∨ op3 = 0x0E ∨ op3 = 0x0F ∨ op3 = 0x42 then
          let o := if op3 = 0x0C then PImmOp.blendps else if op3 = 0x0D then .blendpd
            else if op3 = 0x0E then .pblendw else if op3 = 0x0F then .palignr else .mpsadbw
          m3i fun reg rm v len => sse (.pimm o reg rm v) len
        else if op3 = 0x14 ∨ op3 = 0x15 ∨ op3 = 0x16 ∨ op3 = 0x17 then
          -- PEXTRB r32/m8, PEXTRW r32/m16, PEXTRD/Q r/m32/64, EXTRACTPS r/m32 (`xmm` in reg)
          let e := if op3 = 0x14 then 8 else if op3 = 0x15 then 16
            else if op3 = 0x16 ∧ rexW then 64 else 32
          m3i fun reg rm v len => sse (.pextr e (gpr true 64 rm) reg v) len
        else if op3 = 0x20 ∨ op3 = 0x22 then
          -- PINSRB xmm, r32/m8, imm8; PINSRD/Q xmm, r/m32/64, imm8
          let e := if op3 = 0x20 then 8 else if rexW then 64 else 32
          m3i fun reg rm v len => sse (.pinsr e reg (gpr true 64 rm) v) len
        else if op3 = 0x21 then
          m3i fun reg rm v len =>
            match rm with
            | .xmm r => sse (.pimm .insertps reg (.xmm r) v) len
            | .mem a => sse (.insertpsM reg a v) len
        else if 0x60 ≤ op3 ∧ op3 ≤ 0x63 then
          m3i fun reg rm v len =>
            if v ≥ 128 then none
            else sse (.pcmpstr (op3 < 0x62) (op3 % 2 = 1) rexW reg rm v) len
        else none
  else
  match pfop op with
  | some o =>
    -- packed arithmetic: `0F` = PS, `66 0F` = PD (the scalar F2/F3 forms are `Decode.sseFp`)
    if sel > 1 then none else
    m2 fun reg _ rm _ len => sse (.fpArith o (if sel = 0 then 32 else 64) reg rm) len
  | none =>
  if sel = 1 then
    match pint66 op with
    | some o => m2 fun reg _ rm _ len => sse (.pint o reg rm) len
    | none =>
      if op = 0x71 ∨ op = 0x72 ∨ op = 0x73 then
        m2i fun _ ext rm v len =>
          match rm, shiftGroup op ext with
          | .xmm r, some (o, e) => sse (.pshift o e r v) len
          | _, _ => none
      else if op = 0x5A then m2 fun reg _ rm _ len => sse (.cvt .pd2ps reg rm) len
      else if op = 0x5B then m2 fun reg _ rm _ len => sse (.cvt (.ps2dq false) reg rm) len
      else if op = 0xE6 then m2 fun reg _ rm _ len => sse (.cvt (.pd2dq true) reg rm) len
      else if op = 0xC2 then
        m2i fun reg _ rm v len => if v ≥ 8 then none else sse (.fpCmp 64 reg rm v) len
      else if op = 0xC6 then m2i fun reg _ rm v len => sse (.pimm .shufpd reg rm v) len
      else if op = 0x7C ∨ op = 0x7D then
        m2 fun reg _ rm _ len => sse (.fpHorz (op = 0x7D) 64 reg rm) len
      else if op = 0xD0 then m2 fun reg _ rm _ len => sse (.fpAddsub 64 reg rm) len
      else if op = 0x12 ∨ op = 0x13 ∨ op = 0x16 ∨ op = 0x17 then
        -- MOVLPD/MOVHPD (memory only)
        m2 fun reg _ rm _ len =>
          match rm with
          | .mem a => sse (.movHalf (op ≥ 0x16) (op % 2 = 0) reg a) len
          | .xmm _ => none
      else if op = 0x2B ∨ op = 0xE7 then
        -- MOVNTPD m128, xmm; MOVNTDQ m128, xmm (aligned stores; memory only)
        m2 fun reg _ rm _ len =>
          match rm with
          | .mem a => fin (.sseMov true (.mem a) (.xmm reg)) len
          | .xmm _ => none
      else if op = 0x50 then
        m2 fun reg _ rm _ len =>
          match rm with
          | .xmm r => sse (.movmsk 64 reg r) len
          | .mem _ => none
      else if op = 0xC4 then
        -- PINSRW xmm, r32/m16, imm8
        m2i fun reg _ rm v len => sse (.pinsr 16 reg (gpr true 64 rm) v) len
      else if op = 0xC5 then
        -- PEXTRW r32, xmm, imm8 (register source only)
        m2i fun reg _ rm v len =>
          match rm with
          | .xmm r => sse (.pextr 16 (.reg reg) r v) len
          | .mem _ => none
      else none
  else if sel = 0 then
    if op = 0x14 ∨ op = 0x15 then
      m2 fun reg _ rm _ len => sse (.pint (if op = 0x14 then .unpckl 32 else .unpckh 32) reg rm) len
    else if op = 0x12 ∨ op = 0x16 then
      -- MOVLPS/MOVHPS xmm, m64; MOVHLPS/MOVLHPS xmm, xmm
      m2 fun reg _ rm _ len =>
        match rm with
        | .mem a => sse (.movHalf (op = 0x16) true reg a) len
        | .xmm r => sse (.pint (if op = 0x12 then .movhl else .unpckl 64) reg (.xmm r)) len
    else if op = 0x13 ∨ op = 0x17 then
      m2 fun reg _ rm _ len =>
        match rm with
        | .mem a => sse (.movHalf (op = 0x17) false reg a) len
        | .xmm _ => none
    else if op = 0x2B then
      m2 fun reg _ rm _ len =>
        match rm with
        | .mem a => fin (.sseMov true (.mem a) (.xmm reg)) len
        | .xmm _ => none
    else if op = 0x50 then
      m2 fun reg _ rm _ len =>
        match rm with
        | .xmm r => sse (.movmsk 32 reg r) len
        | .mem _ => none
    else if op = 0x5A then m2 fun reg _ rm _ len => sse (.cvt .ps2pd reg rm) len
    else if op = 0x5B then m2 fun reg _ rm _ len => sse (.cvt .dq2ps reg rm) len
    else if op = 0xC2 then
      m2i fun reg _ rm v len => if v ≥ 8 then none else sse (.fpCmp 32 reg rm v) len
    else if op = 0xC6 then m2i fun reg _ rm v len => sse (.pimm .shufps reg rm v) len
    else if op = 0xC3 then
      -- MOVNTI m32/m64, r32/r64
      m2 fun reg _ rm _ len =>
        match rm with
        | .mem a => sse (.movnti (if rexW then 64 else 32) a reg) len
        | .xmm _ => none
    else none
  else if sel = 2 then
    if op = 0x70 then m2i fun reg _ rm v len => sse (.pimm .pshufhw reg rm v) len
    else if op = 0x5B then m2 fun reg _ rm _ len => sse (.cvt (.ps2dq true) reg rm) len
    else if op = 0xE6 then m2 fun reg _ rm _ len => sse (.cvt .dq2pd reg rm) len
    else if op = 0x12 then m2 fun reg _ rm _ len => sse (.movdup .sldup reg rm) len
    else if op = 0x16 then m2 fun reg _ rm _ len => sse (.movdup .shdup reg rm) len
    else none
  else if sel = 3 then
    if op = 0x12 then m2 fun reg _ rm _ len => sse (.movdup .ddup reg rm) len
    else if op = 0xE6 then m2 fun reg _ rm _ len => sse (.cvt (.pd2dq false) reg rm) len
    else if op = 0x7C ∨ op = 0x7D then
      m2 fun reg _ rm _ len => sse (.fpHorz (op = 0x7D) 32 reg rm) len
    else if op = 0xD0 then m2 fun reg _ rm _ len => sse (.fpAddsub 32 reg rm) len
    else if op = 0xF0 then
      -- LDDQU xmm, m128 (unaligned load; memory only)
      m2 fun reg _ rm _ len =>
        match rm with
        | .mem a => fin (.sseMov false (.xmm reg) (.mem a)) len
        | .xmm _ => none
    else none
  else none

end Janus.Amd64.DecodeSSE
