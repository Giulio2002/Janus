/-!
# x86-64 instruction AST (supported subset)

One constructor per *operation family* of the Intel SDM (Vol. 2), with the operands already
resolved from the encoding (prefixes, REX, ModRM, SIB, displacement, immediate) by
`Janus.Amd64.decode`, which also returns the instruction length:

* Operand widths `w` are the bit widths `8`, `16`, `32` or `64` (the effective operand size
  after `66`/`REX.W`); the decoder never produces anything else.
* Register numbers are the 4-bit encoding numbers `0..15` (`REX.R/X/B` already applied).
* An 8-bit register operand is `.reg r` (the low byte: `AL`…`BL`, `SPL`…`DIL` with a REX
  prefix, `R8B`…`R15B`) or `.high r` (`AH`, `CH`, `DH`, `BH`, i.e. bits 15:8 of register
  `r ∈ 0..3`; only without a REX prefix).
* Immediates are the operand-width values after the SDM's sign extension (`imm8` of `83 /r`,
  `imm32` of `REX.W 81 /r`, …), as naturals `< 2^w`. Branch displacements are the sign-extended
  64-bit values as naturals `< 2^64`; the target is `RIP_next + rel (mod 2^64)`.
* A memory operand is an `Addr`: `[base + index * 2^scale + disp]` with `disp` the
  sign-extended 64-bit displacement, or `[RIP_next + disp]` when `rip = true`.

`exec` (see `Janus.Amd64.Exec`) is only specified on values produced by `decode`.
-/

namespace Janus.Amd64

/-- A memory operand `[base + index * 2^scale + disp]` (or `[RIP_next + disp]`). -/
structure Addr where
  base : Option Nat
  index : Option Nat
  scale : Nat
  disp : Nat
  rip : Bool
deriving Repr, DecidableEq, Inhabited

/-- A general-purpose operand location. -/
inductive Loc where
  /-- Register `r` accessed at the instruction's width (low bits). -/
  | reg (r : Nat)
  /-- `AH`/`CH`/`DH`/`BH`: bits 15:8 of register `r ∈ 0..3` (8-bit operands only). -/
  | high (r : Nat)
  | mem (a : Addr)
deriving Repr, DecidableEq, Inhabited

/-- A source operand: a location or an immediate (`< 2^w`). -/
inductive Src where
  | loc (l : Loc)
  | imm (v : Nat)
deriving Repr, DecidableEq, Inhabited

/-- An SSE operand: `XMMn` or a memory operand. -/
inductive XLoc where
  | xmm (n : Nat)
  | mem (a : Addr)
deriving Repr, DecidableEq, Inhabited

/-- The eight classic ALU operations (`/r` field of `80`/`81`/`83`, low opcode bits of
`00`–`3D`). `cmp` does not write its destination. -/
inductive AluOp where
  | add | or | adc | sbb | and | sub | xor | cmp
deriving Repr, DecidableEq, Inhabited

inductive UnOp where
  | inc | dec | not | neg
deriving Repr, DecidableEq, Inhabited

/-- Shift/rotate group 2 (`RCL`/`RCR` and the `/6` alias are not supported). -/
inductive ShOp where
  | rol | ror | shl | shr | sar
deriving Repr, DecidableEq, Inhabited

inductive BitOp where
  | bt | bts | btr | btc
deriving Repr, DecidableEq, Inhabited

inductive CntOp where
  | bsf | bsr | tzcnt | lzcnt | popcnt
deriving Repr, DecidableEq, Inhabited

inductive FlagOp where
  | clc | stc | cmc
deriving Repr, DecidableEq, Inhabited

/-- SSE 128-bit bitwise operation with a register destination (`XORPS`/`XORPD`/`PXOR`). -/
inductive SseOp where
  | xor
deriving Repr, DecidableEq, Inhabited

inductive Instr where
  /-- `ADD/OR/ADC/SBB/AND/SUB/XOR/CMP dst, src`. -/
  | alu (op : AluOp) (w : Nat) (dst : Loc) (src : Src)
  /-- `TEST a, b` (flags of `a AND b`). -/
  | test (w : Nat) (a : Loc) (b : Src)
  /-- `MOV dst, src` (no flags). -/
  | mov (w : Nat) (dst : Loc) (src : Src)
  /-- `MOVZX`/`MOVSX`/`MOVSXD`: register `dst` (width `dw`) from `src` (width `sw < dw`). -/
  | movx (signed : Bool) (dw sw : Nat) (dst : Nat) (src : Loc)
  /-- `LEA dst, [a]` truncated to `w` bits. -/
  | lea (w : Nat) (dst : Nat) (a : Addr)
  /-- `INC/DEC/NOT/NEG dst`. -/
  | unary (op : UnOp) (w : Nat) (dst : Loc)
  /-- One-operand `MUL` (`signed = false`) / `IMUL` (`signed = true`):
  `rDX:rAX ← rAX * src` (`AX ← AL * src` for `w = 8`). -/
  | mul1 (signed : Bool) (w : Nat) (src : Loc)
  /-- Two/three-operand `IMUL dst, a, b` (`dst ← a * b`, truncated). -/
  | imul (w : Nat) (dst : Nat) (a : Loc) (b : Src)
  /-- `DIV` / `IDIV src`: divide `rDX:rAX` (`AX` for `w = 8`). -/
  | div (signed : Bool) (w : Nat) (src : Loc)
  /-- `ROL/ROR/SHL/SHR/SAR dst, count` (count `imm` or `CL` as `.loc (.reg 1)`). -/
  | shift (op : ShOp) (w : Nat) (dst : Loc) (count : Src)
  /-- `SHLD` (`left = true`) / `SHRD dst, src, count`. -/
  | shd (left : Bool) (w : Nat) (dst : Loc) (src : Nat) (count : Src)
  /-- `BT/BTS/BTR/BTC dst, off` (register offset only with a register `dst`). -/
  | bit (op : BitOp) (w : Nat) (dst : Loc) (off : Src)
  /-- `BSF/BSR/TZCNT/LZCNT/POPCNT dst, src`. -/
  | count (op : CntOp) (w : Nat) (dst : Nat) (src : Loc)
  /-- `BSWAP r` (`w ∈ {32, 64}`). -/
  | bswap (w : Nat) (r : Nat)
  /-- `SETcc dst` (8-bit). -/
  | setcc (cc : Nat) (dst : Loc)
  /-- `CMOVcc dst, src`. -/
  | cmov (cc : Nat) (w : Nat) (dst : Nat) (src : Loc)
  /-- `Jcc rel`. -/
  | jcc (cc : Nat) (rel : Nat)
  /-- `JMP rel`. -/
  | jmp (rel : Nat)
  /-- `JMP r/m64`. -/
  | jmpInd (src : Loc)
  /-- `CALL rel`. -/
  | call (rel : Nat)
  /-- `CALL r/m64`. -/
  | callInd (src : Loc)
  /-- `RET` / `RET imm16` (`pop` extra bytes released). -/
  | ret (pop : Nat)
  /-- `PUSH src` (64-bit; immediates sign-extended to 64 bits). -/
  | push (src : Src)
  /-- `POP r64`. -/
  | pop (dst : Nat)
  /-- `LEAVE` (64-bit). -/
  | leave
  /-- `NOP`, `PAUSE`, multi-byte `NOP r/m` (no memory access). -/
  | nop
  /-- `XCHG a, b` (`b` is a register location). -/
  | xchg (w : Nat) (a b : Loc)
  /-- `CBW`/`CWDE`/`CDQE` (`98`): sign-extend the lower half of `rAX` into `w` bits. -/
  | cbw (w : Nat)
  /-- `CWD`/`CDQ`/`CQO` (`99`): fill `rDX` with the sign of `rAX` at width `w`. -/
  | cwd (w : Nat)
  /-- `CLC`/`STC`/`CMC`. -/
  | flagOp (op : FlagOp)
  /-- 128-bit SSE move (`MOVUPS/MOVUPD/MOVDQU`, or with `aligned` `MOVAPS/MOVAPD/MOVDQA`,
  which fault on a memory operand that is not 16-byte aligned). -/
  | sseMov (aligned : Bool) (dst src : XLoc)
  /-- `XORPS/XORPD/PXOR xmm, xmm/m128` (legacy SSE: a memory operand must be 16-aligned). -/
  | sseOp (op : SseOp) (dst : Nat) (src : XLoc)
  /-- `MOVD`/`MOVQ` between a general operand (`w ∈ {32, 64}`) and `XMMx`: `toX = true` is
  `66 0F 6E` (`XMMx ← ZeroExtend(g)`), `false` is `66 0F 7E` (`g ← XMMx[w-1:0]`). -/
  | movdq (w : Nat) (toX : Bool) (x : Nat) (g : Loc)
  /-- `MOVQ` (`F3 0F 7E` / `66 0F D6`): the low 64 bits of `src` to `dst`; a register
  destination has its upper 64 bits cleared. -/
  | movq (dst src : XLoc)
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64
