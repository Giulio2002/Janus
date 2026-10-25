import Janus.Amd64.InstrSSE

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
  sign-extended 64-bit displacement, or `[RIP_next + disp]` when `rip = true`; with `fs = true`
  (an `FS` segment prefix) the address is `FS.base` plus that.
* Vector widths `l` are `128` (`XMM`, legacy SSE or VEX.L = 0) or `256` (`YMM`, VEX.L = 1).

`exec` (see `Janus.Amd64.Exec`) is only specified on values produced by `decode`.
-/

namespace Janus.Amd64

/-- A memory operand `[base + index * 2^scale + disp]` (or `[RIP_next + disp]`), relative to
the `FS` segment base when `fs`. -/
structure Addr where
  base : Option Nat
  index : Option Nat
  scale : Nat
  disp : Nat
  rip : Bool
  fs : Bool := false
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

/-- Packed-integer / bitwise vector operation with a register destination: `XORPS`/`XORPD`/
`PXOR`/`VPXOR` (`xor`), `PAND`/`VPAND`, `POR`/`VPOR`, `PCMPEQB`/`VPCMPEQB` (each byte `0xFF` if
equal, else `0`), `PUNPCKLBW` (legacy only: interleave the low 8 bytes, destination first),
and the SSSE3 byte operations (legacy only): `PSHUFB` (byte `i` of the result is `0` if bit 7
of byte `i` of the source is set, else byte `src[i] & 15` of the destination, in each 128-bit
lane) and `PSIGNB` (byte `i` of the destination negated, zeroed or kept as byte `i` of the
source is negative, zero or positive). -/
inductive SseOp where
  | xor
  | and
  | or
  | pcmpeqb
  | punpcklbw
  | pshufb
  | psignb
deriving Repr, DecidableEq, Inhabited

/-- SSE scalar floating-point arithmetic (`ADDSD SUBSD MULSD DIVSD MINSD MAXSD SQRTSD` and
the `SS` forms). -/
inductive FPArith where
  | add | sub | mul | div | min | max | sqrt
deriving Repr, DecidableEq, Inhabited

/-- The instructions that read a value of the CPU's environment (WP-C, `Instr.envRead`). -/
inductive EnvOp where
  | cpuid | xgetbv | rdtsc | rdtscp
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
  /-- `RCL` (`left = true`) / `RCR dst, count`: rotate the `w + 1`-bit value `CF:dst` (count
  masked to 5 bits, 6 for `w = 64`). Only `w ∈ {32, 64}` (the 8/16-bit forms reduce the count
  modulo 9/17 and are not modelled). -/
  | rcx (left : Bool) (w : Nat) (dst : Loc) (count : Src)
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
  /-- `NOP`, `PAUSE`, multi-byte `NOP r/m` (no memory access), the fences `LFENCE`,
  `MFENCE`, `SFENCE` (ordering only: the model is single-threaded), the cache hints
  `PREFETCHNTA/T0/T1/T2 m8` (no architectural effect, never fault). -/
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
  /-- `XORPS/XORPD/PXOR/PAND/POR/PCMPEQB/PUNPCKLBW/PSHUFB/PSIGNB xmm, xmm/m128` (legacy SSE: a memory operand
  must be 16-aligned; bits 255:128 of the destination are preserved). -/
  | sseOp (op : SseOp) (dst : Nat) (src : XLoc)
  /-- `PSHUFD xmm, xmm/m128, imm8` (legacy SSE, aligned memory operand): dword `i` of the
  result is dword `imm[2i+1:2i]` of the source. -/
  | pshufd (dst : Nat) (src : XLoc) (imm : Nat)
  /-- `PSHUFLW xmm, xmm/m128, imm8` (`F2 0F 70`, legacy SSE, aligned memory operand): word
  `i < 4` of the result is word `imm[2i+1:2i]` of the source, bits 127:64 are the source's. -/
  | pshuflw (dst : Nat) (src : XLoc) (imm : Nat)
  /-- `MOVSD` (`w = 64`, `F2 0F 10/11`) / `MOVSS` (`w = 32`, `F3 0F 10/11`), the scalar moves:
  memory to register zero-extends into bits 127:0, register to register replaces the low `w`
  bits, register to memory stores the low `w` bits. Bits 255:128 are preserved. -/
  | movsd (w : Nat) (dst src : XLoc)
  /-- `PMOVMSKB r, xmm` (`l = 128`, legacy or VEX.128) / `VPMOVMSKB r, ymm` (`l = 256`): bit
  `i` of the zero-extended result is the top bit of byte `i` of the source. -/
  | pmovmskb (l : Nat) (dst src : Nat)
  /-- VEX `VMOVDQU` (`aligned = false`), `VMOVDQA` and `VMOVNTDQ` (`aligned`: `#GP` unless the
  memory operand is `l/8`-aligned) at width `l`. A register destination of width 128 has bits
  255:128 zeroed. `VMOVNTDQ`'s non-temporal hint does not change the single-threaded result. -/
  | vmov (aligned : Bool) (l : Nat) (dst src : XLoc)
  /-- VEX three-operand `VPXOR/VPAND/VPOR/VPCMPEQB dst, src1, src2` at width `l` (no alignment
  requirement; `l = 128` zeroes bits 255:128 of `dst`). -/
  | vop (op : SseOp) (l : Nat) (dst src1 : Nat) (src2 : XLoc)
  /-- `VPTEST a, b` at width `l`: `ZF = (a AND b = 0)`, `CF = (b AND NOT a = 0)`, `AF OF PF SF`
  cleared. -/
  | vptest (l : Nat) (a : Nat) (b : XLoc)
  /-- `VPBROADCASTB dst, xmm/m8` at width `l`: every byte of `dst` is the low byte of `src`. -/
  | vpbroadcastb (l : Nat) (dst : Nat) (src : XLoc)
  /-- `VZEROUPPER`: bits 255:128 of `YMM0`–`YMM15` become 0. -/
  | vzeroupper
  /-- `MOVD`/`MOVQ` between a general operand (`w ∈ {32, 64}`) and `XMMx`: `toX = true` is
  `66 0F 6E` (`XMMx ← ZeroExtend(g)`), `false` is `66 0F 7E` (`g ← XMMx[w-1:0]`). -/
  | movdq (w : Nat) (toX : Bool) (x : Nat) (g : Loc)
  /-- `MOVQ` (`F3 0F 7E` / `66 0F D6`): the low 64 bits of `src` to `dst`; a register
  destination has its upper 64 bits cleared. -/
  | movq (dst src : XLoc)
  /-- `XADD dst, src` (`0F C0`/`0F C1`, memory `dst` only, optionally `LOCK`ed):
  `TEMP ← dst + src; src ← dst; dst ← TEMP`, flags as `ADD`. `src` is a register location. -/
  | xadd (w : Nat) (dst : Loc) (src : Loc)
  /-- `CMPXCHG dst, src` (`0F B0`/`0F B1`, memory `dst` only, optionally `LOCK`ed): flags of
  `CMP rAX, dst`; if equal `dst ← src`, else `rAX ← dst` (and `dst` is written back
  unchanged). -/
  | cmpxchg (w : Nat) (dst : Loc) (src : Loc)
  /-- `CMPXCHG8B m64` (`w = 64`) / `CMPXCHG16B m128` (`w = 128`, `REX.W`; `#GP` unless
  16-aligned): compare `rDX:rAX` with the memory operand; if equal `ZF ← 1` and
  `m ← rCX:rBX`, else `ZF ← 0` and `rDX:rAX ← m` (written back unchanged). Other flags are
  unaffected. -/
  | cmpxchgDbl (w : Nat) (a : Addr)
  /-- `CLD` (`b = false`) / `STD` (`b = true`): write the direction flag. -/
  | setDF (b : Bool)
  /-- `MOVS` (`A4`/`A5`) at width `w`: copy `w/8` bytes from `[RSI]` to `[RDI]` and advance
  both (by `+w/8`, or `-w/8` when `DF = 1`). With `rep` (`F3`), repeat `RCX` times and leave
  `RCX = 0`. -/
  | movs (rep : Bool) (w : Nat)
  /-- `STOS` (`AA`/`AB`) at width `w`: store the low `w` bits of `RAX` at `[RDI]` and advance
  `RDI` (by `+w/8`, or `-w/8` when `DF = 1`). With `rep` (`F3`), repeat `RCX` times and leave
  `RCX = 0`. -/
  | stos (rep : Bool) (w : Nat)
  -- SSE scalar floating point (`Janus.Amd64.Float`); `w` is 64 (`SD`) or 32 (`SS`).
  /-- `ADDSD/SUBSD/MULSD/DIVSD/MINSD/MAXSD/SQRTSD xmm, xmm/m64` (`w = 64`) and the `SS` forms
  (`w = 32`): the low `w` bits of `XMM[dst]` become `XMM[dst] op src` (`SQRT`: `√src`); the
  other bits are preserved. -/
  | sseArith (op : FPArith) (w : Nat) (dst : Nat) (src : XLoc)
  /-- `UCOMISD`/`UCOMISS` (`signal = false`) and `COMISD`/`COMISS` (`signal`): `ZF PF CF` from
  comparing `XMM[a]` with `b`, `OF AF SF` cleared. -/
  | sseComi (signal : Bool) (w : Nat) (a : Nat) (b : XLoc)
  /-- `CMPSD`/`CMPSS xmm, xmm/m, pred` (`pred < 8`): the low `w` bits become all ones or 0. -/
  | sseCmp (w : Nat) (dst : Nat) (src : XLoc) (pred : Nat)
  /-- `CVTSI2SD`/`CVTSI2SS xmm, r/m32` (`iw = 32`) or `r/m64` (`iw = 64`, `REX.W`). -/
  | cvtsi2f (w iw : Nat) (dst : Nat) (src : Loc)
  /-- `CVTTSD2SI`/`CVTTSS2SI` (`trunc`) and `CVTSD2SI`/`CVTSS2SI r32/r64, xmm/m`. -/
  | cvtf2si (trunc : Bool) (w iw : Nat) (dst : Nat) (src : XLoc)
  /-- `CVTSD2SS` (`w = 64`, the source width) / `CVTSS2SD` (`w = 32`). -/
  | cvtff (w : Nat) (dst : Nat) (src : XLoc)
  /-- `ROUNDSD`/`ROUNDSS xmm, xmm/m, imm8` (SSE4.1, `imm8 < 16`). -/
  | sseRound (w : Nat) (dst : Nat) (src : XLoc) (imm : Nat)
  /-- `ANDPS/ANDPD` (`op = 0`), `ANDNPS/ANDNPD` (`1`: `NOT dst AND src`), `ORPS/ORPD` (`2`) on
  128 bits (legacy SSE: a memory operand must be 16-byte aligned). -/
  | fpLogic (op : Nat) (dst : Nat) (src : XLoc)
  -- BMI1 / BMI2 (VEX-encoded general-purpose instructions; `w ∈ {32, 64}` from `VEX.W`)
  /-- `ANDN dst, src1, src2`: `dst ← NOT src1 AND src2` (`src1` is `VEX.vvvv`); `SF ZF` from the
  result, `CF OF` cleared, `AF PF` undefined. -/
  | andn (w : Nat) (dst src1 : Nat) (src2 : Loc)
  /-- `BLSR` (`op = 1`, `dst ← (src - 1) AND src`), `BLSMSK` (`2`, `dst ← (src - 1) XOR src`),
  `BLSI` (`3`, `dst ← -src AND src`); `dst` is `VEX.vvvv`, `op` the ModRM `reg` field. -/
  | blsx (op : Nat) (w : Nat) (dst : Nat) (src : Loc)
  /-- `BEXTR dst, src, ctl`: the `ctl[15:8]` bits of `src` from bit `ctl[7:0]` on (both up to
  255; bits past the operand are 0); `ZF` from the result, `CF OF` cleared, `AF SF PF`
  undefined. `ctl` is `VEX.vvvv`. -/
  | bextr (w : Nat) (dst : Nat) (src : Loc) (ctl : Nat)
  /-- `BZHI dst, src, idx`: `src` with the bits from `n = idx[7:0]` up cleared (if `n < w`);
  `CF = (n ≥ w)`, `SF ZF` from the result, `OF` cleared, `AF PF` undefined. -/
  | bzhi (w : Nat) (dst : Nat) (src : Loc) (idx : Nat)
  /-- `SHLX`/`SHRX`/`SARX dst, src, cnt` (`op ∈ {shl, shr, sar}`): the shift by
  `cnt` (`VEX.vvvv`) masked to 5 (6 for `w = 64`) bits; flags unaffected. -/
  | shiftx (op : ShOp) (w : Nat) (dst : Nat) (src : Loc) (cnt : Nat)
  /-- `RORX dst, src, imm8`: rotate right by `imm8` masked to 5 (6) bits; flags unaffected. -/
  | rorx (w : Nat) (dst : Nat) (src : Loc) (imm : Nat)
  /-- `MULX hi, lo, src`: the unsigned product `rDX * src`; `lo` (`VEX.vvvv`) gets the low half,
  then `hi` (ModRM `reg`) the high half (so `hi = lo` holds the high half); flags unaffected. -/
  | mulx (w : Nat) (hi lo : Nat) (src : Loc)
  /-- `PDEP dst, src, mask`: the low bits of `src` (`VEX.vvvv`) deposited at the set bits of
  `mask`; flags unaffected. -/
  | pdep (w : Nat) (dst src : Nat) (mask : Loc)
  /-- `PEXT dst, src, mask`: the bits of `src` (`VEX.vvvv`) at the set bits of `mask`, packed to
  the low end; flags unaffected. -/
  | pext (w : Nat) (dst src : Nat) (mask : Loc)
  /-- `MOVBE dst, src` (`0F 38 F0`: register from memory, `0F 38 F1`: memory from register):
  a move with the bytes reversed, `w ∈ {16, 32, 64}`; flags unaffected. -/
  | movbe (w : Nat) (dst src : Loc)
  /-- FMA3 scalar `VFMADD`/`VFMSUB`/`VFNMADD`/`VFNMSUB` `132`/`213`/`231` `SD` (`w = 64`) /
  `SS` (`w = 32`) `dst, src2, src3`, `form ∈ {132, 213, 231}`: the multiplicands and addend are
  `(dst, src3; src2)`, `(src2, dst; src3)`, `(src2, src3; dst)`; the product is negated when
  `negP`, the addend when `negC`, and the sum rounded once (`FP.fma`). The low `w` bits of
  `XMM[dst]` get the result, bits 127:`w` are kept and bits 255:128 zeroed (VEX). -/
  | vfmas (w : Nat) (form : Nat) (negP negC : Bool) (dst src2 : Nat) (src3 : XLoc)
  /-- A `LOCK`ed read-modify-write, or `XCHG` with a memory operand (locked implicitly):
  executes `i`, but first faults (`misaligned`) unless its memory operand (`size` bytes at `a`)
  is naturally aligned, so that the locked access never splits a cache line (Linux with
  `split_lock_detect=fatal` kills a process that does that, `SIGBUS`). -/
  | locked (i : Instr) (a : Addr) (size : Nat)
  -- Kernel, trap, environment and flag-image instructions (WP-C, `Janus.Amd64.DecodeSys`)
  /-- `SYSCALL` (`0F 05`): a Linux system call. Executes as `Fault.kernel`; the kernel
  semantics `Janus.Amd64.Kernel.ReturnsK` gives its effect at the `.syscall` stub the extractor
  puts here. -/
  | syscall
  /-- `CPUID` (`0F A2`), `XGETBV` (`0F 01 D0`), `RDTSC` (`0F 31`), `RDTSCP` (`0F 01 F9`): values
  from the CPU's environment. Execute as `Fault.kernel`; `Janus.Amd64.Kernel` gives them. -/
  | envRead (op : EnvOp)
  /-- `INT3` (`CC`) / `INT 3` (`CD 03`): `Fault.trap pc 5`; `UD2` (`0F 0B`): `Fault.trap pc 4`;
  `HLT` (`F4`, privileged): `Fault.trap pc 11`. `signal` is the Linux signal. -/
  | trap (signal : Nat)
  /-- `PUSHFQ` (`9C`): push the `RFLAGS` image (the six status flags, `DF`, and the fixed
  user-mode bits `IF` and bit 1, `0x202`). Faults (`undefinedFlag`) if a status flag is
  undefined. -/
  | pushfq
  /-- `POPFQ` (`9D`): pop `RFLAGS`, setting the six status flags and `DF`. Faults
  (`systemFlag`) if the popped value sets `TF`, `NT`, `AC` or `ID`; the other system bits are
  ignored at CPL 3 (`IF`, `IOPL`, `RF`, `VM`, `VIF`, `VIP`, the reserved bits). -/
  | popfq
  /-- The legacy-SSE packed instructions (`Janus.Amd64.InstrSSE`, `DecodeSSE`, `ExecSSE`). -/
  | sse (i : SseI XLoc Loc Addr)
deriving Repr, DecidableEq, Inhabited

end Janus.Amd64
