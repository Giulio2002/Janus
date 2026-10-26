# The amd64 (x86-64) backend

Janus proves theorems about Go functions compiled with `GOARCH=amd64`, against the machine code
in the ELF binary. This document describes the model, what a theorem means on amd64 (the
differences from `docs/SOUNDNESS.md`, which otherwise applies unchanged), the tooling and the
proofs.

| piece | files |
|---|---|
| machine state, faults, checked memory | `Janus/Amd64/State.lean` |
| instruction AST | `Janus/Amd64/Instr.lean` |
| decoder (bytes → instruction, length) | `Janus/Amd64/Decode.lean` |
| semantics | `Janus/Amd64/Exec.lean` |
| SSE packed instructions (WP-D): AST, decoder, semantics | `Janus/Amd64/InstrSSE.lean`, `Janus/Amd64/DecodeSSE.lean` (hook in `Decode.decodeLegacy`), `Janus/Amd64/ExecSSE.lean` (hook `Instr.sse` in `exec`) |
| x86 crypto extensions (WP-E): AST, decoder, semantics | `Janus/Amd64/InstrCrypto.lean`, `Janus/Amd64/DecodeCrypto.lean` (hook in `Decode.decodeLegacy`, after `DecodeSSE`), `Janus/Amd64/ExecCrypto.lean` (hook `Instr.crypto` in `exec`); FIPS-197 specification and the instruction lemmas in `Janus/Spec/AES.lean`, Go's AES hash in `Janus/Spec/MemHash.lean` |
| AVX/AVX2/FMA3/F16C on VEX-128/256 (WP-F): AST, decoder, semantics | `Janus/Amd64/InstrAVX.lean`, `Janus/Amd64/DecodeAVX.lean` (hook in `decode`, after `Decode.vexOp`), `Janus/Amd64/ExecAVX.lean` (hook `Instr.avx` in `exec`) |
| AVX-512 (WP-G): EVEX, ZMM0–31, K0–7, the VEX opmask instructions, VEX `VPCLMULQDQ`/GFNI | `Janus/Amd64/InstrEVEX.lean`, `Janus/Amd64/DecodeEVEX.lean` (hooks in `decode`: `62`, and after `DecodeAVX.vex`), `Janus/Amd64/ExecEVEX.lean` (hook `Instr.evex` in `exec`), `Janus/Amd64/TacticEVEX.lean` (stepping, the zero-upper and compatibility theorems) |
| programs, runner, run lemmas | `Janus/Amd64/Program.lean`, `Janus/Amd64/Run.lean` |
| Go ABIInternal on amd64, specs | `Janus/Amd64/GoABI.lean` |
| proof automation | `Janus/Amd64/Tactic.lean`, `Janus/Amd64/TacticAttr.lean`, `Janus/Amd64/TacticExt.lean` (string instructions, block copies and fills), `Janus/Amd64/TacticAVX.lean` (vector operands, byte-mask lemmas, overlapping copies), `Janus/Amd64/TacticSSE.lean` (stepping `ExecSSE`, element lemmas), `Janus/Amd64/TacticAVX2.lean` (stepping `ExecAVX`, the zero-upper theorems, 256-bit element lemmas, `dot32`), `Janus/Amd64/TacticEVEX.lean` (stepping `ExecEVEX`, 512-bit re-assembly, the EVEX zero-upper rule, VEX/SSE on the AVX-512 state, WP-D/WP-F compatibility) |
| extractor | `cmd/janus/amd64.go` (plus small dispatch edits) |
| differential oracle | `oracle-amd64/`, `Oracle/Amd64Main.lean`, `docs/ORACLE-AMD64.md` |
| tests | `JanusTests/Amd64.lean`, `cmd/janus/amd64_test.go` |
| proofs | `examples/proofs-amd64/<Function>/Proof.lean` |

## The model

**State.** The state has the 16 GPRs (encoding order `RAX RCX RDX RBX RSP RBP RSI RDI
R8..R15`), `RIP`, the six status flags, the direction flag `df`, `YMM0`–`YMM15` (256 bits, as two fields: `xmm n` is bits
127:0 and `ymmHi n` bits 255:128), the `FS` segment base `fsBase` and memory. `ymmHi`,
`fsBase` and `df` have defaults (`0`, `false`), so states written without them still mean what they did; every
specification quantifies over them like over any other field. Keeping the upper lanes in a
field of their own matches the architecture: a legacy-SSE instruction writes only `xmm`
(bits 255:128 preserved, SDM Vol. 1 §14.1.3), a VEX.128 instruction writes `xmm` and zeroes
`ymmHi` of its destination, a VEX.256 one writes both. The AVX-512 state (WP-G) extends the split
upward: `zmmHi n` is bits 511:256 of `ZMMn`, indices 16–31 of `xmm`/`ymmHi`/`zmmHi` are
`ZMM16`–`ZMM31`, and `kreg` holds the opmask registers `K0`–`K7` (both default to zero). Legacy SSE
leaves all of it alone, a VEX write zeroes bits 511:`VL` of its destination, an EVEX write of `l`
bits zeroes bits 511:`l`; `VZEROUPPER`/`VZEROALL` affect `ZMM0`–`ZMM15` only. Memory is the
checked byte memory shared with arm64 (`Janus.Arm64.Memory`): every access must lie inside one
caller-provided region that ends at or below `2^48`, and a store needs a writable region and
must not touch any read-only one. The bound is shared with arm64 and is sound for amd64 too:
every real amd64 user mapping lies below `2^47` (4-level paging; Go never asks Linux for 5-level
addresses), so every real call state is representable, and an address in `[2^47, 2^48)` is
non-canonical (`#GP` on hardware); a precondition that granted memory there would describe a
state no process can be in, it cannot make a claim about a real one. Linear address masking
(LAM), the amd64 analogue of arm64 top-byte-ignore, is off unless a process enables it with
`arch_prctl`, which Go does not do. Each flag is `some b` or `none`
(architecturally undefined). An instruction that reads an undefined flag (`Jcc`, `SETcc`,
`CMOVcc`, `ADC`, `SBB`, `CMC`) faults with `undefinedFlag`, so no proof can depend on a value
the SDM does not define.

**Decoder.** `decode : List Nat → Option (Instr × Nat)` is plain `Nat`/`List` code with two
structurally recursive helpers, so `decide` and the kernel evaluate it on literal bytes. It
handles legacy prefixes, REX, the one- and two-byte opcode maps, ModRM, SIB, RIP-relative and
`disp8`/`disp32` addressing, immediates, and the 15-byte limit. It is strict and rejects:

* `LOCK` except on the lockable read-modify-write forms with a memory destination (`ADD ADC
  AND BTC BTR BTS CMPXCHG CMPXCHG8B/16B DEC INC NEG NOT OR SBB SUB XOR XADD XCHG`), and
  `LOCK` together with `F2`/`F3` (the HLE hints);
* `GS` and address-size prefixes, and `FS` everywhere except on the ModRM memory operand of
  `MOV`, the ALU group, `TEST`, `MOVZX`/`MOVSX`/`MOVSXD` (in particular `LEA`, which ignores
  segments, string instructions, branches, register-only forms and SSE/AVX);
* duplicate prefix groups (except `66`), and a REX that is not immediately before the opcode
  (hardware ignores such a REX);
* `66` on branches, `CALL`, `RET`, `PUSH`, `POP` and `LEAVE` (Intel and AMD differ), except
  before `REX.W` on `CALL rel32` (`66 66 48 E8`, the padded `call __tls_get_addr` of the
  general-dynamic TLS sequence: `REX.W` fixes the operand size at 64 bits on both vendors);
* `F2`/`F3` except where they select an instruction (`F3` is `REP` on `MOVS`/`STOS`; `F2`
  and segment overrides on string instructions are rejected);
* segment overrides on branches (hints), except `3E` (CET `NOTRACK`) on the indirect
  `JMP`/`CALL r/m` (`FF /4`, `FF /2`), which executes as the plain branch (see below);
* on the x87 escape opcodes `D8`–`DF`: `66`, `F2`/`F3` and `REX.W` (they select the
  environment-image size of `FNSTENV`/`FSAVE` and are ignored elsewhere), any prefix on a
  register form, the environment and BCD instructions (`FLDENV FNSTENV FRSTOR FNSAVE FBLD
  FBSTP`), `FFREE`/`FFREEP`, the reserved aliases (`D9 D8+i`, `DC D0+i`, ...), the
  transcendental and remainder instructions (`FSIN FCOS FPTAN FPATAN F2XM1 FYL2X FYL2XP1 FPREM
  FPREM1 FSCALE FRNDINT FXTRACT FINCSTP FDECSTP`) and the constants other than `FLD1`/`FLDZ`;
* XOP, the EVEX instructions outside WP-G's list (below), and the VEX instructions not listed below (WP-F's list: `Janus/Amd64/DecodeAVX.lean`
  and below); VEX after any other prefix
  (`66 F2 F3 F0 REX` make it `#UD`; segment overrides are rejected too); a VEX instruction with
  a field the SDM reserves set (`VEX.vvvv ≠ 1111` where it is unused, `VEX.W1` on
  `VPBROADCASTB`, `VEX.L1` on `VZEROUPPER`, which is `VZEROALL`), the memory form of
  `VPMOVMSKB` and the register form of `VMOVNTDQ`, `VEX.L1` on BMI1/BMI2 (`#UD`) and on the
  scalar FMA forms (`LIG`: ignored by hardware, rejected here since no compiler emits it),
  `VEX.vvvv ≠ 1111` on `RORX`; the register forms of `MOVBE` (`#UD`), `F2`/`F3` on `0F 38
  F0/F1` (`CRC32`, reserved), and `PSHUFB`/`PSIGNB` without `66` (MMX); for the WP-F
  instructions every field the SDM fixes (`VEX.vvvv`, `VEX.L` of the 128-only and 256-only
  forms, `VEX.W` where it is `W0`/`W1`, register-only and memory-only forms, reserved immediates,
  VSIB and distinct registers of the gathers; see `DecodeAVX`);
* `RCL`/`RCR` at 8 and 16 bits (the count is reduced modulo 9/17) and the `SAL /6` alias;
* prefixes on `CLD`/`STD`;
* `F6`/`F7 /1`, `MOVSXD` without `REX.W`, and 16-bit `BSWAP`;
* bit-string `BT*` with a register offset into memory, and memory `POP`;
* every opcode not listed below.

**Supported instructions** (all operand sizes 8/16/32/64 where they exist):
`ADD OR ADC SBB AND SUB XOR CMP` (all forms), `TEST`, `MOV` (r/m, reg, imm, imm64),
`MOVZX MOVSX MOVSXD`, `LEA`, `INC DEC NOT NEG`, `MUL IMUL` (1, 2 and 3 operands), `DIV IDIV`,
`ROL ROR SHL SHR SAR` (imm, 1, CL), `SHLD SHRD`, `BT BTS BTR BTC`, `BSF BSR TZCNT LZCNT POPCNT`,
`BSWAP`, `SETcc`, `CMOVcc`, `Jcc` (rel8/rel32), `JMP` (rel, r/m), `CALL` (rel, r/m),
`RET` / `RET imm16`, `PUSH` (r, r/m, imm), `POP r`, `LEAVE`, `NOP` / multi-byte `NOP` / `PAUSE`,
`XCHG`, `CBW/CWDE/CDQE`, `CWD/CDQ/CQO`, `CLC STC CMC`, the SSE moves Go uses: `MOVUPS MOVUPD
MOVDQU` (unaligned) and `MOVAPS MOVAPD MOVDQA` (fault unless 16-aligned), `XORPS XORPD PXOR`,
`MOVD/MOVQ` between GPRs and XMM, `MOVQ xmm/m64`, `MOVSS`/`MOVSD` (the scalar moves), the
packed-integer compares and logic `PCMPEQB PAND POR PMOVMSKB PSHUFD PSHUFLW PUNPCKLBW`; the AVX
and AVX2 instructions of Go's `memmove`, `memclrNoHeapPointers` and `internal/bytealg`:
`VMOVDQU VMOVDQA VMOVNTDQ VPXOR VPAND VPOR VPCMPEQB VPMOVMSKB VPTEST VPBROADCASTB VZEROUPPER`
(128 and 256 bits, 2- and 3-byte VEX); `RCL`/`RCR` at 32 and 64 bits; the hints
`PREFETCHNTA/T0/T1/T2` and `CLD` (no-ops in the model); `FS`-relative memory operands on the
integer forms above (the TLS load `MOVQ FS:-8, R14`); the atomics: `LOCK`-prefixed
read-modify-write forms, `XADD` and `CMPXCHG` (memory destination, locked or not),
`CMPXCHG8B`/`CMPXCHG16B`, `LFENCE MFENCE SFENCE`; and the string instructions `MOVS` and
`STOS` (all widths) with and without `REP`; and the `GOAMD64=v3` scalar extensions: BMI1
`ANDN BLSR BLSMSK BLSI BEXTR` (and `TZCNT`), BMI2 `SHLX SHRX SARX RORX MULX BZHI PDEP PEXT`
(32 and 64 bits), `MOVBE` (16/32/64 bits, load and store), the 48 scalar FMA3 forms
`VF{,N}M{ADD,SUB}{132,213,231}{SD,SS}` (single rounding on the IEEE core, `FP.fma`) and SSSE3
`PSHUFB`/`PSIGNB` on `XMM`. With them every Go-compiled function of the `GOAMD64=v3` std test
binaries decodes (`docs/COVERAGE.md`).

**AVX, AVX2, FMA3 and F16C on VEX-128/256 (WP-F)** (`Janus/Amd64/{InstrAVX,DecodeAVX,
ExecAVX}.lean`): the VEX form of every WP-D packed integer and floating-point instruction at 128
and 256 bits (`VPADDB ... VPMAXUD`, `VPUNPCK*`, `VPACK*`, `VPHADD*`, `VPSADBW`, `VPMADD*`, `VPAVG*`,
`VPSIGN*`, `VPABS*`, `VPANDN`, the shifts by `imm8` and by `xmm/m128`, `VPSLLDQ`/`VPSRLDQ`,
`VPSHUFD/HW/LW`, `VPALIGNR`, `VPBLENDW`, `VMPSADBW`, `VPMOVSX`/`VPMOVZX`, `VPBLENDVB`,
`VBLENDVPS/PD`, `VBLENDPS/PD`, `VSHUFPS/PD`, `VUNPCK*PS/PD`, `VADD SUB MUL DIV MIN MAX SQRT
PS/PD`, `VCMPPS/PD` with all 32 predicates, `VROUNDPS/PD`, `VHADD`/`VHSUB`/`VADDSUB PS/PD`, the
packed conversions, `VMOVMSKPS/PD`, `VTESTPS/PD`, `VANDPS ... VXORPD`, `VMOVUPS ... VMOVNTDQA`,
`VLDDQU`, `VMOVDDUP`/`VMOVSLDUP`/`VMOVSHDUP`; and at 128 bits `VPINSR*`, `VPEXTR*`, `VEXTRACTPS`,
`VINSERTPS`, `VMOVLPS ... VMOVHPD`, `VMOVHLPS`/`VMOVLHPS`, `VPHMINPOSUW`, `VPCMPxSTRx`); the
scalar `V*SS`/`V*SD` forms (`VADDSD ... VSQRTSD`, `VCMPSS/SD`, `VROUNDSS/SD`, `VCVTSS2SD`,
`VCVTSD2SS`, `VCVTSI2SS/SD`, `VCVT(T)SS/SD2SI`, `VUCOMISS/SD`, `VCOMISS/SD`, `VMOVSS`/`VMOVSD`
in all three forms, `VMOVD`/`VMOVQ`); the AVX2 permutes and broadcasts `VPERMD VPERMPS VPERMQ
VPERMPD VPERM2I128 VPERM2F128 VPERMILPS/PD` (immediate and variable), `VPBLENDD`, `VINSERTI128
VINSERTF128 VEXTRACTI128 VEXTRACTF128`, `VPBROADCASTW/D/Q`, `VBROADCASTSS/SD`,
`VBROADCASTI128/F128`; the masked moves `VPMASKMOVD/Q`, `VMASKMOVPS/PD` (load and store); the
variable shifts `VPSLLVD/Q VPSRLVD/Q VPSRAVD`; the gathers `VPGATHERDD/DQ/QD/QQ`,
`VGATHERDPS/DPD/QPS/QPD`; packed FMA3 `VF{,N}M{ADD,SUB}`, `VFMADDSUB`, `VFMSUBADD` `132/213/231
PS/PD` at both lengths; `VZEROALL`; F16C `VCVTPH2PS`, `VCVTPS2PH`. With them every VEX blocker of
the C corpus at `-O3 -march=x86-64-v3` is gone, and of a 773-function AVX2-intrinsics corpus
(llama.cpp's ggml) too (`docs/COVERAGE.md`).

**AVX-512 (WP-G)** (`Janus/Amd64/{InstrEVEX,DecodeEVEX,ExecEVEX}.lean`): EVEX (`62`, maps 1–3)
with 32 registers, vector lengths 128/256/512, write masks with merging and zeroing (`{z}`),
embedded broadcast (`{1toN}`), compressed `disp8·N` displacements by tuple type, embedded rounding
(`{er}`) and `{sae}`, and fault suppression for masked memory operands. Instructions: the moves
`VMOVDQU8/16/32/64`, `VMOVDQA32/64`, `VMOVUPS/PD`, `VMOVAPS/PD` (load, store, register; masked);
`VPANDD/Q VPANDND/Q VPORD/Q VPXORD/Q` and the `PS`/`PD` logic forms; `VPTERNLOGD/Q`; the EVEX
forms of WP-D's packed integer operations (`VPADD*`, `VPSUB*`, saturating, `VPAVG*`,
`VPMULL*` incl. `VPMULLQ`, `VPMULH*`, `VPMULUDQ`/`VPMULDQ`, `VPMADD*`, `VPSADBW`, `VPMIN*`/`VPMAX*`
at all widths, `VPABS*`, `VPUNPCK*`, `VPACK*`, `VPSHUFB`, the shifts by `xmm/m128` and by `imm8`
incl. `VPSRAQ`, `VPSLLDQ`/`VPSRLDQ`, `VPSHUFD/HW/LW`, `VPALIGNR`); `VPROLD/Q`, `VPRORD/Q`,
`VPROLVD/Q`, `VPRORVD/Q`, `VPSLLV*`/`VPSRLV*`/`VPSRAV*` (W, D, Q); `VPERMB/W/D/Q`, `VPERMPS/PD`,
`VPERMI2B/W/D/Q/PS/PD`, `VPERMT2B/W/D/Q/PS/PD`, `VPERMQ/PD imm8`, `VALIGND/Q`,
`VSHUFI/F32X4/64X2`; `VPOPCNTB/W/D/Q`; `VPCOMPRESSB/W/D/Q` and `VPEXPANDB/W/D/Q` (register and
memory); `VPCMP[U]B/W/D/Q`, `VPCMPEQ*`, `VPCMPGT*`, `VPTESTM*`, `VPTESTNM*` into a mask;
`VPBLENDMB/W/D/Q`, `VBLENDMPS/PD`; `VEXTRACTF/I32X4/64X2/32X8/64X4`, `VINSERTF/I...`;
`VPBROADCASTB/W/D/Q` (from `xmm/m` and from a general register), `VBROADCASTSS/SD`,
`VBROADCASTF/I32X2/32X4/64X2/32X8/64X4`; `VPMOVSX/ZX`; `VADD/SUB/MUL/DIV/MIN/MAX/SQRT PS/PD` with
`{er}`/`{sae}`, `VCMPPS/PD` into a mask; `VGF2P8AFFINEQB`, `VGF2P8AFFINEINVQB`, `VGF2P8MULB`;
`VPCLMULQDQ` (EVEX and VEX.128/256); and the VEX opmask instructions `KMOVB/W/D/Q` (mask, general
register, memory), `KAND KANDN KOR KXOR KXNOR KADD KNOT` (B/W/D/Q), `KSHIFTL/R`, `KORTEST`,
`KTEST`, `KUNPCKBW/WD/DQ`. That is every AVX-512 instruction of Go 1.26's std (the 29
`internal/runtime/gc/scan` kernels, `hash/crc32.ieeeCLMUL`, `runtime.asyncPreempt`'s state save
and restore; `docs/COVERAGE.md`). The CPU features this assumes are listed in
`docs/SOUNDNESS.md` (AVX-512 section).

**SSE packed instructions (WP-D)**, legacy-encoded on `XMM` (`Janus/Amd64/{InstrSSE,DecodeSSE,
ExecSSE}.lean`): SSE2 integer `PADDB/W/D/Q PSUBB/W/D/Q PADDS/PADDUS/PSUBS/PSUBUS B/W PMULLW
PMULHW PMULHUW PMULUDQ PMADDWD PCMPEQW/D PCMPGTB/W/D PANDN PUNPCKL/H BW/WD/DQ/QDQ PACKSSWB
PACKSSDW PACKUSWB PMINUB PMAXUB PMINSW PMAXSW PSADBW PAVGB/W`, the shifts `PSLLW/D/Q PSRLW/D/Q
PSRAW/D` by `imm8` and by `xmm/m128` and `PSLLDQ`/`PSRLDQ`, `PSHUFHW`, `PINSRW`, `PEXTRW`; the
packed floating point `ADD SUB MUL DIV MIN MAX SQRT PS/PD`, `CMPPS/PD` (predicates 0–7),
`SHUFPS/PD`, `UNPCKL/H PS/PD`, `MOVLHPS MOVHLPS MOVLPS/PD MOVHPS/PD`, `MOVMSKPS/PD`,
`CVTDQ2PS CVTPS2DQ CVTTPS2DQ CVTDQ2PD CVTPD2DQ CVTTPD2DQ CVTPS2PD CVTPD2PS`; the stores and
loads `MOVNTDQ MOVNTPS MOVNTPD MOVNTI MOVNTDQA LDDQU`; SSE3 `MOVDDUP MOVSLDUP MOVSHDUP HADDPS/PD
HSUBPS/PD ADDSUBPS/PD`; SSSE3 `PHADDW/D/SW PHSUBW/D/SW PMADDUBSW PMULHRSW PSIGNW/D PABSB/W/D
PALIGNR` (with the existing `PSHUFB`/`PSIGNB`); SSE4.1 `PINSRB/D/Q PEXTRB/W/D/Q EXTRACTPS INSERTPS
PBLENDW BLENDPS/PD PBLENDVB BLENDVPS/PD PMOVSX/PMOVZX (all six widths each) PMULLD PMULDQ PTEST
PCMPEQQ PACKUSDW PMINSB/SD/UW/UD PMAXSB/SD/UW/UD PHMINPOSUW MPSADBW ROUNDPS/PD`; SSE4.2 `CRC32`
(`r/m8/16/32/64` into `r32/r64`), `PCMPGTQ` and the string compares `PCMPESTRI PCMPESTRM
PCMPISTRI PCMPISTRM` (every `imm8` mode with bit 7 clear). With them every SSE-family blocker of
the std assembly and of gcc/clang `-O2`/`-O3` C is gone (`docs/COVERAGE.md`).

**x86 crypto extensions (WP-E)**, legacy-encoded (`Janus/Amd64/{InstrCrypto,DecodeCrypto,
ExecCrypto}.lean`): AES-NI `AESENC AESENCLAST AESDEC AESDECLAST AESIMC AESKEYGENASSIST`
(`66 0F 38 DB..DF`, `66 0F 3A DF`), `PCLMULQDQ` (`66 0F 3A 44`, every `imm8`; only bits 0 and 4
select), SHA-NI `SHA1RNDS4` (`NP 0F 3A CC`, every `imm8`; bits 1:0 select), `SHA1NEXTE SHA1MSG1
SHA1MSG2 SHA256RNDS2 SHA256MSG1 SHA256MSG2` (`NP 0F 38 C8..CD`), and ADX `ADCX`/`ADOX`
(`66`/`F3 0F 38 F6`, 32- and 64-bit). The mandatory prefix must be exactly the listed one (`66`
with `F3` is rejected; hardware executes it, a deliberate model gap). The VEX forms (`VAESENC`,
`VPCLMULQDQ`, ...) are not modelled (no std assembly uses them outside AVX-512 `hash/crc32`).

**The x87 FPU** for C `long double` (`Janus/Amd64/X87.lean`, WP-J): `FLD`/`FST`/`FSTP` with `m32fp`, `m64fp`, `m80fp` (`FSTP` only) and `ST(i)`, `FILD`,
`FIST`, `FISTP`, `FISTTP` (`m16/m32/m64int`), `FADD FSUB FSUBR FMUL FDIV FDIVR` (`ST(0), ST(i)`,
`ST(i), ST(0)`, the popping `P` forms, `m32fp`/`m64fp`) and `FIADD FISUB FISUBR FIMUL FIDIV
FIDIVR` (`m16/m32int`), `FCOM FCOMP FCOMPP FUCOM FUCOMP FUCOMPP FICOM FICOMP FTST`, `FCOMI
FCOMIP FUCOMI FUCOMIP`, `FCMOVcc` (all eight), `FXCH`, `FCHS FABS FSQRT`, `FLD1 FLDZ`, `FXAM`,
`FLDCW FNSTCW FNSTSW` (`AX`, `m16`), `FNCLEX FNINIT FNOP FWAIT`; the CET `NOTRACK` indirect
branches and the padded TLS call.

In the `sync/atomic`, `bytes`
and `strings` test binaries 97.9–98.1% of the Go-compiled functions and 53% of the assembly
functions decode completely (`docs/ORACLE-AMD64.md`); with the SSE scalar floating point
(`UCOMISD`, `CVT*`, arithmetic, `ROUNDSD`) now modelled, what is left is `SYSCALL`,
AES/SHA, AVX-512 (scalar FMA is modelled since WP-B, `CRC32` and `PCMPESTRI` since WP-D).

**Semantics** follow the SDM *Operation* and *Flags Affected* sections:

* A 32-bit result zero-extends into the full register. This includes 32-bit `CMOV` with a
  false condition and 32-bit shifts by a masked count of 0, a case the oracle found.
* 8/16-bit results merge into the low bits, and `AH`..`BH` are bits 15:8.
* Flags the SDM lists as undefined are `none`. Where vendors differ, or the SDM's pseudocode
  and prose disagree, the model takes the undefined side: `ZF` after `BT*`, SAR `CF` for an
  8/16-bit count at or above the width, ROL/ROR `OF` at masked count 0.
* Undefined results fault (`undefinedResult`): BSF/BSR of 0 at every width (Intel leaves the
  destination undefined; AMD documents, and this Intel CPU shows, that it is kept — a vendor
  difference, so the model faults; audit round 2, LOW-2), and 16-bit SHLD/SHRD by more than 16.
* BMI1/BMI2 follow the SDM: `ANDN BLSR BLSI BZHI` set `SF ZF` from the result and clear `OF`
  (`CF`: `0`, source zero, source non-zero, index `≥ w`), `BLSMSK` clears `ZF`, `BEXTR` defines
  only `ZF` (`CF OF` cleared); `AF PF` (and `SF` of `BEXTR`) are undefined. `SHLX SHRX SARX
  RORX MULX PDEP PEXT` leave the flags alone. `MULX` writes the low half to `VEX.vvvv`, then the
  high half to ModRM `reg` (equal registers get the high half).
* Scalar FMA (`FP.fma`): the multiplicands and addend are `(dst, src3; src2)` for `132`,
  `(src2, dst; src3)` for `213`, `(src2, src3; dst)` for `231`; one rounding, `DAZ`, `FTZ`,
  tininess after rounding and the exception flags as for the other SSE operations; a single NaN
  operand comes back quieted and never negated. Two or more NaN operands (the NaN chosen is
  Intel's documented order, not AMD's) and `0 × ∞ + NaN` (IEEE 754 leaves `IE` to the
  implementation) fault with `undefinedResult`.
* `#DE` is a fault (`divideError`), and so is a misaligned 16-byte SSE operand
  (`misaligned`).
* A read-modify-write destination must be writable before it is read.
* Branch targets `≥ 2^47` fault (`badTarget`). This is conservative: on hardware those
  targets are either non-canonical, which is `#GP`, or kernel/5-level addresses, which fault
  at fetch.
* **Atomics.** The model is single-threaded (one goroutine, no other agent writes memory), so
  `LOCK` changes nothing: a locked instruction has exactly the semantics of the unlocked one,
  with all flags, and the fences are `NOP`s. `XADD`: `TEMP ← DEST + SRC; SRC ← DEST; DEST ←
  TEMP`, flags of the `ADD`. `CMPXCHG`: flags of `CMP accumulator, DEST`; equal: `DEST ← SRC`
  (a 32-bit success leaves the upper half of `RAX` alone); not equal: `rAX ← DEST`
  (zero-extending at 32 bits) and `DEST` is written back unchanged, so it must be writable
  either way. `CMPXCHG8B/16B` change only `ZF`; `CMPXCHG16B` faults (`misaligned`) unless its
  operand is 16-aligned. Register destinations of `XADD`/`CMPXCHG` are not modelled (Go
  never emits them). **Split locks:** a locked access (every `LOCK` form, and `XCHG` with a
  memory operand, which is always locked) faults (`misaligned`) unless its operand is naturally
  aligned (`Instr.locked`). A locked access that straddles a cache line is a *split lock*:
  Linux with `split_lock_detect=fatal` sends `SIGBUS`, and in the default `warn` mode it traps
  and delays the thread. Natural alignment never splits a line of any size of 16 bytes or more,
  so the rule is independent of the line size; Go aligns every word it accesses atomically
  (audit round 2, LOW-1). On this host (`warn` mode) a misaligned locked access completes, so
  the oracle reports those cases as model gaps. Theorems about atomics therefore say nothing about concurrent
  executions: they are the sequential semantics of the code.
* **String instructions.** `MOVS`/`STOS` move or store one element of `w/8` bytes at
  `[RSI]`/`[RDI]` and advance the pointers; `REP` repeats this `RCX` times and leaves `RCX = 0`
  (64-bit address size: `67` is rejected). A `REP` instruction is the sequential repetition of
  its element step, which is its architectural result also with fast strings (SDM Vol. 1
  §7.3.9.3). **The direction flag** is the state field `df`: `CLD`/`STD` write it, and with
  `df = true` the element step decrements `RSI`/`RDI` instead (`movsIterB`, `stosIterB`;
  modelled exactly rather than faulting, so `runtime.memmove`'s overlapping backward copy
  `STD; REP MOVSQ; CLD` is decodable and provable). Go ABIInternal keeps `DF = 0` at calls
  (`abi-internal.md`: "The direction flag (D) is always cleared (set to the 'forward'
  direction) at a call."), so `GoABI.CallSetup` requires `s.df = false` and `janus64_intro`
  adds `h_df`. Before audit round 2 the state had no `DF` and string instructions always
  stepped forward; that was sound for call theorems, but a theorem about an arbitrary
  mid-function state (`DFRepro.memmove_backward_rep_copies_forward`, about the `REP MOVSQ` right
  after memmove's `STD`) could claim a forward copy that hardware never performs. With `df` in
  the state such a claim holds only for `df = false` states, and
  `JanusTests.Amd64.df_backward_not_forward` checks that from `df = true` the copy goes
  backward. The native oracle sets `DF` in a quarter of its cases and compares it.
* **Crypto extensions (WP-E).** The AES instructions compose the AES transformations shared
  with the arm64 model (`aesShiftRows`, `aesSubBytes`, `aesMixColumns` of `Janus.Arm64.Vector`;
  both ISAs hold the state with byte `i` = FIPS-197 `in[i]`): `AESENC = MixColumns ∘ SubBytes ∘
  ShiftRows` then `XOR` the key, `AESENCLAST` without `MixColumns`, `AESDEC`/`AESDECLAST` the
  inverses, `AESIMC = InvMixColumns`, `AESKEYGENASSIST` the SDM's `SubWord`/`RotWord` of dwords
  1 and 3. `Janus/Spec/AES.lean` proves each of them equal to the FIPS-197 transformation written
  independently (`aesenc_eq`, `aesenclast_eq`, `aesdec_eq`, `aesdeclast_eq`, `aesimc_eq`,
  `keygenAssist_eq`; S-box from the GF(2^8) inverse and the affine map, `sbox_table`).
  `PCLMULQDQ` is `polyMult` of `Janus.Arm64.Crypto` (arm64 `PMULL`); the SHA-NI operations are the
  SDM pseudocode over dwords with `Ch`/`Parity`/`Maj`/`Σ0`/`Σ1` shared with arm64. `ADCX`
  (`ADOX`) adds with `CF` (`OF`) as carry in and out and leaves the other five status flags
  unchanged; an undefined carry in faults (`undefinedFlag`). 128-bit memory operands must be
  16-aligned (exception class 4). `JanusTests/X86Crypto.lean` checks FIPS-197 C.1/C.3 (encryption
  and the Equivalent Inverse Cipher), FIPS 180-4 SHA-1/SHA-256("abc") and the Intel AES-NI white
  paper vectors through these definitions, in the kernel.
* **SSE packed (WP-D).** Each operation is the SDM `Operation` over elements (`ExecSSE`, using
  the arm64 element accessors `elem`/`ofElems`/`sint`/`truncInt` of `Janus.Arm64.Vector`).
  Saturating forms clamp the exact integer; shifts by `imm8` or by the low quadword of an
  `xmm/m128` count give 0 (logical) or the sign fill (arithmetic) for counts at or above the
  element width. Packed floating point applies the scalar `Janus.Amd64.FP` operation to every
  element under the same `MXCSR`: the exception flags of all elements are ORed, and if any
  element raises an exception unmasked in `MXCSR` the instruction faults (`simdFPException`)
  without writing (SDM Vol. 1 §11.5.2). The SSE4.2 string compares follow SDM Vol. 2 §4.1:
  explicit lengths are `|EAX|`/`|EDX|` (`RAX`/`RDX` with `REX.W`) saturated to 16 or 8, implicit
  ones the first null element; `IntRes1` by aggregation, `IntRes2` by polarity (masked negation
  only for the valid elements of the second operand), the index in `ECX` (zero-extended) or the
  mask in `XMM0`, `CF ZF SF OF` as documented and `AF PF` cleared. `CRC32` is the bit-serial
  CRC-32C update of the low 32 bits of the destination, zero-extended
  (`Janus.Spec.CRC32C.crc32c_eq_update` proves it equal to the bytewise textbook CRC-32C).
  128-bit legacy-SSE memory operands must be 16-aligned (`misaligned`) except for the four string
  compares, which do not check alignment; narrower ones (`m64`, the `PMOVSX` sources, `PINSR*`,
  `INSERTPS m32`) are never checked. The decoder rejects the MMX forms, the register forms of
  memory-only moves and vice versa, reserved group members and immediate bits (`CMPPS/PD
  imm8 ≥ 8`, `ROUNDPS/PD imm8 ≥ 16`, `PCMPxSTRx imm8<7>`), `66` together with `F2`/`F3` (except
  the 16-bit `CRC32`), and the instructions whose result is implementation-specific (`RCPPS`,
  `RSQRTPS`) or not modelled (`MASKMOVDQU`, whose fault behaviour on masked-off bytes is
  implementation-specific; `DPPS`/`DPPD`, which no compiler emits at `-O2`/`-O3`; `LDMXCSR`).
* **AVX/AVX2/FMA3/F16C (WP-F).** `ExecAVX` generalises WP-D's lane semantics to the vector
  length instead of copying them: the in-lane instructions apply WP-D's 128-bit operation to each
  128-bit lane (`ExecAVX.perLane`; at 128 bits it *is* WP-D's operation, `pintV_128` and friends),
  with the per-lane immediate bits the SDM assigns (`laneImm`: `VSHUFPD`/`VBLENDPD` `imm8<2j+1:2j>`,
  `VBLENDPS`/`VPBLENDD` `imm8<4j+3:4j>`, `VMPSADBW` `imm8<3j+2:3j>`); element-wise floating point
  runs WP-D's lane formulas over `l / w` elements; the cross-lane instructions (`VPERMD`,
  `VPERMQ`, `VPERM2I128`, `VINSERTI128`, the broadcasts, `VPMOVSX/ZX`, the widening and narrowing
  conversions) are written over `l`-bit values (`cvtV 128 = ExecSSE.cvtOp`). Every register
  result is written by `ExecAVX.setV`: **VEX.128 zeroes bits 255:128 of the destination**
  (`Janus.Amd64.Tactic.exec_vex128_zero_upper`, for every instruction and every register it
  writes at 128 bits), while no legacy-SSE instruction changes any upper half
  (`exec_sse_preserves_upper`); `JanusTests/AVX.lean` runs `VPADDD ymm` → `PADDD xmm` (upper
  half kept) and `VPADDD xmm` → `PADDD xmm` (zeroed) on concrete states. The three-operand forms
  read `src1` from `VEX.vvvv`; memory operands are unaligned except for the aligned moves. The
  32 `VCMP` predicates are `ExecAVX.vcmp` (`= FP.cmp` for the eight legacy ones, `vcmp_legacy`).
  Packed FMA is `FP.fma` per element (single rounding); an element the manuals leave to the
  implementation (two or three NaNs, `0 × ∞ + NaN`) makes the instruction `undefinedResult`.
  `VCVTPH2PS` is exact and applies neither `DAZ` nor `FTZ` and raises no `DE`; `VCVTPS2PH`
  rounds by `imm8` (or `MXCSR.RC` if `imm8<2>`), applies `DAZ` but not `FTZ`. **Masked moves**
  access only the elements whose mask bit is set (a masked-off element cannot fault, SDM
  "Faults occur only due to mask-bit required memory accesses"); conservatively the whole operand
  must lie below `2^47` (else the model faults, also when hardware would not: the SDM states the
  non-canonical `#GP` for the instruction, not per element). **Gathers** load the selected
  elements and zero the mask register; a fault leaves nothing written (the SDM's partial
  completion, which updates the destination and mask for the elements done before the fault, is
  only visible to a signal handler, and a fault ends a Janus execution); destination, index and
  mask registers must differ (`#UD`, rejected).
* **AVX-512 (WP-G).** `ExecEVEX` extends the same machinery to 512 bits rather than copying it:
  `ExecAVX.perLane` now covers four 128-bit lanes, so every WP-D in-lane operation and every
  WP-F width-generic one (`pintV`, `pimmV`, `pshiftV`, `shufV`, `shiftvV`, `pmovxV`) runs at
  `l = 512`; an EVEX.128/256 register write is exactly WP-F's VEX write (`setZ_128`, `setZ_256`).
  The new parts are the write mask (`merge`: element `i` of `e` bits from the result where bit `i`
  of `K[k]` is set, else zero `{z}` or the old element; no mask writes the whole result),
  broadcasts (`rdV`: one element replicated), fault suppression (`rdMasked`/`stMasked`: a masked
  full-width operand of an element-wise instruction is accessed element by element, masked-off
  elements unchecked; everything else is accessed in full), `VPCOMPRESS`/`VPEXPAND` (only the packed
  elements are written/read), the opmask instructions on `State.kreg`, the GF(2⁸) operations
  (`gfAffine`, `gfMul`, `gfInv` = `x²⁵⁴`, modulo `x⁸+x⁴+x³+x+1`), `VPTERNLOG` (the `OR` of the
  minterms `imm8` selects), the carry-less multiply (`clmulN`), and `{er}`/`{sae}` for the packed
  floating point. **The EVEX zero-upper rule** (`Janus.Amd64.Tactic.exec_evex_zero_upper`): every
  register an AVX-512 instruction writes at `l < 512` bits has bits 511:`l` zero afterwards; a VEX
  write zeroes bits 511:256 (`exec_avx_zero_zmm`); legacy SSE changes no AVX-512 state
  (`exec_sse_preserves_avx512`); and `sse_compat`/`avx_compat` show that WP-D's and WP-F's
  results, with the AVX-512 state erased, are what they were before it was added.
  `JanusTests/AVX512.lean` has the decode known answers (GNU `as` and the Go std encodings), masked
  merging and zeroing, `VPCOMPRESSQ`, `VPERMB`, `VPTERNLOGQ`, the GF(2⁸) identities (`0x53⁻¹ =
  0xCA`), `KORTEST`, and the zero-upper rule on literals and for every state.
* **CPU-feature globals.** `runtime.memmove` reads `runtime.memmoveBits` and
  `runtime.memclrNoHeapPointers` reads `internal/cpu.X86.HasERMS`/`HasAVX2`, which Go sets at
  start-up from `CPUID`. They live in `.noptrbss`, so the extractor does not copy them; a
  theorem that reaches them states them in its precondition (readable, and the value it
  assumes), or quantifies over them. The AVX paths are modelled: `Equal64` quantifies over
  `HasAVX2` (both the AVX2 and the SSE loop of `memeqbody` are proved), `CopyBlock512` assumes
  `memmoveBits` has `avxSupported` set and quantifies over `repmovsPreferred`. `ClearWords`,
  written before VEX was modelled, still assumes `HasAVX2 ≠ 1`.
* **Vector instructions.** Vector values are naturals `< 2^l` (`l = 128` or `256`), byte `i`
  being `v / 256^i % 256`; `PCMPEQB`, `PMOVMSKB`, `PUNPCKLBW` and `VPBROADCASTB` are byte-lane
  recursions (`cmpeqBytes`, `msbBytes`, `unpackLoBytes`, `replBytes`). Legacy-SSE memory operands
  of the packed-integer instructions must be 16-aligned (`misaligned` otherwise), VEX ones
  need no alignment except `VMOVDQA` and `VMOVNTDQ` (`l/8` bytes). `VMOVNTDQ`'s non-temporal
  hint changes only the memory ordering towards other agents, so it is an ordinary store in the
  single-threaded model. `VPTEST` sets `ZF = (a AND b = 0)`, `CF = (b AND NOT a = 0)` and clears
  `AF OF PF SF`. `VPMOVMSKB`/`PMOVMSKB` zero-extend the mask into the 64-bit register.
  `MOVSS`/`MOVSD` from memory zero bits 127:32/127:64, register to register they replace only
  the low lane. A `PREFETCHh` has no architectural effect and never faults, so it is a no-op.
* **FS.** An `FS`-relative operand is at `fsBase + ea (mod 2^64)` and goes through the same
  checked memory as every other access: Go's TLS (the `g` slot at `FS:-8`) is ordinary memory a
  precondition provides (`GoABI.TlsG s`: the slot is readable and holds `R14`; `TlsG.load`
  evaluates the TLS load). No modelled instruction changes `fsBase` (`WRFSBASE` and `arch_prctl`
  are not modelled).
* **RCL/RCR** (32/64 bits) rotate the `w + 1`-bit value `CF:dst`; they read `CF` (fault if it is
  undefined) unless the masked count is 0; `OF` is defined only for a count of 1 (a masked count
  of 0 makes it undefined, as for `ROL`/`ROR`: the SDM pseudocode's choice).
* **x87** (`Janus/Amd64/X87.lean`, executed by `Janus/Amd64/X87Exec.lean`). The state field
  `x87` holds the eight 80-bit data registers, `TOP`, the abridged tag word (per register: in
  use or empty), the control word and the status word (exception flags, `SF`, `ES`, `B`, and
  `C0`–`C3`, each `some b` or `none` = undefined, as the RFLAGS bits). Values are double-extended
  encodings read through `X87.std` as the IEEE format (15, 63) of the core (a pseudo-denormal
  as the normal number of the same value), so the arithmetic is the core's exact arithmetic and
  `round`, written back with an explicit integer bit. Precision control rounds `FADD FSUB FMUL
  FDIV FSQRT` to 24/53/64 significand bits with the extended exponent range (the reserved
  `PC = 01` faults with `undefinedResult`); rounding control applies to every rounding operation;
  tininess is detected after rounding; NaNs follow the x87 column of SDM Table 4-7 (two NaNs:
  quiet over signalling, then the larger significand, then the positive one); unnormals,
  pseudo-infinities and pseudo-NaNs are invalid operands (`IE`, the indefinite), with priority
  over NaNs; denormal operands, also binary32/64 memory operands, raise `DE` in arithmetic and
  comparisons, not in stores and integer conversions. Everything was checked on the host. Not
  modelled, and therefore faults: the unmasked responses (any exception unmasked in the control
  word, or pending with `ES` set, is `fpuException`: the hardware would complete the instruction
  and raise `#MF` at the next waiting one, so faulting earlier is conservative), stack overflow
  and underflow (`fpuStack`: the masked response would deliver the indefinite), `FNSTSW` while a
  condition code is undefined (`undefinedFlag`). `C1` is the rounded-up bit after a rounding
  instruction; `FCOMI`/`FUCOMI` leave `C1` undefined (the SDM says cleared, the host keeps it),
  as the SDM leaves `C0 C2 C3` after most instructions. `FLDCW` keeps the bits `FNSTCW` reads back
  (`(v & 0x1F3F) | 0x40`). The instruction and data pointers and the last opcode are not
  modelled. `X87.binop_add_ieee`/`binop_mul_ieee` (proved) show that at 64-bit precision `FADD`
  and `FMUL` are IEEE 754 addition and multiplication on (15, 63) in every rounding direction.
* **`NOTRACK`.** `3E FF /4` and `3E FF /2` are the plain indirect `JMP`/`CALL`: with CET
  indirect-branch tracking enabled the prefix exempts the branch from the `ENDBR64` check, and
  Linux does not enable IBT for user space (so the branch never checks anything); `ENDBR64` is a
  `NOP` for the same reason.
* `RIP` arithmetic is done on naturals. This is equal to the `BitVec` sum, and it keeps proof
  terms kernel-friendly: `BitVec.reduceAdd` proofs on large literals send the kernel into deep
  recursion.

**Program and runner.** An `Amd64.Program` is byte segments (one per function, the symbol's
full range, `INT3` padding included), runtime stubs and read-only data, reusing `Janus.Stub`,
`Janus.StubKind` and `Janus.DataSegment`. `fetch` returns the at most 15 bytes from `RIP` to the
end of its segment. An instruction that would cross a segment end is undecodable: it is never
stitched together from two segments. `Program.run`, `Outcome`, `Steps` and the run lemmas in
`Janus/Amd64/Run.lean` mirror the arm64 ones.

**C code.** gcc-compiled C (cgo, [FFI.md](FFI.md)) adds `ENDBR64` (`F3 0F 1E FA` exactly, a
NOP; the CET landing pad at every function entry under `-fcf-protection`; every other `F3 0F 1E`
encoding and prefix combination is rejected), the `NOTRACK` jump-table dispatch `3E FF E0+r`,
the padded TLS call `66 66 48 E8` (the `data16 lea x@tlsgd(%rip),%rdi` before it is an ordinary
`LEA`, its `66` being overridden by `REX.W`; the call is a plain call of the `__tls_get_addr`
symbol, whose TLS contract belongs to WP-K2) and the x87 instructions above. `janus
blockers` works on amd64 binaries, judging each x86asm-found instruction with `Janus.Amd64.decode`.

## What a theorem means on amd64

`docs/SOUNDNESS.md` applies, with these differences:

* **Trusted:**
  - the Lean x86-64 model (`Decode`, `Exec`, `State`). It is differentially tested against the
    host CPU, with 0 mismatches over 3,420,590 cases (the final runs of this model: `FS`, AVX, `DF`, split locks), and its undefined-flag sets are
    cross-checked against the Sail/ACL2 X86isa model (`docs/ORACLE-AMD64.md`). It is not
    proved;
  - the ELF byte copy in `cmd/janus/amd64.go`;
  - the stub classification (unchanged);
  - the Lean kernel.
  Reachability uses `x86asm` linear sweeps of each function and is untrusted: a missed callee
  only causes `noCode`.
* **Calls.** `GoABI.CallSetup` says:
  - `RIP = entry`;
  - the return address `p.exitAddr` is stored at `[RSP]`, as the caller's `CALL` left it.
    Specifications use `p.withExit ret` for a universally quantified admissible `ret`
    (`GoABI.RetAddr`: below `2^47`, outside the extracted code and stubs); `Ensures` does this
    itself, and direct `Returns`/`Panics` theorems take `ret` and `hret : RetAddr p ret`;
  - `X15 = 0`;
  - the direction flag is clear (`df = false`);
  - integer argument `i` is in `GoABI.argReg i`, in the order `RAX RBX RCX RDI RSI R8 R9 R10 R11`.
  The `RET` reads the return address from memory, so the precondition must provide that slot:
  `StackWritable s below above` with `above ≥ 8`, which also includes the `2^48` bound.
  Reaching `ret` counts as returning; since `ret` is arbitrary, only a jump to the value the
  caller stored (the `RET`) can reach it for every `ret`, as on arm64.
* **Outcomes.** As on arm64: `Returns`, `Panics` (a panic stub), `Faults` (any fault but
  `outOfFuel`: nil or out-of-bounds access, `#DE`, undefined flag, bad branch target, ...),
  `NeverPanics` (no panic stub **and** no fault; on hardware `SIGSEGV`/`SIGFPE` become Go
  panics) and `GrowsStack`.
* **Return obligations** (`GoABI.ABIReturn`): `RSP' = RSP + 8` (the return address is
  popped), and `RBP`, `R14` (g) and `X15` are restored. There are no other callee-saved
  registers.
* **Stack-growth prologue.** `CMPQ SP, 16(R14); JLS morestack` (and the `LEAQ`/`SUBQ` forms for
  bigger frames) falls through under `GoABI.StackGuardOK s k`.
* **CPU assumptions.** The theorems describe an x86-64 CPU in 64-bit user mode under Linux:
  - `RFLAGS.AC` is clear, so there are no alignment checks except where an instruction
    demands one;
  - Linux may enforce split-lock detection (`split_lock_detect=fatal`): the model's locked
    accesses must be naturally aligned (see "Atomics");
  - the CPU implements `CMPXCHG16B` (every x86-64-v2 CPU; Go's `GOAMD64=v1` code does not
    emit it, it is modelled for completeness);
  - the CPU implements `POPCNT`, `LZCNT` and `TZCNT` (BMI1): on older CPUs `F3 0F BC/BD`
    execute as `BSF`/`BSR`. Any x86-64-v3 CPU qualifies; `GOAMD64=v1` code uses them only
    behind run-time feature checks;
  - the CPU implements AVX and AVX2 (and FMA and F16C for those instructions) and the OS has
    enabled the YMM state (Linux does whenever the CPU has AVX), whenever a VEX instruction
    executes (every x86-64-v3 CPU, the level `-march=x86-64-v3` C code targets). `GOAMD64=v1` code executes VEX only behind
    its CPU-feature globals (`internal/cpu.X86.HasAVX2`, `runtime.memmoveBits`), which Go sets at
    start-up from `CPUID`, so a theorem whose precondition states those globals describes a real
    process on a CPU that has the features. A theorem that quantifies over them (such as
    `Equal64`) also covers states in which they claim AVX2 on a CPU without it; such states do
    not occur in a Go process.
  - the CPU implements the AVX-512 features of WP-G (AVX512F/BW/DQ/VL, VBMI, VBMI2, BITALG,
    VPOPCNTDQ, GFNI, VPCLMULQDQ; `docs/SOUNDNESS.md`) and the OS has enabled the opmask and ZMM
    state, whenever an EVEX or opmask instruction executes. Go's runtime and `hash/crc32` execute
    them only behind `internal/cpu` flags (`X86.HasAVX512*`); `Search64` and `ExpandAVX512_2` are
    about such a CPU.
* **Vendor neutrality.** Where Intel and AMD document different results or flags, the model
  takes the undefined side (fault or `none`). A proof cannot depend on the vendor.
* **Not modelled:**
  - floating point other than SSE (scalar and packed) and VEX (`docs/SOUNDNESS.md`, "Floating
    point"): EVEX floating point, x87, `VRCPPS`/`VRSQRTPS` (implementation-specific), `VDPPS`/`VDPPD`;
  - x87/MMX state, AVX-512 state (`ZMM` bits 511:256, `ZMM16`–`31`, masks);
  - writes of `MXCSR`'s control bits (`LDMXCSR`; `State.mxcsr` is read and its flags raised);
  - segment registers other than the `FS` base, and the `GS` base;
  - concurrency (other threads, memory ordering), string instructions other than
    `MOVS`/`STOS`;
  - every other system feature.
  Code that uses them faults (`undecodable`) and cannot be proved to return.

## Proof automation

`Janus.Amd64.Tactic` is the amd64 analogue of `Janus.Tactic`:

* `janus64_intro hs` turns `hs : GoABI.CallSetup p entry [a₀, …] s` into `h_rip`, `h_ret`
  (the return-address slot, `= ret` for `p = p₀.withExit ret`), `h_x15`, and
  `h_a<i> : s.regs r = aᵢ` with `r` the evaluated `argReg i`. Specs start with
  `intro ret hret s hs hpre`.
* With a symbolic return address the executor finds `hret : RetAddr p₀ ret` in the context. It
  evaluates the program facts on the closed `p₀`, derives `rip ≠ ret` from `hret` (there is no
  code and no stub at `ret`), installs `(BitVec.ofNat 64 ret).toNat = ret` and
  `(ret < 2^47) = True` as rewrite rules for the `RET`, and recognises the return when the
  symbolic `RIP` is `BitVec.ofNat 64 ret`.
* `janus64_run [lemmas] (until [addr, …])?` symbolically executes `Reaches`, `Returns`,
  `Panics` or `GrowsStack` goals one instruction at a time. For each step it computes the
  literal `RIP`, decodes the bytes at tactic time, and proves `stepOK p pc bytes i len = true`
  by `Eq.refl true`, checked by the kernel. It then simplifies `exec i len s` with the
  `janus64_exec` simp set and the local state equations. Branches split the goal (into `hbr`
  cases), and `omega` prunes infeasible branches. `janus64_step` performs one step.
  `until` stops at a loop head, so a loop is proved by induction over the iteration count,
  with `Reaches.mono` and the inductive hypothesis (see `examples/proofs-amd64/Sum`).
* The simp set keeps a symbolic state in a normal form. Registers form a sorted, deduplicated
  `setRegF` chain. The `ADD`/`SUB` flags stay folded, with per-field equations. Each condition
  code has its own equation, and signed comparisons after `CMP` become `toInt` comparisons.
  Memory reads over writes are split into disjoint, same-address and inside cases, and
  addresses and carries become `Nat` arithmetic for `omega`. Its side conditions are
  discharged by `janus64_disch`: `decide` on closed goals (never `omega` from a possibly
  contradictory context), memory accessibility from local `accessible` facts, and `omega`.
* `GoABI.DataLoaded.readLE` turns reads of copied `.rodata` into literals, through `listLE`
  of the data bytes, evaluated by `decide`; `janus64_data hd` does the same as `janus_data`
  (readability of each data segment and a rewrite rule evaluating loads at literal addresses).
* `Janus.Amd64.TacticExt` (imported by `Janus`) extends the simp sets and adds the pieces the
  atomics and memory routines need, all proved from the model:
  - `REP STOS`/`REP MOVS` with a symbolic count: stop in front of the instruction
    (`janus64_run until [addr]`) and apply `Reaches.repStos`/`Reaches.repMovs`, which take
    the addresses and the count explicitly and continue from the closed form (`fillLE`,
    `copyLE`; `stosIter_ok`, `movsIter_ok`);
  - block copies: `copy_first`/`copy_step` turn a chain of chunk stores of loaded values into
    `readLE dst n = readLE src n`; `readLE_writeLE_last` splits a read at its last write;
  - zero fills: `Zeroed M M' d n` (`[d, d + n)` zeroed, nothing else changed) with
    `Zeroed.trans`, `Zeroed.readLE`, `Zeroed.readLE_outside`, `zeroed_fillLE`, and the
    `zeroed_writes` tactic for a chain of overlapping zero stores;
  - `bv_add_add_neg`: negative displacements in indexed addresses (`-16(DI)(BX*1)`) are folded
    with the literal on the left. The generic folding produced `n + (2^64 - k)`, whose kernel
    check unfolded `Nat.add` along the literal (minutes, then deep recursion);
  - `setWidth8_merge`/`setWidth16_merge` (a `SETcc` byte read back by `TEST`),
    `bv8_sub_eq_zero` (`CMPB m8, $c` on a feature byte as a `Nat` equation), and `bvn`, which
    closes `register = BitVec.ofNat 64 k` goals by `omega`.
* `Janus.Amd64.TacticAVX` (imported by `Janus`) adds the vector instructions:
  - `readV`/`writeV`/`setV`/`getV` are unfolded and `ymmHi` gets the `setXmmF` normal form;
    `ymmJoin_ofNat` re-assembles a 256-bit value written by `setV`, and the `_mod` lemmas drop
    the `mod 2^256` for 32-byte reads and `PCMPEQB` masks;
  - mask lemmas: `msbBytes_cmpeq` (`PMOVMSKB (PCMPEQB a b)` is all ones iff the bytes are
    equal), `msbBytes_land` (all ones of an `AND` iff of both), `msbBytes_cmpeq_land`, and the
    branch forms `avx2_mask_eq` (`CMPL DX, $-1`) and `mask16_test` (`CMPL DX, $0xffff`);
    `readLE_eq_halves` splits an equality of reads;
  - address arithmetic: `land_align32` (`ANDQ $-32` as `x - x % 32`), `align32_add_mod`;
    `setWidth8_merge_bv`, `bv8_and_one_eq_zero` (`TESTB $1, AL` on a feature byte),
    `setWidth8_merge_ite` (a `SETcc` result in `AL`);
  - overlapping copies: `copied_writes` proves `M'.bytes x = M.bytes y` for a chain of chunk
    stores of `M`'s bytes in any order, overlapping, byte by byte (`cb_step`, `cb_skip`);
    `readLE_of_bytes` turns that into a `readLE` equality.

It has the same interface as the arm64 automation (`docs/PROOFS.md`, *Tactics*):

| arm64 | amd64 | notes |
|---|---|---|
| `janus_run [l] until [..] calls [..] (budget := N)` | `janus64_run [l] until [..] calls [..] (budget := N)` | |
| `janus_step`, `janus_simp [l]`, `janus_arith`, `janus_data h`, `janus_cases h` | `janus64_step`, `janus64_simp [l]`, `janus64_arith`, `janus64_data h`, `janus64_cases h` | `janus64_arith` turns `SBB`/`ADC` carries `(decide (2^64 ≤ t)).toNat` into `t / 2^64` (`janus64_arith_norm`) |
| `janus_frame` | `janus_frame` | shared (memory is the same type) |
| `segAddr p "f"` | `segAddr p "f"`, `dataBase p i`, `ripTarget p pc`, `janus64_addrs` | layout-independent addresses, see below |

**Callee summaries.** `Summary p entry pre post` says: from any state at `entry` satisfying
`pre`, ordinary steps reach a state whose `RIP` is the return address the caller's `CALL`
pushed, `retAddrOf s` (the word at `[RSP]` on entry), satisfying `post s`. Prove it with
`janus64_run` on the `ReachesRet` goal (also with `calls [...]` for its own callees), and use it
with `janus64_run calls [h, …]`: at the callee's entry (after the `CALL` instruction) the
precondition is proved for the current state and the postcondition is destructured
(existentials, conjunctions, `s' = …` substituted). A leaf callee:

```lean
theorem square_summary :
    Summary Extracted.program (segAddr Extracted.program "example.com/basic.square")
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 * s.regs 0)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩
```

The precondition must provide the return-address slot (`RET` reads it and checks it is below
`2^47`). A non-leaf callee's postcondition also says which memory it may change,
`MemFrame s.mem m [(rsp - frame, rsp), …]` (its saved `RBP`, the return addresses of its own
calls, spills into its caller's frame), proved by `janus_frame`; `POP RBP` restoring the
caller's `RBP` disappears from the register chain. `examples/proofs-amd64/AddThree` and
`SumSquares` use summaries; `bench/proofs-amd64/Chain1.lean` is a five-level chain.

**Layout independence.** No proof contains an address copied from a disassembly, so adding
functions to `examples/basic` (which moves code, data and globals) does not break them:

* loop heads are `Extracted.entry + off` (the offset within the function);
* callee entries are `segAddr Extracted.program "pkg.f"`;
* `.rodata` objects are `dataBase Extracted.program i` (the base of the `i`-th copied data
  segment; the extractor names segments by offset, so the index is the stable handle);
* writable globals, which the extractor does not copy, are `ripTarget Extracted.program pc`:
  the address the RIP-relative operand of the instruction at `pc` (e.g. `Extracted.entry`)
  refers to, read off the extracted code.

`janus64_addrs` (or `simp only [reduceSegAddr, reduceDataBase, reduceRipTarget] at h`) evaluates
these terms to literals, each by a kernel-checked `rfl` lemma, so that `omega` sees the same
numbers as the executor; the executor evaluates them itself in `until [...]`, `calls [...]` and
state equations.

**Stuck diagnostics** are the same as on arm64 (`docs/PROOFS.md`, *Troubleshooting*), with the
instruction printed in Intel syntax (`Janus.Amd64.Disasm.disasm`), and fault explanations for
`#DE`, undefined flags, misaligned SSE operands and bad branch targets.

## Proved (verified end to end by `janus verify`)

Run `scripts/build-examples-amd64.sh`, then `scripts/verify-amd64-examples.sh`. All of these
are about `artifacts/examples-amd64` (`examples/basic`, `GOAMD64=v1`, Go 1.26.0, built
`-trimpath -buildvcs=false`, so the binary does not depend on the git state). No proof contains
a hard-coded address (see *Layout independence* above), so adding functions to
`examples/basic` does not break them. They use only `propext`, `Quot.sound` and
`Classical.choice`, and `leanchecker` replays each one.

| function | theorem |
|---|---|
| `Add` | returns `[x + y]` |
| `Max` | returns `[if y < x then x else y]` (unsigned) |
| `Add128` | `hi·2^64 + lo = (xh:xl + yh:yl) mod 2^128` |
| `Mul64` | `hi·2^64 + lo = x·y` |
| `Add256` | `*z = (*x + *y) mod 2^256`, with `z` overlapping neither operand nor the return slot (operands may alias) |
| `Div` | returns `[x / y]` for `y ≠ 0`; `Proof.panics`: panics (`runtime.panicdivide`) for `y = 0` |
| `Get` | returns `xs[i]` when `i < len` (slice disjoint from the frame); `Proof.panics`: `runtime.panicBounds` when `i ≥ len` |
| `Sum` | returns `Σ xs[j] mod 2^64` (a loop, by induction; spill slot disjoint from the slice) |
| `AddThree` | `Add(Add(x, y), z)`: through the stack-check prologue and two calls, with a callee `Summary` of `Add` |
| `Table` | `t[i & 7]` of the constant table (64 bytes of `.rodata` copied through `X14`) |
| `HexDigit` | byte `i & 15` of the `.rodata` string |
| `SetOne256` | `*z = 1` (32 bytes of `.rodata` through `X14`) |
| `GlobalTable` | `tbl[i & 7]` of the writable global, provided by the precondition |
| `Bump` | `counter += d` on the writable global, returning the new value |
| `AddLimbs` | `*z = (*x + *y) mod 2^256` by the 4-iteration carry loop (unrolled; carries through `SBB`/`NEG`) |
| `CopyWords` | returns `n = min(len(dst), len(src))` and `dst[j] = src[j]` for `j < n` (a loop writing memory, by induction; slices disjoint from each other and the frame) |
| `SumSquares` | `square(x) + square(y)`: the stack-check prologue and two calls, with a callee `Summary` of `square` |
| `AtomicAdd` | `LOCK XADDQ`: `*p = old + d` and returns `old + d` (`p` 8-aligned: no split lock) |
| `AtomicMax` | the `LOCK CMPXCHGQ` retry loop: returns `old` and leaves `*p = max(old, v)` (single-threaded: the CAS succeeds the first time; the retry edge is proved infeasible; `p` 8-aligned) |
| `CopyBlock` | `copy(dst[:], src[:])` of `[16]uint64` through the real `runtime.memmove` (its 65–128-byte SSE path): the 128 bytes at `dst` equal the old 128 bytes at `src`, for any overlap |
| `ClearWords` | `clear(b)` through the real `runtime.memclrNoHeapPointers`, for **every** length: all `len(b)` words are 0 and no other byte outside the frame changes. Covers the straight-line cases, the 256-byte `MOVDQU` loop and the `REP STOSQ` path; quantifies over `internal/cpu.X86.HasERMS` and assumes `HasAVX2 ≠ 1` |
| `Equal64` | `bytes.Equal` of two `[64]byte` through the real `runtime.memequal`/`memeqbody`: `AL = 1` iff the 64 bytes are equal, else `AL = 0`, for **every** value of `internal/cpu.X86.HasAVX2` (the AVX2 loop: `VMOVDQU`, `VPCMPEQB`, `VPAND`, `VPMOVMSKB`, `VZEROUPPER`; the SSE loop: `MOVDQU`, `PCMPEQB`, `PAND`, `PMOVMSKB`), including `a = b` |
| `HashWith` | the interface call `h.Hash(x)` (`CALL DX` through `Fun[0]` of the itab in `RAX`): `x · K` if the itab is `*MulHasher`'s, `rotl(x, 13) + K` if it is `*RotHasher`'s (`Janus.Spec.ItabIs`; callee summaries of both methods) |
| `HashTwice` | `ApplyTwice(h.Hash, x)` through the method value wrapper `(*MulHasher).Hash-fm` (funcval built in the frame, context in `DX`): returns `x · K · K` |
| `MapSum` | `Σ f(xs[j])` for the closure `f` = `AffineSum.func1` capturing `a`, `b` (`FuncvalIs`, `ClosureCtx`): returns `Σ (a·xs[j] + b) mod 2^64` (a loop calling the closure, by induction) |
| `DeferAdd` | `r = x` with an open-coded `defer` of a closure adding `y` to `r`: returns `[x + y]` |
| `CopyBlock512` | `copy(dst[:], src[:])` of `[64]uint64` (512 bytes) through `runtime.memmove`'s **AVX path** (`VMOVDQU` loads, 32-aligned `VMOVDQA` stores, `VZEROUPPER`), for every alignment of `dst`, disjoint arrays, given `memmoveBits & 1 = 1`: the 512 bytes at `dst` equal the old ones at `src`. (256 bytes or fewer never reach the AVX path: `memmove` copies them with SSE.) |

Two are about `artifacts/examples-amd64-sse`: `examples/basic/sse` (Go functions calling small
SSE Go assembly functions, ABI0, called directly with their arguments on the stack), built
`GOAMD64=v1` into a binary of its own.

| function | theorem |
|---|---|
| `Index32` | the index of the first byte of `*p` (`[32]byte`) equal to `c`, 32 if none (`firstIdx`): `PUNPCKLBW`/`PSHUFLW`/`PUNPCKLQDQ` broadcast, two `PCMPEQB`/`PMOVMSKB` masks, `BTSQ` sentinel, `BSFQ` |
| `CRC32C16` | `^crc32cBlock(^crc, p)` with two `CRC32Q`: returns `Janus.Spec.CRC32C.checksum crc p[0..15]`, the bytewise textbook CRC-32C of `hash/crc32.Update(crc, MakeTable(Castagnoli), p[:])` |

The cgo examples `CSum32` (the clang `-O2` SSE2-vectorised loop: two `PADDD` accumulators,
`PSHUFD`/`PADDD` fold, scalar tail) and `GoSum32` (Go → cgo → that loop → Go, under the trusted
`CgoCall`) are in `examples/proofs-cgo/amd64` (`scripts/verify-cgo-examples.sh`, binary
`artifacts/examples-cgo-clang-amd64`, built with `CC=clang`).

Two are about `artifacts/examples-amd64-avx`: `examples/basic/avx` (Go functions calling small
AVX2 Go assembly functions, ABI0), built `GOAMD64=v1` into a binary of its own (WP-F).

| function | theorem |
|---|---|
| `Index64` | the index of the first byte of `*p` (`[64]byte`) equal to `c`, 64 if none (`firstIdx`): `VMOVD`, `VPBROADCASTB ymm`, two `VPCMPEQB ymm, m256`/`VPMOVMSKB ymm` masks joined into 64 bits, `TZCNTQ`, `VZEROUPPER` |
| `MaxU32x8` | the largest of the eight words of `*p` (`[8]uint32`, `maxWords`): `VMOVDQU ymm`, `VEXTRACTI128`, `VPMAXUD xmm`, `VPSHUFD`/`VPMAXUD` twice, `VMOVD` |

The cgo examples `CDot32` (the clang `-O3 -march=x86-64-v3` AVX2 dot product: 32 `VPMULLD`
products per iteration into four YMM accumulators, a `VEXTRACTI128`/`VPSHUFD` reduction, an XMM
epilogue, a scalar tail; `dot32`, for every length) and `GoDot32` (`Dot32(a, b []uint32)` → cgo →
that loop → Go, under the trusted `CgoCall`) are in `examples/proofs-cgo/amd64` (binary
`artifacts/examples-cgo-avx-amd64`, the package's `#cgo CFLAGS: -O3 -march=x86-64-v3`).

Two are about AVX-512 (WP-G). `Search64` is in `artifacts/examples-amd64-avx512`
(`examples/basic/avx512`, a Go function calling an AVX-512 Go assembly function, ABI0, built
`GOAMD64=v1` into a binary of its own); `ExpandAVX512_2` is a function of Go's own runtime,
extracted from the `internal/runtime/gc/scan` test binary (`artifacts/examples-amd64-scan.test`).

| function | theorem |
|---|---|
| `Search64` | `Search64(p, nq, c)` for **every** `nq ≤ 8`: the index of the first of the `8·nq` bytes at `p` equal to `c`, 64 if none (`firstIdx`), with only those `8·nq` bytes readable: `KMOVB` of the qword mask, a masked zeroing `VMOVDQU64` load (fault suppression: only the selected qwords are accessed), `VPBROADCASTB zmm, r32`, `BZHIQ`/`KMOVQ` byte mask, `VPCMPEQB` into `K2` under `K3`, `KMOVQ`, `TZCNTQ`, `VZEROUPPER` |
| `ExpandAVX512_2` | `internal/runtime/gc/scan.expandAVX512_2`, the GC span scanner's bitmap expander for size class 2 (custom convention: the 64-byte packed bitmap at `[AX]`, results in `Z1`/`Z2`; a `Summary`): bit `j` of `Z1` is bit `j/2` of the input and bit `j` of `Z2` bit `256 + j/2`, for every `j < 512` (`Expanded`), through `VMOVDQU64` table loads, `VPERMB` and `VGF2P8AFFINEQB`; the tables are the binary's `.rodata` (`DataLoaded`) |

Three more are about `artifacts/examples-amd64-v3`: `examples/basic/v3` built with
`GOAMD64=v3` into a binary of its own (so the v1 binary above does not change), extracted by the
same script.

| function | theorem |
|---|---|
| `BitMix` | `ANDN`, `SHLX`, `BLSR`: returns `[(x &&& ~~~y) ^^^ (x &&& (x - 1)) ^^^ (y <<< (n mod 64))]` for all `x y n` |
| `Fma` | `math.FMA(a, b, c)` as one `VFMADD231SD`: under `GoMXCSR`, the low 64 bits of `X0` are IEEE 754 `fusedMultiplyAdd(a, b, c)` rounded once to nearest even (`Janus.Float.fma`, the arm64 `FMADD` specification), or a NaN when that is a NaN, whenever the result is architecturally defined (`FP.FmaDefined`: at most one NaN operand, not `0 × ∞ + NaN`) |
| `LoadBE` | `binary.BigEndian.Uint64(b[:])` as one `MOVBE`: the big-endian value of the 8 readable bytes at `b` |

Four are about `artifacts/examples-amd64-crypto`: `examples/basic/xcrypto` (Go code using
`crypto/aes`, `math/big` and an 8-byte-key map), built `GOAMD64=v1` into a binary of its own; the
proved functions are std assembly it links (WP-E).

| function | theorem |
|---|---|
| `Memhash64` | `runtime.memhash64(p, h)`, the hash of every 8-byte map key: `Janus.Spec.MemHash.aesHash64 k0 k1 k2 h v` (three FIPS-197 AES rounds keyed by `runtime.aeskeysched`, seed in the low quadword, data in the high one) when `runtime.useAeshash ≠ 0`, `fallbackHash64` (`memhash64Fallback`, the `mix` of `runtime.hashkey`) otherwise |
| `Memhash32` | `runtime.memhash32(p, h)`: `aesHash32` (the data at dword 2) / `fallbackHash32` |
| `EncryptBlock` | `crypto/internal/fips140/aes.encryptBlockAsm(nr, xk, dst, src)` for `nr ∈ {10, 12, 14}`: writes FIPS-197 `Cipher(src, nr, w)` with `w` the words at `xk` to `dst` and nothing else (`src = dst` allowed); `corollaryAES128`: `AES-128(key, src)` when `xk` holds `KeyExpansion(key)`; `corollaryFIPS197`: the appendix C.1 vector through the machine code |
| `AddMulVVWW` | `math/big.addMulVVWW(z, x, y, m, a)`, both the ADX/BMI2 path and the `MULQ` path (either value of `hasADX`), **every length**: `z + 2^(64n)·c = x + y·m + a` over `n = len(z)` words with the carry word `c`, `z = x` allowed, nothing but `z` and the result slot written |

## Known gaps

* Dynamic calls (`CALL reg`) are followed only to a target the hypotheses determine
  (`Janus.Spec.Dynamic`, `janus_dyn`; the closure context register is `RDX`). `recover`,
  panics unwinding through defers and non-open-coded defers (`runtime.deferproc*`) are not
  supported; see docs/RUNTIME-CONTRACTS.md.

* 8/16-bit `RCL`/`RCR`, the VEX forms of AES-NI and `PCLMULQDQ`, EVEX (AVX-512),
  `CMPS`/`SCAS`/`LODS`, `DPPS`/`DPPD` (and `VDPPS`/`VDPPD`), `RCPPS`/`RSQRTPS` (and the VEX forms),
  `MASKMOVDQU`/`VMASKMOVDQU`, `LDMXCSR`/`VLDMXCSR`, `STMXCSR`, MMX, `GS`-relative accesses and the
  x87 instructions outside the subset above (transcendentals, `FPREM`, `FRNDINT`, `FSCALE`, BCD,
  environment save/restore) are not modelled. Their encodings fault.
* `janus64_run` keeps the AES/SHA/`PCLMULQDQ` results folded (`aesRound .enc x k`, irreducible
  for the elaborator, `TacticCrypto`); proofs rewrite them with `Janus.Spec.AES.aesenc_eq` etc.
* `janus64_run` keeps the packed operations folded (`pintOp (.add 32) x y`, `pshufdNat`, ...) and
  evaluates elements with `elem_pintOp_add` etc.; `ExecSSE.crc32c` is irreducible for the
  elaborator (`TacticSSE`), proofs go through `Janus.Spec.CRC32C`.
* x87 proofs with a symbolic `TOP` rely on the `TacticX87` simp lemmas (`x87_mod8_*`) to
  decide which physical register `ST(i)` is; the abridged tag word is a function
  (`X87.St.tags : Nat → Bool`) so that an in-use test is an `if` the executor can prune
  (`examples/proofs-cgo/amd64/CLdMul`). A context full of disjunctive `Outside` facts makes every
  `omega` call of the executor split exponentially; `GoLdMul` keeps them folded (`Keep`) during
  the runs and unfolds them only where a disjointness is needed.
* Proofs whose loop invariants describe intermediate states and step a string instruction must
  carry `t.df = false` in the invariant (`Reaches.repStos`/`repMovs` take it as `hdf`), as
  `examples/proofs-amd64/ClearWords`' `Inv` does.
* `simp only [d]` on a definition `d := segAddr Extracted.program "f" + k` can hit the
  recursion limit on a large extraction (`memmove`); `unfold d at h` and then
  `simp only [reduceSegAddr, Nat.reduceAdd] at h` does not (`examples/proofs-amd64/CopyBlock512`).
* `Janus.Amd64.TacticAVX` normalises register arithmetic of the AVX loop only when the proof
  passes `BitVec.ofNat_add_ofNat` and a `BitVec.ofNat` subtraction rule to `janus64_run`
  (`examples/proofs-amd64/CopyBlock512`); without them the symbolic registers of a 3-iteration
  loop grow until the kernel's recursion limit. Proofs that compare vector masks make
  `msbBytes`/`cmpeqBytes` locally irreducible (unfolding the 32-lane recursions during `whnf`
  is the expensive part).
* `SETcc` is accepted only with `ModRM.reg = 0`, and `66`-prefixed branches, `PUSH` and `POP`
  are rejected. These are model gaps in the oracle, conservative by design.
* The undefined-flag sets of BSF/BSR/TZCNT/LZCNT/POPCNT/BSWAP/BTS/BTR/BTC are not
  cross-checked: the formal model does not implement those instructions.
* Side conditions are discharged by `omega`, which needs addresses as `Nat` terms; normalise
  preconditions phrased with BitVec literals (`(0x5751b8#64).toNat`) with
  `BitVec.toNat_ofNat`/`janus64_addrs` first, as `examples/proofs-amd64/Bump` does. If a
  discharger call is expensive the run now reports a heartbeat diagnostic instead of timing out
  silently.
