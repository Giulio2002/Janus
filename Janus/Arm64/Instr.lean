import Janus.Arm64.InstrCrypto

/-!
# AArch64 instruction AST (supported subset)

One constructor per *encoding class* of the ARM Architecture Reference Manual (ARM ARM, A64
base instructions), carrying the raw encoding fields, not a "cleaned up" meaning:

* `sf` (bit 31 of data-processing words) is kept as a `Bool`: `true` = 64-bit `X` form,
  `false` = 32-bit `W` form. Load/store `size` (bits 31:30) and `opc` fields are kept as the
  raw `Nat`s.
* Register fields are the raw 5-bit numbers `0..31`. What register 31 *means* depends on the
  operand position; each constructor documents it as `ZR` (reads 0, writes are discarded) or
  `SP` (the stack pointer). The executor uses `State.readZR`/`readSP`/`writeZR`/`writeSP`
  accordingly.
* Immediates are the raw unsigned field values (e.g. `imm26`, `imm9`); sign extension and
  scaling happen in `Exec`, following the ARM ARM pseudocode.

Aliases (MOV, CMP, CMN, TST, NEG, MVN, LSL/LSR/ASR #imm, UBFX, SXTW, ROR #imm, ...) are not
separate constructors: they are the underlying encodings (so are the SIMD aliases: `MOV Vd, Vn`
is ORR, `MOV Xd, Vn.D[i]` is UMOV, `MOV Vd.T[i], ...` is INS, `MVN` is NOT, `SXTL`/`UXTL` are
SSHLL/USHLL #0). Advanced SIMD classes carry their raw `Q`, `U`, `size` and `opcode` fields; the
operation they select is computed in `Janus.Arm64.Vector`. SIMD&FP register fields (`Vt`, `Vn`,
...) are plain numbers `0..31` (there is no zero register or SP among them).

`decode` (see `Janus.Arm64.Decode`) only produces values of this type that correspond to a
valid, allocated encoding of the subset; `exec` is only specified on such values.
-/

namespace Janus.Arm64

/-- The system registers whose value comes from the execution environment, read by `MRS`
(`Instr.mrsEnv`; WP-C, `Janus.Kernel`): the virtual counter `CNTVCT_EL0`, its frequency
`CNTFRQ_EL0`, the CPU's `MIDR_EL1` (emulated by Linux for EL0) and `PSTATE.DIT`. -/
inductive EnvReg where
  | cntvct
  | cntfrq
  | midr
  | dit
deriving Repr, DecidableEq, Inhabited

/-- Shift type field `shift` (2 bits): 00 LSL, 01 LSR, 10 ASR, 11 ROR. -/
inductive ShiftType where
  | lsl | lsr | asr | ror
deriving Repr, DecidableEq, Inhabited

/-- Extend type field `option` (3 bits): `option<2>` = signed, `option<1:0>` = 8/16/32/64. -/
inductive ExtendType where
  | uxtb | uxth | uxtw | uxtx | sxtb | sxth | sxtw | sxtx
deriving Repr, DecidableEq, Inhabited

/-- Logical operation field `opc` (2 bits): 00 AND, 01 ORR, 10 EOR, 11 ANDS.
With the `N` (invert) bit of the shifted-register form these become BIC/ORN/EON/BICS. -/
inductive LogicOp where
  | and | orr | eor | ands
deriving Repr, DecidableEq, Inhabited

/-- Move-wide `opc` field: 00 MOVN, 10 MOVZ, 11 MOVK (01 is unallocated). -/
inductive MoveWideOp where
  | movn | movz | movk
deriving Repr, DecidableEq, Inhabited

/-- Bitfield `opc` field: 00 SBFM, 01 BFM, 10 UBFM (11 is unallocated). -/
inductive BitfieldOp where
  | sbfm | bfm | ubfm
deriving Repr, DecidableEq, Inhabited

/-- Addressing mode of the single-register `imm9` load/store forms (bits 11:10):
00 unscaled offset (LDUR/STUR), 01 post-index, 11 pre-index. (10, unprivileged, is not
supported.) -/
inductive Imm9Mode where
  | unscaled | post | pre
deriving Repr, DecidableEq, Inhabited

/-- Addressing mode of the register-pair forms (bits 24:23):
01 post-index, 10 signed offset, 11 pre-index. (00, LDNP/STNP, is not supported.) -/
inductive PairMode where
  | post | offset | pre
deriving Repr, DecidableEq, Inhabited

/-- LSE atomic memory operation (`o3:opc`, bits 15:12): 0000 LDADD, 0001 LDCLR, 0010 LDEOR,
0011 LDSET, 0100 LDSMAX, 0101 LDSMIN, 0110 LDUMAX, 0111 LDUMIN, 1000 SWP. -/
inductive AtomicOp where
  | add | clr | eor | set | smax | smin | umax | umin | swp
deriving Repr, DecidableEq, Inhabited

inductive Instr where
  -- Data processing: immediate
  /-- ADR (`op = false`) / ADRP (`op = true`). `rd`: ZR. -/
  | adr (op : Bool) (immlo immhi : Nat) (rd : Nat)
  /-- ADD/ADDS/SUB/SUBS (immediate). `op = true` is SUB, `S` sets flags, `sh` = LSL #12.
  `rn`: SP. `rd`: SP if `S = false` (ADD/SUB), ZR if `S = true` (ADDS/SUBS, CMP/CMN). -/
  | addSubImm (sf op S sh : Bool) (imm12 rn rd : Nat)
  /-- AND/ORR/EOR/ANDS (immediate); the bitmask is `DecodeBitMasks(N, imms, immr)`.
  `rn`: ZR. `rd`: SP for AND/ORR/EOR, ZR for ANDS (TST). -/
  | logicalImm (sf : Bool) (opc : LogicOp) (N : Bool) (immr imms rn rd : Nat)
  /-- MOVN/MOVZ/MOVK; the immediate is placed at bit `16 * hw`. `rd`: ZR. -/
  | moveWide (sf : Bool) (opc : MoveWideOp) (hw imm16 rd : Nat)
  /-- SBFM/BFM/UBFM. `rn`, `rd`: ZR. -/
  | bitfield (sf : Bool) (opc : BitfieldOp) (N : Bool) (immr imms rn rd : Nat)
  /-- EXTR (and ROR #imm when `rn = rm`). `rm`, `rn`, `rd`: ZR. -/
  | extr (sf N : Bool) (rm imms rn rd : Nat)
  -- Branches, hints, barriers
  /-- B (`op = false`) / BL (`op = true`). -/
  | b (op : Bool) (imm26 : Nat)
  /-- B.cond. -/
  | bcond (imm19 cond : Nat)
  /-- CBZ (`op = false`) / CBNZ (`op = true`). `rt`: ZR. -/
  | cb (sf op : Bool) (imm19 rt : Nat)
  /-- TBZ (`op = false`) / TBNZ (`op = true`) of bit `b5:b40`. `rt`: ZR. -/
  | tb (b5 op : Bool) (b40 imm14 rt : Nat)
  /-- BR. `rn`: ZR. -/
  | br (rn : Nat)
  /-- BLR. `rn`: ZR. -/
  | blr (rn : Nat)
  /-- RET. `rn`: ZR. -/
  | ret (rn : Nat)
  /-- HINT `CRm:op2` (only the ones whose effect is "none" in this model: see `Decode`). -/
  | hint (crm op2 : Nat)
  /-- DSB (`op2 = 4`) / DMB (`op2 = 5`) / ISB (`op2 = 6`) with option `CRm`. -/
  | barrier (crm op2 : Nat)
  /-- CLREX #`CRm`: clears the local exclusive monitor. The monitor is not modelled (no
  store-exclusive is accepted, see `Decode`), so this only advances `pc`. -/
  | clrex (crm : Nat)
  /-- MRS `Xt`, DCZID_EL0 (the only system register read accepted). `rt`: ZR. The value is
  `State.dczid`, an implementation-defined constant that theorems quantify over. -/
  | mrsDczid (rt : Nat)
  /-- DC ZVA, `Xt`: zero the naturally aligned block of `4 << DCZID_EL0.BS` bytes containing
  `X[t]`. `rt`: ZR. -/
  | dcZva (rt : Nat)
  /-- MRS `Xt`, TPIDR_EL0 (the EL0 thread pointer). `rt`: ZR. The value is `State.tpidr`. -/
  | mrsTpidr (rt : Nat)
  -- Loads and stores (general-purpose registers only, `V = 0`)
  /-- LDR (literal): `opc` 00 = LDR Wt, 01 = LDR Xt, 10 = LDRSW Xt. `rt`: ZR. -/
  | ldrLit (opc imm19 rt : Nat)
  /-- LDR/STR family, unsigned scaled 12-bit offset. `size`: log2 of the access size;
  `opc`: 00 store, 01 load (zero-extend), 10 load signed to 64 bits, 11 load signed to 32 bits.
  `rn`: SP. `rt`: ZR. -/
  | ldstUImm (size opc imm12 rn rt : Nat)
  /-- LDUR/STUR family and pre/post-indexed forms with signed `imm9`. Fields as in
  `ldstUImm`. `rn`: SP. `rt`: ZR. -/
  | ldstImm9 (size opc : Nat) (mode : Imm9Mode) (imm9 rn rt : Nat)
  /-- LDR/STR family, register offset `ExtendReg(rm, option, S ? size : 0)`.
  `rn`: SP. `rm`, `rt`: ZR. -/
  | ldstReg (size opc rm : Nat) (option : ExtendType) (S : Bool) (rn rt : Nat)
  /-- LDP/STP/LDPSW: `opc` 00 = 32-bit, 01 = LDPSW (`L = true` only), 10 = 64-bit; `L` = load.
  `rn`: SP. `rt`, `rt2`: ZR. -/
  | ldstPair (opc : Nat) (mode : PairMode) (L : Bool) (imm7 rt2 rn rt : Nat)
  /-- PRFM/PRFUM (immediate, unscaled, register and literal forms): a prefetch hint. It never
  faults and has no architectural effect, so only `pc` advances. `prfop` is the raw `Rt`
  field. -/
  | prefetch (prfop : Nat)
  -- Ordered, exclusive and atomic accesses (single-threaded model: see `Exec`)
  /-- LDAR/STLR (`L` = load) of `2^size` bytes; LDAPR when `rcpc`. `rn`: SP. `rt`: ZR. -/
  | ldstOrdered (size : Nat) (L rcpc : Bool) (rn rt : Nat)
  /-- LDXR (`o0 = false`) / LDAXR (`o0 = true`) of `2^size` bytes (store-exclusives are not
  decoded). `rn`: SP. `rt`: ZR. -/
  | ldExcl (size : Nat) (o0 : Bool) (rn rt : Nat)
  /-- LSE atomic `LD<op>{A}{L}` / `SWP{A}{L}` of `2^size` bytes: `A` = acquire, `R` = release.
  The ST<op> aliases are `rt = 31`. `rn`: SP. `rs`, `rt`: ZR. -/
  | atomic (size : Nat) (A R : Bool) (rs : Nat) (op : AtomicOp) (rn rt : Nat)
  /-- CAS{A}{L}{B,H} of `2^size` bytes: `L` = acquire, `o0` = release. `rn`: SP. `rs`, `rt`: ZR. -/
  | cas (size : Nat) (L o0 : Bool) (rs rn rt : Nat)
  /-- CASP{A}{L} of a register pair, 32-bit (`sz = false`) or 64-bit (`sz = true`) halves;
  `rs`, `rt` even. `rn`: SP. `rs`, `rs+1`, `rt`, `rt+1`: ZR. -/
  | casp (sz L o0 : Bool) (rs rn rt : Nat)
  -- SIMD&FP loads and stores (`V = 1`): the transfer register `rt`/`rt2` is a V register.
  /-- LD1/ST1 (multiple structures, `L` = load) of `rpt` = 1–4 consecutive registers
  (`opcode` 0111/1010/0110/0010), `Q` = 128-bit registers, `size` the element size (it does not
  change the bytes transferred). `post`: post-index by `X[m]`, or by the transfer size for
  `rm = 31`. `rn`: SP. -/
  | vldstMulti (Q L : Bool) (opcode size : Nat) (post : Bool) (rm rn rt : Nat)
  /-- LD1–LD4 / ST1–ST4 (single structure: one lane of `selem = opcode<0>:R + 1` consecutive
  registers) and LD1R–LD4R (load and replicate, `opcode = 11x`). Lane and element size from
  `Q:S:size` as in the decode pseudocode (`vSingleLayout`). `post`: post-index by `X[m]`, or by
  the transfer size for `rm = 31`. `rn`: SP. -/
  | vldstSingle (Q L R : Bool) (opcode : Nat) (S : Bool) (size : Nat) (post : Bool) (rm rn rt : Nat)
  /-- LDR St/Dt/Qt (literal): `opc` 00 = 4 bytes, 01 = 8, 10 = 16. -/
  | vldrLit (opc imm19 rt : Nat)
  /-- LDR/STR B/H/S/D/Q, unsigned scaled offset; access size `2^(opc<1>:size)` bytes,
  `opc<0>` = load. `rn`: SP. -/
  | vldstUImm (size opc imm12 rn rt : Nat)
  /-- LDUR/STUR and pre/post-indexed LDR/STR of B/H/S/D/Q. `rn`: SP. -/
  | vldstImm9 (size opc : Nat) (mode : Imm9Mode) (imm9 rn rt : Nat)
  /-- LDR/STR B/H/S/D/Q, register offset. `rn`: SP. `rm`: ZR. -/
  | vldstReg (size opc rm : Nat) (option : ExtendType) (S : Bool) (rn rt : Nat)
  /-- LDP/STP of S/D/Q registers: `opc` 00 = 4 bytes, 01 = 8, 10 = 16. `rn`: SP. -/
  | vldstPair (opc : Nat) (mode : PairMode) (L : Bool) (imm7 rt2 rn rt : Nat)
  -- Advanced SIMD data processing (integer and move instructions only)
  /-- Three same (vector), integer subset: `opcode = w<15:11>` (see `threeSameOp`). -/
  | vThreeSame (Q U : Bool) (size rm opcode rn rd : Nat)
  /-- Scalar three same on D registers (`size = 11`): ADD/SUB, CMTST/CMEQ, CMGT/CMHI,
  CMGE/CMHS. -/
  | vScalarThreeSame (U : Bool) (size rm opcode rn rd : Nat)
  /-- Copy: DUP (element, `imm4 = 0000`), DUP (general, `0001`; `rn`: ZR), INS (general, `0011`;
  `rn`: ZR), SMOV (`0101`; `rd`: ZR), UMOV (`0111`; `rd`: ZR); INS (element) for `op = 1`. -/
  | vCopy (Q op : Bool) (imm5 imm4 rn rd : Nat)
  /-- Across lanes: SADDLV/UADDLV, SMAXV/UMAXV, SMINV/UMINV, ADDV (`opcode = w<16:12>`). -/
  | vAcross (Q U : Bool) (size opcode rn rd : Nat)
  /-- Two-register miscellaneous, integer subset (`opcode = w<16:12>`, see `twoMiscOp`; XTN is
  `opcode = 10010`). -/
  | vTwoMisc (Q U : Bool) (size opcode rn rd : Nat)
  /-- Shift by immediate (`immh ≠ 0`): SSHR/USHR, SSRA/USRA, SHL, SLI, SRI, SHRN, SSHLL/USHLL. -/
  | vShiftImm (Q U : Bool) (immh immb opcode rn rd : Nat)
  /-- Modified immediate: MOVI/MVNI/ORR/BIC (vector, immediate) and FMOV (vector, immediate);
  `imm8 = a:b:c:d:e:f:g:h`. -/
  | vModImm (Q op : Bool) (cmode imm8 rd : Nat)
  /-- EXT: bytes `imm4 ..` of `V[m]:V[n]`. -/
  | vExt (Q : Bool) (rm imm4 rn rd : Nat)
  /-- TBL (`op = false`) / TBX of `len + 1` table registers starting at `V[n]`. -/
  | vTbl (Q : Bool) (rm len : Nat) (op : Bool) (rn rd : Nat)
  /-- AESE (`opcode = 00100`), AESD (`00101`), AESMC (`00110`), AESIMC (`00111`) (FEAT_AES). -/
  | vAes (opcode rn rd : Nat)
  /-- The cryptographic-extension (SHA1/SHA256/SHA512/SHA3, PMULL), CRC32, permute (ZIP/UZP/TRN)
  and scalar DUP classes: `Janus.Arm64.CryptoInstr` (`Janus/Arm64/InstrCrypto.lean`). -/
  | crypto (c : CryptoInstr)
  /-- FMOV between a general and a SIMD&FP register (bit moves only): `sf`, `ftype`, `rmode`,
  `opcode` as encoded (`opcode = 110`: to general, `111`: to SIMD&FP). General register: ZR. -/
  | fmovGen (sf : Bool) (ftype rmode opcode rn rd : Nat)
  -- Scalar floating point (`Janus.Arm64.ExecFloat`); `ftype` is 00 (single) or 01 (double).
  /-- Floating-point data-processing (1 source), `opcode = w<20:15>`: FMOV (0), FABS (1),
  FNEG (2), FSQRT (3), FCVT to single (4) / double (5), FRINTN/P/M/Z/A (8–12), FRINTX (14),
  FRINTI (15). -/
  | fpDP1 (ftype opcode rn rd : Nat)
  /-- Floating-point data-processing (2 source), `opcode = w<15:12>`: FMUL (0), FDIV (1),
  FADD (2), FSUB (3), FMAX (4), FMIN (5), FMAXNM (6), FMINNM (7), FNMUL (8). -/
  | fpDP2 (ftype rm opcode rn rd : Nat)
  /-- Floating-point data-processing (3 source): FMADD (`o1 o0 = 00`), FMSUB (01),
  FNMADD (10), FNMSUB (11). -/
  | fpDP3 (ftype : Nat) (o1 : Bool) (rm : Nat) (o0 : Bool) (ra rn rd : Nat)
  /-- FCMP (`opc<1> = 0`) / FCMPE (`opc<1> = 1`), with `#0.0` when `opc<0> = 1` (then
  `rm = 0`). -/
  | fpCmp (ftype rm opc rn : Nat)
  /-- FCCMP (`signal = false`) / FCCMPE. -/
  | fpCcmp (ftype rm cond : Nat) (signal : Bool) (rn nzcv : Nat)
  /-- FCSEL. -/
  | fpCsel (ftype rm cond rn rd : Nat)
  /-- FMOV (scalar, immediate), `imm8 = w<20:13>`. -/
  | fpImm (ftype imm8 rd : Nat)
  /-- Conversion between floating point and integer other than FMOV: FCVT{N,P,M,Z}{S,U}
  (`opcode = 00u`, rounding `rmode`), SCVTF/UCVTF (`01u`, `rmode = 00`), FCVTA{S,U} (`10u`,
  `rmode = 00`). General register (`rn` of SCVTF/UCVTF, `rd` of the others): ZR. -/
  | fpCvtInt (sf : Bool) (ftype rmode opcode rn rd : Nat)
  -- Data processing: register
  /-- AND/BIC/ORR/ORN/EOR/EON/ANDS/BICS (shifted register); `N` inverts the second operand.
  All registers: ZR. -/
  | logicalShifted (sf : Bool) (opc : LogicOp) (shift : ShiftType) (N : Bool) (rm imm6 rn rd : Nat)
  /-- ADD/ADDS/SUB/SUBS (shifted register); `shift` is never ROR. All registers: ZR. -/
  | addSubShifted (sf op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat)
  /-- ADD/ADDS/SUB/SUBS (extended register), `imm3 ≤ 4`.
  `rn`: SP. `rm`: ZR. `rd`: SP if `S = false`, ZR if `S = true`. -/
  | addSubExt (sf op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat)
  /-- ADC/ADCS/SBC/SBCS. All registers: ZR. -/
  | addSubCarry (sf op S : Bool) (rm rn rd : Nat)
  /-- CCMN (`op = false`) / CCMP (`op = true`), register. Registers: ZR. -/
  | condCmpReg (sf op : Bool) (rm cond rn nzcv : Nat)
  /-- CCMN / CCMP, 5-bit unsigned immediate. `rn`: ZR. -/
  | condCmpImm (sf op : Bool) (imm5 cond rn nzcv : Nat)
  /-- CSEL (`op=0,o2=0`), CSINC (`0,1`), CSINV (`1,0`), CSNEG (`1,1`). Registers: ZR. -/
  | condSel (sf op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat)
  /-- MADD (`o0 = false`) / MSUB (`o0 = true`). Registers: ZR. -/
  | madd (sf o0 : Bool) (rm ra rn rd : Nat)
  /-- SMADDL/SMSUBL (`U = false`), UMADDL/UMSUBL (`U = true`); always 64-bit. Registers: ZR. -/
  | maddl (U o0 : Bool) (rm ra rn rd : Nat)
  /-- SMULH (`U = false`) / UMULH (`U = true`). Registers: ZR. -/
  | mulh (U : Bool) (rm rn rd : Nat)
  /-- UDIV (`o1 = false`) / SDIV (`o1 = true`). Registers: ZR. -/
  | div (sf o1 : Bool) (rm rn rd : Nat)
  /-- LSLV/LSRV/ASRV/RORV. Registers: ZR. -/
  | shiftV (sf : Bool) (op2 : ShiftType) (rm rn rd : Nat)
  /-- RBIT. Registers: ZR. -/
  | rbit (sf : Bool) (rn rd : Nat)
  /-- REV16 (`opc = 1`), REV32 (`opc = 2`, 64-bit) / REV (`opc = 2`, 32-bit),
  REV (`opc = 3`, 64-bit only). Registers: ZR. -/
  | rev (sf : Bool) (opc rn rd : Nat)
  /-- CLZ. Registers: ZR. -/
  | clz (sf : Bool) (rn rd : Nat)
  /-- CLS. Registers: ZR. -/
  | cls (sf : Bool) (rn rd : Nat)
  -- Kernel, trap and environment instructions (WP-C, `Janus.Arm64.DecodeSys`, `Janus.Kernel`)
  /-- SVC #`imm16` (only `#0` is decoded): a Linux system call. Executes as `Fault.kernel`; the
  kernel semantics `Janus.Kernel.ReturnsK` gives its effect at the `.syscall` stub the
  extractor puts here. -/
  | svc (imm16 : Nat)
  /-- BRK #`imm16`: a breakpoint, `Fault.trap pc 5` (`SIGTRAP`). -/
  | brk (imm16 : Nat)
  /-- UDF #`imm16` (the permanently undefined encoding `0x0000xxxx`): `Fault.trap pc 4`
  (`SIGILL`). -/
  | udf (imm16 : Nat)
  /-- MRS `Xt`, `r` for an environment register `r` (`CNTVCT_EL0`, `CNTFRQ_EL0`, `MIDR_EL1`,
  `DIT`). `rt`: ZR. Executes as `Fault.kernel`; `Janus.Kernel` gives the value. -/
  | mrsEnv (r : EnvReg) (rt : Nat)
  /-- MSR DIT, #`imm` (`imm ∈ {0, 1}`): sets `PSTATE.DIT`. Executes as `Fault.kernel`. -/
  | msrDitImm (imm : Nat)
  /-- MSR DIT, `Xt` (`PSTATE.DIT ← Xt<24>`). `rt`: ZR. Executes as `Fault.kernel`. -/
  | msrDitReg (rt : Nat)
  /-- MRS `Xt`, NZCV: `N Z C V` in bits 31:28, zero elsewhere. `rt`: ZR. -/
  | mrsNzcv (rt : Nat)
  /-- MSR NZCV, `Xt`: the flags from bits 31:28 of `Xt`. `rt`: ZR. -/
  | msrNzcv (rt : Nat)
  /-- MRS `Xt`, FPSR (zero-extended). `rt`: ZR. -/
  | mrsFpsr (rt : Nat)
  /-- MSR FPSR, `Xt`: `FPSR ← Xt<31:0>` restricted to the implemented bits (`fpsrMask`). `rt`: ZR. -/
  | msrFpsr (rt : Nat)
deriving Repr, DecidableEq, Inhabited

end Janus.Arm64
