# Janus soundness audit: floating point

This round reviews the scalar floating-point support (`Janus/Float`, `Janus/Arm64/Float.lean`,
`ExecFloat.lean`, `DecodeFloat.lean`, `Janus/Amd64/Float.lean`, the bridge lemmas, and the four
`examples/basic/float.go` theorems on both ISAs). It is the first audit of that code.

Guarantee under review: *a `Verified` result about floating-point code is true on real hardware,
and does not read as more than what is proven.*

The rows are in `audit/rt-fp/` (`run.sh`; the corpus generators `gen-a64/` and `gen-x64/`, the
decoder sweep `decode/`, the specification check `SpecTestFloat.lean`/`spec-testfloat.sh`, and
the hardware probe `probe/mxcsr/`). Severities are as in earlier rounds. **Critical** means a
misleading account prints `Verified`. **High** means a false claim about the binary prints
`Verified`, or (here) a theorem that reads as covering Go calls covers none of them. **Low**
means hygiene.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| X64-MXCSR-STICKY | **high** (vacuity) | **The amd64 FP theorems held for no real call.** `AddF64`, `Dot3` and `F64ToU64` on amd64 required `s.mxcsr = 0x1F80`, "the value Linux gives every process and Go never changes". `MXCSR` also holds the six sticky status flags, and Go's own floating point raises them: a Go program's `main` already runs with `MXCSR = 0x1FA0` (`PE` set by the runtime's start-up arithmetic). After that, no call satisfies the precondition, so the three theorems said nothing about any call made by initialised Go code, while their docstrings, the README and `SOUNDNESS.md` presented them as covering every Go call. | **BROKEN → fixed** |
| DOC-ABI-MXCSR | low | `SOUNDNESS.md` said "the ABI says nothing about FPSR/MXCSR flags on return". Go's `abi-internal.md` calls the MXCSR status bits callee-save. Go code does not preserve them (the verified `AddF64` itself sets `PE`), and `ABIReturn` does not include them, so "obeys the ABI" was stronger in the text than in the definition. | fixed (documented) |
| DOC-TRAP | low | README: `F64ToU64` on arm64 gives "the exact `FPToFixed` for every `FPCR`". The theorem assumes `FP.trapEnables s.fpcr.toNat = 0`. | fixed |
| DOC-ORACLE | low | `ORACLE-AMD64.md` still listed the MXCSR status bits as "neither modelled nor compared". The FP harness compares them. | fixed |
| X64-V3-FMA | hazard | With `GOAMD64=v3`, Go fuses `Dot3` into `MULSD` and two `VFMADD231SD`, as `fma(a2, b2, fma(a0, b0, a1·b1))`. That is a third association, different from both theorems. The decoder rejects VEX FMA, so the v1 theorem cannot be carried over to such a build. | no issue (row keeps it so) |
| A64-*, X64-*, DEC-*, SPEC-TF | none | 469,029 new arm64 cases against qemu and Sail, 446,027 new amd64 cases against the host CPU, a 2.9M-word decoder sweep against GNU objdump, and 1.5M SoftFloat vectors run directly against the specifications: no disagreement anywhere. | no issue |

**This round found one BROKEN item, X64-MXCSR-STICKY (high: the amd64 floating-point theorems
were vacuous for real Go calls). It is fixed and has regression rows. The models themselves held
on every new case.**

---

## X64-MXCSR-STICKY (HIGH, BROKEN → fixed): the amd64 FP preconditions excluded every real call

`MXCSR` is one register with two parts. Bits 15:6 are control bits (`FTZ`, `RC`, the masks,
`DAZ`); bits 5:0 are the sticky status flags `IE DE ZE OE UE PE`. Go's `abi-internal.md` fixes
the control bits at every call. It cannot fix the flags, which are sticky, and every inexact SSE
operation sets `PE`. The three amd64 example theorems asked for the whole register:

```
(fun s => … ∧ s.mxcsr = 0x1F80)
```

**Probe** (`audit/rt-fp/probe/mxcsr`, `GOAMD64=v1`, go1.26.0, on the Xeon Gold 5412U host). The
program reads `MXCSR` with `STMXCSR` at the start of `main` and after one addition:

```
$ mxcsr 0.1 0.2
main-entry=0x1fa0 after-add=0x1fa0 sum=0.30000000000000004
$ mxcsr 1 2
main-entry=0x1fa0 after-add=0x1fa0 sum=3
```

The runtime's initialisation does inexact arithmetic of its own (GC pacing, for one), so `PE` is
set before any user code runs, and nothing in Go clears it. Every call from user code therefore
has `MXCSR ≠ 0x1F80`, and the three theorems said nothing about it. Their statements printed
correctly, so this is not a false claim about the binary. But each docstring, the README row
("under the default `FPCR`/`MXCSR`") and `SOUNDNESS.md` ("Go never changes them") presented the
precondition as what every Go call has. On arm64 the flags live in a separate register, `FPSR`,
which the theorems leave free. `FPCR` reads 0 at `main` under qemu (row A64-FPCR-REAL), so the
arm64 theorems are not affected.

**Fix.**

* `Janus.Amd64.GoABI.GoMXCSR s := s.mxcsr.toNat / 64 = 0x1F80 / 64`. This fixes the control
  bits and the reserved bits 31:16, and leaves the six flags arbitrary: exactly what the ABI
  guarantees at a call.
* `Janus.Amd64.Tactic.GoMXCSR.ctl`, `.unmasked` and `.mod` (`Janus/Amd64/TacticFloat.lean`, proved).
  Given to `janus64_run`, they make every trap check and every rounding control a closed literal,
  also after earlier instructions have raised flags (`ctl_raise`, `unmasked_raise`). An
  `example` checks that `GoMXCSR` accepts `0x1FA0`.
* The amd64 `AddF64`, `Dot3` and `F64ToU64` theorems now assume `GoMXCSR s`. The proofs changed
  only in what they pass to `janus64_run`. The printed statements now end in
  `Janus.Amd64.GoABI.GoMXCSR s`, a framework definition documented like `StackWritable`.
* `SOUNDNESS.md` ("State and quantification"), `State.lean`, the README and the proof
  docstrings say what the flags do.

**Rows.** `X64-MXCSR-STICKY hw` re-runs the probe and checks in Lean (`decide`) that the value
`main` sees satisfies `GoMXCSR` but not `= 0x1F80`. `X64-MXCSR-STICKY proofs` fails if any amd64
example proof states `s.mxcsr = 0x1F80` again, and verifies the three theorems, checking that
`GoMXCSR` is in each printed statement.

## DOC-ABI-MXCSR (low): "obeys the ABI" and the MXCSR flags

Go's `abi-internal.md` (amd64) says: "The MXCSR status bits are callee-save." No Go function
honours this. `AddF64` is a single `ADDSD`: it sets `PE` on every inexact sum and returns. Janus's
`ABIReturn` (RSP, RBP, R14, X15) does not include the flags, so a verified "obeys the ABI" cannot
mean them. `SOUNDNESS.md` used to say the ABI was silent about them. It now says what the ABI
says, that Go does not do it, and that `ABIReturn` (and so every theorem) leaves the flags out.
`FPSR` on arm64 is scratch in the ABI, which matches.

## DOC-TRAP, DOC-ORACLE (low)

The README now states the trap-enable condition of the arm64 `F64ToU64`/`AddF64` `exact`
theorems (`FP.trapEnables s.fpcr.toNat = 0`). `ORACLE-AMD64.md` no longer lists the MXCSR status
bits among the uncompared state. Row `DOC-FP` checks both texts.

## X64-V3-FMA (hazard): the amd64 Dot3 theorem is a `GOAMD64=v1` theorem

`Dot3` from a `GOAMD64=v3` build (GNU `objdump -d`; Go's own objdump misprints the VEX
encodings as `MOVL`):

```
f2 0f 59 e1          mulsd       %xmm1,%xmm4              # X4 = a1*b1
c4 e2 e1 b9 e0       vfmadd231sd %xmm0,%xmm3,%xmm4        # X4 = b0*a0 + X4
c4 e2 d1 b9 e2       vfmadd231sd %xmm2,%xmm5,%xmm4        # X4 = b2*a2 + X4
0f 10 c4             movups      %xmm4,%xmm0
c3                   ret
```

That is `fma(a2, b2, fma(a0, b0, a1·b1))`. Arm64 fuses the other way round,
`fma(a2, b2, fma(a1, b1, a0·b0))`, and v1 does not fuse at all. The Go spec allows all three. A
theorem is about one binary (SHA-256), and the README and `float.go` say which fusion each one
proves. Row `X64-V3-FMA` builds the v3 binary, checks that the fused instructions are there,
and checks that the v1 proof does not verify against it: the decoder rejects VEX FMA, so no
theorem about a v3 build can be had by accident. Likewise, `math.FMA`'s `VFMADD231SD` path
behind `x86HasFMA` and `ROUNDSD` behind `x86HasSSE41` (`math.Floor` …) are reached only with
the flag's memory stated in a precondition (a writable `.noptrbss` byte, never copied).

## Models against hardware (no issue)

The stock corpora (`docs/ORACLE*.md`) sample `FPCR`/`MXCSR` at random. These rows add
systematic grids where random sampling is thin.

**A64-QEMU** (`gen-a64`, 469,029 cases against qemu 10.2.1 `-cpu max`, 0 MISMATCH, 0 gap):

* `FMADD FMSUB FNMADD FNMSUB`, S and D, over the cube of 11 special operands (±0, ±∞, ±normal,
  a negative denormal, quiet and signalling NaNs of both signs with payloads). FPCR runs over 24
  values: `RMode` RNE/RMI crossed with `FZ`, `DN`, `AH`, `FIZ` alone and together, and `NEP`
  (255,552 cases). Exact cancellation (`3·5 − 15` under every one of the 64 `RMode × FZ × DN × AH
  × FIZ` values, zero products with signed zero addends) and fused results at the underflow
  boundary (8,192).
* The nine 2-source operations over a 13×13 grid under 24 FPCR values, plus products and
  quotients just below the minimum normal under all 64 (93,744).
* `FCMP`/`FCMPE` (register and `#0.0`) with `FZ`/`FIZ`/`AH` flushing denormals to equal zero
  (8,112). `FSQRT` of −0, negative denormals (flushed or not), −∞ and NaNs, under all 64 FPCR
  values, with and without `NEP` (4,608).
* `FCVT` D→S at the single-precision underflow boundary, where tininess before rounding (`AH =
  0`) and after rounding (`AH = 1`) disagree, for example `2^-126 − 2^-151` with `FZ = 1`
  (flushed to zero with `UFC` when `AH = 0`, rounded to `2^-126` when `AH = 1`). Also the
  overflow threshold `(2 − 2^-24)·2^127` ± ε, ties, D denormals, and NaN payloads that live only
  in the 29 truncated bits; `FCVT` S→D of denormals and NaNs. All 64 FPCR values (5,061).
* `FCVT{N,P,M,Z,A}{S,U}` to W and X from S and D at ±2^31, ±2^32, ±2^63, ±2^64, one ulp either
  side, `2^k − ulp/2`, `2^k ± 0.5`, ties at .5, denormals with `FZ`/`FIZ`/`AH`, NaN and ∞
  (25,680). `SCVTF`/`UCVTF` of integers at the S and D rounding ties around every power of two
  from 2^20 to 2^63, signed and unsigned, 32 and 64 bit, all four `RMode` values (50,944).
* `FRINT{N,P,M,Z,A,X,I}` on ties and near-ties at every magnitude up to 2^53 (including
  `2^52 − 0.5` and `2^23 − 0.5`), denormals, ±0, NaNs, under 24 FPCR values (17,136).

**A64-SAIL**: the same corpus on the Sail Armv9.4-A model (`scripts/oracle-sail.sh run`, driver
built from this tree), three ways: Janus vs Sail 0 MISMATCH (469,029 agree), qemu vs Sail 0
MISMATCH. NEP, AH, FIZ, DN and FZ were included, alone and together.

**X64-HOST** (`gen-x64`, 446,027 cases against the Xeon Gold 5412U, 0 MISMATCH, 91,046 of them
`#XM` on both sides):

* `ADD MUL SUB DIV SQRT MIN MAX` `SD`/`SS` over a 14×14 grid (the indefinite among the NaNs).
  Each runs under the 16 `RC × FTZ × DAZ` settings with everything masked, then under **all 64
  exception-mask subsets** (random `RC`/`FTZ`/`DAZ`). This tests which exception traps first
  when several are unmasked (219,520).
* Operand pairs that raise several exceptions at once (`DE` with `UE`/`PE`, `OE` with `PE`, `ZE`
  with `DE`, `IE` with `DE`, exact tiny results), under all 64 mask subsets × `FTZ` × `DAZ`
  (53,760).
* `UCOMISD COMISD UCOMISS COMISS` over the grid under the same 80 `MXCSR` values (62,720).
  `CMPSD`/`CMPSS` with each of the 8 predicates over the grid, with `DAZ` and `IE`/`DE`
  unmasked (18,816).
* `CVTSI2SD/SS` of 32- and 64-bit integers, negative ones included, at every S/D tie from 2^20
  to 2^63, in all four `RC` values with `PE` masked and unmasked (45,344). `CVT(T)SD2SI` and
  `CVT(T)SS2SI` at the integer boundaries and ties, denormals under `DAZ` in every `RC`, NaNs,
  with `IE`/`PE` unmasked (12,800). `CVTSD2SS` at the single underflow and overflow boundaries
  and with NaN payloads, and `CVTSS2SD`, under every `RC × FTZ × DAZ` value and `UE`/`OE`/`PE`
  unmasked (1,272). `ROUNDSD`/`ROUNDSS` with every `imm8` low nibble on ties, denormals under
  `DAZ`, NaNs, with `IE`/`PE` unmasked (16,000).

**DEC-A64.** `janus-decode` against `aarch64-linux-gnu-objdump` on 2,949,120 words: every
value of bits 31:24 in the scalar FP space (`M`, `S`, 3-source) and the Advanced SIMD vector
and scalar neighbours, every value of bits 23:10, and 9 patterns of bits 9:0. The comparison
fails if the model accepts a word objdump calls undefined, decodes an FP word as another
instruction, precision or register size, or decodes an FP mnemonic as a non-FP instruction.
Result: 0 disagreements, 176,229 accepted. The words objdump accepts and the model rejects are
all half precision (`ftype = 11`), the fixed-point conversions, and FMOV to and from `H`.
`ftype = 10`, `FRINT32*/64*`, `BFCVT` and `FJCVTZS` are all rejected.

**DEC-X64**: 39 legacy-prefix/REX combinations (repeated, mixed or reordered mandatory
prefixes, REX before a legacy prefix, double REX, `67`, segment overrides, `LOCK`) on 45 SSE
opcodes of the `0F` and `0F 3A` maps, register and memory forms: 15,795 host cases, 0 MISMATCH
(about 4,700 gaps, all encodings the decoder rejects on purpose).

**SPEC-TF.** The *specifications* `Janus.Float.add`, `mul` and `fma` (all five rounding
directions) and `truncInt` (to `i32 i64 ui32 ui64`), checked directly against SoftFloat 3e
(`testfloat_gen`, level 1): 1,534,752 vectors, 0 mismatches. Before, only the machine models
had been checked against SoftFloat (`scripts/testfloat.sh`), and the specifications only
through the proved bridge lemmas. The specifications are defined with the same rounding core as
the models, so this checks that "the IEEE sum" in a printed theorem is the IEEE sum, against an
implementation that shares no code with Janus.

**What the statements assume.** The arm64 `correctness` theorems print `s.fpcr = 0`
(`FPCR.RMode = RNE`, no `FZ`/`DN`/`AH`/`FIZ`/`NEP`, no trap enables). The `exact` theorems print
`FP.trapEnables s.fpcr.toNat = 0`. The amd64 theorems now print `GoABI.GoMXCSR s`. No FP
assumption is hidden in `CallSetup`: the amd64 one fixes only `X15 = 0` and `DF = 0`, the arm64
one nothing FP. `FPSR` and the `MXCSR` flags are free in every call state.

**Hazards that remain, documented.**

* The amd64 rows ran on one Intel CPU. The theorems use only `GoMXCSR` (all masked, no
  `DAZ`/`FTZ`) and state no flags, so the vendor differences that are possible (`DE`, the
  `MINSD`/`MAXSD`-under-`DAZ` rule the model learned from this host) cannot affect them.
* Arm64 is checked against qemu and Sail, not silicon. Both implement FEAT_AFP. With `FPCR = 0`
  the AFP bits play no part. The `exact` theorems quantify over `AH`/`FIZ`/`NEP` too, which a
  CPU without FEAT_AFP keeps zero (`SOUNDNESS.md`).
* `s.fpcr = 0` also asks for `FZ16`, `AHP` and the RES0 bits to be zero. Go's ABI does not
  mention them, but Linux starts processes with `FPCR = 0` and nothing in Go writes it
  (A64-FPCR-REAL).

## Result table (`audit/rt-fp/run.sh`)

| row | expect | result |
|---|---|---|
| A64-QEMU (469k cases) | ok | 0 MISMATCH, 469,029 agree, 0 gap |
| A64-SAIL | ok | Janus vs Sail 0 MISMATCH (469,029 agree); qemu vs Sail 0 MISMATCH |
| X64-HOST (446k cases) | ok | 0 MISMATCH, 441,332 agree, ~4,700 gap (all in the prefix sweep; the count varies with the random states) |
| DEC-X64 | ok | 15,795 cases, 0 MISMATCH |
| DEC-A64 | ok | 0 disagreements, 176,229 accepted |
| SPEC-TF | ok | 1,534,752 vectors, 0 mismatches |
| X64-MXCSR-STICKY hw | ok | main sees `0x1fa0`; `GoMXCSR` accepts it, `= 0x1F80` does not |
| X64-MXCSR-STICKY proofs | ok | AddF64, Dot3, F64ToU64 verify with `GoMXCSR` in the statement |
| A64-FPCR-REAL | ok | main sees `FPCR = 0`, `FPSR = 0x10` |
| X64-V3-FMA | blocked | the v1 proof does not verify against the v3 binary |
| DOC-FP | ok | README/SOUNDNESS corrected |
