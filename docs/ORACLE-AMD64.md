# The amd64 differential oracle

The Lean x86-64 model (`Janus.Amd64.step`: decoder in `Janus/Amd64/Decode.lean`, semantics in
`Janus/Amd64/Exec.lean`) is in Janus's trusted base for amd64 proofs. The oracle tests it one
instruction at a time against the x86-64 host CPU itself. No emulator is involved.

## Results

For the final model (`Janus/Amd64/*`) on an Intel Xeon Gold 5412U host (Sapphire Rapids),
Linux with 5-level paging, Go 1.26.0:

| run | cases | agree | of which both fault | model-gap | **MISMATCH** | unobserved |
|---|---:|---:|---:|---:|---:|---:|
| `full`, `SEED=1`, `N=1200 GROUP=60000 K=6 PER_CLASS=6000` | 1,384,074 | 1,210,212 | 358,487 | 173,861 | **0** | 1 |
| `full`, `SEED=7`, same knobs | 1,384,116 | 1,212,897 | 358,151 | 171,219 | **0** | 0 |
| targeted harvest, `K=200`, every distinct real encoding of the new and changed classes (VEX, SSE packed integer, `MOVSS/MOVSD`, `RCL/RCR`, hints, `CLD/STD`, `MOVS/STOS`, `XCHG/XADD/CMPXCHG`, `BSF/BSR`) and every `FS`-prefixed one | 652,400 | 578,353 | 387,855 | 74,047 | **0** | 0 |
| `full`, `SEED=1`, same knobs, with the SSE floating-point model, `MXCSR` in every case, and the `math` harvest (2026-10-24) | 2,028,068 | 1,596,644 | | 431,424 | **0** | 0 |
| `fp` (the floating-point corpus below) | 1,076,394 | 804,700 | 113,299 | 271,694 | **0** | 0 |
| **total** | **6,525,052** | 5,402,806 | | 1,122,245 | **0** | 1 |

The one unobserved case is an `XBEGIN` (TSX) that left the code page. These runs cover `FS`,
YMM/AVX, the SSE packed-integer instructions, `MOVSS/MOVSD`, `RCL/RCR`, the hints, the
direction flag and the split-lock rule (below). Earlier models: 1,187,981 cases (atomics, string
instructions, SSE moves) and 1,011,430, both with 0 mismatches. Quick runs during development
(`SEED=2..4`, about 270,000 cases each) also had 0.

`SEED=1`, broken down by case source:

| source | cases | agree | model-gap | MISMATCH |
|---|---:|---:|---:|---:|
| `harvest/*`: distinct instructions of real Go amd64 code, modelled classes | 422,736 | 421,461 | 1,275 | 0 |
| `harvest-other/*`: a sample of real instructions outside the subset (SSE arithmetic, AVX-512, AES, ...) | 5,346 | 1,784 | 3,562 | 0 |
| `gen/*`: targeted random encodings, about 150 classes plus 25 VEX families | 809,192 | 663,324 | 145,868 | 0 |
| `edge/*`: hand-picked edge families (see below) | 86,800 | 78,995 | 7,805 | 0 |
| `rand/*`: random prefix/opcode/tail strings | 60,000 | 44,648 | 15,351 | 0 |

Model gaps by fault kind (`SEED=1`): `undecodable` 152,082 (encodings outside the subset),
`misaligned` 19,062 (locked accesses that are not naturally aligned: the split-lock rule; this
host runs `split_lock_detect=warn`, so they complete natively), `undefinedResult` 1,727
(BSF/BSR of 0, 16-bit SHLD/SHRD by more than 16), `outsideAllocation` 685 (accesses the
hardware served from mapped memory outside the buffer, e.g. RIP-relative loads from the code
page), `badTarget` 305 (branches to addresses `≥ 2^47`, which are canonical on this
5-level-paging host).

**New and changed classes** (`SEED=1`; `SEED=7` is within a few percent; the targeted
harvest in parentheses). `VEX` is every case starting with `C4`/`C5`, `FS` every case with a `64`
prefix; `MOVS/STOS` are split by the direction flag on entry (the generator sets `DF` in a
quarter of all cases, and half of the `edge/string` ones).

| group | cases | agree | of which both fault | model-gap | MISMATCH |
|---|---:|---:|---:|---:|---:|
| VEX (`VMOVDQU/A`, `VMOVNTDQ`, `VPXOR/VPAND/VPOR/VPCMPEQB`, `VPMOVMSKB`, `VPTEST`, `VPBROADCASTB`, `VZEROUPPER`, near misses, real AVX outside the subset) | 62,682 (+93,000) | 58,773 (+69,288) | 30,018 (+44,030) | 3,909 (+23,712) | 0 |
| SSE packed integer (`PCMPEQB PAND POR PMOVMSKB PSHUFD PSHUFLW PUNPCKLBW`, `edge/vec-cmp`) | 24,237 (+11,800) | 19,986 (+11,800) | 4,042 (+149) | 4,251 | 0 |
| `MOVSS`/`MOVSD` | 21,572 (+394,400) | 20,321 (+394,400) | 10,242 (+309,691) | 1,251 | 0 |
| `RCL`/`RCR` | 57,919 (+4,800) | 32,307 (+4,800) | 10,687 | 25,612 (8/16-bit forms) | 0 |
| `PREFETCHh` | 2,526 (+1,400) | 2,198 (+1,400) | 39 | 328 (reserved hint NOPs, prefixed forms) | 0 |
| `CLD`/`STD` | 2,642 (+400) | 2,043 (+400) | 52 | 599 (prefixed forms) | 0 |
| `MOVS`/`STOS`, `DF = 0` on entry | 13,097 (+454) | 12,560 (+454) | 4,912 (+191) | 537 | 0 |
| `MOVS`/`STOS`, `DF = 1` on entry (backward) | 5,411 (+146) | 5,219 (+146) | 1,648 (+62) | 192 | 0 |
| locked accesses (`LOCK` forms, `XCHG` with memory, `XADD`, `CMPXCHG*`) | 143,773 (+96,600) | 120,379 (+56,089) | 72,753 (+17,790) | 23,394 (19,062 + 40,511 `misaligned`) | 0 |
| `BSF`/`BSR` | 9,069 (+21,800) | 6,162 (+21,561) | 432 | 2,907 (1,647 + 239 `undefinedResult`: zero source) | 0 |
| `FS`-prefixed (`gen`, `edge/tls`, `rand`, harvest) | 42,797 (+2,400) | 33,147 (+2,400) | 20,156 (+327) | 9,650 (`LEA`, string, SSE and other forms the decoder refuses) | 0 |

Every case also compares the upper YMM halves (`YMMH`, captured from the signal frame's XSAVE
area) and the direction flag: most cases start with random nonzero upper halves, so a
legacy-SSE instruction that cleared them, or a VEX.128 one that kept them, would be a mismatch,
and so would a `CLD`/`STD`/string instruction that left `DF` differently from the model.

**Atomics, string instructions and 128-bit moves** (`SEED=1`; `SEED=7` is within a few
percent, also with 0 mismatches):

| cases | count | agree | of which both fault | model-gap |
|---|---:|---:|---:|---:|
| `gen`: `LOCK`-prefixed encodings (every lockable opcode, forced memory and random ModRM) | 55,568 | 54,365 | 30,127 | 1,203 |
| `gen`: `XADD`, `CMPXCHG`, `CMPXCHG8B/16B`, fences, `PAUSE` | 5,075 | 3,602 | 611 | 1,473 |
| `gen`: `MOVS`/`STOS` (and `CMPS`/`LODS`/`SCAS`, rejected) with and without `REP` | 7,116 | 6,778 | 2,904 | 338 |
| `gen`: SSE 128-bit moves and `PXOR`/`XORPS` | 11,009 | 10,744 | 2,983 | 265 |
| `edge`: `cmpxchg-xadd`, `cmpxchg-dbl`, `string`, `lock-ud`, `sse-memmove` | 14,000 | 12,800 | 4,536 | 1,200 |
| `harvest`: real `LOCK`/`XADD`/`CMPXCHG`/`REP` instructions and SSE moves | 6,837 | 6,829 | 2,126 | 8 |
| `rand`: random strings that decode to these classes | 5,935 | 5,671 | 5,429 | 264 |

The gaps are deliberate rejections: `XADD`/`CMPXCHG` with a register destination (Go never
emits them), `F0` together with `F2`/`F3` (HLE hints, which hardware accepts), `REPNE` on
`MOVS`/`STOS`, `CMPS`/`LODS`/`SCAS`, and REX bits on `PAUSE`. The REP cases (counts mostly
0..255) ran 1,334,297 single-stepped iterations in 8,274 cases (at most 4,063 in one case,
where the count ran past the buffer and both sides fault). The runner also records
`RFLAGS.DF` after each case: it was set only after `STD` (68 cases), which the model
rejects, so the invariant `DF = 0` that the string instructions rely on held in every case
the model executes.

**Bugs found.** The native oracle found one real bug. The first full run found 140 mismatches in 127 encodings, all from one
model bug. A 32-bit shift, rotate, `SHLD` or `SHRD` whose masked count is 0 still writes its
destination, so the upper 32 bits of the register are cleared. The model had treated count 0
as "no change". `Exec.lean` now writes the destination back, and `JanusTests/Amd64.lean` pins
the case. Separately, the formal cross-check (below) found two places where the model defined a
flag that a formal model leaves undefined. Hardware agreed with the model's value in both, but
the vendors do not fully pin them down, so the model was made stricter: SAR CF for an 8/16-bit
count at or above the width, and ROL/ROR OF at masked count 0, are now undefined. Both runs
above use the final model.

**Decoder coverage on real Go code.** Over the Go-compiled functions (not `.abi0` assembly) of
`math/big`, `strconv`, `sort`, `bytes`, `strings`, `encoding/binary`, `math/bits` (test
binaries, `GOAMD64=v1`) and `examples/basic`, `decode` accepted 99.60% of the 214,504 instruction
occurrences (99.21% of the 39,730 distinct encodings) before the atomics and string
instructions were added. The rest was scalar floating point
(`MOVSD/MOVSS/UCOMISD/CVT*`, ...), `MOVQ R14, FS:-8` (the TLS load in ABI wrappers: FS is never
modelled), `REP MOVSQ/STOSQ`, `XADD`/`CMPXCHG` and `RCR`; the first of these still fault as
`undecodable`.

**Function-level coverage (`oracle coverage`).** `oracle coverage -model M -pkgs P,... BIN...`
is the amd64 analogue of `janus blockers`: it sweeps every function symbol with `x86asm`, runs
every distinct encoding through the Lean decoder, and counts the functions in which every
instruction is accepted ("fully decodable"; functions are split into Go-compiled and assembly
by the pclntab file of their entry). On `go test -c` binaries (Go 1.26.0, `GOAMD64=v1`),
before and after the atomics and string instructions:

| binary | Go-compiled functions | fully decodable before | after | instruction occurrences accepted before | after |
|---|---:|---:|---:|---:|---:|
| `sync/atomic.test` | 3,416 | 2,695 (78.9%) | **3,044 (89.1%)** | 98.57% | 98.80% |
| `bytes.test` | 4,666 | 3,950 (84.7%) | **4,251 (91.1%)** | 98.95% | 99.10% |
| `strings.test` | 4,640 | 3,935 (84.8%) | **4,234 (91.2%)** | 98.95% | 99.10% |
| `artifacts/examples-amd64` | 1,625 | 1,168 (71.9%) | **1,337 (82.3%)** | 98.04% | 98.38% |

By package (fully decodable functions, before → after): in `sync/atomic.test`, `sync/atomic`
12 → 14 of 14, `sync/atomic_test` 165 → 254 of 256, `internal/runtime/atomic` 3 → 4 of 4 and
`runtime` 977 → 1,126 of 1,485; in `bytes.test`, `runtime` 992 → 1,142 of 1,503 and `bytes`
52 → 52 of 59; in `strings.test`, `strings` 66 → 67 of 69. The assembly functions stay at 53
of 202: the linear sweep of `runtime.memmove` and `runtime.memclrNoHeapPointers` includes their
AVX paths (VEX), which are not modelled; the `CopyBlock` and `ClearWords` proofs show that the
non-AVX paths execute when the feature flags are stated (`docs/AMD64.md`). The largest
remaining blocker is the FS-relative TLS load `MOVQ FS:-8, R14` (about 530 occurrences per
binary), then AES, SSE floating point and SSE compares.

**FS, YMM/AVX and the next blockers.** Before and after `FS`, the VEX instructions, YMM state,
the SSE packed-integer compares, `MOVSS`/`MOVSD`, `PSHUFLW`, 32/64-bit `RCL`/`RCR`, the
prefetch hints and `CLD`/`STD` (same binaries, Go 1.26.0, `GOAMD64=v1`; "before" is the model at
`faa8833`, measured with the same, corrected sweep: `x86asm` decodes `VZEROUPPER` one or two
bytes too long, which desynchronised the linear sweep after every `VZEROUPPER`; `gen.Decode`
now fixes its length):

| binary | Go-compiled functions | fully decodable before | after | assembly functions | before | after | occurrences accepted before | after |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sync/atomic.test` | 3,416 | 3,044 (89.1%) | **3,344 (97.9%)** | 202 | 53 | **108** | 98.80% | 99.27% |
| `bytes.test` | 4,666 | 4,251 (91.1%) | **4,576 (98.1%)** | 202 | 53 | **108** | 99.10% | 99.46% |
| `strings.test` | 4,640 | 4,234 (91.2%) | **4,552 (98.1%)** | 202 | 53 | **108** | 99.10% | 99.46% |
| `artifacts/examples-amd64` | 1,629 | 1,341 (82.3%) | **1,579 (96.9%)** | 175 | 47 | **101** | 98.39% | 99.17% |

By package, after: `bytes` 59 of 59 and `strings` 69 of 69 fully decodable (were 52 and 67);
`internal/bytealg` 16 of 16 (14); `runtime` 1,413 of 1,503 in `bytes.test` (1,142). Among the
assembly functions `memeqbody`, `cmpbody`, `countbody`, `indexbytebody` and
`runtime.memclrNoHeapPointers` and `runtime.memmove` (its backward copy's `STD`/`CLD` now set
the modelled direction flag) decode completely; `indexbody` is blocked only by `PCMPESTRI`.

`oracle coverage` now also reports, per instruction class, the number of functions in which it
is the **only** rejected class (accepting it would make them fully decodable), and `-show
PREFIX,...` (`-show-enc`) lists the rejected classes (encodings) of matching functions. That is
how the follow-up instructions were chosen. Before this round the sole-blocker ranking in
`bytes.test` was `fs:mov` 324 functions, `syscall` 31, `movsd_xmm` 10, `ucomisd` 6, `rcr` 4,
`prefetcht0` 4, `pmovmskb` 2, ...; after `FS` and the vector instructions it was `syscall` 32,
`pshuflw` 22 (the Swiss-table group match in `internal/runtime/maps` and `runtime.mapaccess*`),
`ucomisd` 14, `cvtss2sd` 6, `rcr` 5 (`RCRQ $1` in the compiler's division-by-constant
sequences); `PSHUFLW` and `RCL`/`RCR` were added. What remains is not a move or a compare:
`SYSCALL`, scalar floating point (`UCOMISD`, `CVT*`, arithmetic; MXCSR is not modelled), `CRC32`,
AES/SHA, AVX-512 (`VMOVDQU64`, `VPERMB`, ...), `CPUID`/`XGETBV` and `PCMPESTRI`.

## Results with SSE scalar floating point (2026-10-24)

`OUT=artifacts/oracle-amd64-fp JOBS=16 N=1200 scripts/oracle-amd64.sh fp`: the targeted
floating-point specs (`ADD SUB MUL DIV SQRT MIN MAX` `SD`/`SS`, `UCOMIS*`/`COMIS*`, `CMPSD`/`CMPSS`
with every predicate, the `CVT*` conversions with 32/64-bit integers, `CVTSD2SS`/`CVTSS2SD`,
`ROUNDSD`/`ROUNDSS` with every `imm8` low nibble, the bitwise `AND(N)/OR PS/PD`; register and
memory operands, `REX` variants, packed and VEX neighbours), the `edge/fp-*` families (each case
under all 16 combinations of `RC` × `FTZ` × `DAZ` with every exception masked, plus each exception
unmasked alone), and every distinct floating-point instruction of the `math`, `strconv` and
`sort` test binaries. Operands come from the IEEE edge-value generator (as on arm64, with the
x86 indefinite among the NaNs) with random upper bits, and `MXCSR` is random per case (all
masked about 70% of the time, otherwise random masks; random initial flags). Cases carry
`mxcsr`; the runner loads it with `LDMXCSR` right before entering the instruction, reads it back
from the signal frame's `fxsave` area, and restores the host's value.

| source | cases | agree | of which both fault | model-gap | MISMATCH |
|---|---:|---:|---:|---:|---:|
| `gen/*` (targeted encodings and neighbours) | 580,034 | 320,371 | 135,427 | 259,663 | 0 |
| `edge/fp-*` (systematic MXCSR families) | 475,200 | 463,169 | 13,248 | 12,031 | 0 |
| `harvest/*` (math/strconv/sort FP instructions) | 18,360 | 18,360 | 6,774 | 0 | 0 |
| **total** | 1,076,394 (incl. 2,800 others) | 804,700 | | 271,694 | **0** |

Over the in-scope instructions 646,234 cases succeeded on both sides with identical registers,
flags, `XMM`/`YMM` state, memory and `MXCSR`, and 113,299 faulted on both, 39,691 of them with
`SIGFPE` (`#XM`, an unmasked exception: the model's `simdFPException`). The gaps are encodings the
decoder refuses on purpose: `REX.W` on instructions that ignore it, `66` together with `F2`/`F3`,
the packed forms, VEX/EVEX, the MMX conversions, `CMPSD`/`ROUNDSD` immediates with reserved
bits, and 20 accesses the host served from memory outside the buffer. The first run found 95
mismatches in 28 encodings, all one bug: under `DAZ`, `MINSD`/`MAXSD` deliver the second operand
*as read through `DAZ`* (a subnormal comes back as a zero) also when the other operand is a NaN.
`Janus/Amd64/Float.lean` was fixed (`minmax`), and the run above is of the fixed model.

Probes of the host CPU that the model follows (each also covered by the corpus): `FTZ` flushes
every tiny result, exact or not (with `UE PE`); tininess is detected after rounding; `DE` is not
raised when a NaN operand or a division by zero takes precedence, but is for `∞ × subnormal`; an
unmasked underflow traps on every tiny result; `ROUNDSD` never raises `DE`; `MINSD`/`MAXSD` return
the second operand for any NaN (a signalling one unquieted) and for mixed-sign zeros; out-of-range
and NaN conversions give the integer indefinite.

**Coverage effect** (`oracle coverage -pkgs math.,strconv.,sort.` on `go test -c` binaries,
Go 1.26.0, `GOAMD64=v1`, before → after the floating-point model):

| binary | Go-compiled functions | fully decodable before | after | occurrences accepted before | after |
|---|---:|---:|---:|---:|---:|
| `math.test` | 3,362 | 3,146 (93.6%) | **3,357 (99.9%)** | 98.41% | 99.42% |
| `strconv.test` | 3,298 | 3,208 (97.3%) | **3,298 (100%)** | 99.25% | 99.41% |
| `sort.test` | 3,574 | 3,479 (97.3%) | **3,574 (100%)** | 99.26% | 99.42% |

By package: `math` 8 → 67 of 68 functions fully decodable (the remaining one is `math.FMA`'s
`VFMADD231SD` path behind `x86HasFMA`), `sort` 63 → 66 of 66, `strconv` 20 of 20 (14 → 14 in
`math.test`'s copy). The last floating-point sole blockers were `UCOMISD` (19 functions),
`CVTSS2SD` (6), `CVTTSD2SI` (5) and the arithmetic; what remains is `SYSCALL`, `CRC32`, AES/SHA,
AVX-512 and `CPUID`/`XGETBV`.

### gcc-compiled C and `ENDBR64` (2026-10-24)

The C code of cgo programs ([FFI.md](FFI.md)) needed one decoder addition, `ENDBR64`
(`F3 0F 1E FA`, a NOP). Runs on the model with it:

| run | cases | agree | model-gap | **MISMATCH** |
|---|---:|---:|---:|---:|
| `quick`, `SEED=1`, including the new `edge/endbr` family (the exact bytes, 21 prefix variants, `ENDBR32`) | 281,243 | 230,833 | 50,410 | **0** |
| of which `edge/endbr` | 8,800 | 1,200 (400 exact `ENDBR64`, 800 `LOCK` forms that both fault) | 7,600 (every other prefix combination, rejected) | **0** |
| harvest of every distinct instruction of gcc 15.2 `-O2` code (`examples/cgo/ccover.c` + `cfuncs.c`), `K=200`, `-per-class 0` | 56,200 | 56,161 | 39 (branches leaving the code page, one `BSR` of 0) | **0** |

The harvested classes include `cmov`, `setcc`, `lea`, `imul`, `mul`, `div`/`idiv`,
`movsx`/`movzx`/`movsxd`, `cqo`/`cdqe`, `bswap`, `bsr`, `ror`, `leave`, `push`/`pop` and the
`ENDBR64`/`nopw` forms. `scripts/oracle-amd64.sh full` now adds this C corpus to the harvest.

### GOAMD64=v3 extensions (2026-10-25)

BMI1 (`ANDN BLSR BLSMSK BLSI BEXTR`), BMI2 (`SHLX SHRX SARX RORX MULX BZHI PDEP PEXT`), `MOVBE`,
the 48 scalar FMA3 forms and SSSE3 `PSHUFB`/`PSIGNB` (WP-B). `scripts/oracle-amd64.sh v3` runs
the targeted specs (`gen.V3Specs`: `MOVBE` load/store/16-bit with the `CRC32` and `F3`
neighbours and the `#UD` register forms, `PSHUFB`/`PSIGNB` with their MMX forms and the other
SSSE3 opcodes; `gen.V3VexSpecs`: every BMI opcode/`pp` pair, the `#UD` neighbours, and the
scalar and packed FMA opcodes, with `VEX.vvvv` uniform, `VEX.W` uniform, `VEX.L1` one time in
eight, and stray prefixes, maps and `pp`), the `edge/fma` family (each of the 48 forms on
register triples whose addend is crafted against the product: the negated rounded product, so
that only a single rounding gets the sum right, one ulp away, half an ulp of it, or an IEEE edge
value; each under the 16 `RC` × `FTZ` × `DAZ` settings and with each exception unmasked alone)
and every v3-extension instruction of `GOAMD64=v3` test binaries of `math math/big strconv
internal/strconv internal/runtime/maps encoding/binary math/bits reflect internal/abi math/rand
runtime`. `SHLX SHRX SARX BEXTR BZHI` get interesting counts/controls in `VEX.vvvv`, `PDEP`/`PEXT`
sparse, dense and contiguous masks, `PSIGNB`/`PSHUFB` zero, positive and negative bytes.

| run | cases | agree | of which both fault | model-gap | **MISMATCH** |
|---|---:|---:|---:|---:|---:|
| `v3`, `SEED=1`, `N=600`, `V3_K=12` | 198,440 | 167,902 | 38,887 | 30,538 | **0** |
| `v3`, `SEED=2`, `N=1200`, `V3_K=24` | 396,740 | 333,512 | 78,024 | 63,228 | **0** |
| of which (`SEED=2`) `edge/fma` | 158,400 | 133,577 | 6,314 | 24,823 | **0** |
| of which (`SEED=2`) targeted BMI/`MOVBE`/`PSHUFB`/`PSIGNB` | 65,545 | 63,829 | 13,573 | 1,716 | **0** |
| of which (`SEED=2`) targeted scalar FMA | 66,450 | 57,078 | 8,754 | 9,372 | **0** |
| of which (`SEED=2`) harvested (v3 binaries) | 36,840 | 35,986 | 6,341 | 854 | **0** |
| `full` (now with 4 `GOAMD64=v3` binaries in the harvest) | 1,189,811 | 933,564 | | 256,247 | **0** |

The gaps are what the decoder refuses on purpose or where the model faults on purpose, and were
checked case by case: every `undefinedResult` gap of an FMA case is one with two or more NaN
operands or `0 × ∞ + NaN` (15,412 of 15,412 register-form cases in the `SEED=1` run recomputed
from the case state, `DAZ` included); the other FMA gaps are `VEX.L1` (`LIG`, executed by the
host); `PSHUFB`/`PSIGNB` gaps are the MMX forms; `MOVBE`/`RORX` gaps are `RIP`-relative accesses
outside the buffer. Host probes (`Intel Xeon Gold 5412U`) that fixed the FMA rules before the
run: with several NaN operands Intel returns the first in the order multiplicand, multiplicand,
addend (quieted, `IE` for any signalling one); a NaN is never negated by `VFNMADD`/`VFMSUB`;
`0 × ∞ + qNaN` returns the NaN without `IE`; `DE` is not raised when a NaN takes precedence. The
model faults in the two vendor-dependent cases (see `FP.fma`).

### SSE packed instructions (WP-D, 2026-10-25)

The SSE2/SSE3/SSSE3/SSE4.1/SSE4.2 packed instructions of `Janus/Amd64/ExecSSE.lean`.
`scripts/oracle-amd64.sh sse` runs the targeted specs (`gen.SSESpecs`, `oracle-amd64/gen/sse.go`:
every modelled `66 0F xx` packed-integer opcode in register and memory forms with its MMX and
`F3` neighbours, the shift groups `66 0F 71/72/73` with every `/r`, the `MOVLPS`/`MOVHLPS`/
`MOVHPS`/`MOVLHPS`/`MOVDDUP`/`MOVSLDUP`/`MOVSHDUP` opcodes under every mandatory prefix, the
non-temporal moves, `LDDQU`, `MASKMOVDQU` (not modelled), the shuffles, `PINSRW`/`PEXTRW`, every
modelled `66 0F 38 xx` and `66 0F 3A xx` opcode with their MMX/`F3` neighbours and unmodelled
ones (`DPPS`, `PCLMULQDQ`, AES), `CRC32` at every width and prefix order, and the packed
floating point including `RCPPS`/`RSQRTPS`); the edge families (`gen.SSEEdges`: every
`PCMPESTRI/PCMPESTRM/PCMPISTRI/PCMPISTRM` `imm8` with clear bit 7 on strings over a small
alphabet with nulls, needles copied from the haystack and explicit lengths around 0, ±8, ±16
and the 32/64-bit boundaries, with and without `REX.W`; the shifts by immediate at counts around
the element width; the saturating, packing, averaging, min/max and multiply-high operations on
boundary elements; every packed floating-point operation on IEEE edge values in every lane under
the 16 `RC` × `FTZ` × `DAZ` settings and with each exception unmasked alone; `CRC32` at every
width); and every WP-D-class instruction harvested from the `GOAMD64=v1` test binaries of
`internal/chacha8rand hash/crc32 bytes strings crypto/internal/fips140/nistec crypto/aes
crypto/sha256 crypto/sha1 crypto/cipher math` and from the C corpus (`scripts/coverage/ccorpus`,
`examples/cgo/ccover.c`) compiled by gcc and clang at `-O2` and `-O3`. States: element edge
values in every XMM register and in the memory operand, 16-byte memory operands mostly aligned,
shift counts with high garbage bits, `XMM0` blend masks, integer lanes for `CVTDQ2PS/PD`.

| run | cases | agree | of which both fault | model-gap | **MISMATCH** |
|---|---:|---:|---:|---:|---:|
| `sse`, `SEED=1`, `N=600`, `SSE_K=12` | 861,894 | 792,884 | 267,052 | 69,010 | **0** |
| of which `edge/sse-fp` | 105,600 | 105,600 | 6,434 | 0 | **0** |
| of which the other edge families | 10,350 | 10,350 | 750 | 0 | **0** |
| of which harvested | 6,144 | 6,144 | 317 | 0 | **0** |
RUN2ROWS

Every model gap was checked by class and encoding: the `67` (address size) prefix, the MMX forms,
`66` with `F2`/`F3`, the reserved immediates the decoder refuses (`CMPPS/PD imm8 ≥ 8`,
`ROUNDPS/PD imm8 ≥ 16`, `PCMPxSTRx imm8<7>`), duplicated `F2`, `REX.W` on the 16-bit `CRC32`,
the unmodelled `DPPS`/`DPPD`/`RCPPS`/`RSQRTPS`/`MASKMOVDQU`/AES/`PCLMULQDQ`, and 7 `RIP`-relative
accesses outside the buffer (served by the host from its own pages). None is an alignment
disagreement: the model faults with `misaligned` exactly when the host raises `#GP`, including
for `PTEST`, `PALIGNR`, `PMULLD`, `ROUNDPS` (aligned) and `PCMPESTRI`, `PMOVSX` `m64`,
`CVTDQ2PD m64` (unaligned).

## Running it

```
scripts/oracle-amd64.sh selftest   # build, check the native harness on known answers (109 checks)
scripts/oracle-amd64.sh quick      # generated cases only (~100k)
scripts/oracle-amd64.sh full       # generated + edge + harvested from real Go binaries (default)
scripts/oracle-amd64.sh fp         # SSE scalar floating point only
scripts/oracle-amd64.sh v3         # the GOAMD64=v3 extensions only (BMI1/BMI2, MOVBE, FMA, PSHUFB/PSIGNB)
scripts/oracle-amd64.sh sse        # the SSE packed instructions of WP-D only (SSE2..SSE4.2)
```

Knobs: `OUT` (default `artifacts/oracle-amd64`), `JOBS` (default 16, capped at 24), `N`
(encodings per targeted spec), `GROUP` (random strings), `K` (states per harvested
instruction), `PER_CLASS`, `SEED`, `MODEL` (`MODEL=oracle-amd64/bin/fakemodel` exercises the
pipeline without Lean). After a model change the native side can be reused:
`oracle-amd64/bin/oracle run -reuse-native -runner oracle-amd64/bin/runner -model .lake/build/bin/janus-oracle-amd64 -cases A,B -out DIR`.
`oracle minimize -out DIR` shrinks mismatching cases into `repro.md`/`repro.jsonl`. A full run
takes about 90 s, including the corpus build.
`oracle harvest -only REGEX` keeps only the harvested instructions whose class matches (with a
large `-k`, e.g. `-k 200 -per-class 0 -only '^(v.*|pcmpeqb|pand|...)$'` for the vector run
above), and `-fs` only the `FS`-prefixed ones.

Pieces: `oracle-amd64/` (a separate Go module: `layout/` is the contract, `cmd/runner` the
native executor, `cmd/oracle` the gen/harvest/run/compare/minimize/selftest driver, `gen/` the
generators) and `Oracle/Amd64Main.lean` (the `janus-oracle-amd64` executable).

## What a case is

A case (`layout.Case`) holds the instruction bytes (1 to 15, hex) and a complete initial state:
the 16 GPRs, the six status flags, `XMM0`–`XMM15`, optionally bits 255:128 of `YMM0`–`YMM15`
(`ymmh`, absent = 0) and the `FS` base (`fsbase`, absent = 0), a seed for the 4 KiB data
buffer, and optional `init` byte overrides (used to plant return addresses and popped values).
The generator gives most cases random nonzero upper YMM halves and an `FS` base near the buffer
(steered so that an `FS`-relative operand mostly lands in it). The addresses are fixed:

| address | what |
|---|---|
| `0x10_0000_0800` (`TestPC`) | the instruction. The rest of its page is `0xCC` (`INT3`) |
| `0x10_0004_0000` (`DataBase`), 4096 bytes | the data buffer, byte `i` = `Pattern(seed, i)`, then `init` |
| `0x0F_FFF0_0000` (`CtxPage`) | trampoline context: host save area, input and captured state |

The Lean side builds a `State` with these registers, all six flags defined, `rip = TestPC`,
and `mem.regions = [⟨DataBase, 4096, writable⟩]`: exactly the buffer and nothing else. It runs
`Janus.Amd64.step` on the code-page bytes from `TestPC`, which are the case bytes followed by
`0xCC` to the end of the page. Both sides therefore see identical instruction bytes even when
an encoding is longer than the bytes a random case supplies.

## How the native side observes one instruction

`oracle-amd64/cmd/runner` (Go, `GOARCH=amd64`) runs all cases of a shard in one process:

1. The trampoline (`trampoline_amd64.s`) saves the host's callee state and its own `FS` base
   (`RDFSBASE`) in the context page, sets the case's `FS` base (`WRFSBASE`; the runner checks
   at start-up that the kernel enables FSGSBASE), loads `XMM0`–`XMM15` (`MOVUPS`) and their
   upper halves (`VINSERTI128`), the 16 GPRs, and enters `TestPC` with `IRETQ`. Nothing between
   `WRFSBASE` and the resume sequence touches the Go runtime's TLS. The `IRETQ` frame
   sets `RSP` and `RFLAGS` (the case's status flags plus **TF**) atomically with `RIP`.
2. With TF set, the CPU raises a single-step debug trap after **exactly one instruction**. That
   trap is a SIGTRAP with `si_code = TRAP_TRACE` and saved `RIP` = the next instruction:
   `TestPC + len` on fall-through, or the branch target on a taken branch, even an unmapped
   one, because the trap precedes the next fetch. An instruction that faults by itself raises
   SIGSEGV/SIGBUS/SIGILL/SIGFPE, or SIGTRAP for `INT3`/`INT1`, with saved `RIP` = `TestPC`
   (just after it for `INT3`). There is no fall-through-into-`INT3` guesswork and no watchdog:
   `JMP .` is observed as `ok` with `pc = TestPC`. The one exception is a `REP` string
   instruction, which traps after every iteration with `RIP` still at `TestPC` (SDM Vol. 3
   §18.3.1.4): the runner re-enters it from the captured registers, flags and XMM state (the
   buffer is kept) until `RIP` moves on or it faults, and reports the number of re-entries.
3. A raw signal handler is installed with `rt_sigaction`, bypassing the Go runtime, and runs
   on the thread's sigaltstack. It copies `uc_mcontext` (GPRs, `RIP`, `RFLAGS`), the XMM
   registers from the signal frame's fxsave area and, when the frame has an XSAVE area
   (`FP_XSTATE_MAGIC1`), `XSTATE_BV` and the `YMM_Hi128` component (offset 576, checked against
   `CPUID.(EAX=0DH,ECX=2)` at start-up) into the context page. With `XSTATE_BV` bit 2 clear the
   upper halves are in their initial state and reported as 0. It then resets the
   frame's x87/SSE control state, clears TF/DF/AC and redirects the saved `RIP` to a resume
   sequence. That sequence restores the host `FS` base and registers (and `X15 = 0`, `R14 = g`,
   `VZEROUPPER`) and returns into Go.

The runner reports `ok`, with every GPR, the status bits of `RFLAGS`, the XMM registers, `pc`
and the changed buffer bytes, or `fault`, or `escaped`/`error`. `oracle selftest` checks the
machinery against hand-computed answers: ALU flags, loads and stores, push/pop/call/ret,
branches, faults, `#DE`, `UD2`, self loops, SSE moves, `LOCK XADD`, `LOCK CMPXCHG` (equal and
not), `MFENCE`, `REP MOVSB` (5 iterations), `REP STOSQ` (counts 0 and 2), upper YMM halves
kept by `NOP` and a legacy `MOVUPS` and zeroed by `VZEROUPPER` and a VEX.128 load, a 256-bit
`VMOVDQU` load and store, a misaligned `VMOVDQA` (`#GP`), `FS:-8` loads and stores, an
`FS:[RBX]` load and a fault with `FS` base 0, and flag and register preservation under all 64
combinations of the six status flags (109 checks).

**Safety.** Random encodings run natively on a shared host, so the runner refuses case bytes
that contain system-call, segment-load, FP-environment-load or other system encodings
(`layout.Forbidden`: `SYSCALL`, `SYSENTER`, `INT n`, `MOV Sreg`, `POP FS/GS`, `LSS/LFS/LGS`,
`0F AE` except the unprefixed `LFENCE`/`MFENCE`/`SFENCE`, `0F 01`, `POPF`, `IRET`, `0F 00`, `0F 35`), and also every GS-prefixed
instruction. FS-prefixed ones run: the FS base is the case's for exactly the duration of the
case, so they cannot reach the runtime's TLS. VEX/EVEX instructions run; the one that loads
control state, `VLDMXCSR`, is undone by the handler's MXCSR reset. A seccomp-BPF filter on
all threads makes every system call issued from the code page fail with `EPERM`, and outside
the code page only a short allow list is permitted. This was tested by injecting `getpid` and
`kill(1, 9)` through a test-only bypass of the byte filter: both returned `-EPERM` and did
nothing. The runner is a PIE, so stray jumps into Go text are improbable. A crashing shard is
restarted after the failing case, which is recorded as `error`.

## Case generation

* **Harvested** (`harvest/<mnemonic>`): every distinct instruction of the executable code of
  real Go amd64 binaries, decoded by a linear sweep of each function with
  `golang.org/x/arch/x86/x86asm`. The binaries are a program using `math/big`,
  `crypto/sha256`, `sort`, `encoding/json`, `regexp`, `compress/flate`, ...
  (`oracle-amd64/harvest/bigprog`), `go test -c` binaries of `math/big strconv sort
  crypto/sha256 bytes strings math/bits encoding/binary sync/atomic`, and `artifacts/examples-amd64`.
  Each modelled class is capped at `PER_CLASS` (uniformly sampled) and each instruction runs
  under `K` random states. Instructions outside the subset are sampled sparsely
  (`harvest-other/*`) so that the model's rejection is exercised on real encodings too.
* **Targeted** (`gen/<class>`): random encodings per class for the opcodes Go emits, with
  random legal and illegal prefixes, REX bits, ModRM/SIB/displacement forms and immediates.
  `x86asm` steers the state: memory operands get base/index values so that the effective
  address mostly lands in the buffer, sometimes straddles its ends and sometimes is wild. `RSP`
  is mostly an 8-aligned pointer into the buffer, and branch targets mostly stay in the code
  page. Conditional classes (`Jcc`, `SETcc`, `CMOVcc`, `ADC`, `SBB`, `CMC`) run each encoding
  under 8 flag combinations.
* **Atomics and strings** (`gen/*`): `LOCK` on every lockable opcode (forced memory
  destination and random ModRM, which also hits the `#UD` register forms), `LOCK` on `MOV`,
  `TEST` and `BT`, `XADD`/`CMPXCHG` locked and unlocked, `CMPXCHG8B/16B`, the fences, and
  `MOVS`/`STOS`/`CMPS`/`LODS`/`SCAS` with `F3`, `F2` or no prefix. For string instructions
  the state is steered to small counts (`RCX` mostly 0..255) with `RSI`/`RDI` in the buffer,
  sometimes overlapping.
* **Edge families** (`edge/<family>`): BSF/BSR with a zero source at 16, 32 and 64 bits; 32-bit
  `CMOV` with a false condition; MUL/IMUL/DIV/IDIV edge operands, including `IDIV` quotients of
  `-2^(w-1)` and every overflow; `AH`..`BH` versus `SPL`..`DIL` with and without REX;
  RIP-relative accesses (disp32 from `TestPC` reaches the buffer); `MOVAPS/MOVDQA/XORPS/PXOR`
  on misaligned memory; `XCHG mem, reg`; push/pop/call/ret/leave with `RSP` at and across the
  buffer ends; `CMPXCHG`/`XADD` on memory with the accumulator equal to the memory operand
  half of the time (`cmpxchg-xadd`); `CMPXCHG8B/16B`, aligned or not, equal or not
  (`cmpxchg-dbl`); `MOVS`/`STOS` at every width with counts 0..200 over disjoint,
  overlapping and buffer-leaving ranges (`string`); `LOCK` where it is `#UD` (`lock-ud`); and
  `MOVDQU`/`MOVUPS` in memmove's `-disp(DI)(BX*1)` form near the buffer ends (`sse-memmove`);
  the TLS slot `MOVQ FS:-8, R14` (load and store, other registers and offsets, `FS:[RAX]`, and
  `LEA` with `FS`, which must be rejected) with `FS:-8` inside, at the ends of and outside the
  buffer (`tls`); `PCMPEQB`/`PAND`/`POR`/`PMOVMSKB`/`PSHUFD`/`PUNPCKLBW` and their VEX
  counterparts, `VPTEST`, `VPBROADCASTB`, `VZEROUPPER` and `VEX.128`/`VEX.256` moves on
  registers that are all copies of one value with a few bytes changed, so that equal and
  unequal lanes both occur (`vec-cmp`); and `VMOVDQA`/`VMOVNTDQ`/`MOVDQA` at 16/32-byte
  (mis)alignments and `VMOVDQU` across the buffer ends (`vec-align`).
* **VEX** (`gen/v*`): 2- and 3-byte VEX encodings of each modelled opcode (and of near misses:
  `VPANDN`, `VPCMPEQW`, `VPBROADCASTW`, `VPALIGNR`, `MULX`, the no-prefix and `F2` forms of
  `6F`), with random `R X B W L` bits, `VEX.vvvv` mostly `1111` and sometimes random, an
  occasional wrong map or `pp`, and an occasional stray prefix before `C4`/`C5`.
* **Random** (`rand/*`): random prefix sequences (`66 67 F2 F3 F0 2E 3E 26 36 64 65`, REX),
  random one- and two-byte opcodes and random tails. These test that the decoder rejects what
  it does not understand and agrees on what it accepts, including instruction length.

## What agreement means

The comparator is `oracle-amd64/cmd/oracle/compare.go`.

| hardware | model | verdict |
|---|---|---|
| ok | ok, identical GPRs, defined status flags, `pc`, `XMM0`–`XMM15`, bits 255:128 of `YMM0`–`YMM15` and buffer bytes, and `DF` clear on hardware | **agree** |
| fault | fault (any `Fault`) | **agree** (fault kinds are not compared) |
| ok | fault | **model-gap**: the model is conservative (`undecodable`, `undefinedResult`, `badTarget`, or an access outside the buffer that hardware served from other mapped memory) |
| ok | ok, any difference | **MISMATCH** |
| fault | ok | **MISMATCH**: the model admits an execution hardware refuses |
| `escaped`/`error` | — | **unobserved** (excluded) |

**Flags.** The model reports which status flags are *defined* after the instruction (`Model.defined`).
Only those are compared. A flag the model leaves undefined (for example `SF ZF AF PF` after
`MUL`, all six after `DIV`, `AF` after logic ops, `OF` after multi-bit shifts) makes no claim
about the value, and reading it later faults in the model (`undefinedFlag`). The oracle
therefore checks every flag value the model does claim, and the model's undefined set must
be a superset of what the hardware leaves unspecified. That superset property is a model
design rule (SDM *Flags Affected*, plus undefined wherever Intel and AMD differ), not
something a single CPU can confirm. See "Limits".

## Known limits of the reference

* **One CPU, one vendor.** The native reference is this Intel host. The formal cross-check
  above covers the undefined-flag sets for most of the integer subset. Where the SDM says "undefined" or
  vendors differ, the model faults or leaves the flag undefined rather than copying this CPU:
  - BSF/BSR of 0 at 16 and 32 bits faults (`undefinedResult`), although this CPU keeps the
    destination.
  - `ZF` after `BT*` is undefined, although Intel leaves it unaffected.
  - 64-bit BSF/BSR of 0 keeps the destination. AMD documents this, Linux relies on it, and this
    CPU agrees.
  A proof can never depend on a vendor-specific value, but neither oracle can show that the
  model's *undefined* sets are complete for every other CPU.
* **CPU features.** The model decodes `POPCNT` (`F3 0F B8`), `TZCNT` and `LZCNT` (`F3 0F BC/BD`).
  On a CPU without BMI1/LZCNT, `F3 0F BC/BD` executes as BSF/BSR. Theorems that use them assume
  an x86-64-v3-class CPU (see `docs/AMD64.md`). `GOAMD64=v1` code only reaches them behind
  run-time CPU checks.
* **GS** is never executed natively (it would reach the runner's own state); the decoder
  rejects `65`, which only `JanusTests/Amd64.lean` checks. `FS` runs with the case's base.
* **Split locks.** This host runs `split_lock_detect=warn`: a locked access that straddles a
  cache line completes (with a kernel warning), so the model's `misaligned` fault for a locked
  access that is not naturally aligned is a model gap here. Under `fatal` the hardware side would
  be `SIGBUS` and the cases would agree.
* **AVX-512 state.** VEX instructions zero `ZMM` bits 511:256 on this host; neither side
  compares them (the model does not have them, and no modelled instruction reads them).
* **Canonical addresses.** This host has 5-level paging, so `2^47..2^56` is canonical: a jump
  there is a fetch fault (hw ok) and the model's `badTarget` is a gap. Non-canonical targets
  `#GP` at the branch itself, with `RSP` unchanged, and the model faults too.
* **Memory outside the buffer.** The model knows only the buffer. The native process also has
  the code page and its own mappings, so an access there succeeds natively and faults in the
  model (gap), never the other way round. Only the 4 KiB buffer is compared byte by byte.
* **No system state.** `RFLAGS` system bits, segment registers other than the `FS` base,
  x87 state and `ZMM` bits 511:256 are neither modelled nor compared. (`MXCSR`, flags
  included, is modelled and compared since the floating-point model; see above.)

## Formal x86 model (third reference)

The Sail translation of the ACL2 X86isa model (`rems-project/sail-x86-from-acl2` at
`0c6c023`, Sail 0.20.3) is built into a single-step emulator and run on a stratified sample
of 20,000 integer cases. This mainly checks something hardware cannot show: *which flags are
undefined*. Each case runs twice, with the formal model's undefined flags drawn as 0 and as 1.
Build, driver and analysis are in `oracle-amd64-formal/` (`README.md`, `build.sh`,
`compare.py`). On the final model:

| | cases |
|---|---:|
| both models succeed | 17,686 |
| identical on every field both define | 17,356 |
| **flag undefined in the formal model but defined in ours** | **0** |
| flag undefined in ours but defined in the formal model (`ZF` after `BT`, deliberate: AMD leaves it undefined) | 336 |
| results differ | 330, each a case where ours equals the hardware (formal-model bugs: `AL, imm8` with REX.W, over-wide 8/16-bit rotates) and 3 XMM-sourced stores the driver cannot initialise |
| formal model faults or lacks the opcode (BSF/BSR/TZCNT/LZCNT/POPCNT/BSWAP/BTS/BTR/BTC) | 2,314 |

**Atomics and string instructions.** The same driver was run on every case of the new
classes in the `SEED=1` run that our model executes (`compare.py --classes`; `REP` string
instructions are fed back step by step, because the formal model executes one iteration
per step):

| class | both succeed | identical | differ | formal model faults or lacks it |
|---|---:|---:|---:|---:|
| `LOCK`-prefixed `ADD ADC SUB SBB AND OR XOR INC DEC NEG NOT XCHG` (gen, edge, harvest) | 19,906 | **19,906** | 0 | 0 |
| `LOCK BTS/BTR/BTC`, `XADD`, `CMPXCHG8B/16B`, `LFENCE/MFENCE/SFENCE` | 0 | | | all (not implemented) |
| `CMPXCHG` (locked or not) | 3,338 | 746 | 2,592, flags only | 0 |
| `MOVS`/`STOS` without `REP`, every width | 2,238 | **2,238** | 0 | 0 |
| `MOVS`/`STOS` with `REP` | 4,726 | 0 | 4,726 | 8 |

No case has a flag that the formal model leaves undefined and ours defines. The differences
are formal-model bugs, and the native oracle agrees with our model on every one of these
cases:

* `CMPXCHG` flags: the formal model sets the flags of `DEST − accumulator`; the SDM and the
  hardware use `accumulator − DEST` (e.g. `f0 0f b0 32`, `AL = 0x37`, `[RDX] = 0xda`: hardware
  and ours `CF AF`, formal `SF PF`). Registers, memory and `RIP` agree in all 3,338 cases.
* `REP MOVS`/`REP STOS`: the formal model performs one iteration before it tests the count
  (so `RCX = 0` copies one element and wraps `RCX` to `2^64 - 1`), and it ends an `F3`
  repetition on `ZF`, which only `CMPS`/`SCAS` should do. Its `REP` results are therefore
  not comparable; the single-element forms agree exactly.

**FS, YMM and the new instructions.** `build.sh` now also lets the driver set the `FS` base
(`-C fsbase=`, which in 64-bit mode the formal model takes from `IA32_FS_BASE`) and the low 256
bits of `ZMM0`–`ZMM15` (`-C ymm{i}q{j}=`, quadword `j`), and prints them back; `compare.py`
passes the case's `fsbase`, `xmm` and `ymmh`, compares YMM registers too, no longer skips the
SSE classes, and takes `--fs 1` (only `64`-prefixed cases). On every case of the new and
newly comparable classes in the final `SEED=1` run that our model executes (`gen`, `edge`,
`harvest`):

| classes | cases | formal model faults or lacks it | both succeed | identical | differ |
|---|---:|---:|---:|---:|---:|
| `FS`-prefixed (`--fs 1`: `MOV`, `MOVZX/MOVSX/MOVSXD`, ALU, `CMP`, `TEST`, `edge/tls`) | 12,907 | 0 | 12,907 | **12,907** | 0 |
| `RCL`/`RCR`, `MOVSS`/`MOVSD`, legacy SSE moves (`MOVUPS MOVAPS MOVUPD MOVAPD MOVDQU`, `edge/sse-*`), `CLD`, `MOVD`/`MOVQ` | 54,312 | — | 54,312 | 53,318 | 994 |
| VEX (all 11), `PCMPEQB PAND POR PMOVMSKB PSHUFD PSHUFLW PUNPCKLBW PXOR XORPS`, `PREFETCHh`, `MOVDQA`, some `MOVQ` forms | 46,701 | 46,701 | 0 | | |

* **Flags undefined in the formal model but defined in ours: 0.** The other direction: 2,064
  `RCL`/`RCR` cases with a masked count of 0, where ours makes `OF` undefined (the SDM
  pseudocode) and the formal model leaves every flag unchanged (the prose); the conservative
  side, as for `ROL`/`ROR`. For counts 1 and above both agree on which flags are defined and on
  their values.
* **Legacy SSE preserves YMM bits 255:128 in the formal model too**, in every case that writes
  an XMM register (about 2,900 of them with nonzero upper halves in the earlier quick run that
  was inspected per case), and `MOVSS`/`MOVSD` zero bits 127:32/127:64 on a load, merge on a
  register move, and store 4/8 bytes, exactly as ours.
* **The 994 differences are a formal-model bug**: all are `MOVD`/`MOVQ xmm, r/m`
  (`66 [REX.W] 0F 6E`), where the formal model (`x86_movd_movq_to_xmm` writes only the operand
  size) keeps bits 127:32/127:64 of the destination; the SDM, the hardware (same case ids in
  `hw.jsonl`) and our model zero-extend to 128 bits. E.g. `660f6edb` (`movd xmm3, ebx`).
* **The formal model implements no VEX instruction** (every VEX branch of its dispatch is
  guarded by `& false`, so they end in `#UD` or "unimplemented") and none of the packed-integer
  instructions or prefetches; those classes are checked by the native oracle alone.

Neither ACL2 X86isa itself, nor Remill or the K semantics, was tried: the Sail model ran on the
first attempt and exposes the undefined-flag masks directly. The bit-scan, population-count,
byte-swap and bit-modify classes are checked by the native oracle alone, because the formal
model does not implement them.
