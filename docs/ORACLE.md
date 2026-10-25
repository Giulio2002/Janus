# The differential oracle

The Lean AArch64 model (`Janus.Arm64.step`, decoder in `Janus/Arm64/Decode.lean`, semantics
in `Janus/Arm64/Exec.lean`) is in Janus's trusted base: every theorem about a Go function is
only as good as the model's account of what each instruction does. The oracle tests that model
one instruction at a time against real AArch64 execution, with `qemu-aarch64` user mode as the
reference (or bare metal, on an arm64 Linux host).

## Running it

```
scripts/oracle.sh selftest   # build everything, check the native harness on known answers
scripts/oracle.sh quick      # ~60k generated cases, a few seconds
scripts/oracle.sh full       # generated + harvested from real Go arm64 binaries (default)
```

Results land in `artifacts/oracle/` (override with `OUT=`):

| file | contents |
|---|---|
| `summary.md` | per-class table, model-gap breakdown, every mismatch group with examples |
| `repro.md`, `repro.jsonl` | minimised reproductions of every mismatching word (only written if there are mismatches) |
| `verdicts.jsonl.zst` | one verdict per case (`agree` / `model-gap` / `MISMATCH` / ...) with diffs |
| `mismatches.jsonl` | the `MISMATCH` verdicts, uncompressed (only written if there are mismatches) |
| `cases.jsonl.zst`, `hw.jsonl.zst`, `model.jsonl.zst` | the inputs and both sides' raw outputs |

A full run writes several GB of JSON lines. When the script ends (however it ends) it keeps the
summaries and compresses the dumps with zstd (`zstd -dc verdicts.jsonl.zst | …` reads one;
`scripts/lib/artifacts.sh`); `gen.jsonl` and `harvest.jsonl`, whose union is `cases.jsonl`, are
removed. `KEEP=zst` compresses those too, `KEEP=1` keeps every file raw, as before. The drivers
that read the corpus (`scripts/oracle-sail.sh`, `scripts/asl.sh check`, `scripts/x86formal.sh
check`, `oracle-amd64-formal/compare.py`, `JanusASL/tools/evidence.py`) accept the compressed
files.

Knobs: `JOBS`, `N` (words per generated class), `K` (states per harvested word), `PER_CLASS`
(harvested distinct words per class), `SEED`, `QEMU` (set `QEMU=` on an arm64 host to run
the runner natively). After a model change you can skip the native side (it reads `hw.jsonl`
from the output directory, so decompress the corpus first:
`zstd -d artifacts/oracle/{cases,hw}.jsonl.zst`):
`oracle/bin/oracle run -reuse-native -out artifacts/oracle -cases artifacts/oracle/cases.jsonl`.

Single pieces, all in `oracle/` (a separate Go module) and `Oracle/Main.lean`:

```
oracle/bin/oracle gen -n 2000 -o gen.jsonl              # randomised encodings per class
oracle/bin/oracle harvest -k 3 -o h.jsonl BINARY...     # every distinct .text word of arm64 ELFs
GODEBUG=asyncpreemptoff=1 qemu-aarch64 oracle/bin/runner < cases.jsonl > hw.jsonl
.lake/build/bin/janus-oracle < cases.jsonl > model.jsonl
oracle/bin/oracle run -cases gen.jsonl,h.jsonl -out DIR # both sides in parallel + compare
oracle/bin/oracle minimize -out DIR                     # shrink mismatches to repro.md
```

## What a case is

A case (`oracle/layout/layout.go`, `Case`) is one 32-bit instruction word plus a complete
initial state: `X0`–`X30`, `SP`, `NZCV`, `V0`–`V31` (field `v`, 128-bit hex; absent = zero),
`TPIDR_EL0` (field `tpidr`), a seed for the contents of a 4 KiB data
buffer, and `dczid`, the reference CPU's `DCZID_EL0`. That register is IMPLEMENTATION DEFINED
and read-only, so it cannot be set per case: `scripts/oracle.sh` asks the runner for its CPU's
value (`runner -dczid`; qemu `-cpu max` reports 7) and writes it into every case
(`oracle gen/harvest/selftest -dczid N`), the runner refuses a case whose value differs from its
own, and the Lean side uses it as `State.dczid`. Everything is at fixed addresses, so a case is closed and deterministic:

| address | what |
|---|---|
| `0x10_0000_0800` (`TestPC`) | the instruction; every other word of its page is `0` (= `UDF #0`) |
| `0x10_0004_0000` (`DataBase`), 4096 bytes | the data buffer; byte `i` = `Pattern(seed, i)` |
| `0xF_F810_0000` / `0xF_F810_1000` | trampoline code / context page (127 MiB below, out of the way) |

everything else nearby is unmapped. The Lean side (`janus-oracle`) builds a `State` with
these registers (`State.vregs`, `State.tpidr`), `pc = TestPC`, `dczid` from the case, and
`mem.regions = [⟨DataBase, 4096, writable⟩]` — exactly the buffer, nothing else — and runs
`Janus.Arm64.step word state`.

## How the native side observes one instruction

`oracle/cmd/runner` (Go, `GOARCH=arm64`) runs all cases of a shard in one process, without
landing pads or per-case subprocesses:

1. It writes the word at `TestPC`, refills the buffer, and calls a hand-assembled entry
   sequence that saves the host's callee-saved registers, SP and `TPIDR_EL0`, writes the case's
   `TPIDR_EL0` (`MSR`, allowed at EL0), loads `V0`–`V31` (`LDR Q`), `NZCV`, `SP`, `X0`–`X30`,
   executes `CLREX` and branches to `TestPC`.
2. Whatever the instruction does, the *next* thing that happens is a signal: falling
   through hits the `UDF` at `TestPC+4` (SIGILL); a branch lands on a `UDF` of the code page
   (SIGILL) or on an unmapped or non-executable page (SIGSEGV with `si_addr == pc`); a
   branch to a misaligned address raises SIGBUS/SIGSEGV at that address; an instruction that
   itself faults raises SIGILL/SIGSEGV/SIGBUS/SIGTRAP with `pc == TestPC`; a branch to itself
   spins until a watchdog thread sends SIGALRM (reported as `selfloop`, state = post-state).
3. A raw signal handler, installed with `rt_sigaction` (bypassing the Go runtime) and running
   on the thread's sigaltstack, copies `uc_mcontext` (`X0`–`X30`, `SP`, `PC`, `PSTATE`) and the
   `fpsimd_context` record of the signal frame (`V0`–`V31`; the runner checks its magic) into
   the context page and rewrites the saved PC to a resume sequence that restores the host
   registers and `TPIDR_EL0` and returns into Go.

So the captured state is precisely the architectural state after one instruction, and the
captured PC is where it went (fall-through, any branch target, or the instruction itself if
it faulted). The runner then reports registers, SP, NZCV, PC, `V0`–`V31` and the list of buffer
bytes that changed. `oracle selftest` checks this machinery against hand-computed answers (register and
flag preservation under all 16 NZCV values, loads, stores, guard faults, branches, self loops,
vector-register and `TPIDR_EL0` round trips, `LDR Q`, `UMOV`, `DUP`, `MRS TPIDR_EL0`).

`GODEBUG=asyncpreemptoff=1` is required (the runner refuses to start without it): an
asynchronous-preemption signal arriving while the test instruction runs would enter the Go
handler with a foreign `g` register.

## Case generation

* **Harvested** (`harvest/<class>`): every distinct word of the executable sections of real Go
  arm64 binaries — a program using `math/big`, `crypto/sha256`, `sort`, `encoding/json`,
  `regexp`, `compress/flate`, ... (`oracle/harvest/bigprog`), `go test -c` binaries of
  `math/big strconv sort crypto/sha256 bytes strings sync/atomic runtime` (the last two bring
  the atomics, `LDAR`/`STLR`, exclusives, `PRFM`, `MRS DCZID_EL0` and `DC ZVA` the runtime
  uses), and any `artifacts/*-arm64` — minus system encodings other than `MRS` and the C7
  cache-maintenance `SYS` space (SIMD&FP words are included, also the floating-point ones the
  model rejects), capped per class (`PER_CLASS`) by uniform sampling, each
  under `K` random states.
* **Targeted** (`gen/<class>`): random encodings per class with fixed opcode bits and fields
  biased towards allocated encodings, plus a share of unallocated variants.
  `ls.excl` mixes CAS/CASP (even registers), LDAR/STLR and LDXR/LDAXR (should-be-one fields
  mostly all ones, so most words are allocated) and store-exclusives; `ls.atomic` covers every
  `LD<op>`, `SWP` and `LDAPR`; `sys.mrs` is half `MRS Xt, DCZID_EL0`, half random system
  register reads; `sys.sys` is half `DC ZVA, Xt` (with `Xt` mostly in the buffer), half random
  `SYS #op1, C7, Cm, #op2` operations.
  The SIMD classes: `vls.multi` (LD1–LD4/ST1–ST4 multiple structures), `vls.single`
  (single structure and replicate), `vls.uimm`/`imm9`/`regoff`/`pair`/`literal` (SIMD&FP
  registers), `simd.3same`, `simd.s3same`, `simd.copy`, `simd.across`, `simd.2misc`,
  `simd.shift`, `simd.modimm`, `simd.ext`, `simd.tbl`, `simd.aes`, `simd.fmovgen`, each mostly
  over the opcodes the model covers plus random neighbours; `sys.mrs` also reads `TPIDR_EL0`.
  Vector register values are random, edge values, bytes from a small alphabet, or copies of
  another register with a few bytes changed (so element compares hit both outcomes); `TBL`
  indices are mostly in range; SIMD&FP memory accesses land in the buffer like the integer ones.
* **Group-random** (`rand/<class>`): fully random words inside each top-level encoding group
  (data-processing immediate / register, branches, loads/stores, SIMD&FP data processing,
  SIMD&FP loads/stores) — tests that the decoder rejects what it does not understand.

The class is assigned by `oracle/gen/classify.go` from the fixed opcode bits of the
top-level A64 tables; it only groups results and steers state generation, it never decides
what an instruction does. States: register values are a mix of edge values (`0`, `1`, `2^31`,
`2^32-1`, `2^63`, `2^64-1`, ...), random 64/32-bit values, small signed values and buffer
pointers. For loads/stores the base (and index) register is chosen so the effective address
mostly lands inside the buffer, sometimes straddles its ends, is misaligned, or is wild; for
`CAS*` the compare register matches memory half of the time; for `BR/BLR/RET` the target is
mostly a code-page address. Conditional classes (`B.cond`, `CCMP/CCMN`, `CSEL` family,
`ADC/SBC`) run each word under all 16 NZCV combinations. Encodings that are
CONSTRAINED UNPREDICTABLE in ways implementations may differ on (writeback with `Rt == Rn`,
load pair `Rt == Rt2`, store-exclusive status overlapping operands, odd `CASP` registers) are
never generated; harvested ones are tagged `!unpredictable` and reported separately.

## What agreement means

For each case the comparator (`oracle/cmd/oracle/compare.go`) produces one verdict:

| hardware | model | verdict |
|---|---|---|
| succeeds | succeeds, identical `X0`–`X30`, `SP`, `NZCV`, `pc`, `V0`–`V31`, buffer bytes | **agree** |
| faults (any signal at `TestPC`) | faults (any `Fault`) | **agree** (fault kinds are not compared: `undecodable` vs SIGILL, `outsideAllocation` vs SIGSEGV, ...) |
| branches to a misaligned address | `pcMisaligned` | **agree** |
| succeeds | faults | **model-gap**: the model is conservative here. Fine when it is `undecodable` (not in the supported subset yet) or `outsideAllocation` for an access that hardware served from mapped non-buffer memory (e.g. a literal load from the code page) |
| succeeds | succeeds with any difference | **MISMATCH** — a soundness bug |
| faults | succeeds | **MISMATCH** — the model admits an execution hardware refuses |
| no clean observation (control escaped into other executable memory, harness error) | — | **unobserved** (excluded) |

MISMATCH is the headline number: a proof about Go code is only sound if the model never claims
a successful step that differs from the machine. Model gaps only cost coverage (a proof
would get stuck on a fault), never soundness.

## Results with the Advanced SIMD classes of `NeonInstr` (2026-10-25, `scripts/oracle.sh neon`, qemu 10.2.1 `-cpu max`)

`OUT=artifacts/oracle-neon JOBS=8 SEED=1 scripts/oracle.sh neon` runs:

* **targeted** (`gen/`): the classes `neon.3same`, `neon.3samefp`, `neon.s3same`, `neon.3diff`,
  `neon.s3diff`, `neon.2misc`, `neon.s2misc`, `neon.across`, `neon.spair`, `neon.perm`,
  `neon.shift`, `neon.sshift`, `neon.elem`, `neon.selem`, `neon.sdup`, `vls.struct` (LD2–LD4/ST2–ST4,
  with and without post-index) and `vls.np` (LDNP/STNP), 20,000 words each (`oracle/gen/neon.go`).
  Every field is drawn uniformly, so every opcode, `size`, `Q`, `U`, `immh`, `L:M:H` and arrangement
  occurs, allocated or not. States: for the floating-point forms (`neonFP`) **every lane** gets an
  IEEE edge value of the lane's format (±0, subnormals, ±∞, quiet and signalling NaNs, halfway and
  boundary values), with crafted relations between the lanes of `Rn`, `Rm` and `Rd` (ties, exact
  cancellation, under/overflow boundaries) and random `FPCR` (`RMode`, `FZ`, `DN`, `AH`, `FIZ`,
  `NEP`) and `FPSR`; integer conversions get integer edge lanes; the integer forms get lanes at the
  saturation boundaries and small signed shift counts in `Rm` for the register shifts; `FPSR.QC`
  is compared like any other bit;
* **random** (`rand/`): 20,000 fully random words per top-level group;
* **harvested** (`harvest/`): every distinct SIMD&FP word of the supplementary C corpus
  (`oracle/harvest/neon`, 476 auto-vectorised loops built by gcc 15.2 and clang 21 at -O0/-O2/-O3,
  20 states each) and of the Go harvest binaries (3 states each);
* **sequence mode** (`seq/neon`, `oracle/cmd/neonseq`): 50,000 straight-line blocks of 4–24
  decodable SIMD&FP data-processing and load/store words (`Case.Words`; the runner lays them out
  from `TestPC`, `janus-oracle` threads the state through `runSeq`), with registers drawn from a
  small pool so instructions consume each other's results, base registers into the buffer, and the
  lane-wise states above. A block is one case; the whole final state is compared.

653,793 cases: **0 MISMATCH**, 637,430 agree, 16,363 model-gap (16,170 `undecodable`, 145
`trapped`, 31 `outsideAllocation`, 17 `unaligned`), 0 unobserved.

| part | cases | agree | model-gap | MISMATCH |
|---|---:|---:|---:|---:|
| targeted `gen/` | 340,000 | 327,362 | 12,638 | 0 |
| random `rand/` | 120,000 | 116,663 | 3,337 | 0 |
| harvested `harvest/` (C 133,152, Go 10,641) | 143,793 | 143,456 | 337 | 0 |
| sequences `seq/neon` | 50,000 | 49,949 | 51 | 0 |

Every `undecodable` gap is an encoding the decoder rejects by design: FP16 (the scalar and vector
`h`/`.4h`/`.8h` forms, `FCVTL`/`FCVTN` to or from half precision, fixed-point conversions with
`immh = 001x`), BFloat16, dot products, `FCMLA`/`FCADD`, `SQRDMLAH`/`SQRDMLSH`, `FMLAL`/`FMLSL`,
`FRINT32*/64*`, `PMULL`/`PMULL2`, the crypto extensions, and, in the random groups, the base
encodings the model rejects (store-exclusives, `LDNP`/`STNP` of general registers, unprivileged
loads, MTE, `BC.cond`, CSSC, MOPS). The `trapped` gaps are the two corners where the model refuses
to choose (`docs/SOUNDNESS.md`, "Advanced SIMD"): single-precision `FRECPE`/`FRSQRTE` under
`FPCR.AH = 1` (FEAT_RPRES), and vector `FABS`/`FNEG` under `FPCR.AH = 1` with a NaN lane. For the
latter, an earlier model followed the ASL (`FPAbs`/`FPNeg` leave a NaN unchanged under `AH`) and
qemu disagreed on 33 cases (20 words, 4 of them in sequences); the Sail model, run on those 33
cases, agreed with the ASL transcription on all of them, so this is a qemu deviation (it flips or
clears the NaN's sign bit), and the model now faults there instead.

The same corpus against the Sail model (`docs/ORACLE-SAIL.md`): Janus vs Sail 0 MISMATCH
(638,122 agree, 15,637 model-gap, 34 unobserved Sail errors on MOPS/PAuth words).

`JanusTests/Neon.lean` holds one hardware result per mnemonic the C corpora produce (208 words),
re-checked by the kernel.

After merging agent/armcrypto (main a3626db), whose `CryptoInstr.permute`/`dupScalar` replace the
NEON copies of ZIP/UZP/TRN and scalar DUP (the targeted `neon.perm`/`neon.sdup` classes are gone;
those words are now in `simd.permute`/`simd.dupscalar`), the same mode with `SEED=2`
(`OUT=artifacts/oracle-neon-final`): 616,007 cases, **0 MISMATCH**, 600,490 agree, 15,517
model-gap, 0 unobserved (targeted 300,000, random 120,000, harvested 146,007, sequences 50,000).

## Results with the crypto extension, CRC32 and permutes (2026-10-25, `scripts/oracle.sh crypto`, qemu 10.2.1 `-cpu max`)

The crypto corpus (`OUT=artifacts/oracle-crypto JOBS=8 scripts/oracle.sh crypto`, defaults
`N=20000`, `CRYPTO_HARVEST_K=40`, `SEQ_N=10000`, `SEQ_WINDOWS=20000`):

* **generated** (`gen/<class>`): the classes of `oracle/gen/crypto.go`, each the whole encoding
  group of the A64 tables (so its unallocated and UNDEFINED neighbours are classified with it):
  `crypto.sha3reg` (SHA1C/P/M/SU0, SHA256H/H2/SU1), `crypto.sha2reg` (SHA1H/SU1, SHA256SU0),
  `crypto.sha512` (SHA512H/H2/SU0/SU1, RAX1, and the SM3PARTW/SM4 neighbours), `crypto.sha3`
  (EOR3, BCAX, XAR, SM3SS1), `simd.pmull`, `simd.permute` (ZIP/UZP/TRN), `simd.dupscalar`,
  `dpr.crc32`, plus `simd.aes`, `simd.ext` and `simd.tbl`. A quarter of each class's words are
  fully random below its fixed bits; the rest come from targeted generators (allocated opcodes,
  edge `imm6` values, the reserved sizes).
* **harvested** (`harvest/<class>`): every distinct word of these classes in the `go test -c`
  binaries of `crypto/sha1`, `crypto/sha256`, `crypto/sha512`, `crypto/sha3`, `crypto/cipher`
  (AES-GCM), `hash/crc32` and `crypto/tls` (chacha20), each under 40 random states.
* **sequence mode** (`seq/<family>`, new): straight-line blocks laid out from `TestPC` that the
  runner executes in one go (falling through to the `UDF` after the last word) and `janus-oracle`
  steps word by word, comparing the final state. `oracle seqgen` writes synthetic chains of 2–12
  instructions over a small register pool per family (`sha1`, `sha256`, `sha512`, `sha3`,
  `ghash`, `crc32`, `permute`), so each instruction consumes what an earlier one produced, and
  `seq/harvest`: windows of 2–16 consecutive non-branch, non-memory words of the real crypto
  kernels (symbols matching `crypto/`, `hash/crc32`, `vendor/golang.org/x/crypto/`), each under
  4 states. Case field `words` (`oracle/layout/layout.go`); the format is the one of
  `audit/rt-model`'s sequence oracle. `scripts/oracle.sh full` now also runs a smaller sequence
  corpus (`SEQ_N=500`, `SEQ_WINDOWS=2000`).

389,440 cases: **0 MISMATCH**, 385,790 agree (40,278 of them both faulting), 3,650 model-gap, 0
unobserved. Every gap is `undecodable` SM3/SM4 (`sm3ss1` 1,375, `sm4e` 820, `sm3partw2` 498,
`sm4ekey` 495, `sm3partw1` 462), which the model does not implement and qemu does.

| class | cases | agree | of which both fault | model-gap | MISMATCH |
|---|---:|---:|---:|---:|---:|
| gen/crypto.sha2reg | 20,000 | 20,000 | 6,695 | 0 | 0 |
| gen/crypto.sha3 | 20,000 | 18,625 | 1,337 | 1,375 | 0 |
| gen/crypto.sha3reg | 20,000 | 20,000 | 5,453 | 0 | 0 |
| gen/crypto.sha512 | 20,000 | 17,725 | 2,220 | 2,275 | 0 |
| gen/dpr.crc32 | 20,000 | 20,000 | 3,310 | 0 | 0 |
| gen/simd.aes | 17,538 | 17,538 | 0 | 0 | 0 |
| gen/simd.dupscalar | 20,000 | 20,000 | 6,448 | 0 | 0 |
| gen/simd.ext | 20,000 | 20,000 | 5,006 | 0 | 0 |
| gen/simd.permute | 20,000 | 20,000 | 3,890 | 0 | 0 |
| gen/simd.pmull | 20,000 | 20,000 | 3,457 | 0 | 0 |
| gen/simd.tbl | 20,000 | 20,000 | 0 | 0 | 0 |
| gen/simd.other (AES-group neighbours) | 2,462 | 2,462 | 2,462 | 0 | 0 |
| harvest (11 classes, 486 distinct words × 40 states) | 19,440 | 19,440 | 0 | 0 | 0 |
| seq/crc32, ghash, permute, sha1, sha256, sha3, sha512 | 70,000 | 70,000 | 0 | 0 | 0 |
| seq/harvest (real kernel windows) | 80,000 | 80,000 | 0 | 0 | 0 |
| **total** | 389,440 | 385,790 | 40,278 | 3,650 | **0** |

The whole-ISA regression with the crypto model (`scripts/oracle.sh full`, `SEED=1`, default
knobs; the harvest now includes the crypto test binaries and the run includes 11,500 sequence
cases): 867,719 cases, **0 MISMATCH**, 832,639 agree, 35,079 model-gap (34,572 `undecodable`,
354 `unaligned`, 106 `noCode`, 47 `outsideAllocation`), 1 unobserved.

The model was right the first time on this corpus. Independently of qemu and Sail,
`JanusTests/Crypto.lean` checks the operations against the standards' test vectors (kernel
evaluation): SHA-1("abc") and SHA-256("abc") of FIPS 180-4 computed with SHA1C/P/M/H/SU0/SU1 and
SHA256H/H2/SU0/SU1 the way Go's kernels compose them, the CRC-32 and CRC-32C check values of
"123456789" with CRC32B/H/W/X and CRC32CB/CX, and PMULL/PMULL2 against independently computed
carry-less products.

## Results with scalar floating point (2026-10-24, `scripts/oracle.sh fp`, qemu 10.2.1 `-cpu max`)

The FP corpus (`OUT=artifacts/oracle-fp JOBS=16 N=25000 FP_HARVEST_K=40 scripts/oracle.sh fp`):
every scalar floating-point encoding class of the A64 tables (`fp.dp1` 1-source, `fp.dp2`
2-source, `fp.dp3` FMADD family, `fp.cmp`, `fp.ccmp` and `fp.csel` under all 16 NZCV values,
`fp.imm`, `fp.cvtint`, and the rejected fixed-point conversions `fp.cvtfix` as neighbours), plus
every distinct floating-point word of the `math`, `strconv`, `sort`, `math/big`, ... test binaries
under 40 states each. States come from an IEEE edge-value generator (±0, the smallest and
largest subnormal and normal numbers, random subnormals, ±1, ±0.5, values one ulp around
powers of two, ±∞, quiet and signalling NaNs of both signs with random payloads, integers and
halfway values around 2^24, 2^31, 2^32, 2^53, 2^63, 2^64, random encodings) with random bits above
the S/D value, and crafted operand pairs/triples for rounding ties, exact cancellation, and the
underflow/overflow boundaries; `FPCR` is random per case (`RMode` uniformly, `FZ`, `DN`, `AH`, `FIZ`,
`NEP` each about 22%), `FPSR` starts with random cumulative flags, and both are compared after
the step.

1,131,099 cases (1,094,987 generated, 36,112 harvested from 904 distinct words): **0 MISMATCH**,
993,577 agree (137,015 of them both faulting), 137,522 model-gap, 0 unobserved. Every gap is
`undecodable`: half precision (`ftype = 11`, FEAT_FP16), BFCVT, FRINT32/64, FJCVTZS,
fixed-point conversions, and the CONSTRAINED UNPREDICTABLE forms the decoder refuses (an
`FCMP #0.0` with a non-zero `Rm`, non-zero should-be-zero bits). Every `FPCR` mode was exercised
(`RMode` 0/1/2/3: 495,322 / 211,527 / 211,352 / 212,898 cases; `FZ` 253,447, `DN` 253,432, `AH`
253,667, `FIZ` 254,526, `NEP` 255,411).

| class | cases | agree | of which both fault | model-gap | MISMATCH |
|---|---:|---:|---:|---:|---:|
| fp.ccmp | 200,000 | 188,992 | 12,032 | 11,008 | 0 |
| fp.cmp | 100,000 | 86,500 | 20,344 | 13,500 | 0 |
| fp.csel | 200,000 | 189,952 | 10,752 | 10,048 | 0 |
| fp.cvtfix | 100,000 | 35,176 | 35,176 | 64,824 | 0 |
| fp.cvtint | 93,316 | 88,696 | 5,244 | 4,620 | 0 |
| fp.dp1 | 100,000 | 80,248 | 21,024 | 19,752 | 0 |
| fp.dp2 | 100,000 | 95,384 | 10,104 | 4,616 | 0 |
| fp.dp3 | 100,000 | 95,332 | 5,876 | 4,668 | 0 |
| fp.imm | 100,000 | 95,608 | 15,132 | 4,392 | 0 |
| simd.fmovgen | 1,671 | 1,577 | 1,331 | 94 | 0 |
| harvest (`fp.*`, 7 classes) | 36,112 | 36,112 | 0 | 0 | 0 |
| **total** | 1,131,099 | 993,577 | 137,015 | 137,522 | **0** |

A case now carries `fpcr`/`fpsr` (hex); the runner writes them with `MSR` before the step,
reads `FPCR` back (a case whose value the reference drops is an `error`; qemu ignores writes to
the trap-enable bits, so the generator never sets them) and reports both from the signal
frame's `fpsimd_context`. The comparator treats a difference in `FPSR` or `FPCR` like one in a
register. The model was right the first time on this corpus.

The whole-ISA regression run with the floating-point model and the new `fp.*` classes
(`scripts/oracle.sh full`, `SEED=1`, default knobs, harvest now including `math`): 766,650 cases
(436,177 generated, 330,473 harvested): **0 MISMATCH**, 730,803 agree, 35,846 model-gap
(35,272 `undecodable`, 416 `unaligned`, 105 `noCode`, 53 `outsideAllocation`), 1 unobserved.
Together with the FP corpus: 1,897,749 arm64 cases against qemu, 0 MISMATCH.

### TestFloat (Berkeley TestFloat 3e / SoftFloat 3e)

`scripts/testfloat.sh` builds SoftFloat three times, with the specializations that match the
architectures (`ARM-VFPv2` for `FPCR.DN = 0` with tininess before rounding, `ARM-VFPv2-defaultNaN`
for `DN = 1`, `8086-SSE` with tininess after rounding), generates TestFloat's level-1 vectors for
every operation and rounding mode, and runs each through the model (`janus-testfloat`,
`Oracle/TestFloat.lean`), comparing result bits and the five IEEE flags:

| model | functions × modes | vectors | mismatches | known NaN-rule differences |
|---|---:|---:|---:|---:|
| arm64, `FPCR` = `RMode` only (`f32`/`f64` add sub mul div sqrt mulAdd, roundToInt (5 modes, exact and not), conversions S↔D, from and to `i32 ui32 i64 ui64` (5 modes), the six comparisons) | 160 | 51,180,432 | **0** | 52,932 |
| arm64, `DN = 1` | 44 | 50,189,664 | **0** | 0 |
| arm64, `AH = 1` (tininess after rounding) | 48 | 50,558,304 | **0** | 288 |
| x86-64 SSE, all exceptions masked (`MXCSR.RC` from the mode) | 108 | 2,086,272 | **0** | 0 |
| **total** | 360 | 154,014,672 | **0** | 53,220 |

Two larger samplings follow (`LEVEL=1 N=2000000`: 2,000,000 vectors per two-operand
function and mode, and `LEVEL=2 N=1000000` for the one-operand functions; TestFloat refuses the
others at these sizes): 672,000,000 and 192,000,000 more vectors, **0 mismatches** (arm64
304M + 108M, `DN = 1` 72M + 12M, `AH = 1` 80M + 8M, x86 216M + 64M). In all, 1,018,014,672
TestFloat vectors.

The "known" rows are NaN results where SoftFloat's specialization differs from the architecture
and both are NaNs: SoftFloat's `ARM-VFPv2` `mulAdd` propagates a product operand's NaN before the
addend's, whereas Arm's `FPProcessNaNs3` takes the addend first (which qemu and Sail confirm);
and SoftFloat does not model `FPCR.AH = 1`'s NaN rules (no `IOC` for `0 × ∞ + qNaN`). Every
other vector matches bit for bit, flags included.

## gcc-compiled C (2026-10-24)

Every distinct word of gcc 15.2 `-O2` arm64 code (`examples/cgo/ccover.c` + `cfuncs.c` linked
with the C runtime: 205 words, `K=200`, 37,136 cases) is in the decoded subset already. Under qemu:
36,720 agree, 416 model-gap, **0 MISMATCH**. The gaps are `paciasp`/`autiasp` from the C start
files (not in compiled functions) and branches leaving the code page. In the Sail three-way run
on the same cases, Janus never produced a result that Sail does not (0 soundness cases).
`scripts/oracle.sh full` now adds this corpus to the harvest when `aarch64-linux-gnu-gcc` is
installed.

## Results with Advanced SIMD (2026-10-23, `scripts/oracle.sh full`, qemu 10.2.1 `-cpu max`, DCZID_EL0 = 7)

584,412 cases (260,000 generated, 324,412 harvested): **0 MISMATCH**, 568,770 agree, 15,639
model-gap (15,175 `undecodable`, 334 `unaligned`, 87 `noCode`, 43 `outsideAllocation`), 3
unobserved. Every case now carries `V0`–`V31` and `TPIDR_EL0`, and every successful case
compares all 32 vector registers.

The SIMD&FP classes and `MRS TPIDR_EL0` (grouped by encoding class, so a row also counts the
unmodelled neighbours inside the class: `LDNP`/`STNP`, `LD2`–`LD4` multiple, half-precision
`FMOV`, saturating and rounding shifts, ..., which are the model-gaps; the floating-point words
of `simd.other`/`vls.other` are not in the table):

| class | cases | harvest | agree-ok | agree-fault | model-gap | MISMATCH | unobserved | distinct words |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| simd.2misc | 4055 | 51 | 2218 | 1556 | 281 | 0 | 0 | 3962 |
| simd.3same | 4780 | 507 | 3490 | 945 | 345 | 0 | 0 | 4441 |
| simd.across | 4015 | 6 | 2004 | 2000 | 11 | 0 | 0 | 3910 |
| simd.aes | 4063 | 561 | 4063 | 0 | 0 | 0 | 0 | 2485 |
| simd.copy | 4152 | 117 | 2717 | 1435 | 0 | 0 | 0 | 4053 |
| simd.ext | 4076 | 57 | 3049 | 1027 | 0 | 0 | 0 | 4030 |
| simd.fmovgen | 4562 | 558 | 3586 | 445 | 531 | 0 | 0 | 3291 |
| simd.modimm | 4013 | 0 | 3778 | 230 | 5 | 0 | 0 | 4005 |
| simd.s3same | 4115 | 3 | 3385 | 596 | 134 | 0 | 0 | 4092 |
| simd.shift | 4302 | 48 | 2086 | 1917 | 299 | 0 | 0 | 4269 |
| simd.tbl | 4027 | 18 | 4027 | 0 | 0 | 0 | 0 | 3996 |
| sys.mrs `mrs tpidr_el0` | 1354 | 3 | 1354 | 0 | 0 | 0 | 0 | 32 |
| vls.imm9 | 4538 | 6 | 1968 | 2570 | 0 | 0 | 0 | 4533 |
| vls.literal | 4973 | 0 | 3526 | 1447 | 0 | 0 | 0 | 4909 |
| vls.multi | 4517 | 369 | 3769 | 665 | 83 | 0 | 0 | 4227 |
| vls.pair | 6911 | 990 | 5292 | 1246 | 373 | 0 | 0 | 6251 |
| vls.regoff | 4419 | 306 | 2435 | 1984 | 0 | 0 | 0 | 4212 |
| vls.single | 4303 | 33 | 2324 | 1978 | 1 | 0 | 0 | 4268 |
| vls.uimm | 9265 | 4224 | 7138 | 2126 | 1 | 0 | 0 | 6447 |
| **total** | 86440 | 7857 | 62209 | 22167 | 2064 | 0 | 0 | 77413 |

Before the extension (486,463 cases) the SIMD&FP words were not tested at all.

## Earlier results: atomics (2026-10-23, `scripts/oracle.sh full`, qemu 10.2.1 `-cpu max`, DCZID_EL0 = 7)

486,463 cases (172,000 generated, 314,463 harvested): **0 MISMATCH**, 475,022 agree, 11,440
model-gap (10,902 `undecodable`, 385 `unaligned`, 107 `noCode`, 46 `outsideAllocation`), 1
unobserved. The previous run, before the atomics/`DC ZVA` extension, had 427,845 cases, 0
MISMATCH and 19,725 model-gaps.

The instructions added with the single-threaded atomics model (`agree-ok`: both sides succeeded
with identical registers, flags, pc and memory; `agree-fault`: both faulted). Rows for encodings
the model still rejects (`LDLAR/STLLR`, `LDXP/STXP`, `STXR/STLXR`) show that hardware
successes there are only model-gaps:

| instruction | cases | harvest | agree-ok | agree-fault | model-gap | MISMATCH | unobserved | distinct words |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| CAS | 1554 | 273 | 1017 | 480 | 57 | 0 | 0 | 1370 |
| CASP | 548 | 0 | 289 | 250 | 9 | 0 | 0 | 544 |
| CLREX | 498 | 0 | 498 | 0 | 0 | 0 | 0 | 16 |
| DC ZVA | 2047 | 3 | 1705 | 342 | 0 | 0 | 0 | 32 |
| LD<op> | 3134 | 531 | 2682 | 325 | 127 | 0 | 0 | 2778 |
| LDAPR | 336 | 0 | 209 | 115 | 12 | 0 | 0 | 328 |
| LDAR/STLR | 2005 | 885 | 1457 | 454 | 94 | 0 | 0 | 1339 |
| LDLAR/STLLR | 203 | 0 | 0 | 161 | 42 | 0 | 0 | 203 |
| LDXP/STXP | 583 | 0 | 0 | 52 | 531 | 0 | 0 | 582 |
| LDXR/LDAXR | 1083 | 396 | 710 | 117 | 256 | 0 | 0 | 785 |
| MRS DCZID_EL0 | 1988 | 3 | 1988 | 0 | 0 | 0 | 0 | 32 |
| PRFM (literal) | 1169 | 0 | 1169 | 0 | 0 | 0 | 0 | 1153 |
| PRFM/PRFUM | 855 | 0 | 602 | 253 | 0 | 0 | 0 | 854 |
| STXR/STLXR | 1072 | 471 | 0 | 1 | 1071 | 0 | 0 | 756 |
| SWP | 1051 | 78 | 898 | 112 | 41 | 0 | 0 | 999 |
| **total** | 18126 | 2640 | 13224 | 2662 | 2240 | 0 | 0 | 11771 |

`unaligned` gaps are qemu's FEAT_LSE2 behaviour (a misaligned ordered/atomic access inside 16
bytes succeeds; the model requires natural alignment). The other gaps of the accepted
classes are encodings the model rejects and qemu executes anyway: should-be-one `Rs`/`Rt2`
fields that are not all ones (CONSTRAINED UNPREDICTABLE; qemu ignores the fields) and odd
`CASP` registers. The rows are grouped by encoding
fields, so they also count unallocated neighbours (e.g. `PRFUM` with a writeback mode, which
both sides reject: `agree-fault`). The 24 `prfm` words of the Go runtime are not in the
harvest sample (`ls.uimm` is capped at `PER_CLASS`); the generated ones cover every `prfop`.

## Known limits of the reference

* **qemu, not silicon.** qemu's AArch64 user-mode emulation is the reference; with the default
  `-cpu max` it implements recent extensions (LSE atomics, CSSC `ABS/CNT/CTZ/SMAX`, MTE `STG*`,
  PAuth, `BC.cond`, ...). A model that rejects those is merely conservative. Running
  `QEMU= scripts/oracle.sh` on an arm64 Linux machine uses real hardware instead.
* **SP alignment.** Linux sets `SCTLR_EL1.SA0`, so an SP-based access with a misaligned SP
  faults on hardware, and the model faults with `spMisaligned`; qemu user mode does not check
  SP alignment, so such cases appear as model-gaps. The oracle therefore cannot confirm the
  model's SP-alignment rule, only that it is conservative. The generator keeps SP 16-aligned.
* **Top-byte-ignore.** Linux enables TBI for EL0, so a register branch to an address with a
  non-zero top byte sets `PC` to the address with bits 63:56 replaced by bit 55
  (`AArch64.BranchAddr`); qemu does the same.
* **Exclusive monitor.** Each case starts with the monitor open (`CLREX`), so on hardware a
  single `STXR` always fails (status 1, no store). The model rejects every store-exclusive
  (see `docs/SOUNDNESS.md`), so these are model-gaps.
* **Alignment of atomics.** qemu `-cpu max` implements FEAT_LSE2: an `LDAR`/`STLR`/LSE atomic
  that is misaligned but stays inside 16 bytes succeeds. The model requires natural alignment
  (`Fault.unaligned`), so these are model-gaps (`unaligned`); misaligned accesses that cross 16
  bytes fault on both sides.
* **Memory outside the buffer.** The model only knows the buffer; the native process also has
  the code page and the Go runtime mapped. An access that lands on mapped non-buffer memory
  succeeds natively and faults in the model (model-gap), never the other way round.
* Only the 4 KiB buffer is compared byte by byte; a store that writes a byte equal to the
  pattern value already there is invisible (to both sides).
