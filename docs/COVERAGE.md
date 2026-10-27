# Coverage: what Janus can verify today, and the measured gap to all single-threaded Go

**Scope.** Janus should verify every single-threaded program built by Go 1.26 for linux/arm64 and
linux/amd64: Go-compiled code, hand-written Go assembly (including its SIMD and crypto
extensions) and the C code of cgo programs. The Go runtime is trusted through documented
contracts ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md)). The one exclusion is concurrency:
goroutines, channels, `select`, `sync`, and the runtime entry points behind them. Everything else
listed below is a gap with a work package in [the plan](#6-work-plan).

**Baseline.** main at 139f774, plus the unmerged branches agent/alloc, agent/maps, agent/ffi and
agent/iface-alloc (read with `git show`, nothing merged). Go 1.26.0 (`GOTOOLCHAIN=go1.26.0`),
gcc 15.2.0 (Ubuntu 15.2.0-16ubuntu1, native and `aarch64-linux-gnu`), clang 21.1.8. Measured
2026-10-24.

**Update (agent/rtiface, R2 of the plan).** The interface runtime contracts (`convT*`,
`assertE2I(2)`, `typeAssert`, `interfaceSwitch`, `efaceeq`, `ifaceeq`, with the cache model of
`emptyTypeAssertCache`/`emptyInterfaceSwitchCache`) and the four interface construct proofs on
both ISAs (`Box`, `AsHasher`, `Classify`, `Equal`) are counted in the numbers below by hand on top
of the measured baseline: 15 more runtime names (14 linked), 4 more construct rows. The rest of
the page is the measured baseline.

**Regenerating.** `scripts/coverage.sh` rebuilds every number on this page. It builds the std
test binaries in a fresh `mktemp -d` under `/var/tmp` and removes it at the end (about 4.2 GB;
`KEEP=1` keeps it). It writes the raw tables to `artifacts/coverage/`. The stages are `build`,
`insn` (criteria 1 and 4), `runtime` (criterion 2) and `cc` (criterion 5). The measuring program
is `scripts/coverage/` (Go; see [Method](#method)). It runs at most one heavy job, waits while
MemAvailable is below 40 GiB, and caches decoder verdicts per decoder executable. The first amd64
pass decodes about 10.6 M distinct encodings, which takes roughly 25 minutes; later passes reuse
the cache.

## Headline numbers

| criterion | arm64 | amd64 (GOAMD64=v1) | amd64 (GOAMD64=v3) |
|---|---:|---:|---:|
| 1. Go-compiled std functions that fully decode | 15,517 / 16,602 (**93.46%**) | 16,625 / 16,625 (**100%**) | 16,614 / 16,614 (**100%**; 94.60% before WP-B) |
| 1. Go assembly functions that fully decode | 151 / 207 (**72.95%**; 139 / 207 = 67.15% before WP-H) | 160 / 265 (**60.38%**; 148 before WP-D) | 157 / 262 (**59.92%**; 145 before WP-D) |
| 1. compiler-generated wrappers / Go test code | 99.40% / 97.09% | 100% / 100% (99.98% before WP-B) | 100% / 100% (99.60% / 99.16% before WP-B) |
| 2. runtime entry points with a contract, stub or proof (main + branches) | 78 of 309 names (39 on main; agent/rtiface adds 15, agent/panic 7) | same | same |
| 2. … of the 191 linked on arm64/amd64: still missing | 134 (12 of them concurrency, excluded) | | |
| 3. language constructs with a proved example | 67 of 75 rows (8 have none on either ISA; agent/constructs closes 20, agent/rtiface 4, agent/panic 3) | | |
| 5. C corpus functions that fully decode, cgo default `-O2` (gcc / clang) | **100% / 100%** (all six configurations, WP-I; 93.6% / 86.2% before) | **96.4% / 98.2%** since WP-D (83.6% / 78.0% before: SSE2 packed) | `-O3 -march=x86-64-v3`: 59.1% / 58.7% (VEX, WP-F) |

Main findings:

* **arm64 Go code has one blocker.** It is the store-exclusive family (`STLXR`, `STLXRB`) of the
  LL/SC fallback that every `sync/atomic` and `internal/runtime/atomic` operation carries next to
  its LSE fast path. The decoder rejects it on purpose (a store-exclusive may fail spuriously;
  [SOUNDNESS.md](SOUNDNESS.md)). That one family blocks 1,085 Go-compiled functions, 36 wrappers
  and 724 test functions, and accounts for all arm64 Go gaps.
* **amd64 v1 Go code decodes completely.** The 5 test functions (`math_test`, `VFMADD231SD`
  behind `x86HasFMA`) that were rejected at the baseline decode since WP-B (re-measured
  2026-10-25: 24,881 / 24,881).
* **amd64 v3 Go code decodes completely since WP-B** (agent/amd64v3, measured 2026-10-25).
  It was blocked by four scalar extensions: BMI1/BMI2 (`SHLX`, `SHRX`, `SARX`, `ANDN`, `BLSR`,
  `BLSI`) unblocked 676 functions, `MOVBE` 349, scalar FMA 79 and SSSE3 (`PSHUFB`, `PSIGNB` in
  the Swiss-table group match) 26. With them modelled (and oracle-tested, 0 MISMATCH) every
  Go-compiled, wrapper and test function of the v3 std test binaries decodes.
* **The SSE packed families are modelled since WP-D** (agent/sse, measured 2026-10-25): SSE2
  integer and floating point, SSE3, SSSE3, SSE4.1 and SSE4.2 (`CRC32`, `PCMPESTRI`...), oracle
  0 MISMATCH. That unblocked 12 amd64 assembly functions (`indexbody`, `chacha8rand.block`,
  `castagnoliSSE42`/`castagnoliSSE42Triple`, the four P-256 constant-time selects and the four
  AES `_expand_key_*` helpers; no assembly function is blocked by an SSE family any more) and
  took the C corpus at cgo's `-O2` from 78.0% to 98.2% (clang) and 83.6% to 96.4% (gcc); what
  is left there is x87, the `NOTRACK` jump tables and the TLS call sequence (WP-J).
* **Assembly is blocked by system instructions first, then SIMD and crypto.** `SVC`/`SYSCALL`,
  `BRK`/`INT3`/`UD2`, `MRS`/`MSR` of ID and DIT registers, `CPUID`/`XGETBV`/`RDTSC` are the sole
  blocker of 53 arm64 and 46 amd64 assembly functions. Then come AVX-512 (29 GC-scan
  `expandAVX512_*` kernels), the SSE packed-integer family, AES-NI, PCLMULQDQ, SHA-NI, AVX2, ADX,
  the arm64 crypto extensions (PMULL, SHA1/SHA256/SHA512/SHA3) and CRC32.
* **The hottest assembly callees already decode** on both ISAs: `morestack*`, `panicBounds`,
  `gcWriteBarrier1..8`, `memmove`, `memequal`, `memclrNoHeapPointers`, `cmpstring`, `IndexByte*`,
  `Compare`, `Count*` and `Index*`. Blocked, in order of Go callers: `systemstack` on amd64
  (`INT $3` after its abort path), the syscall wrappers (`nanotime1`, `Syscall6`, `exit`,
  `osyield`, ...), `math.archExp` on amd64 (FMA/AVX path), `cputicks` (`RDTSC`), the AES-NI
  `memhash32`/`memhash64`, and the crypto kernels.
* **C code is blocked mainly by the vector code that compilers auto-vectorise.** On amd64 that
  was SSE2 packed integer at `-O2`/`-O3` (modelled since WP-D) and is AVX2/BMI2/FMA with
  `-march=x86-64-v3`. On arm64 it is
  `ADDP`, `UADDW`, `UMULL`, `FMLA`, `UZP1` and `LD4`/`ST4`. Three further encodings block gcc
  code on amd64: `ENDBR64` (on every gcc function, Ubuntu's default `-fcf-protection`; fixed on
  agent/ffi), `NOTRACK JMP` (the CET form of jump-table dispatch) and the general-dynamic TLS call
  sequence. `long double` needs x87. The C ABI model of agent/ffi handles integer register
  arguments only (see [5](#5-cgo-c-code)).

## Method

* **Corpus.** `go test -c -trimpath` of every std package with test files (250, from
  `go list std`), `CGO_ENABLED=0`, built three times: `GOARCH=arm64`, `GOARCH=amd64 GOAMD64=v1` and
  `GOAMD64=v3`. Each also has the two packages that need cgo (`runtime/cgo`,
  `internal/runtime/cgobench`) built with `CGO_ENABLED=1` (gcc, `-O2 -g`), whose C functions are
  reported as kind `c`. That gives 250 binaries per configuration, about 1.4 GB each.
* **Functions.** Every `STT_FUNC` symbol in an executable section that starts a pclntab function
  (or lies inside a pclntab entry without a file: the C code of an externally linked binary). The
  kind comes from the pclntab file of the entry PC: `.s` is **assembly**; `<autogenerated>` is a
  **wrapper** (ABI wrappers, method-value and interface wrappers, generated `eq`/`hash`
  functions); `_test.go` and the test main are **test**; everything else is **Go-compiled**. A
  function is counted once, by its linked name, over all 250 binaries, and it counts as blocked if
  any copy of it is.
* **Decoding.** The instruction stream is swept linearly. arm64 is fixed-width: trailing
  zero-word padding and the literal pools of `LDR (literal)` are excluded, since they are data.
  amd64 uses `x86asm` (via `oracle-amd64/gen.Decode`, with the `VZEROUPPER` length fix), with
  fallbacks that keep the sweep in step over encodings `x86asm` does not know: VEX/EVEX lengths,
  legacy `0F 38`/`0F 3A` such as `ADCX`/`ADOX`, and `ENDBR64`. Every distinct encoding then goes to
  **the trusted Lean decoder**. On arm64 that is `janus-decode` (`Janus.Arm64.decode`); on amd64 it
  is `janus-oracle-amd64` (`Janus.Amd64.step`), where an encoding is accepted iff the result is
  not `undecodable` and the decoded length equals the sweep's. A function **fully decodes** iff
  every swept instruction is accepted.
* **What "fully decodes" means.** It is the precondition for verifying a function, not a
  verification. It is conservative in two directions. First, a feature-gated path counts even when
  a proof could exclude it (the AVX path of `memmove` decodes; `math.archExp`'s FMA path does not,
  although v1 code never takes it). Second, it says nothing about the semantics proofs need beyond
  decoding (for example the dynamic-call hypotheses or the runtime contracts of criterion 2).
  Rejected encodings are named by `arm64asm`/`x86asm` mnemonic and grouped into ISA families
  (`scripts/coverage/decode.go`). The naming is informational; the verdict is always the Lean
  decoder's.
* **Rankings.** "Functions blocked" counts the functions in which a class or family occurs at
  least once among the rejected encodings. "Sole" counts those in which it is the only one. The
  greedy tables add families one at a time, always the one that makes the most functions fully
  decodable.

## 1. Instruction coverage

### 1.1 Functions that fully decode

| kind | arm64 | amd64 v1 | amd64 v3 |
|---|---:|---:|---:|
| Go-compiled (std, non-test) | 15,517 / 16,602 (**93.46%**) | 16,625 / 16,625 (**100.00%**) | 16,614 / 16,614 (**100.00%**) |
| Go assembly (`.s`) | 151 / 207 (**72.95%**, after WP-H) | 160 / 265 (**60.38%**; 148 before WP-D) | 157 / 262 (**59.92%**; 145 before WP-D) |
| compiler-generated (`<autogenerated>`) | 5,960 / 5,996 (99.40%) | 6,002 / 6,002 (100.00%) | 6,000 / 6,000 (100.00%) |
| Go test code | 24,128 / 24,852 (97.09%) | 24,881 / 24,881 (100.00%) | 24,881 / 24,881 (100.00%) |
| C in the cgo binaries (`runtime/cgo`, gcc `-O2`) | 20 / 20 (100%) | 20 / 20 (100%; `ENDBR64` since agent/ffi, `PUNPCKLQDQ` since WP-D) | 20 / 20 |
| instruction occurrences accepted (Go-compiled) | 99.906% | 100.000% | 100.000% |
| distinct encodings decoded | 1,038,143 | 10,633,357 (v1 and v3 together, cached) | |

By package (Go-compiled): on arm64, 244 of 301 packages decode completely; the largest gaps
(blocked/total) are `runtime` 229/1,809, `net/http` 223/1,138, `database/sql` 69/224,
`crypto/tls` 43/511, `internal/sync` 42/105, `unique` 36/139, `internal/poll` 29/135, `testing`
27/206, `sync` 24/255 and `internal/runtime/atomic` 23/57, all from `STLXR`. On amd64 v3 every
package decodes completely (before WP-B 184 of 301 did; the largest gaps were `runtime`
110/1,807, `slices` 49/535, `unique` 48/139, `crypto/tls` 40/511, `internal/runtime/maps` 37/66,
`math` 34/61, `math/big` 28/259, `encoding/gob` 28/270, `internal/sync` 25/105 and `hash/fnv`
24/64). Per-package tables for every
kind are in `artifacts/coverage/insn-<cfg>.txt`.

### 1.2 Go-compiled code: rejected encodings, ranked by functions blocked

Functions here include wrappers and test code (47,450 on arm64; 47,508 on v1; 47,495 on v3).

| ISA | class (mnemonic) | family | functions blocked (Go / wrapper / test) | sole blocker | example |
|---|---|---|---:|---:|---|
| arm64 | `STLXR` (W and X) | exclusive (store-exclusive) | 1,070 / 36 / 715 | 1,062 / 36 / 712 | `881bfc41` `STLXR W27, W1, [X2]` in `internal/runtime/exithook.Run` |
| arm64 | `STLXRB` | exclusive (store-exclusive) | 23 / 0 / 12 | 15 / 0 / 9 | `081bfc02` `STLXRB W27, W2, [X0]` in `runtime.lock2` |
| amd64 v1 | `VFMADD231SD` (VEX) | FMA | 0 / 0 / 5 | 5 | `c4e2f9b9e1` in `math_test.TestFMA` |
| amd64 v3 | `SHLX` | BMI2 | 360 + 10 wrappers | 264 | `c4e2e1f7f6` `shlxq %rbx,%rsi,%rsi` in `internal/abi.Name.IsBlank` |
| amd64 v3 | `MOVBE` | MOVBE | 290 + 13 wrappers | 279 | `480f38f1542428` in `runtime.randinit` (`encoding/binary` big-endian) |
| amd64 v3 | `SHRX` | BMI2 | 199 + 3 | 109 | `c4e2ebf7f0` in `internal/strconv.atof64exact` |
| amd64 v3 | `ANDN` | BMI1 | 67 | 45 | `c4c2c0f2f8` in `internal/runtime/maps.(*table).Clear` |
| amd64 v3 | `VFMADD231SD` | FMA (scalar) | 49 | 44 | `c4e2e9b9c1` in `runtime.fastexprand` |
| amd64 v3 | `BLSR` | BMI1 | 48 | 17 | `c4e2e8f3ce` in `internal/strconv.formatBits` |
| amd64 v3 | `PSHUFB` | SSSE3 | 24 | 0 | `66410f3800c7` in `internal/runtime/maps.(*Map).getWithKeySmall` |
| amd64 v3 | `SARX` | BMI2 | 14 + 4 | 4 | `c4e2eaf7c9` in `reflect.(*rtype).OverflowInt` |
| amd64 v3 | `PSIGNB` | SSSE3 | 13 | 0 | `660f3808c0` in `internal/runtime/maps.(*table).getWithKey` |
| amd64 v3 | `VFMADD231SS` | FMA (scalar) | 4 | 2 | `c4e269b9c1` in `math/rand.(*Rand).ExpFloat64` |
| amd64 v3 | `BLSI` | BMI1 | 1 | 0 | `c4e2f0f3de` in `math/big.nat.itoa` |

That is the complete list of rejected classes in Go-compiled code as measured at the baseline;
the amd64 v3 rows are all modelled since WP-B (agent/amd64v3), which leaves v3 Go code with no
rejected class. The greedy order:

| ISA | step | family | + functions | fully decodable after (incl. wrappers, tests) |
|---|---:|---|---:|---:|
| arm64 | 1 | store-exclusive (`STXR`/`STLXR`, B/H) | +1,845 | 47,450 / 47,450 (100%) |
| amd64 v1 | 1 | FMA (scalar) | +5 | 47,508 / 47,508 (100%) |
| amd64 v3 | 1 | BMI1/BMI2 | +676 | 47,041 / 47,495 (99.0%) |
| amd64 v3 | 2 | MOVBE | +349 | 47,390 (99.8%) |
| amd64 v3 | 3 | FMA (scalar) | +79 | 47,469 (99.9%) |
| amd64 v3 | 4 | SSSE3 (`PSHUFB`, `PSIGNB`) | +26 | 47,495 (100%) |

### 1.3 Assembly functions

**Update (WP-H, agent/armcrypto, 2026-10-25).** The arm64 crypto extensions (`SHA1*`, `SHA256*`,
`SHA512*`, `EOR3`/`RAX1`/`XAR`/`BCAX`, `PMULL`/`PMULL2`), `CRC32*`/`CRC32C*`, the permutes
(`ZIP`/`UZP`/`TRN`) and scalar `DUP` (`MOV Sd, Vn.S[0]`) now decode (`Janus/Arm64/DecodeCrypto.lean`).
`scripts/coverage.sh insn` (arm64, same corpus) gives **151 / 207 (72.95%)** assembly functions
fully decoded, up from 139, and 99.228% of assembly instructions accepted (94.566% before). The 12
functions gained are the 5 GCM kernels, `sha1block`, `blockSHA2`, `blockSHA512`,
`keccakF1600NEON`, `castagnoliUpdate`, `ieeeUpdate` and chacha20's `xorKeyStreamVX`. The remaining
arm64 assembly blockers are system instructions (53 functions), the `UDF #0` traps (2) and
`STLXR` in `cgoSigtramp` (1). The tables below are the pre-WP-H measurement.

Assembly is a verification target with the same weight as Go code, not only a callee. Of the
assembly functions, 145 of 207 on arm64 and 170 of 265 on amd64 are ABI0 (`.abi0` symbols), and
the rest are ABIInternal. Fully decoding today: ABI0 90/145 and ABIInternal 49/62 on arm64; ABI0
91/170 and ABIInternal 57/95 on amd64 v1. The ABI0 calling convention ([WP-L](#6-work-plan), done:
[ABI0.md](ABI0.md)) states theorems about every ABI0 function (`GoABI0.Ensures0`,
`Amd64.GoABI0.Ensures0`), about the ABI wrappers in both directions and about Go code with direct
ABI0 calls, on both ISAs (`examples/asm`); what still limits the 145 / 170 is decoding.

**ISA families, greedy order** (functions that become fully decodable when the family is added
after the rows above):

| step | arm64 (207) | + | after | amd64 v1 (265) | + | after |
|---:|---|---:|---:|---|---:|---:|
| 1 | system: `SVC`, `BRK`, `MRS`/`MSR` (MIDR, DIT), `MSR DIT` (PSTATE) | +53 | 192 (92.8%) | system: `SYSCALL`, `INT 3`, `UD2`, `CPUID`, `XGETBV`, `RDTSC(P)`, `HLT` | +46 | 194 (73.2%) |
| 2 | crypto extensions: `PMULL`/`PMULL2`, `SHA1*`, `SHA256*`, `SHA512*`/SHA3 (`EOR3`, `RAX1`, `XAR`, `BCAX`) | +8 | 200 (96.6%) | AVX-512 (EVEX, opmask `K*`; GFNI, VBMI, `VPOPCNTB`, `VPCOMPRESSQ`, `VPTERNLOGD`, `VPCLMULQDQ`) | +29 | 223 (84.2%) |
| 3 | `UDF #0` inside `rt0_go`/`callNNN` (trap) | +2 | 202 (97.6%) | SSE2 packed integer and shuffles (`PADDD`, `PSLLDQ`, `PSRLDQ`, `PCMPEQD`, `PANDN`, `SHUFPS`, ...) | +9 | 232 (87.5%) |
| 4 | CRC32 (`CRC32{B,H,W,X}`, `CRC32C*`) | +2 | 204 (98.6%) | SSE4.2 (`CRC32`, `PCMPESTRI`) | +3 | 235 (88.7%) |
| 5 | ASIMD `ZIP1`/`ZIP2`, `MOV` (element) | +2 | 206 (99.5%) | AES-NI | +3 | 238 (89.8%) |
| 6 | store-exclusive (`cgoSigtramp`) | +1 | 207 (100%) | SSE4.1 (`PINSR*`, `PEXTR*`, `PBLENDW`) | +2 | 240 (90.6%) |
| 7 | | | | SSSE3 (`PSHUFB`, `PALIGNR`) | +5 | 245 (92.5%) |
| 8 | | | | PCLMULQDQ | +5 | 250 (94.3%) |
| 9 | | | | SHA-NI | +2 | 252 (95.1%) |
| 10–14 | | | | `PUSHFQ`/`POPFQ` (`asyncPreempt`), AVX-128, FMA (`math.archExp`), the `boring/sig` marker (data, not code), BMI | +4 | 256 (96.6%) |
| 15 | | | | AVX2 (256-bit VEX) | +5 | 261 (98.5%) |
| 16 | | | | ADX (`ADCX`/`ADOX`, with BMI2 `MULX`) | +4 | 265 (100%) |

amd64 v3 is the same as v1, except that 3 v1-only `math` assembly functions are absent (the
compiler uses the instructions directly): 145 of 262 decode.

**Since WP-D** (SSE packed, agent/sse) steps 3, 4, 6 and 7 of the amd64 column are modelled:
160 of 265 (v1) and 157 of 262 (v3) assembly functions decode, 82.3% → 87.2% of their instruction
occurrences. The 12 functions that became fully decodable are `indexbody` (`PCMPESTRI`),
`internal/chacha8rand.block`, `hash/crc32.castagnoliSSE42` and `castagnoliSSE42Triple`,
`crypto/internal/fips140/nistec.p256MovCond`, `p256Select`, `p256SelectAffine`,
`p256PointAddAffineAsm`, and `_expand_key_128`, `_expand_key_192a`, `_expand_key_192b`,
`_expand_key_256b`. No amd64 assembly function has an SSE-family blocker left; the remaining
families are system instructions (WP-C), AVX-512 (WP-G), AES-NI, `PCLMULQDQ`, SHA-NI and ADX
(WP-E), AVX/AVX2 (WP-F).

**Per std package** (fully decodable / assembly functions; the families blocking them):

| package | arm64 | amd64-v1 | amd64-v3 | blocking families (functions, arm64 / amd64-v1) |
|---|---:|---:|---:|---|
| runtime | 80/129 | 92/134 | 92/134 | arm64: system / barrier / hint 46, padding/udf 2, exclusive / acquire-release 1; amd64-v1: system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 38, AES-NI 3, SSE4.1 2, SSE/SSE2 1, SSSE3 1, AVX-512 (EVEX, opmask) 1, integer/base 1 |
| internal/runtime/gc/scan | – | 0/29 | 0/29 | amd64-v1: AVX-512 (EVEX, opmask) 29 |
| crypto/internal/fips140/aes | 7/7 | 5/12 (1 before WP-D) | 5/12 | amd64-v1: AES-NI 7, SSE/SSE2 5, SSE4.1 4, SSSE3 4 |
| crypto/internal/fips140/aes/gcm | 0/5 | 0/5 | 0/5 | arm64: crypto extension (AES/SHA/PMULL/SHA3) 5; amd64-v1: PCLMULQDQ 5, SSE/SSE2 5, SSSE3 5, SSE4.1 4, AES-NI 3 |
| crypto/internal/fips140/nistec | 15/15 | 16/16 (12 before WP-D) | 16/16 | amd64-v1: SSE/SSE2 4 |
| hash/crc32 | 0/2 | 2/3 (0 before WP-D) | 2/3 | arm64: CRC32 2; amd64-v1: SSE4.2 2, AVX (128-bit VEX) 1, AVX-512 (EVEX, opmask) 1, PCLMULQDQ 1, SSE/SSE2 1, SSE4.1 1 |
| syscall | 0/2 | 0/3 | 0/3 | arm64: system / barrier / hint 2; amd64-v1: system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 3 |
| crypto/internal/fips140/bigmod | 4/4 | 0/3 | 0/3 | amd64-v1: ADX 3, BMI1/BMI2/LZCNT 3 |
| crypto/internal/fips140/sha256 | 0/1 | 0/2 | 0/2 | arm64: crypto extension (AES/SHA/PMULL/SHA3) 1; amd64-v1: AVX (128-bit VEX) 1, AVX2 (256-bit VEX) 1, BMI1/BMI2/LZCNT 1, SHA-NI 1, SSE/SSE2 1, SSE4.1 1, SSSE3 1 |
| crypto/sha1 | 0/1 | 0/2 | 0/2 | arm64: ASIMD (NEON vector) 1, crypto extension (AES/SHA/PMULL/SHA3) 1; amd64-v1: AVX2 (256-bit VEX) 1, BMI1/BMI2/LZCNT 1, SHA-NI 1, SSE/SSE2 1, SSE4.1 1, SSSE3 1 |
| internal/cpu | 0/1 | 1/3 | 1/3 | arm64: system / barrier / hint 1; amd64-v1: system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 2 |
| vendor/golang.org/x/crypto/chacha20poly1305 | – | 1/3 | 1/3 | amd64-v1: AVX2 (256-bit VEX) 2, BMI1/BMI2/LZCNT 2, SSE/SSE2 2, SSSE3 2 |
| vendor/golang.org/x/sys/cpu | – | 0/2 | 0/2 | amd64-v1: system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 2 |
| crypto/internal/fips140/sha512 | 0/1 | 0/1 | 0/1 | arm64: crypto extension (AES/SHA/PMULL/SHA3) 1; amd64-v1: AVX2 (256-bit VEX) 1, BMI1/BMI2/LZCNT 1 |
| internal/runtime/sys | 0/3 | – | – | arm64: system / barrier / hint 3 |
| internal/runtime/syscall/linux | 0/1 | 0/1 | 0/1 | arm64: system / barrier / hint 1; amd64-v1: system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 1 |
| crypto/internal/boring/sig | 1/1 | 0/1 | 0/1 | amd64-v1: AVX/AVX2 other (VEX) 1, integer/base 1, system (SYSCALL/CPUID/XGETBV/fences/MXCSR) 1 |
| internal/bytealg | 11/11 | 15/15 (14 before WP-D) | 15/15 | amd64-v1: SSE4.2 1 |
| internal/chacha8rand | 1/1 | 1/1 (0 before WP-D) | 1/1 | amd64-v1: SSE/SSE2 1 |
| math | 4/4 | 7/8 | 4/5 | amd64-v1: AVX (128-bit VEX) 1, FMA 1 |
| math/big | 6/6 | 5/6 | 5/6 | amd64-v1: ADX 1, BMI1/BMI2/LZCNT 1 |
| crypto/internal/fips140/sha3 | 0/1 | 1/1 | 1/1 | arm64: crypto extension (AES/SHA/PMULL/SHA3) 1 |
| vendor/golang.org/x/crypto/chacha20 | 0/1 | – | – | arm64: ASIMD (NEON vector) 1 |
| crypto/internal/fips140/check/checktest | 3/3 | 3/3 | 3/3 |  |
| crypto/internal/fips140/edwards25519/field | – | 2/2 | 2/2 |  |
| crypto/internal/fips140/subtle | 1/1 | 1/1 | 1/1 |  |
| crypto/md5 | 1/1 | 1/1 | 1/1 |  |
| internal/abi | 1/1 | 1/1 | 1/1 |  |
| internal/runtime/startlinetest | – | 1/1 | 1/1 |  |
| reflect | 2/2 | 2/2 | 2/2 |  |
| runtime/cgo | 2/2 | 2/2 | 2/2 |  |
| vendor/golang.org/x/crypto/internal/poly1305 | – | 1/1 | 1/1 |  |

Every rejected class in assembly, per configuration:

<details><summary>arm64: all 31 rejected classes in assembly functions (functions blocked / sole blocker)</summary>

`SVC` 33/33, `BRK` 14/14, `MRS` 5/3, `PMULL (vector)` 5/0, `PMULL2 (vector)` 5/0, `MSR` 2/1, `udf #0` 2/2, `(SHA512/SHA3/SM3/SM4, unknown to arm64asm)` 2/2, `(system register / PSTATE, unknown to arm64asm)` 1/0, `STLXR` 1/1, `CRC32CB` 1/0, `CRC32CH` 1/0, `CRC32CW` 1/0, `CRC32CX` 1/0, `CRC32B` 1/0, `CRC32H` 1/0, `CRC32W` 1/0, `CRC32X` 1/0, `SHA256H (vector)` 1/0, `SHA256H2 (vector)` 1/0, `SHA256SU0 (vector)` 1/0, `SHA256SU1 (vector)` 1/0, `MOV (vector)` 1/0, `SHA1C (vector)` 1/0, `SHA1H` 1/0, `SHA1M (vector)` 1/0, `SHA1P (vector)` 1/0, `SHA1SU0 (vector)` 1/0, `SHA1SU1 (vector)` 1/0, `ZIP1 (vector)` 1/0, `ZIP2 (vector)` 1/0

</details>

<details><summary>amd64-v1: all 94 rejected classes in assembly functions (functions blocked / sole blocker)</summary>

`syscall` 36/34, `vmovdqu64/evex` 31/2, `vgf2p8affineqb/evex` 25/0, `vpermb/evex` 25/0, `vpermi2b/evex` 19/0, `kmovq/vex128` 12/0, `pshufb` 12/0, `vporq/evex` 11/0, `aesenc` 11/0, `psrldq` 8/0, `aesenclast` 8/0, `paddd` 7/0, `pslldq` 7/0, `pinsrq` 6/0, `pclmulqdq` 6/0, `mulx/vex128` 6/0, `vpalignr/vex256` 5/0, `vpshufb/vex256` 5/0, `pslld` 4/0, `psrld` 4/0, `int` 4/2, `vpaddd/vex256` 4/0, `vpslld/vex256` 4/0, `vpsrld/vex256` 4/0, `shufps` 4/2, `adcx` 4/0, `adox` 4/0, `pcmpeqd` 4/0, `cpuid` 3/3, `pinsrd` 3/0, `rorx/vex128` 3/0, `vperm2i128/vex256` 3/0, `palignr` 3/0, `xgetbv` 2/2, `vpcompressq/evex` 2/0, `ud2` 2/2, `crc32` 2/2, `pextrd` 2/0, `vpsrlq/vex256` 2/0, `vbroadcasti128/vex256` 2/0, `pinsrb` 2/0, `pandn` 2/0, `psubd` 2/0, `pcmpestri` 1/1, `kmovw/vex128` 1/0, `vpcmpuq/evex` 1/0, `kmovb/vex128` 1/0, `vmovdqa64/evex` 1/0, `vpandq/evex` 1/0, `vpopcntb/evex` 1/0, `pinsrw` 1/0, `pshufhw` 1/0, `rdtsc` 1/0, `rdtscp` 1/0, `popfq` 1/0, `pushfq` 1/0, `vaddsd/vex128` 1/0, `vfmadd213sd/vex128` 1/0, `vfnmadd231sd/vex128` 1/0, `psrlq` 1/0, `vextractf32x4/evex` 1/0, `vmovaps/vex128` 1/0, `vpclmulqdq/evex` 1/0, `vpternlogd/evex` 1/0, `vpxorq/evex` 1/0, `vpshufb/vex128` 1/0, `vpshufd/vex256` 1/0, `pblendw` 1/0, `sha256msg1` 1/0, `sha256msg2` 1/0, `sha256rnds2` 1/0, `vpaddq/vex256` 1/0, `vpblendd/vex256` 1/0, `vperm2f128/vex256` 1/0, `vpsllq/vex256` 1/0, `aesdec` 1/0, `aesdeclast` 1/0, `aesimc` 1/0, `aeskeygenassist` 1/0, `paddq` 1/0, `(vex256 unknown to x86asm)` 1/0, `hlt` 1/0, `lret` 1/0, `mov` 1/0, `andn/vex128` 1/0, `vinserti128/vex256` 1/0, `vpslldq/vex256` 1/0, `vpsrldq/vex256` 1/0, `sha1msg1` 1/0, `sha1msg2` 1/0, `sha1nexte` 1/0, `sha1rnds4` 1/0, `psrad` 1/0, `pextrb` 1/0

</details>

<details><summary>amd64-v3: all 88 rejected classes in assembly functions (functions blocked / sole blocker; after WP-B, which removed `pshufb`, `mulx`, `rorx`, `andn`, `vfmadd213sd`, `vfnmadd231sd`)</summary>

`syscall` 36/34, `vmovdqu64/evex` 31/2, `vgf2p8affineqb/evex` 25/0, `vpermb/evex` 25/0, `vpermi2b/evex` 19/0, `kmovq/vex128` 12/0, `vporq/evex` 11/0, `aesenc` 11/0, `psrldq` 8/0, `aesenclast` 8/0, `paddd` 7/0, `pslldq` 7/0, `pinsrq` 6/0, `pclmulqdq` 6/0, `vpalignr/vex256` 5/0, `vpshufb/vex256` 5/0, `pslld` 4/0, `psrld` 4/0, `int` 4/2, `vpaddd/vex256` 4/0, `vpslld/vex256` 4/0, `vpsrld/vex256` 4/0, `shufps` 4/2, `adcx` 4/0, `adox` 4/0, `pcmpeqd` 4/0, `cpuid` 3/2, `xgetbv` 3/2, `pinsrd` 3/0, `vperm2i128/vex256` 3/0, `palignr` 3/0, `vpcompressq/evex` 2/0, `ud2` 2/2, `crc32` 2/2, `pextrd` 2/0, `vpsrlq/vex256` 2/0, `vbroadcasti128/vex256` 2/0, `pinsrb` 2/0, `pandn` 2/0, `psubd` 2/0, `pcmpestri` 1/1, `kmovw/vex128` 1/0, `vpcmpuq/evex` 1/0, `kmovb/vex128` 1/0, `vmovdqa64/evex` 1/0, `vpandq/evex` 1/0, `vpopcntb/evex` 1/0, `pinsrw` 1/0, `pshufhw` 1/0, `rdtsc` 1/0, `rdtscp` 1/0, `popfq` 1/0, `pushfq` 1/0, `vaddsd/vex128` 1/0, `psrlq` 1/0, `vextractf32x4/evex` 1/0, `vmovaps/vex128` 1/0, `vpclmulqdq/evex` 1/0, `vpternlogd/evex` 1/0, `vpxorq/evex` 1/0, `vpshufb/vex128` 1/0, `vpshufd/vex256` 1/0, `pblendw` 1/0, `sha256msg1` 1/0, `sha256msg2` 1/0, `sha256rnds2` 1/0, `vpaddq/vex256` 1/0, `vpblendd/vex256` 1/0, `vperm2f128/vex256` 1/0, `vpsllq/vex256` 1/0, `aesdec` 1/0, `aesdeclast` 1/0, `aesimc` 1/0, `aeskeygenassist` 1/0, `paddq` 1/0, `(vex256 unknown to x86asm)` 1/0, `hlt` 1/0, `lret` 1/0, `mov` 1/0, `vinserti128/vex256` 1/0, `vpslldq/vex256` 1/0, `vpsrldq/vex256` 1/0, `sha1msg1` 1/0, `sha1msg2` 1/0, `sha1nexte` 1/0, `sha1rnds4` 1/0, `psrad` 1/0, `pextrb` 1/0

</details>

"System" instructions are not SIMD, but they are the largest block, so here is what each one needs.
`SVC #0` and `SYSCALL` need a kernel-call contract. `BRK`, `INT 3`, `UD2`, `HLT` and an
in-function `UDF` are traps, which the model should take as faults (the code after them is
unreachable). `CPUID`, `XGETBV`, `RDTSC(P)`, `MRS MIDR_EL1` and the DIT `MRS`/`MSR` need an
environment-value contract or a modelled register. All are in [WP-C](#6-work-plan).
`crypto/internal/boring/sig.StandardCrypto` is a marker made of data bytes and is never executed.

### 1.4 What earlier measurements said, and what changed

[ORACLE-AMD64.md](ORACLE-AMD64.md) measured `bytes`, `strings`, `sync/atomic`, `math`, `strconv`
and `sort` at 97.9–100% (amd64 v1, per binary, runtime included). This page covers all of std,
deduplicated by function, and also measures arm64 and amd64 v3. The amd64 v1 result (100% of
Go-compiled std) confirms that the floating-point, `FS`, string, atomic and SSE-move rounds
closed every gap in compiler output. The arm64 store-exclusive gap is deliberate: the decoder
rejects it ([SOUNDNESS.md](SOUNDNESS.md)), and the atomics proofs state `arm64HasATOMICS` so that
the LL/SC fallback is unreachable ([PROOFS.md](PROOFS.md), "LSE vs LL/SC"). This page measures
for the first time how far that reaches: 1,845 functions, every one of them blocked by nothing
else. Programs built with `GOARM64=v8.1` or later have no fallback; the default `v8.0` does.

## 2. Runtime entry points

The list holds every runtime function or variable the compiler can reference, 309 names:

* the declarations of `cmd/compile/internal/typecheck/_builtin/runtime.go`;
* every `LookupRuntime*("…")` in `ssagen`, `walk`, `reflectdata`, `compare`, `noder`, `typecheck`,
  `ssa`, `staticinit`, `escape`, `inline` and `pkginit`;
* names chosen in `walk`/`ssagen`/`compare` and passed to `LookupRuntime*`, when the runtime
  links them (`fmin64`, `strmax`, `memequal8`, ...);
* the `fmt.Sprintf` families (`mallocgcSmallNoScanSC%d`, ...);
* the `runtime.*` symbols the assembler back ends emit (`morestack`, `morestack_noctxt`,
  `morestackc`, `duffzero`, `duffcopy`, `tls_g`, `retpoline`);
* the `runtime.cgo*` / `_cgo_runtime_*` calls in `cmd/cgo`.

Each name is checked against the symbol tables of all std test binaries ("linked"), against the
runtime source for linux/arm64 and linux/amd64 (`go/build` constraints; "defined"), and against
what each branch has:

* a Lean contract mentioning it (`Janus/Contracts/*.lean`, `Janus/FFI.lean`,
  `Janus/Amd64/FFI.lean`);
* a stub in `cmd/janus/extract.go` (`.panic`, `.morestack`);
* a `--contract` in `scripts/example-contracts.sh`;
* real code executed by a proved example.

Full table: `artifacts/coverage/runtime.tsv`.

| category | names | linked by std (arm64/amd64) | contract/stub/proof on main | on main or a branch |
|---|---:|---:|---:|---:|
| alloc | 5 | 2 | 0 | 2 |
| slice/growslice | 16 | 10 | 0 | 2 |
| map | 26 | 24 | 0 | 9 |
| string | 22 | 20 | 0 | 0 |
| interface/type assertion | 13 | 12 | 0 | 13 |
| memory/equality | 23 | 20 | 3 | 3 |
| hashing/rand | 17 | 16 | 0 | 0 |
| write barrier | 11 | 11 | 0 | 1 |
| panic/recover/defer | 43 | 21 | 34 | 41 |
| stack growth | 3 | 3 | 2 | 2 |
| conversion/soft arithmetic | 43 | 6 | 0 | 0 |
| print (`println` builtin) | 19 | 18 | 0 | 0 |
| cgo | 9 | 3 | 0 | 1 |
| CPU feature flags (variables) | 10 | 5 | 0 | 0 |
| misc | 11 | 8 | 0 | 4 |
| instrumentation (msan/asan/fuzz/cover) | 17 | 0 | 0 | 0 |
| concurrency (excluded) | 21 | 12 | 0 | 0 |
| **total** | **309** | **191** | **39** | **78** |

**What exists today** (main unless noted):

* **stubs** `.panic`: `panicBounds`, `panicdivide`, `panicshift`, `panicwrap`, `panicdottypeE/I`,
  `panicnildottype`, `panicmakeslicelen/cap`, `panicoverflow`, `panicrangestate`,
  `panicunsafe*`, `panicSimdImm`, `gopanic` and the wasm-only `goPanic*`;
* **stubs** `.morestack`: `morestack`, `morestack_noctxt`;
* **executed in proofs**: `memmove` (CopyBlock, CopyBlock512), `memclrNoHeapPointers`
  (ClearWords), `memequal` (A64Equal64/Equal64); `gcWriteBarrier2` fast path (agent/alloc,
  SetNext, with a `wbBufFlush` contract);
* **contracts**:
  * agent/alloc (also carried by maps, ffi and iface-alloc): `mallocgc` (with the MallocFast proof
    of the real fast path on arm64), `newobject`, `makeslice`, `growslice`, `zerobase`;
  * agent/maps: `makemap_small`, `mapaccess1_fast64` (with the MapAccess1Small proof of the real
    code), `mapaccess2_fast64`, `mapaccess2`, `mapassign_fast64`, `mapdelete_fast64`, `mapclear`,
    `mapIterStart`, `mapIterNext`;
  * agent/ffi: `cgocall`, `tls_g`/`_cgo_topofstack` (`TopOfStack`);
  * agent/rtiface: `convT`, `convTnoptr`, `convT16`, `convT32`, `convT64`, `convTstring`,
    `convTslice`, `assertE2I`, `assertE2I2`, `typeAssert`, `interfaceSwitch`, `efaceeq`,
    `ifaceeq` (each pinned to the runtime's code and proved satisfiable), and the content of
    `emptyTypeAssertCache` / `emptyInterfaceSwitchCache` (the cache model `TACacheOK.empty`,
    `ISCacheOK.empty`).

**Missing: no contract, stub or proof on any branch, and linked by std** (134; the 12
concurrency names are excluded, which leaves **122 in scope**):

* **CPU feature flags (variables)**: `arm64HasATOMICS` `x86HasAVX` `x86HasFMA` `x86HasPOPCNT` `x86HasSSE41`
* **cgo**: `cgoAlwaysFalse` `cgoCheckPointer`
* **concurrency (excluded)**: `block` `chancap` `chanlen` `chanrecv1` `chanrecv2` `chansend1` `closechan` `makechan` `newproc` `selectgo` `selectnbrecv` `selectnbsend`
* **conversion/soft arithmetic**: `complex128div` `f32to64` `f64to32` `fadd64` `fdiv64` `fmul64`
* **hashing/rand**: `c128hash` `c64hash` `f32hash` `f64hash` `interhash` `memhash` `memhash0` `memhash128` `memhash16` `memhash32` `memhash64` `memhash8` `memhash_varlen` `nilinterhash` `rand` `strhash`
* **map**: `makemap` `mapaccess1` `mapaccess1_fast32` `mapaccess1_faststr` `mapaccess1_fat` `mapaccess2_fast32` `mapaccess2_faststr` `mapaccess2_fat` `mapassign` `mapassign_fast32` `mapassign_fast64ptr` `mapassign_faststr` `mapdelete` `mapdelete_fast32` `mapdelete_faststr`
* **memory/equality**: `c128equal` `c64equal` `f32equal` `f64equal` `interequal` `memclrHasPointers` `memequal0` `memequal128` `memequal16` `memequal32` `memequal64` `memequal8` `memequal_varlen` `nilinterequal` `strequal` `typedmemclr` `typedmemmove`
* **misc**: `KeepAlive` `gostring` `staticuint64s` `zeroVal`
* **print (println builtin)**: `printbool` `printcomplex128` `printcomplex64` `printeface` `printfloat32` `printfloat64` `printhex` `printint` `printlock` `printnl` `printpointer` `printquoted` `printslice` `printsp` `printstring` `printuint` `printuintptr` `printunlock`
* **slice/growslice**: `growsliceBuf` `makeslicecopy` `moveSlice` `moveSliceNoCap` `moveSliceNoCapNoScan` `moveSliceNoScan` `slicecopy` `typedslicecopy`
* **stack growth**: `morestackc`
* **string**: `cmpstring` `concatbyte2` `concatbyte3` `concatbyte4` `concatbyte5` `concatbytes` `concatstring2` `concatstring3` `concatstring4` `concatstring5` `concatstrings` `countrunes` `decoderune` `intstring` `slicebytetostring` `slicerunetostring` `stringtoslicebyte` `stringtoslicerune` `strmax` `strmin`
* **write barrier**: `gcWriteBarrier1` `gcWriteBarrier3` `gcWriteBarrier4` `gcWriteBarrier5` `gcWriteBarrier6` `gcWriteBarrier7` `gcWriteBarrier8` `wbMove` `wbZero` `writeBarrier`

**Missing, defined by the linux/arm64 or amd64 runtime but not linked by std** (54; 3 of them
concurrency). Std never uses these, but other programs reach them: constructs std avoids, such as
`defer` inside a range-over-func body (`deferprocat`, `deferrangefunc`), `println` of a non-empty
interface (`printiface`) or `assertE2I`; the cgo checks generated in user packages (`cgoUse`,
`cgoCheck*`, `cgoKeepAlive`, `cgoNoCallback`, `gobytes`, `gostringn`); `-d=checkptr`
(`checkptr*`, `unsafe*checkptr`); `-msan`, `-asan` and `-cover` (`msan*`, `asan*`, `addCovMeta`);
`GOEXPERIMENT`s (`growslice*NoAlias`); and the soft-float helpers of `-gcflags=-d=softfloat`:

* **cgo**: `cgoCheckMemmove` `cgoCheckPtrWrite` `cgoCheckResult` `cgoKeepAlive` `cgoNoCallback` `cgoUse`
* **concurrency (excluded)**: `goschedguarded` `makechan64` `selectsetpc`
* **conversion/soft arithmetic**: `f32toint32` `f32toint64` `f32touint64` `f64toint32` `f64toint64` `f64touint64` `fadd32` `fdiv32` `feq32` `feq64` `fge32` `fge64` `fgt32` `fgt64` `fint32to32` `fint32to64` `fint64to32` `fint64to64` `fmul32` `fuint64to32` `fuint64to64`
* **hashing/rand**: `rand32`
* **instrumentation (msan/asan/fuzz/cover)**: `addCovMeta` `asanread` `asanregisterglobals` `asanwrite` `msanmove` `msanread` `msanwrite`
* **map**: `makemap64` `mapassign_fast32ptr`
* **memory/equality**: `duffcopy` `duffzero`
* **misc**: `gobytes` `gostringn`
* **panic/recover/defer**: `panicExtend`
* **print (println builtin)**: `printiface`
* **slice/growslice**: `checkptrAlignment` `checkptrArithmetic` `growsliceBufNoAlias` `growsliceNoAlias` `makeslice64` `unsafeslicecheckptr`
* **string**: `slicebytetostringtmp` `unsafestringcheckptr`

**Emitted for arm64/amd64 only under a build mode, with no definition in the default runtime:**
`libfuzzer*` (`-gcflags=-d=libfuzzer`, build tag `libfuzzer`), `retpoline*` (`-spectre=ret`), the
size-specialised `mallocgc*SC<n>` families (`GOEXPERIMENT`), and `race*` (the race detector,
which is concurrency tooling and excluded). **Not applicable** (other GOARCHes only): `int64div`,
`int64mod`, `uint64div`, `uint64mod`, `udiv`, `float64to*`, `int64tofloat*`, `uint32tofloat64`,
`uint64tofloat*`, `wasm*`, `armHasVFPv4`, `loong64Has*`, `riscv64HasZbb`, `duff`, `throwinit`, the
wasm-only `goPanic*`, `panicExtend`, `makeslice64`, `makemap64`, `mapassign_fast32ptr` and `rand32`
(32-bit; these five are in the list above only because the runtime defines them on every
GOARCH). In Go 1.26, `duffzero`/`duffcopy` are declared but not generated for arm64/amd64: large
zeroing and copying is inline or `memmove`/`memclrNoHeapPointers`.

## 3. Language constructs

For each construct of the Go spec: the proved example that exercises it in compiled code, per
architecture and branch, and what it rests on. A construct counts as covered only when a proof
(no `sorry`) about a function whose compiled code path uses it exists. Lists read from
`scripts/verify-examples.sh`, `examples/proofs*/`, `scripts/example-contracts.sh` and
`scripts/verify-cgo-examples.sh` on each branch (`git show`). main has 28 arm64 proofs (plus the
`WrongAdd` counterexample) and 31 amd64 proofs; agent/alloc adds 5+4, agent/maps 10+10,
agent/ffi 5+5 (cgo), agent/iface-alloc none (mechanism and allocation contracts only),
agent/rtiface 4+4 (interfaces: `Box`, `AsHasher`, `Classify`, `Equal`).
agent/constructs (package M1, `examples/basic/zconstructs.go`) adds 29 arm64 + 26 amd64:
`Triangle`, `GotoSum`, `Find2D`, `RowsWith`, `Log2`, `TotalMeters`, `TotalFeet`, `Fact`,
`SumBelow`, `IterSum`, `ReverseArray`, `DivMod10`, `SwapBig`, `Compose`, `DotBoth`, `BitMerge`,
`Shifts`, `MinMax`, `ClearArray`, `Sum3`, `AlignUp`, `Slice3`, `Slice2`, `Mod`, `IncTwice`,
`MakeAdder` on both
ISAs, and the arm64 proofs of the existing `Bump`, `GlobalTable`, `Table`.

| construct | arm64 proof (branch) | amd64 proof (branch) | depends on |
|---|---|---|---|
| assignment, short var decl | `Sum`, `CopyWords`, `AddLimbs`, `Add128` (main) | same (main) | – |
| `+`, wrap-around | `Add`, `Sum`, `AddThree` (main) | same | – |
| `-` | `DivMod10`, `MinMax`, `Slice3`, `AlignUp` (constructs); `WrongAdd` is a counterexample only | same (constructs) | – |
| `*` | `SumSquares`, `HashTwice`, `HashWith` (main) | same | – |
| `/` and the divide check | `Div` (main), incl. "panics iff y = 0" | `Div` (main) | `runtime.panicdivide` stub |
| `%` | by a constant: `DivMod10` (constructs; magic multiply, `x - 10q`); by a variable: `Mod` (constructs, incl. "panics iff y = 0") | same (constructs) | `runtime.panicdivide` stub |
| shifts `<<` `>>` by a variable | `Shifts` (constructs: signed and unsigned, every count incl. `≥ 64`) | same (constructs) | – |
| `&`, `&^` | `HexDigit`, `Abs` (main); `BitMerge`, `AlignUp` (constructs) | same + `Table`, `GlobalTable` | – |
| `\|`, `^` | `BitMerge` (constructs) | same (constructs) | – |
| comparisons | `Max`, `CopyWords`, `AtomicMax` (main) | same | – |
| if / else, `&&` `\|\|` | `Max`, `CopyWords`, `AtomicMax` (main); `GoSum` (ffi) | same | – |
| for (3-clause) | `AddLimbs`, `CopyWords` (main) | same | – |
| for cond / for + break | `Log2` (for cond), `Find2D` (break) (constructs) | same (constructs) | – |
| infinite for exiting by return | `AtomicMax` (main) | same | – |
| labeled break / continue, goto | `Find2D` (labeled break), `RowsWith` (labeled continue), `GotoSum` (goto) (constructs) | same (constructs) | – |
| expression switch, fallthrough | `Triangle` (constructs: 9 dense cases, a `.rodata` jump table, a `fallthrough` chain) | same (constructs) | jump tables need no runtime; decoder has `BR`/`JMP r` |
| type switch | `Classify` (rtiface: `nil`, `uint64`, `string`, `Hasher`, default) | same | `interfaceSwitch` contract; hash/type compares and the switch-cache probe executed |
| range over array | `ReverseArray` (constructs) | same (constructs) | – |
| range over slice | `Sum`, `MapSum` (main) | same | – |
| range over string | none | none | `runtime.decoderune` |
| range over map | `SumValues` (maps) | `SumValues` (maps) | `mapIterStart`/`mapIterNext` contracts |
| range over int | `SumBelow` (constructs) | same (constructs) | – |
| range over func (iterators) | inlined iterator: `IterSum` (constructs; no runtime call left); non-inlined: none | same (constructs) | inlined: none; otherwise closures, `runtime.panicrangestate`, `deferrangefunc` |
| static call, multiple results | `AddThree`, `SumSquares`, `Add128`, `Mul64` (main); `Lookup` (maps); named results: `DivMod10`, `MinMax` (constructs) | same | callee `Summary` |
| variadic call | `Sum3` (constructs; the argument slice in the caller's frame) | same (constructs) | slice construction (stack or `newobject`) |
| method call, value receiver; static pointer-receiver call | value receiver: `DotBoth` (constructs; `Vec2.Dot-fm` calls `Vec2.Dot`); pointer receiver: `IncTwice` (constructs) | same (constructs) | – |
| interface method call | `HashWith`, `HashTwice` (main) | same | `ItabIs` hypothesis, `--targets` |
| method value | `HashTwice` (main); value receiver: `DotBoth` (constructs) | same | dynamic-call section of RUNTIME-CONTRACTS |
| method expression | `DotBoth` (constructs; the static funcval `Vec2.Dot·f`) | same (constructs) | – |
| closure call (captured vars) | `MapSum` (`AffineSum.func1`), `DeferAdd` (main) | same | `FuncvalIs`, `ClosureCtx` |
| closure creation, escaping closure | non-escaping: `Compose` (constructs; funcval in the frame); escaping: `MakeAdder` (constructs; funcval from the `newobject` contract) | same (constructs) | `newobject` (escaping) |
| defer, open-coded | `DeferAdd` (main); `DeferInc` (panic) | same | `deferreturn` contract (agent/panic; the call after a recover) |
| defer in a loop / heap defer | `DeferTwice` (panic; both ISAs), `DeferMix` (heap records and open-coded defers on one frame; arm64) | same | `deferproc`, `deferprocStack`, `deferprocat`, `deferrangefunc` contracts and the `deferreturn` engine (agent/panic2) |
| runtime panics (bounds, divide) | `Get`, `Div` (main); `Slice2`, `Slice3`, `Mod` (constructs); `IndexAt` (panic: `.panicked` with a `boundsError`) | same | `panicBounds`, `panicdivide` stubs, classified as `runtime.Error` kinds (agent/panic) |
| explicit `panic`, `recover`, unwinding | `PanicIf` (`.panicked v`), `RecoverSet` (recover in a deferred closure, named result set), `DeferOrder` (several open-coded defers run last to first during a panic; arm64), `NestedPanic` (a deferred call panics again; arm64), `NestedRecover` (the second panic is recovered by a later deferred call; arm64) | same | the `gopanic` engine (all pending deferred calls of the frame, nested panics, recovery, unwinding past the frame), `gorecover` (agent/panic2) |
| `runtime.Goexit` | `GoexitDefer` (the deferred calls run, `recover()` finds no panic, the goroutine exits; arm64) | same | the `Goexit` engine contract (agent/panic2) |
| defer in a range-over-func body | `RangeDefer` (`deferrangefunc`, `deferprocat`, `deferreturn`; arm64) | same | `deferrangefunc`, `deferprocat` contracts and the `deferreturn` engine (agent/panic2) |
| generics (shape + dictionary) | `TotalMeters`, `TotalFeet` (constructs: one `go.shape.uint64` body, two dictionaries, method call through the dictionary) | same (constructs) | dictionary loads (`.rodata`), no runtime |
| large struct copy | `SwapBig` (constructs: 64 bytes, inline `LDP`/`STP`) | `SwapBig` (constructs: inline `MOVUPS`) | `runtime.duffcopy` is gone in 1.26; inline `LDP/STP` / `MOVUPS` loops, `memmove`, `typedmemmove` |
| array copy | `SetOne256`, `CopyBlock` (main); value semantics: `ReverseArray` (constructs) | same + `CopyBlock512` | `memmove` executed |
| pointer deref | `Add256`, `AddLimbs`, `AtomicAdd` (main) | same | – |
| nil dereference fault | `LoadField` (panic: a fault below `0x1000` is a panic with `runtime.Error` kind `mem`) | same | fault classification in `goClass`, `sigpanic` contract (agent/panic) |
| slice `a[:]` of an array | `CopyBlock`, `A64Equal64` (main) | `CopyBlock`, `Equal64` | – |
| slice `a[i:j]`, `a[i:j:k]` | `Slice2`, `Slice3` (constructs, incl. "panics iff not `0 ≤ i ≤ j (≤ k) ≤ cap`") | same (constructs) | `panicSlice*` (`panicBounds`) |
| indexing + bounds check | `Get`, `CopyWords`, `HexDigit` (main) | same | `panicBounds` stub |
| `append` | `AppendOne` (alloc) | `AppendOne` (alloc) | `growslice` contract |
| `copy` | `CopyBlock` (main) | `CopyBlock`, `CopyBlock512` | `memmove` executed |
| `len`, `cap` | `CopyWords` (main); `CountKeys` (maps); `AppendOne` (alloc) | same | – |
| `make([]T)`, `new`, `&T{}` | `MakeSlice`, `NewPair` (alloc) | same | `makeslice`, `newobject` contracts |
| `make(map)` | `NewMap` (maps) | same | `makemap_small` contract |
| map read / write / delete / clear | `Lookup`, `LookupKey16`, `Insert`, `InsertGet`, `Delete`, `ClearMap` (maps) | same | `mapaccess*`, `mapassign_fast64`, `mapdelete_fast64`, `mapclear` contracts |
| the map runtime itself | `MapAccess1Small` (maps, real `mapaccess1_fast64` vs its contract) | same | `Janus/Spec/SwissMap.lean` |
| string indexing | `HexDigit` (main) | same | `Program.data` |
| string concatenation | none | none | `concatstring2..5`, `concatstrings` |
| string comparison | none (`A64Equal64`/`Equal64` are `bytes.Equal`) | none | `memequal` (executed), `cmpstring` |
| string ↔ `[]byte`, `[]rune`; `string(rune)` | none | none | `slicebytetostring`, `stringtoslicebyte`, `slicerunetostring`, `intstring`, ... |
| int ↔ float, float32 ↔ float64 | none | none | FP decoder (done on main) |
| float → uint64 | `F64ToU64` (main) | same | FP decoder |
| float bits, float arithmetic | `Abs`, `AddF64`, `Dot3` (main) | same | FP decoder |
| complex numbers | none | none | FP; `complex128div` |
| `unsafe.Pointer` | `GoSum` (ffi) | same | – |
| `uintptr` arithmetic | `AlignUp` (constructs) | same (constructs) | – |
| interface boxing (`convT*`) | `Box` (rtiface) | same | `convT64` contract (`convT`, `convT16/32`, `convTstring`, `convTslice`, `convTnoptr` contracts too) |
| type assertion (both forms) | `AsHasher` (rtiface, comma-ok to an interface) | same | `typeAssert` contract, assertion-cache probe executed; `assertE2I(2)` contracts; the panicking form ends in the `panicnildottype` stub or excluded `typeAssert` panic |
| interface comparison | `Equal` (rtiface, `any`) | same | `efaceeq` contract (`ifaceeq` too); type `Equal` functions abstract (`R.eq`, byte equality for `TFlagRegularMemory`) |
| `min`, `max` builtins | integers: `MinMax` (constructs); floats, strings: none | same (constructs) | inline (`CSEL`/`CMOV`); `fmin`/`fmax`, `strmin`/`strmax` |
| `clear` | `ClearWords` (main), `ClearMap` (maps); small array, inline stores: `ClearArray` (constructs) | same | `memclrNoHeapPointers` executed; `mapclear` |
| `math/bits` | `Add128`, `Add256`, `AddLimbs`, `Mul64`, `RotHasher` (main) | same | – |
| sync/atomic (single-threaded) | `AtomicAdd`, `AtomicMax` (main) | same | arm64 LL/SC fallback needs `STXR` (rejected, below) |
| package variables | `Bump`, `GlobalTable` (constructs) | `Bump`, `GlobalTable` (main) | data objects |
| constants in `.rodata` | `HexDigit`, `SetOne256` (main); `Table`, `Triangle` (jump table), `TotalMeters` (dictionary) (constructs) | same + `Table` | `Program.data` |
| escape to heap | `NewPair` (alloc); `MallocFast` proves the real `mallocgc` fast path (alloc, arm64) | `NewPair` (alloc) | `Janus/Contracts/Alloc.lean` |
| pointer store (write barrier) | `SetNext` (alloc) | same | barrier fast path executed, `wbBufFlush` contract |
| stack growth | none (every proof assumes `GuardOK`) | none | `morestack` stub; no theorem about the grown case |
| recursion | `Fact` (constructs; `Summary.induction`, stack for every frame assumed) | same (constructs) | `Summary` induction (done); the grown stack: `morestack` (R7) |
| cgo call into C | `GoAdd`, `GoSum`, `GoCount` (ffi) | same | `CgoCall` contract |
| C code alone | `CAdd`, `CSum`, `CStore`, `CCount` (NEON, arm64) (ffi) | same | `CEnsures` |
| `//export` callback C → Go | none | none | `crosscall2`, `cgocallback` |
| goroutines, channels, select, `sync` | excluded (concurrency) | excluded | – |

Not covered on any branch or architecture (with agent/constructs and agent/rtiface): range over
string; string concatenation,
comparison and conversions; int/float and float32/float64 conversions; complex numbers;
the grown-stack case; `//export` callbacks. Within
covered rows these forms still have no example: a non-inlined range-over-func loop, float and
string `min`/`max`. amd64 lacks `IndexByte` (the arm64 example is in an
arm64-only file) and `MallocFast`.

Two rows are uncertain: whether `CopyWords` and `HexDigit` keep a bounds check in compiled code
(`Get` certainly does).

Most of these need no new decoder feature: the instructions are already accepted (criterion 1),
so the gap is examples, proofs and (for the runtime-backed ones) the contracts of criterion 2.

## 4. Library assembly and SIMD: what Go-compiled std code calls

Counted as the direct calls and tail branches (`BL`/`B`; `CALL`/`JMP rel32`) from Go-compiled std
functions to assembly functions. Go code calls ABI0 assembly directly; a call through an
`<autogenerated>` ABI wrapper is counted for the assembly function behind it. "Go callers" is the
number of distinct Go-compiled functions. Full tables: `artifacts/coverage/asmcalls-<cfg>.txt`
(130 assembly callees on arm64, 145 on amd64 v1).

| assembly function | Go callers arm64 / amd64 | decodes arm64 | amd64 v1 | amd64 v3 | what blocks it |
|---|---:|:-:|:-:|:-:|---|
| `runtime.morestack_noctxt` | 12,190 / 11,872 | yes | yes | yes | (stub `.morestack`) |
| `runtime.panicBounds` | 3,566 / 3,598 | yes | yes | yes | (stub `.panic`) |
| `runtime.gcWriteBarrier2` | 3,239 / 3,241 | yes | yes | yes | |
| `runtime.morestack` | 2,490 / 2,467 | yes | yes | yes | (stub) |
| `runtime.gcWriteBarrier1` | 1,833 / 1,834 | yes | yes | yes | |
| `runtime.memmove` | 916 / 946 | yes | yes | yes | (AVX path decodes, `CopyBlock512`) |
| `runtime.gcWriteBarrier4` | 560 / 559 | yes | yes | yes | |
| `runtime.memequal` | 560 / 532 | yes | yes | yes | |
| `runtime.gcWriteBarrier3` | 435 / 435 | yes | yes | yes | |
| `runtime.memclrNoHeapPointers` | 157 / 158 | yes | yes | yes | |
| `runtime.systemstack` | 93 / 93 | yes | no | no | amd64: `INT $3` after the bad-switch abort |
| `runtime.gcWriteBarrier5..8` | 71+62+38+13 / 71+63+38+14 | yes | yes | yes | |
| `runtime.cmpstring` | 69 / 69 | yes | yes | yes | |
| `runtime.nanotime1` | 69 / 56 | no | no | no | `SVC` / `SYSCALL` (vDSO fallback) |
| `internal/bytealg.IndexByteString` | 56 / 57 | yes | yes | yes | |
| `internal/bytealg.IndexByte` | 35 / 35 | yes | yes | yes | |
| `runtime.mcall` | 22 / 22 | yes | yes | yes | |
| `math.archExp` | 17 / 17 | yes | no | no | amd64: `VFMADD213SD`, `VFNMADD231SD`, `VADDSD` (FMA path) |
| `math.archLog` | – / 18 | – | yes | yes | |
| `crypto/internal/fips140/edwards25519/field.feMul`, `feSquare` | – / 17, 8 | – | yes | yes | |
| `internal/runtime/syscall/linux.Syscall6`, `syscall.rawSyscallNoError` | 16, 16 / 16, 16 | no | no | no | `SVC` / `SYSCALL` |
| `runtime.memhash` | 15 / 15 | yes | yes | yes | (jumps to `aeshashbody` on amd64: AES-NI, `PSHUFB`) |
| `runtime.osyield`, `exit`, `rtsigprocmask`, `usleep`, `open`, `read`, `madvise`, `sigaltstack` | 4–14 each | no | no | no | `SVC` / `SYSCALL` |
| `runtime.asmcgocall` | 11 / 11 | yes | yes | yes | (agent/ffi: `cgocall` contract) |
| `runtime.cputicks` | – / 15 | – | no | no | `RDTSC`, `RDTSCP` |
| `runtime.procyieldAsm` | 7 / 5 | no | yes | yes | arm64: `MRS CNTFRQ_EL0` |
| `internal/chacha8rand.block` | 6 / 6 | yes | yes | yes | (amd64 SSE2 `PADDD`, `PSLLD`, `PSRLD`: WP-D) |
| `crypto/internal/fips140/nistec.p256Mul`, `p256Sqr`, `p256FromMont`, `p256PointDoubleAsm`, `p256OrdMul` | 1–6 | yes | yes | yes | |
| `crypto/internal/fips140/nistec.p256MovCond`, `p256Select`, `p256SelectAffine`, `p256PointAddAffineAsm` | 1–4 | yes | yes | yes | (amd64 SSE2 `PCMPEQD`, `PANDN`, `PADDD`, `PSUBD`: WP-D) |
| `internal/bytealg.Compare`, `Count`, `CountString`, `Index`, `IndexString` | 2–5 | yes | yes | yes | |
| `math/big.addVV`, `subVV`, `lshVU`, `rshVU`, `mulAddVWW` | 3–4 | yes | yes | yes | |
| `math/big.addMulVVWW`, `bigmod.addMulVVW1024/1536/2048` | 3, 2 | yes | no | no | amd64: ADX `ADCX`/`ADOX`, BMI2 `MULX` |
| `runtime.memhash32`, `memhash64` | 2 / 2 | yes | no | no | amd64: AES-NI `AESENC`, SSE4.1 `PINSRD`/`PINSRQ` |
| `hash/crc32.ieeeUpdate`, `castagnoliUpdate` (arm64); `castagnoliSSE42`, `ieeeCLMUL` (amd64) | 1–2 | no | `castagnoliSSE42*` yes (WP-D); `ieeeCLMUL` no | same | arm64: `CRC32*`; amd64 `ieeeCLMUL`: `PCLMULQDQ`, AVX-512 `VPCLMULQDQ`/`VPTERNLOGD` |
| `crypto/internal/fips140/aes.encryptBlockAsm`, `decryptBlockAsm`, `expandKeyAsm`, `ctrBlocks{1,2,4,8}Asm` | 1 | yes | no | no | amd64: AES-NI (`AESENC`, `AESENCLAST`, `AESDEC*`, `AESIMC`, `AESKEYGENASSIST`), SSSE3 `PSHUFB`, SSE4.1 `PINSRQ` |
| `crypto/internal/fips140/aes/gcm.gcmAes{Init,Enc,Dec,Data,Finish}` | 1–2 | no | no | no | arm64: `PMULL`/`PMULL2`; amd64: `PCLMULQDQ`, AES-NI, `PSHUFB`, `PSLLDQ`/`PSRLDQ` |
| `crypto/internal/fips140/sha256.blockSHA2` (arm64), `blockSHANI`, `blockAVX2` (amd64) | 1 | no | no | no | arm64: `SHA256H/H2/SU0/SU1`; amd64: SHA-NI; AVX2 + `RORX` |
| `crypto/internal/fips140/sha512.blockSHA512` (arm64), `blockAVX2` (amd64) | 1 | no | no | no | arm64: SHA512 (`CE6xxxxx`, unknown to arm64asm); amd64: AVX2 + `RORX` |
| `crypto/sha1.sha1block` (arm64), `blockSHANI`, `blockAVX2` (amd64) | 1 | no | no | no | arm64: `SHA1C/H/M/P/SU0/SU1`; amd64: SHA-NI; AVX2, `ANDN`, `RORX` |
| `crypto/internal/fips140/sha3.keccakF1600NEON` (arm64), `keccakF1600` (amd64) | 1 / 3 | no | yes | yes | arm64: SHA3 `EOR3`, `RAX1`, `XAR`, `BCAX` |
| `vendor/.../chacha20.xorKeyStreamVX` (arm64), `chacha20poly1305.chacha20Poly1305Open/Seal` (amd64) | 1 | no | no | no | arm64: `ZIP1`/`ZIP2`; amd64: AVX2, `MULX`, SSE2/SSSE3 |
| `crypto/md5.block`, `crypto/internal/fips140/subtle.xorBytes`, `poly1305.update` | 1–2 | yes | yes | yes | |

**SIMD status.** The arm64 decoder already covers the Advanced SIMD integer, move and AES
instructions that `memequal`, `IndexByte`, `Count`, `Compare`, `memhash`/`aeshash` and AES-CTR
use, so every hot arm64 callee decodes. The arm64 SIMD gaps are the crypto extensions (PMULL,
SHA1/SHA256/SHA512/SHA3), CRC32 and `ZIP1`/`ZIP2`. On amd64, `memmove`, `memclr`, `memequal`,
`IndexByte`, `Count`, `Compare` and `cmpstring` (including their AVX2 paths) decode. The gaps
needing SIMD encodings, by hot callee:

* AES-NI + `PSHUFB` + `PINSR*` for `aeshash`/`memhash32`/`memhash64`, which every map with
  non-fast keys and every `string` map hash reaches;
* (done in WP-D: SSE2 packed integer for `chacha8rand.block` (`runtime.rand`) and the
  constant-time P-256 selects, SSE4.2 for `indexbody` and `castagnoliSSE42*`);
* ADX/BMI2 for `math/big` and `bigmod`;
* FMA for `math.archExp`;
* the crypto kernels (AES-NI, PCLMULQDQ, SHA-NI, AVX2, AVX-512 `VPCLMULQDQ`);
* AVX-512 for the 29 `internal/runtime/gc/scan.expandAVX512_*` kernels of the GC. These are
  reached through the allocator's GC assist, not by a direct call.

## 5. cgo C code

### 5.1 Decoder coverage of compiled C

The corpus has 110 functions: 79 in `scripts/coverage/ccorpus/*.c` plus agent/ffi's
`examples/cgo/ccover.c` (28) and `cfuncs.c` (3), read with `git show`:

* `vec.c`: 21 loops that compilers auto-vectorise: sums, element-wise add/xor/mul/shift, saxpy,
  dot product, min/max reduction, byte count, widen/narrow, reverse, `tolower`, `int`→`double`,
  `strlen`, a 4×4 matrix multiply;
* `switch.c`: dense switches that become jump tables, sparse switches that become trees,
  case ranges, a lexer state machine, a computed-`goto` interpreter;
* `abi.c`: varargs (integer and `double`), small, large, mixed and HFA structs by value,
  10-argument stack passing, FP arguments, a callback through a function pointer, globals, a
  `static` counter, `.rodata` tables, an `extern` global, `__thread`, `setjmp`/`longjmp`,
  `alloca`, libc calls, `long double`, `double complex`, `__int128`, bitfields, recursion;
* `fp.c`: scalar FP: polynomials, conversions, comparisons, `sqrt`, `fma`, `floor`/`ceil`/`round`,
  `fabs`/`copysign`, `fmin`/`fmax`, libm calls;
* `misc.c`: CRC table, FNV, popcount/ctz, bit loops, a SHA-256 round, `strcmp`, `memset`/`memcpy`/
  `memcmp` builtins, struct copy, 128-bit multiply-high, division by constants, byte swaps, GCC
  atomics.

Each file is compiled the way cgo invokes the C compiler (`-fPIC -pthread -g`, plus the
`CGO_CFLAGS` level) into object files, and each function is decoded as in criterion 1.

| compiler | arm64 -O0 | arm64 -O2 | arm64 -O3 | amd64 -O0 | amd64 -O2 | amd64 -O3 | amd64 -O3 `-march=x86-64-v3` |
|---|---:|---:|---:|---:|---:|---:|---:|
| gcc 15.2 | 106/110 (96.4%) | 102/109 (93.6%) | 93/109 (85.3%) | 0/110 (0%) | 1/110 (0.9%) | 1/110 (0.9%) | 1/110 (0.9%) |
| gcc, once agent/ffi's `ENDBR64` is merged | | | | 108/110 (98.2%) | 92/110 (83.6%) | 85/110 (77.3%) | 58/110 (52.7%) |
| clang 21.1 | 106/110 (96.4%) | 94/109 (86.2%) | 94/109 (86.2%) | 105/110 (95.5%) | 85/109 (78.0%) | 85/109 (78.0%) | 55/109 (50.5%) |
| gcc, after WP-D (2026-10-25; `ENDBR64` merged) | | | | 108/110 (98.2%) | **106/110 (96.4%)** | **106/110 (96.4%)** | 65/110 (59.1%) |
| clang, after WP-D | | | | 108/110 (98.2%) | **107/109 (98.2%)** | **107/109 (98.2%)** | 64/109 (58.7%) |

After WP-D no amd64 C function at `-O0`/`-O2`/`-O3` has an SSE blocker: what is left is
`a_ldouble` (x87), `a_use_tls` (the padded `call __tls_get_addr`) and, for gcc, the two `NOTRACK`
jump tables (`s_dense`, `s_name`), all WP-J; under `-march=x86-64-v3` the VEX instructions of
WP-F.

**Blocking families, all configurations** (functions blocked, excluding `ENDBR64`):

* **amd64**:
  * *ENDBR64*: every gcc function (Ubuntu's `-fcf-protection` default); decoded on agent/ffi.
  * *SSE2 packed integer and FP* (modelled since WP-D): `PADDQ`, `PADDD`, `PSUBD`, `PSRLDQ`, `PSLLD`, `PSRLD`, `PSRAD`,
    `PCMPEQD`, `PCMPGTD`, `PANDN`, `PUNPCK*`, `PACKUSWB`, `PMULLW`, `PMULHUW`, `PMULUDQ`, `PMINUB`,
    `PMAXUB`, `PSUBUSB`, `SHUFPS`, `ADDPS`, `MULPS`, `MULPD`, `UNPCKHPD`, `CVTDQ2PD`, `MOVLHPS`,
    `MOVLPS`. They block 14–22 functions per config at -O2/-O3 (gcc and clang) and are the sole
    blocker of 22 clang -O2 functions.
  * *AVX/AVX2*: under `-march=x86-64-v3`, 36–40 functions have a VEX-128 blocker and 21–23 a
    VEX-256 one (`VPADD*`, `VEXTRACTI128`, `VPBROADCAST*`, `VPERMD`, `VPBLENDVB`, `VMOVUPS`, the
    `V*SD` scalar forms).
  * *BMI1/BMI2*: 9 functions (`SHLX`, `SHRX`, `SARX`, `RORX`, `ANDN`, `BLSI`, `BLSR`, `MULX`).
  * *FMA*: 6–7 functions.
  * *x87*: `a_ldouble` (`long double`: `FLD`, `FLDT`, `FLD1`, `FADDP`, `FMULP`).
  * *`NOTRACK JMP *%reg`* (`3E FF E0`): gcc's CET jump-table dispatch in `s_dense`, `s_name`.
  * *TLS general-dynamic call* (`66 66 48 E8`, the padded `call __tls_get_addr`): `a_use_tls`
    with `-fPIC`.
* **arm64**:
  * *ASIMD*: `ADDP` (22 function-configs), `UADDW`/`UADDW2`, `UMULL`/`UMULL2`, `MUL` (vector),
    `FMLA`, `FMUL`, `FNEG` (vector), `UZP1`, `ZIP1`, `LD4`/`ST4`, `SCVTF` (vector), `USHR`. They
    are the sole blocker of every arm64 failure at -O2/-O3.
  * *scalar FP conversions at -O0*: `SCVTF`, `UCVTF`, `FCVTZS`, `FCVTZU` in the forms that gcc and
    clang `-O0` emit.

The C code in the cgo binaries of criterion 1 (`runtime/cgo`'s `gcc_*.c`, gcc `-O2`) decodes
completely on arm64 (20 functions, including `paciasp`/`bti`) and is blocked only by `ENDBR64`
on amd64. On amd64 there is also one `PUNPCKLQDQ`.
### 5.3 Advanced SIMD in compiled C and Go assembly (package I, agent/neon)

Measured on agent/neon (main 987d96d plus `Janus/Arm64/NeonInstr.lean`, `DecodeNeon.lean`, `Neon.lean`, `NeonFP.lean`, `ExecNeon.lean`),
same toolchains. Rerun with `scripts/coverage.sh cc` (the official corpus) and
`oracle/harvest/neon/build.sh` plus `scripts/coverage/` `insn -c` (the supplementary corpus).

| corpus | arm64 config | before (main) | after (agent/neon) |
|---|---|---:|---:|
| official C corpus (5.1) | gcc -O0 / -O2 / -O3 | 106/110 / 102/109 / 93/109 | **110/110 / 109/109 / 109/109** |
| | clang -O0 / -O2 / -O3 | 106/110 / 94/109 / 94/109 | **110/110 / 109/109 / 109/109** |
| supplementary NEON corpus (`oracle/harvest/neon`, 476 functions) | gcc -O0 / -O2 / -O3 | 462/480 / 348/476 / 177/476 | **480/480 / 476/476 / 476/476** |
| | clang -O0 / -O2 / -O3 | 472/480 / 192/476 / 192/476 | **480/480 / 476/476 / 476/476** |
| Go assembly (1.3) | std, `go test -c` | 139/207 (67.15%) | **140/207 (67.63%)** alone; 151/207 (72.95%) merged with agent/armcrypto, the same as WP-H alone |
| Go-compiled, wrappers, test code (1.1) | std | 93.46% / 99.40% / 97.09% | unchanged (no Go-compiled code uses the new classes) |

The supplementary corpus is 476 small loop idioms over every element type (element-wise
arithmetic, compares and selects, shifts, widening and narrowing, saturation written the C way,
reductions, interleaved structures, conversions, rounding, `fma`), plain C11 without intrinsics,
so only the auto-vectorisers emit NEON; it measures the instruction set compiled C needs far
beyond the 21 loops of `vec.c`. In assembly, `vendor/golang.org/x/crypto/chacha20.xorKeyStreamVX`
now decodes (`ZIP1`/`ZIP2` on `.4S`/`.2D`, `MOV` element); `crypto/sha1.sha1block` is left
with its SHA1 instructions only. After merging agent/armcrypto (whose `CryptoInstr.permute` /
`dupScalar` now decode ZIP/UZP/TRN and scalar DUP; the NEON copies were dropped) the arm64 assembly
count is 151/207 (re-measured 2026-10-25), every remaining blocker a system instruction (`SVC`,
`BRK`, `MRS`, `MSR`), padding or `STLXR`, and the C corpus is still 100% in all six configurations.

**Ranking** (supplementary corpus, all six configurations, 2,864 function-configurations, 1,021
blocked before; class = `arm64asm` mnemonic). By functions blocked:

| class | functions blocked | sole blocker |
|---|---:|---:|
| `UZP1` | 114 | 41 |
| `FMLA` | 70 | 30 |
| `FMUL` | 59 | 19 |
| `ZIP1` | 54 | 5 |
| `UZP2` | 52 | 9 |
| `LD2` | 52 | 16 |
| `UMULL` | 43 | 0 |
| `UMULL2` | 42 | 0 |
| `UADDW` | 42 | 0 |
| `ZIP2` | 40 | 0 |
| `SMULL` | 40 | 0 |
| `SMULL2` | 40 | 0 |
| `FCVTZS` | 39 | 23 |
| `LD4` | 37 | 6 |
| `UADDW2` | 35 | 0 |
| `FCMGT` | 31 | 19 |
| `FADD` | 31 | 11 |
| `ST4` | 30 | 0 |
| `SCVTF` | 29 | 22 |
| `SMLAL` | 27 | 0 |
| `SMLAL2` | 25 | 0 |
| `SADDW` | 25 | 0 |
| `UADDL` | 24 | 0 |
| `UADDL2` | 24 | 0 |
| `ST2` | 24 | 9 |
| `SADDW2` | 24 | 0 |
| `ADDP` | 24 | 3 |
| `USUBL` | 23 | 2 |
| `UCVTF` | 22 | 16 |
| `FNEG` | 22 | 14 |

Greedy order (the class that makes the most functions fully decodable next):

| step | class added | + functions | fully decodable |
|---:|---|---:|---:|
| 1 | `UZP1` | +41 | 1884 (65.8%) |
| 2 | `FMLA` | +30 | 1914 (66.8%) |
| 3 | `FCVTZS` | +30 | 1944 (67.9%) |
| 4 | `SCVTF` | +22 | 1966 (68.6%) |
| 5 | `FMUL` | +23 | 1989 (69.4%) |
| 6 | `LD2` | +20 | 2009 (70.1%) |
| 7 | `FCMGT` | +19 | 2028 (70.8%) |
| 8 | `USHL` | +19 | 2047 (71.5%) |
| 9 | `UCVTF` | +18 | 2065 (72.1%) |
| 10 | `FNEG` | +17 | 2082 (72.7%) |
| 11 | `ST2` | +18 | 2100 (73.3%) |
| 12 | `SSHL` | +16 | 2116 (73.9%) |
| 13 | `MLA` | +16 | 2132 (74.4%) |
| 14 | `FADD` | +15 | 2147 (75.0%) |
| 15 | `CLZ` | +15 | 2162 (75.5%) |
| 16 | `UZP2` | +13 | 2175 (75.9%) |
| 17 | `MUL` | +13 | 2188 (76.4%) |
| 18 | `MOV` | +13 | 2201 (76.9%) |
| 19 | `ZIP1` | +12 | 2213 (77.3%) |
| 20 | `ZIP2` | +21 | 2234 (78.0%) |
| 21 | `FMAXNM` | +12 | 2246 (78.4%) |
| 22 | `FCMEQ` | +12 | 2258 (78.8%) |
| 23 | `URHADD` | +12 | 2270 (79.3%) |
| 24 | `FDIV` | +12 | 2282 (79.7%) |
| 25 | `FSUB` | +14 | 2296 (80.2%) |

and so on down to the last of 112 classes (`RADDHN`); `scripts/coverage/rank-classes.py` prints
the full tables from the `insn -c -json` outputs (computed with the decoder of main). On the official corpus alone the
greedy order is:

| step | class added | + functions | fully decodable |
|---:|---|---:|---:|
| 1 | `ADDP` | +17 | 612 (93.3%) |
| 2 | `FNEG` | +8 | 620 (94.5%) |
| 3 | `SCVTF` | +5 | 625 (95.3%) |
| 4 | `FMLA` | +4 | 629 (95.9%) |
| 5 | `UZP1` | +4 | 633 (96.5%) |
| 6 | `USHR` | +2 | 635 (96.8%) |
| 7 | `UCVTF` | +2 | 637 (97.1%) |
| 8 | `MUL` | +2 | 639 (97.4%) |
| 9 | `MOV` | +1 | 640 (97.6%) |
| 10 | `FMUL` | +2 | 642 (97.9%) |
| 11 | `FCVTZU` | +1 | 643 (98.0%) |
| 12 | `FCVTZS` | +1 | 644 (98.2%) |
| 13 | `UADDW` | +0 | 644 (98.2%) |
| 14 | `UADDW2` | +2 | 646 (98.5%) |
| 15 | `ZIP2` | +0 | 646 (98.5%) |
| 16 | `ZIP1` | +3 | 649 (98.9%) |
| 17 | `UMULL2` | +0 | 649 (98.9%) |
| 18 | `UMULL` | +4 | 653 (99.5%) |
| 19 | `ST4` | +0 | 653 (99.5%) |
| 20 | `LD4` | +2 | 655 (99.8%) |
| 21 | `UZP2` | +0 | 655 (99.8%) |
| 22 | `TRN2` | +1 | 656 (100.0%) |

What the decoder still rejects in these classes, by design: half precision (FEAT_FP16, and
`FCVTL`/`FCVTN` to or from half), BFloat16, dot products, `SQRDMLAH`/`SQRDMLSH`, `FMLAL`/
`FMLSL`, `FCMLA`/`FCADD`, `FRINT32*`/`FRINT64*` (optional features no corpus function uses),
and `PMULL`/`PMULL2` (package H).

### 5.2 The C-side ABI, against agent/ffi's model

agent/ffi models the AAPCS64 and System V calls (`Janus/CABI.lean`, `Janus/Amd64/CABI.lean`). The
model covers integer arguments in registers (`X0`–`X7`; `RDI RSI RDX RCX R8 R9`), one or two
integer results, the callee-saved general registers, stack alignment, the red zone, `DF`, and the
cgo boundary contract (`CgoCall`, `TopOfStack`). Measured against the corpus:

| ABI feature | corpus function | decodes today (arm64 / amd64 gcc -O2) | agent/ffi model | missing |
|---|---|---|---|---|
| integer register args/results | `cc_*`, `c_add`, `c_sum` | yes / yes (with `ENDBR64`) | **yes** (`CCall`, `CReturn`) | – |
| stack arguments (> 8 / > 6) | `a_stackargs` | yes / yes | no: `CCall` takes at most `numArgRegs` args | stack-argument layout in `CCall`/`CEnsures` |
| FP/SIMD args and results | `a_fargs`, `f_*` | yes / yes (`-O0` arm64: `SCVTF` forms no) | no ("a C function using floating point is outside the model") | `V0`–`V7` / `XMM0`–`XMM7` args, `D0`/`XMM0` results; callee-saved `V8`–`V15` low halves; FPCR/MXCSR and x87 control word preserved |
| struct by value, ≤ 16 bytes | `a_small`, `a_small_arg`, `a_mixed`, `a_hfa` | yes / `a_hfa`: `SHUFPS` no | partly: an all-INTEGER struct is two integer args; no classification | SysV classification (INTEGER/SSE/MEMORY), AAPCS64 HFA/HVA, mixed classes |
| struct by value, large / `sret` | `a_big`, `a_big_arg` | yes / `PADDQ` no | no: `X8` (indirect result) not in `CCall`; hidden `RDI` pointer unstated | indirect result register, caller-allocated copies |
| varargs | `a_varargs`, `a_varargs_f` | yes / yes | no | `AL` = vector-register count (amd64), register save area, `va_list` layout for both ABIs, `va_arg` over the overflow area |
| callbacks C → Go (`//export`) | – (cgo-generated `_cgoexp_*`, `crosscall2`) | `crosscall2` decodes | no (FFI.md: nothing on it) | `crosscall2` → `cgocallback` contract (re-entering Go: `g`, stack switch, `X28`/`R14`), the reverse composition theorem |
| calls through function pointers | `a_callback` | yes / yes | yes as code (dynamic targets) | a C-side `FuncvalIs` analogue (function-pointer hypotheses) |
| C globals, `.rodata` tables | `a_globals` | yes / yes | partly: read-only data copied; writable data "referenced, not copied"; `-fPIC` GOT loads unmodelled | writable data objects for C `.data`/`.bss`, GOT-indirect access (`adrp :got:` / `mov sym@GOTPCREL`) |
| thread-local storage | `a_use_tls` | yes / **no** (`66 66 48 E8`) | no (only Go's `tls_g`) | initial-exec (`MRS TPIDR_EL0` / `FS:` offset) and general-dynamic (`__tls_get_addr`, TLSDESC) with a TLS-block contract |
| `setjmp`/`longjmp` | `a_setjmp` | yes / yes | no | libc contracts with a non-local return outcome (`jmp_buf` contents, restored callee-saved state) |
| `alloca`, VLAs | `a_alloca`, `cc_vla` | `-O3`: `ADDP` / `PADDQ` no; `-O2`: yes | yes for VLAs (the `CSum`/`cc_vla` frame) | dynamic-frame lemmas for `alloca` |
| libc calls (`memcpy`, `strlen`, `malloc`) | `a_libc` | yes / yes (PLT calls) | no ("would be handled with `--contract`") | PLT stub recognition, per-function libc contracts |
| `long double`, `_Complex`, `__int128` | `a_ldouble`, `a_complex`, `a_u128` | yes / `long double`: x87 no | no | x87 80-bit state (amd64), quad precision via `__multf3` calls (arm64), complex returns in two FP registers |
| bitfields, recursion | `a_bitfield`, `a_recursive` | yes / yes | yes as code | – |
| atomics (GCC `__atomic`) | `m_atomic_inc`, `m_cas` | yes: calls to the outline-atomics helpers `__aarch64_ldadd4_acq_rel`, `__aarch64_cas4_acq_rel` / yes (`LOCK XADD`, `LOCK CMPXCHG`) | yes as code | libgcc outline-atomics helpers (LSE or LL/SC, so they need [WP-A](#6-work-plan)) |


## 6. Work plan

Every gap above is in exactly one package. Packages own disjoint files. Where two of them need the
same dispatcher (`Janus/Arm64/Decode.lean`, `Janus/Amd64/Decode.lean`), the earlier one adds a
one-line hook to a new file and the later ones own only their new files. Sizes are agent effort:
**S** ≈ 1 day, **M** ≈ 2–4 days, **L** ≈ 1–2 weeks, **XL** > 2 weeks or several agents in
sequence. Every decoder package includes the oracle work that comes with a model change (targeted
`gen` specs and the harvest; 0 MISMATCH on qemu/hardware and, on arm64, the Sail three-way run)
and a proved example on each ISA it touches.

**Pending merges.** The branches touch shared files:

* agent/alloc, agent/maps and agent/iface-alloc touch `cmd/janus/{extract,identity,main,verify,
  explain,consumer,blockers}.go`, `Janus/Program.lean`, `Janus/Tactic/*` and
  `Janus/Amd64/{Program,Tactic}.lean`;
* agent/ffi additionally touches `Janus/Amd64/Decode.lean` (`ENDBR64`), `Janus/Tools/Decode.lean`
  and `oracle-amd64/gen/*`.

They merge in the order **alloc → maps → ffi → iface-alloc**. So:

* arm64 decoder packages (A, H, I) can start now;
* amd64 decoder packages (B, D, E, F, G, J) start after **ffi** (`Janus/Amd64/Decode.lean`, the
  oracle generator);
* everything that adds a stub kind, a contract or extraction behaviour (C, K, L, R1–R9) starts
  after **iface-alloc**, which carries the final `--contract` / `Program.contracts` mechanism;
* example packages (M1, M2) can start now on files of their own.

### Ordered by coverage gain

| # | package | gap closed (measured) | owns | size | depends on |
|---:|---|---|---|:-:|---|
| 1 | **A. arm64 store-exclusive** (`STXR`/`STLXR` B/H/W/X, `STXP`/`STLXP`): a sound model of the exclusive monitor. A store-exclusive may fail, so the status result comes from an explicit environment choice in the state, which theorems quantify over. LL/SC retry loops then need a stated progress hypothesis (the k-th attempt succeeds), recorded in SOUNDNESS.md. | arm64 Go-compiled 93.46% → **100%** (+1,085), wrappers +36, test +724, assembly +1 (`cgoSigtramp`); C outline-atomics helpers | `Janus/Arm64/{Decode,Instr,Exec,State}.lean` (exclusive part), `oracle/gen` `ls.excl`, docs/SOUNDNESS.md § atomics | M | none |
| 2 | **B. amd64 v3 scalar extensions** (**done**, agent/amd64v3: Go-compiled v3 94.60% → 100%, wrappers and tests 100%; `docs/AMD64.md`): BMI1 (`ANDN`, `BLSR`, `BLSI`, `BLSMSK`, `BEXTR`, `TZCNT`), BMI2 (`SHLX`, `SHRX`, `SARX`, `RORX`, `MULX`, `BZHI`, `PDEP`, `PEXT`), `MOVBE`, scalar FMA (`VFMADD{132,213,231}{SD,SS}` and the `VFMSUB`/`VFNMADD`/`VFNMSUB` forms, single rounding on the IEEE core, as arm64 `FMADD`), SSSE3 `PSHUFB`/`PSIGNB` on XMM | amd64 v3 Go-compiled 94.60% → **100%** (+897), v3 wrappers +24, tests +209; v1 tests +5; C `-march=v3` BMI/FMA (9 + 7 functions) | `Janus/Amd64/{Decode,Instr,Exec}.lean` (scalar part), `Janus/Amd64/Float.lean` (FMA), `oracle-amd64/gen` specs | M | ffi |
| 3 | **L. Go assembly ABI0 and ABI wrappers** (**done**: [ABI0.md](ABI0.md), `examples/asm`, 5 theorems per ISA): ABI0 call/return (arguments and results in the caller's frame, everything caller-saved, `g` from TLS / `X28`/`R14` on re-entry, `X15` zeroing), `Ensures0`/`Summary0`, and lemmas for the ABIInternal↔ABI0 wrappers and for the direct ABI0 calls the compiler emits from Go | lets theorems be stated about the 145 (arm64) / 170 (amd64) ABI0 assembly functions; 90 / 91 of them already decode | `Janus/GoABI0.lean`, `Janus/Amd64/GoABI0.lean`, `Janus/Tactic/ABI0.lean`, `examples/asm/` | M | iface-alloc (tactic files) |
| 4 | **C. Kernel and system instructions**: `SVC #0`/`SYSCALL` as a `.syscall` stub with per-syscall contracts (`write`, `read`, `openat`, `exit_group`, `clock_gettime` and vDSO, `mmap`/`munmap`/`madvise`, `rt_sigprocmask`, `sigaltstack`, `sched_yield`, `nanosleep`, ...); `BRK`/`INT3`/`UD2`/`HLT`/in-function `UDF` as trap faults; `CPUID`, `XGETBV`, `RDTSC(P)`, `MRS MIDR_EL1`, `MRS CNTFRQ_EL0`, DIT `MRS`/`MSR` as environment-value contracts; `PUSHFQ`/`POPFQ` | assembly: arm64 +53 (→ 92.8%), amd64 +46 (→ 73.2%); makes the syscall wrappers (`nanotime1`, `Syscall6`, `rawSyscallNoError`, `exit`, `osyield`, `open`, `read`, ...) and their Go callers (`os`, `time`, `println`) provable | `Janus/Contracts/Syscall.lean`, `Janus/Contracts/SyscallAmd64.lean`, the `SVC`/`SYSCALL`/trap entries of both decoders, stub kind in `cmd/janus/extract.go` | M | iface-alloc |
| 5 | **J. amd64 C-specific encodings**: merge agent/ffi's `ENDBR64`; `NOTRACK` (`3E`) on `JMP`/`CALL r/m` (CET jump tables); the padded `call __tls_get_addr` sequence (`66 66 48 E8`); x87 for `long double` (`FLD`/`FSTP` 80-bit, `FADDP`, `FMULP`, `FLD1`, `FXCH`, the x87 stack and control word on the IEEE core) | gcc amd64 C: 0.9% → **83.6%** (-O2); `s_dense`/`s_name` jump tables, `a_use_tls`, `a_ldouble` | `Janus/Amd64/Decode.lean` (prefix handling), new `Janus/Amd64/X87.lean` | S (ENDBR, NOTRACK, TLS call) + L (x87) | ffi |
| 6 | **D. SSE packed integer and FP (XMM)** (**done**, agent/sse: assembly v1 148 → 160, C `-O2` clang 78.0% → 98.2%, gcc 83.6% → 96.4%, oracle 0 MISMATCH; `docs/AMD64.md`): SSE2 integer (`PADD*`, `PSUB*`, `PMUL*`, `PCMP*`, `PAND(N)`, shifts incl. `PSLLDQ`/`PSRLDQ`, `PUNPCK*`, `PACK*`, `PMIN/PMAX*`, `PSADBW`), packed FP (`ADDPS/PD`, `MULPS/PD`, `SHUFPS`, `UNPCK*`, `MOVLHPS`, `CVTDQ2PD`), SSSE3 (`PALIGNR`, `PSHUFB`, `PABS*`), SSE4.1 (`PINSR*`, `PEXTR*`, `PBLENDW`, `BLENDV*`, `PMOV[SZ]X*`, `PMULLD`, `PTEST`), SSE4.2 (`CRC32`, `PCMPESTRI`/`PCMPISTRI`, `PCMPGTQ`) | C: clang -O2 78.0% → ≈ 99%, gcc -O2 (after J) 83.6% → ≈ 99%; assembly: `chacha8rand.block`, P-256 selects, `indexbody`, `castagnoliSSE42*`, part of AES/GCM/SHA (+19 sole, more with E) | new `Janus/Amd64/{DecodeSSE,ExecSSE}.lean` (hook in `Decode.lean`) | L | ffi; B for the shared `PSHUFB` |
| 7 | **E. x86 crypto extensions**: AES-NI (`AESENC(LAST)`, `AESDEC(LAST)`, `AESIMC`, `AESKEYGENASSIST`), `PCLMULQDQ`, SHA-NI (`SHA1*`, `SHA256*`), ADX (`ADCX`/`ADOX`) | assembly: `aeshashbody`, `memhash32/64` (every map hash), AES block/CTR/key expansion (12), GCM (5), SHA-NI (2), `math/big.addMulVVWW`, `bigmod.addMulVVW*` (4) | new `Janus/Amd64/{DecodeCrypto,ExecCrypto}.lean` | M | D, B (`MULX`) |
| 8 | **I. arm64 ASIMD for compiled C**: `ADDP`, `UADDW(2)`, `UMULL(2)`, `MUL` (vector), `FMLA`/`FMUL`/`FNEG` (vector FP, on the IEEE core), `SCVTF` (vector), `UZP1`/`ZIP1`, `LD4`/`ST4`, `USHR`, and the scalar `SCVTF`/`UCVTF`/`FCVTZS`/`FCVTZU` forms of gcc/clang `-O0` | C arm64: gcc -O3 85.3%, clang -O2/-O3 86.2%, gcc -O2 93.6%, -O0 96.4% → **100%** (done on agent/neon, 5.3: every arrangement of the integer and single/double FP classes, `LD2`–`ST4`, `LDNP`/`STNP`; supplementary corpus 37.2–98.3% → 100%; assembly +1, `chacha20.xorKeyStreamVX`) | `Janus/Arm64/Vector.lean` (+ new `VectorFP.lean`), `Janus/Arm64/DecodeFloat.lean` (conversion forms) | M | none |
| 9 | **H. arm64 crypto extensions, CRC32, permutes** (done on agent/armcrypto: 151/207 assembly, `A64Crc32` proved; see 1.3): `PMULL`/`PMULL2` (1Q), `SHA1C/H/M/P/SU0/SU1`, `SHA256H/H2/SU0/SU1`, `SHA512H/H2/SU0/SU1`, SHA3 `EOR3`/`RAX1`/`XAR`/`BCAX`, `CRC32{B,H,W,X}`, `CRC32C{B,H,W,X}`, `ZIP1`/`ZIP2` on 2D, `MOV` element | arm64 assembly +12 (GCM ×5, SHA-1/256/512, SHA3, CRC32 ×2, chacha20); with C 206/207, the last being A's `cgoSigtramp` | new `Janus/Arm64/Crypto.lean` (hook in `Decode.lean`) | M | none (I for the shared `ZIP1`) |
| 10 | **F. AVX/AVX2 (VEX-128/256, YMM)** beyond the moves and compares `memmove`/`memequal` use: integer and FP arithmetic, shuffles and permutes (`VPSHUFB`, `VPALIGNR`, `VPERM2I128`, `VPERMD`, `VPBLENDD`, `VINSERTI128`, `VEXTRACTI128`, `VPBROADCAST*`), packed FMA, the `V*SD/SS` scalar forms | C `-march=x86-64-v3`: gcc 52.7%, clang 50.5% → ≈ 99%; assembly: `math.archExp`, SHA-1/256/512 AVX2, chacha20poly1305 (+7 in the greedy table) | new `Janus/Amd64/{DecodeAVX,ExecAVX}.lean` | L | D (lane semantics generalised to 256 bits) |
| 11 | **G. AVX-512**: EVEX decoding (`disp8*N`, broadcast, masking, zeroing), ZMM state, `K0`–`K7` and `KMOV*`, `VMOVDQU64`, `VPERMB`/`VPERMI2B` (VBMI), `VGF2P8AFFINEQB` (GFNI), `VPOPCNTB`, `VPCOMPRESSQ`, `VPTERNLOGD`, `VPCLMULQDQ`, `VEXTRACTF32X4`, `VPCMPUQ`, the `asyncPreempt` state save | assembly +29 (`internal/runtime/gc/scan.expandAVX512_*`, the GC's span scanning), `ieeeCLMUL`, `asyncPreempt` → amd64 assembly 100% (with C, D, E, F) | new `Janus/Amd64/{DecodeEVEX,ExecEVEX}.lean`, ZMM/K fields in `Janus/Amd64/State.lean` | XL | F |
| 12 | **K1. C ABI: arguments and results**: stack arguments, FP/SIMD arguments and results, callee-saved `V8`–`V15` low halves, FPCR/MXCSR/x87-CW preservation, SysV classification (INTEGER/SSE/MEMORY), AAPCS64 HFA/HVA, indirect results (`X8`, hidden `RDI`), varargs (`AL`, register save area, `va_list` for both ABIs), `long double`/`_Complex` returns | rows 2–6 and 15 of the table in 5.2 | `Janus/CABI.lean`, `Janus/Amd64/CABI.lean`, docs/FFI.md § 1 | L | ffi |
| 13 | **K2. C ABI: environment**: `//export` callbacks (`crosscall2` → `cgocallback` contract and the reverse composition theorem), function-pointer hypotheses, writable C globals and `-fPIC` GOT access as data objects, TLS (initial-exec, general-dynamic, TLSDESC), PLT stubs and libc contracts (`memcpy`, `memset`, `strlen`, `malloc`/`free`, outline atomics), `setjmp`/`longjmp` (non-local return), `alloca` frame lemmas | rows 7–13 of 5.2 | `Janus/FFI.lean`, `Janus/Amd64/FFI.lean`, new `Janus/Contracts/Libc.lean`, the cgo part of `cmd/janus/extract.go`, docs/FFI.md §§ 2–4 | L | K1, iface-alloc |
| 14 | **R1. String runtime contracts**: `concatstring2..5`/`concatstrings`, `concatbyte2..5`/`concatbytes`, `slicebytetostring`, `slicebytetostringtmp`, `stringtoslicebyte`, `stringtoslicerune`, `slicerunetostring`, `intstring`, `cmpstring` (executed: decodes), `decoderune`, `countrunes`, `strmin`/`strmax`, `gostring`, `gostringn`, `gobytes` | 20 linked + 3 | `Janus/Contracts/String.lean` (+`Amd64`), `Janus/Spec/String.lean` | M | iface-alloc (alloc contracts) |
| 15 | **R2. Interface runtime contracts** (done on agent/rtiface): `convT`, `convTnoptr`, `convT16/32/64`, `convTstring`, `convTslice`, `assertE2I`, `assertE2I2`, `typeAssert`, `interfaceSwitch` (+ `emptyTypeAssertCache`, `emptyInterfaceSwitchCache`), `ifaceeq`, `efaceeq` | 12 linked + 1 + 2 caches; unlocks type switches and assertions (criterion 3) | `Janus/Contracts/Iface.lean` (+`Amd64`), `Janus/Spec/Type.lean` | M | iface-alloc |
| 16 | **R3. Remaining map contracts**: `makemap`, generic `mapaccess1`/`mapassign`/`mapdelete`, the `_fast32`, `_faststr`, `_fat` and `_fast64ptr` variants | 15 linked | `Janus/Contracts/Map*.lean` (extending agent/maps) | M | maps, R4 (key hashing) |
| 17 | **R4. Equality and hashing contracts**: `memequal0/8/16/32/64/128`, `memequal_varlen`, `f32equal`, `f64equal`, `c64equal`, `c128equal`, `strequal`, `interequal`, `nilinterequal`; `memhash*`, `strhash`, `f32hash`, `f64hash`, `c64hash`, `c128hash`, `interhash`, `nilinterhash`, `rand` (seeded hash as an uninterpreted function with its laws); `typedmemmove`, `typedmemclr`, `memclrHasPointers` | 17 + 16 linked | `Janus/Contracts/Mem.lean`, `Janus/Contracts/Hash.lean` | M | iface-alloc; E to execute `aeshash` instead of assuming it |
| 18 | **R5. Slices and write barriers**: `growsliceBuf`, `growslice*NoAlias`, `makeslicecopy`, `moveSlice*`, `slicecopy`, `typedslicecopy`; `gcWriteBarrier1`, `3`–`8`, `wbZero`, `wbMove`, the `writeBarrier` flag | 8 + 2 and 10 linked | `Janus/Contracts/Alloc*.lean` (extending agent/alloc), `Janus/Contracts/WriteBarrier.lean` | S–M | alloc, iface-alloc |
| 19 | **R6. Panics, defer, recover**: `gopanic` with unwinding through deferred calls, `gorecover`, `deferproc`, `deferprocStack`, `deferreturn`, `deferprocat`, `deferrangefunc`, `sigpanic` (nil dereference and other faults as Go panics), `panicrangestate`; an outcome `.panicked v` that `recover` can turn back into a return. **Done on agent/panic, generalised on agent/panic2** (both ISAs): `EnsuresGo`/`GoReturns` with `.panicked v` and `.goexit`, the runtime contracts (`gopanic`, `Goexit`, `gorecover`, `deferproc`, `deferprocStack`, `deferreturn`, `deferprocat`, `deferrangefunc`) pinned and proved satisfiable — `gopanic`, `Goexit` and `deferreturn` are one general engine (every pending open-coded and heap defer of the frame, in order; each deferred call may return, panic again or recover; recovery resumes the frame; the panic unwinds past the frame otherwise), satisfied by a model engine with `Janus/Contracts/PanicSat*.lean` (arm64) and `PanicSatAmd64*.lean` (amd64) — `sigpanic` (pinned) as the fault classification of `goClass`, `panicrangestate` as a classified stub, examples `PanicIf`, `DeferInc`, `RecoverSet`, `IndexAt`, `LoadField`, `DeferTwice` (both ISAs), `DeferOrder`, `DeferMix`, `GoexitDefer`, `RangeDefer`, `NestedPanic`, `NestedRecover` (arm64) ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md#panics-defer-recover)) | 5 linked + 2; the defer/panic/recover rows of criterion 3 | `Janus/Spec/Panic.lean`, `Janus/Contracts/Panic.lean`, `Janus/Contracts/PanicAmd64.lean`, panic-outcome changes in `Janus/GoABI.lean` | L–XL | iface-alloc (defer mechanism), R2 (panic values are interfaces) |
| 20 | **R7. Stack growth**: a contract for `morestack`/`newstack` (the grown case: the frame is copied and stack pointers adjusted), `morestackc`; theorems that hold without assuming `GuardOK` | 1 linked + the `.morestack` stubs; recursion and deep calls (criterion 3) | `Janus/Contracts/Stack.lean`, `GuardOK`/`GrowsStack` in `Janus/GoABI.lean` | XL | R6 (the panics during growth), iface-alloc |
| 21 | **R8. `print`/`println`**: `printlock`/`printunlock` and the 16 `print*` functions, as output-trace contracts over `write(2)` | 18 linked + `printiface` | `Janus/Contracts/Print.lean` | S | C |
| 22 | **R9. Remaining runtime**: `complex128div`, `f32to64`/`f64to32`, `fadd64`/`fmul64`/`fdiv64` and the soft-float set (`-d=softfloat`); `KeepAlive`, `zeroVal`, `staticuint64s`, `cgoAlwaysFalse`, `cgoCheckPointer`, `cgoUse`, `cgoCheck*`, `cgoKeepAlive`, `cgoNoCallback`; the CPU feature flags (`arm64HasATOMICS`, `x86HasAVX`, `x86HasFMA`, `x86HasPOPCNT`, `x86HasSSE41`) as stated hypotheses; the instrumented build modes (`-msan`, `-asan`, `-cover`, `-d=checkptr`, `-d=libfuzzer`, `-spectre=ret`) and the `mallocgc*SC<n>` size-specialised allocator of the GOEXPERIMENT | 22 linked + the rest of the defined-not-linked list | `Janus/Contracts/Misc.lean`, `Janus/Contracts/Instrument.lean` | M | iface-alloc |
| 23 | **M1. Construct examples, no new runtime** (agent/constructs: done except int↔float and float32↔float64 conversions, the nil-dereference fault path and amd64 `IndexByte`; see section 3): `-`, `%`, variable shifts, `\|`, `^`; for-cond/break/labels/goto; expression switch (jump tables), fallthrough; range over array, int and func; static and value-receiver method calls, method expressions, variadic calls, closure creation; generics (shape + dictionary); large struct copies; `a[i:j]`, `a[i:j:k]`; `min`/`max`; `uintptr`; int↔float and float32↔float64 conversions; the nil-dereference fault path; arm64 globals (`Bump`, `GlobalTable`, `Table`); amd64 `IndexByte` | 21 of the 35 "none" rows of criterion 3, both ISAs | `examples/basic/lang*.go`, `examples/proofs/Lang*.lean`, `examples/proofs-amd64/Lang*/` | L | none (A/B for atomics-free builds of the examples) |
| 24 | **M2. Construct examples on new contracts**: strings (concat, compare, conversions, range over string), interfaces (boxing, assertions, type switch, comparison), panic/recover, heap defer, the grown-stack case, recursion, complex numbers, `//export` callbacks | the 14 remaining "none" rows | `examples/basic/rt*.go`, `examples/proofs*/Rt*` | L | R1, R2, R6, R7, R9, K2 |

### What remains after the plan

Nothing in scope. Concurrency stays excluded: the 12 linked and 3 defined channel, select and
goroutine entry points, the `race*` instrumentation, `sync` and the multi-threaded parts of the
runtime. Single-threaded `sync/atomic` is in scope and covered by A and B. The two numbers to
re-measure after each package are the `insn` summary of `scripts/coverage.sh` (criteria 1, 4, 5)
and the `runtime` table (criterion 2).
