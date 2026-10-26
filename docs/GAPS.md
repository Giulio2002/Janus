# Gap analysis: what the next wave needs (2026-10-26)

This page is input for choosing the next wave of work. It re-measures instruction coverage on
main and on the integration branch, over the Go standard library, the C corpus and a large
real-world program. It lists the runtime entry points that still have nothing, and the framework
needs that came up while working out a large verification target. Each item has an effort
estimate and work packages sized for one agent. [COVERAGE.md](COVERAGE.md) §6 stays the plan of
record; the packages here continue it as **N1–N8**.

**Status (agent/cover, 2026-10-26).** Three of the packages below are done on `agent/cover`
(branched from integ/wave1 `b52a353`): **N2** (amd64 `REP RET`/`BND RET`), **N5** (arm64 `MRS` of the
feature-ID registers) and **R9′** (`KeepAlive` and the soft-float `fadd64`/`fsub64`/`fmul64`/`fdiv64`
contracts). The rows they close are marked **done** in the ranked table (ranks 3, 5 and 6) and in
the package table of section 4; their results are in [ORACLE-AMD64.md](ORACLE-AMD64.md) (N2),
[SOUNDNESS.md](SOUNDNESS.md) and [RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md) (N5, R9′).

**Baseline.**

* main at `4a75ac7`. Its decoders were built in a worktree of this branch: `janus-decode` SHA-256
  `04c752c5…`, `janus-oracle-amd64` `eaa05f07…`.
* integ/wave1 at `e623b1b`, which merges NEON, SSE, AVX, AVX-512, x87, store-exclusive, syscall,
  panic and cgo. It was only read. Its decoders were copied out of its build directory before any
  measurement ran (`janus-decode` `e724b11e…`, `janus-oracle-amd64` `c9d41272…`). No arm64 decoder
  file changed after that build, and the worktree's only uncommitted changes are proof files.
* Go 1.26.0 (`GOTOOLCHAIN=go1.26.0`), gcc 15.2.0, clang 21.1.8.

**Corpora.**

1. **std**: the corpus of COVERAGE.md. That is `go test -c -trimpath` of the 250 std packages
   with tests, `CGO_ENABLED=0` (plus `runtime/cgo` with cgo), for arm64, amd64 `GOAMD64=v1` and
   amd64 `GOAMD64=v3`.
2. **C corpus**: `scripts/coverage/ccorpus/*.c` plus `examples/cgo/{ccover,cfuncs}.c`, in the 14
   compiler configurations of `scripts/coverage.sh cc`.
3. **A large application** (new). An open-source Go program: about 66k functions, many
   third-party modules, and Go assembly from `golang.org/x/crypto`, `golang.org/x/sys` and
   CPU-feature libraries. It is built `CGO_ENABLED=0` (arm64 and amd64 v1). Its three cgo C
   libraries are measured separately: elliptic-curve, pairing and polynomial-commitment
   cryptography, one of them with perlasm-generated assembly. Their objects come from a
   `go build -work` and are decoded as kind `c`.

**Method.** The `insn` stage of `scripts/coverage/` (the program behind `scripts/coverage.sh`). It
sweeps every function and runs every distinct encoding through the trusted Lean decoder. It is
run once per decoder set over the same binaries, so main and integ/wave1 are compared on
identical input. Criterion 2 is the `runtime` stage with `-branches "origin/main integ/wave1"`.
Section 6 has the commands.

## 0. Summary

**On integ/wave1 the decoders accept essentially all of std, the C corpus and the application's
Go code, on both ISAs.** Merging integ/wave1 into main is therefore the single largest coverage
step. Apart from the merge, the remaining gaps are three small instruction families found only in
real third-party code, the absence of any contract for single-threaded `sync`, and runtime and
framework pieces.

### Ranked: top general coverage gaps

| rank | gap | measured weight (functions blocked or affected) | effort | packages |
|---:|---|---|:-:|---|
| 1 | **Merge integ/wave1 into main.** On main: arm64 `STLXR`/`STLXRB` (std: 1,085 Go-compiled + 36 wrappers + 724 test functions; application: 3,977 Go-compiled + 193 wrappers); arm64 asm `SVC`/`BRK`/`MRS`/`MSR` (56 std asm functions); amd64 asm `SYSCALL`, AVX-512, AES-NI, `PCLMULQDQ`, AVX2, ADX, `CPUID`/`XGETBV`/`INT3`/`UD2` (105 of 265 std asm functions, 128 of 360 application asm functions); C: x87, `NOTRACK JMP`, the TLS call, VEX (up to 45 of 110 corpus functions at `-march=x86-64-v3`). integ/wave1 decodes all of it. | 4,000+ functions | (merge) | – |
| 2 | **Single-threaded `sync` contracts.** `sync` is excluded with concurrency, but single-threaded code calls it all the time. In the application, **4,467 of 66,086 functions (6.8%)** call `sync`/`internal/sync` directly: `Mutex.lockSlow`/`unlockSlow` 1,224/1,269, `RWMutex.Lock`/`Unlock` 438/443, `Pool.Get`/`Put` 254/287, `Once.doSlow` 202. In std, `fmt` and `math/big` get their scratch state from a `sync.Pool`. Without a contract, extraction follows these into `runtime_procPin`, lock-free dequeues, semaphores and `GOMAXPROCS`. | 4,467 direct callers (application) | M–L | N1a–N1d |
| 3 | **done (agent/cover, N2): amd64 `REP RET` (`F3 C3`).** The AMD branch-predictor idiom of perlasm/OpenSSL-style assembly, which integ/wave1's decoder rejects. Related, same family: `BND RET` (`F2 C3`) and the other ignored prefixes on near `RET`/`JMP`/`CALL`. | **98** of 785 cgo C functions (the perlasm library: 87.5% → ≈ 100%) | S | N2 |
| 4 | **arm64 pointer authentication and BTI hints.** `PACIASP` (`HINT #25`, `d503233f`) and `AUTIASP` (`HINT #29`, `d50323bf`) in hand-written C-library assembly. Both decoders reject them. Linux enables the PAuth keys for EL0 on hardware that has them, so they are not `NOP`s: X30 is signed and then authenticated. The family also has `PACIBSP`/`AUTIBSP`, `RETAA`/`RETAB`, `XPACLRI` and `BTI` (what `-mbranch-protection=standard` emits). | **35** of 772 arm64 cgo C functions | M | N3 |
| 5 | **done (agent/cover, N5): arm64 `MRS` of the ID registers in user assembly.** `ID_AA64ISAR0_EL1`, `ID_AA64ISAR1_EL1`, `ID_AA64PFR0_EL1`, `ID_AA64ZFR0_EL1` (`S3_0_C0_C6_0`, `S3_0_C0_C6_1`, `S3_0_C0_C4_0`, `S3_0_C0_C4_4`). The kernel traps and emulates them at EL0. They appear in `golang.org/x/sys/cpu.get{isar0,isar1,pfr0,zfr0}` and `klauspost/cpuid`. integ/wave1 models `MRS MIDR_EL1` and `CNTFRQ` as environment values, not these. | **6** asm functions (the only arm64 Go/asm gap left in the application) | S | N5 |
| 6 | **`KeepAlive` and `fadd64`/`fmul64`/`fdiv64` done (agent/cover, R9′); the rest open.** **Runtime entry points with nothing on either branch** (corrected count, section 2): the 18 `print*`/`printlock`/`printunlock` of `println` (R8), the grown-stack case of `morestack` and `morestackc` (R7), `KeepAlive`, and the soft-float `f64to32`, `fadd64`, `fmul64`, `fdiv64` (these execute as code; there is no proof or spec). | 24 linked names (+12 concurrency, excluded) | S (R8 print, R9 rest) + XL (R7) | R7, R8, R9 |
| 7 | **Mutual-recursion summaries.** `Summary.induction` (`Janus/Tactic/Recursion.lean`, `Janus/Amd64/Recursion.lean`) takes one entry. Mutually recursive functions (multiplication ↔ Karatsuba, squaring ↔ Karatsuba squaring, even/odd dispatch in exponentiation, all common in bignum code) need a version over a finite family of entries with one measure. | every SCC of size > 1 | S | N4 |
| 8 | **"A global holds its link-time initial value" precondition.** Code reads writable package variables that nothing writes at run time: tuning thresholds in `.noptrdata`, constant `nat`s in `.data`, pools in `.bss`, CPU-feature booleans set by `init`. The extractor lists them as "writable data referenced (not copied)". Each theorem now writes its own precondition. A predicate built from the ELF image (`GlobalInit p sym`: the bytes are the `.data`/`.noptrdata` initialiser, zero for `.bss`) and a tactic lemma would make this uniform. | every function that reads such a global | S | N6 |
| 9 | **Pin the allocation, slice and write-barrier contracts.** `makeslice`, `newobject`, `growslice`, `gcWriteBarrier1..8` (and on integ/wave1 the `Slice.lean`/`String.lean` specs) are contracts but not in `runtimeContractStubs`, so `--contract` matches them by name only. `memmove`, `memclrNoHeapPointers`, the interface/map/hash/equality contracts and the panic contracts are pinned to the runtime's code. | 3 + 8 of the most-called entry points (std Go callers: `gcWriteBarrier2` 3,239, `gcWriteBarrier1` 1,833) | S | N7 |
| 10 | **Measurement and extraction tooling.** (a) The `blockers` amd64 sweep lacks the coverage tool's `VZEROUPPER` length fix and loses sync after `ADCX`/`ADOX`. It reports `memmove`, `memclrNoHeapPointers`, `memeqbody`, `indexbytebody` as rejected, plus junk (`movq %mm5`, `fcomip`, `fisttp`, `data16`). (b) Dynamic-target inference adds an unrelated function from another package (a hash constructor) to an amd64 extraction. (c) The `runtime` stage only credits a contract file that writes `runtime.<name>`, so it reports 64 linked names missing on integ/wave1 where 36 are. (d) The `insn` stage measures only 6,248 of about 66k functions of an externally linked cgo binary (pclntab lookups miss), so cgo programs must be measured as above. (e) `scripts/coverage.sh`'s default `BRANCHES` still lists merged branches, and integ/wave1's COVERAGE.md carries "not yet re-measured together" figures that section 1 now measures. | accuracy of every later measurement | S each | N8a–N8d |

## 1. Instruction coverage, re-measured

### 1.1 std (250 test binaries per configuration)

Fully decoding functions, by kind:

| configuration | kind | main | integ/wave1 |
|---|---|---:|---:|
| arm64 | Go-compiled | 15,517 / 16,602 (93.46%) | **16,602 / 16,602 (100%)** |
| | assembly | 151 / 207 (72.95%) | **207 / 207 (100%)** |
| | wrappers / test | 99.40% / 97.09% | **100% / 100%** |
| | C (`runtime/cgo`) | 20 / 20 | 20 / 20 |
| amd64 v1 | Go-compiled / wrappers / test | 100% / 100% / 100% | 100% / 100% / 100% |
| | assembly | 160 / 265 (60.38%) | **264 / 265 (99.62%)** |
| amd64 v3 | Go-compiled / wrappers / test | 100% / 100% / 100% | 100% / 100% / 100% |
| | assembly | 157 / 262 (59.92%) | **261 / 262 (99.62%)** |

The one amd64 assembly function left on integ/wave1 is `crypto/internal/boring/sig.StandardCrypto`.
It is a marker: its "body" is a byte signature (`hlt`, `lret`, an unknown VEX prefix) that is never
executed. So **every executable instruction of std decodes on integ/wave1, on both ISAs**. This
confirms the integ/wave1 COVERAGE.md headline figures marked "not yet re-measured together": arm64
assembly 206 + 1 = 207, and amd64 98.9% expected, measured 99.62%.

Restricted to single-threaded packages (excluding `sync`, `internal/sync`, `context`,
`internal/singleflight`, `runtime/trace`, `internal/trace/…`, `os/signal`, `…/synctest`), arm64 main
is 14,852 / 15,814 Go-compiled (93.92%) and integ/wave1 100%; the other figures do not change.

**Top rejected mnemonics on main, weighted by functions blocked** (all closed by integ/wave1).
"Sole" is the count where the mnemonic is the function's only blocker.

| ISA | mnemonic (family) | functions blocked (sole) | where |
|---|---|---:|---|
| arm64 | `STLXR` (store-exclusive) | Go 1,070 (1,062), test 715, wrappers 36, asm 1 | LL/SC fallback of every atomic |
| arm64 | `STLXRB` | Go 23 (15), test 12 | `runtime.lock2`, … |
| arm64 | `SVC` | asm 33 (33) | syscall wrappers |
| arm64 | `BRK` | asm 14 (14) | `debugCall*` |
| arm64 | `MRS` / `MSR` (ID, DIT) | asm 5 (3) / 2 (1) | `internal/cpu.getMIDR`, `sys.EnableDIT` |
| amd64 | `SYSCALL` | asm 36 (34) | syscall wrappers |
| amd64 | AVX-512 (`VMOVDQU64` 31, `VGF2P8AFFINEQB` 25, `VPERMB` 25, `VPERMI2B` 19, `KMOVQ` 12, `VPORQ` 11, `VPCOMPRESSQ` 2) | asm 31 (29 as a family) | `internal/runtime/gc/scan.expandAVX512_*` |
| amd64 | AES-NI (`AESENC` 11, `AESENCLAST` 8, `AESDEC`/`AESDECLAST`/`AESIMC`/`AESKEYGENASSIST` 1 each) | asm 13 (10) | `aeshashbody`, `memhash32/64`, fips140 AES |
| amd64 | `PCLMULQDQ` | asm 6 (2) | GCM, `hash/crc32.ieeeCLMUL` |
| amd64 | AVX2 (`VPALIGNR`, `VPSHUFB`, `VPADDD`, `VPSLLD`, `VPSRLD`, `VPERM2I128`, …) | asm 5 (4) | SHA-256/512 AVX2, chacha20 |
| amd64 | ADX (`ADCX`, `ADOX`) | asm 4 (4) | `math/big.addMulVVWW`, `bigmod.addMulVVW*` |
| amd64 | `INT3`, `CPUID`, `UD2`, `XGETBV` | asm 4, 3, 2, 2 (all sole) | `systemstack`, `internal/cpu` |

### 1.2 The large application (Go and Go assembly)

| ISA | kind | main | integ/wave1 |
|---|---|---:|---:|
| arm64 | Go-compiled | 46,361 / 50,338 (92.10%) | **50,338 / 50,338 (100%)** |
| | assembly | 163 / 225 (72.44%) | 219 / 225 (97.33%) |
| | wrappers | 15,151 / 15,344 (98.74%) | **100%** |
| amd64 v1 | Go-compiled / wrappers | 100% / 100% | 100% / 100% |
| | assembly | 232 / 360 (64.44%) | **359 / 360** (the same `sig.StandardCrypto` marker) |

On main: arm64 `STLXR` 3,962 Go functions (3,954 sole), `STLXRB` 23, `SVC` 32 asm, `BRK` 14, `MRS`
12. amd64: `SYSCALL` 34, AVX-512 30, **ADX 20** (third-party bignum and field arithmetic: ADX is 5×
more frequent here than in std), AES-NI 11, `CPUID` 7, `PCLMULQDQ` 6, AVX2 6, `XGETBV` 4.

On integ/wave1 the **only** remaining gap is arm64 `MRS` of the ID registers (rank 5): 6 asm
functions, `golang.org/x/sys/cpu.getisar0/getisar1/getpfr0/getzfr0` and
`klauspost/cpuid/v2.getProcFeatures/getInstAttributes`.

### 1.3 C

**The C corpus** (110 functions, 14 configurations). integ/wave1: **100% in every
configuration**, gcc and clang, `-O0`/`-O2`/`-O3`, both ISAs, and `-O3 -march=x86-64-v3` on amd64.
main: arm64 100% everywhere. amd64 gcc `-O2` 96.36% (`NOTRACK JMP` ×2, x87, the TLS call), clang
`-O2` 98.17%, `-O3 -march=x86-64-v3` gcc 59.09% / clang 58.72% (VEX: `VMOVQ`, `VEXTRACTI128`,
`VPADDQ`, `VPSHUFD`, `VADDSD`, …).

**The application's cgo libraries** (`-O2` as cgo compiles them, plus their perlasm `.S`):

| ISA | main | integ/wave1 | blocker on integ/wave1 |
|---|---:|---:|---|
| arm64 | 737 / 772 (95.47%) | 737 / 772 (95.47%) | `PACIASP`/`AUTIASP` (`HINT #25`/`#29`), 35 functions, all in the perlasm library |
| amd64 | 686 / 785 (87.39%) | 687 / 785 (87.52%) | `REP RET` (`f3 c3`), 98 functions (sole blocker of all 98), all perlasm |

main additionally rejects `ADCX`/`ADOX` (6), `CPUID` (1) and SHA-NI (`SHA256MSG1`/`MSG2`/`RNDS2`, 1)
here. The small corpus never exercised either of the integ/wave1 blockers: hand-written
assembly, not compiler output, is where the remaining encodings live.

## 2. Runtime entry points

309 names the Go 1.26 compiler can emit calls to; 191 are linked by the std test binaries. The
`runtime` stage credits main with 94 of the 191 and integ/wave1 with 127. It undercounts
integ/wave1 (N8, item (c)): it misses contracts whose file names the function without the
`runtime.` prefix (`concatstring2..5`/`concatbyte2..5` in `String.lean`, `memequal8..128` in
`Mem.lean`, `memhash16`/`128` in `Hash.lean`, `gcWriteBarrier1..8` as `gcWriteBarrierN` in
`WriteBarrier.lean`, `sigpanic` in `Panic.lean`, `x86HasAVX/FMA/SSE41` in `Misc.lean`, and
`f32to64`, executed in `examples/rtmisc`). Checked by hand, **the linked names with nothing on
integ/wave1 are 36**:

| category | names | package |
|---|---|---|
| concurrency (excluded) | `block`, `chancap`, `chanlen`, `chanrecv1`, `chanrecv2`, `chansend1`, `closechan`, `makechan`, `newproc`, `selectgo`, `selectnbrecv`, `selectnbsend` | – |
| `print`/`println` | `printbool`, `printcomplex128`, `printcomplex64`, `printeface`, `printfloat32`, `printfloat64`, `printhex`, `printint`, `printlock`, `printnl`, `printpointer`, `printquoted`, `printslice`, `printsp`, `printstring`, `printuint`, `printuintptr`, `printunlock` | R8 (S–M; the `write(2)` contract now exists on integ/wave1) |
| stack growth | `morestackc`; and no theorem covers the grown case of `morestack` | R7 (XL) |
| soft float | `f64to32`, `fadd64`, `fmul64`, `fdiv64` (Go code that decodes; no proof or spec) | R9 (S) |
| misc | `KeepAlive` | R9 (S) |

Beyond the compiler-emitted entry points, single-threaded code reaches `sync` (rank 2): 4,467
direct callers in the application. There is no contract for it on either branch.

## 3. Framework needs found while planning a large verification target

Working out the call graph of a real ~85-function bignum target (an exponentiation routine with
Montgomery, Karatsuba and recursive division, called from a third-party module) showed six
generic needs. Each is independent of that target.

1. **`sync.Pool` used single-threaded** (N1a, N1b). Bignum code takes scratch memory from a
   package-level `sync.Pool` and returns it in a deferred call. The contract has to say what a
   single-threaded program may rely on: `Get` returns either `nil` (the GC may empty a pool at any
   time; with `New` set, `New()`'s result) or a value that a `Put` stored earlier and no `Get` has
   returned since; `Put` stores it; both change only pool-owned memory (an `rt`-style range list
   plus the `p.local` arrays). A pool invariant (every pooled value is a valid `*T` outside the
   caller's data) lets the caller use what `Get` returns. The satisfiability witness can be toy
   code, as for the allocation contracts; the real `Get`/`Put` are trusted, as `mallocgc` is.
   `sync` is not `runtime`, so `checkContractPin` needs to pin functions of other std packages
   by their pclntab file and code hash (generalise `scripts/gen-stubpins.sh`).
2. **Mutual recursion** (N4): see rank 7.
3. **Initialised globals** (N6): see rank 8.
4. **Pinning** (N7): see rank 9. The contracts of the two most-called allocation entry points
   (`makeslice`, `newobject`) are the ones a bignum target uses most (32 and 7 of its functions).
5. **Open-coded defers through a register** (`CALL AX` / `BLR` to a `deferwrap` closure) are
   handled already: the extractor infers the closures for non-std packages. Nothing is needed.
6. **ABI0 leaves called directly from Go** (`addVV`, `mulAddVWW`, …) are handled by docs/ABI0.md;
   the work is the proofs, not framework.

## 4. General work packages

Sizes as in COVERAGE.md: **S** ≈ 1 agent-day, **M** ≈ 2–4 days, **L** ≈ 1–2 weeks, **XL** > 2
weeks. Each package is sized for one agent, owns its own files, and covers both ISAs unless it
says otherwise. Every decoder package includes the oracle work (targeted `gen` specs, 0 MISMATCH)
and one proved example per ISA it touches.

| package | content | owns | size | depends on |
|---|---|---|:-:|---|
| **N1a** | `sync.Pool` contract: `PoolModel` (abstract pooled values, GC may drop), `PoolGetContract`/`PoolPutContract` on both ISAs, the pool invariant and its preservation lemmas, a `*Sat` witness, an example (`Get`/use/`Put` in a deferred call) proved on both ISAs | `Janus/Contracts/Pool*.lean`, `examples/basic/pool.go`, proofs | M | integ merge (Panic/defer contracts) |
| **N1b** | Pinning for non-runtime std functions: `stdContractStubs` (`sync.(*Pool).Get`/`Put`, `sync.(*Once).doSlow`, …) checked by pclntab file and code hash; `gen-stubpins.sh` over `sync`; `identity.json` `"pinned"` | `cmd/janus/extract.go` (contract part), `cmd/janus/stubpins_gen.go`, `scripts/gen-stubpins.sh` | S | – |
| **N1c** | `sync.Once` single-threaded: `Do`'s fast path executes; contract for `doSlow` (runs `f` once through its funcval, then marks `done`), using the dynamic-call hypotheses | `Janus/Contracts/Once*.lean`, example | S–M | N1b |
| **N1d** | `sync.Mutex`/`RWMutex` uncontended: the inlined fast paths execute (atomics, already modelled); contracts that `lockSlow`/`rUnlockSlow`/`SemacquireRWMutexR` are never reached when the lock state is unlocked, and that a contended call does not return (so a theorem about single-threaded code shows it is unreachable) | `Janus/Contracts/Mutex*.lean`, example | M | N1b |
| **N2** (**done**, agent/cover: `F3`/`F2` before `C3` and `C2 imm16` decode as `RET`; `edge/repret` oracle family, 0 MISMATCH over 1,017,804 cases; `JanusX86.Proofs.Call.ret_agree` without `p.rep = 0`; example `CRepRet`; the same prefixes on `JMP`/`CALL` are not done: the measured gap is `RET` only) | amd64 `REP RET`/`BND RET` and the ignored legacy prefixes on near `RET`/`JMP`/`CALL` (Intel SDM: `F3`/`F2` have no effect there), oracle on hardware | `Janus/Amd64/Decode.lean` (prefix rule), `oracle-amd64/gen` spec | S | integ merge |
| **N3** | arm64 PAuth and BTI: `PACIASP`/`PACIBSP`/`AUTIASP`/`AUTIBSP`/`PACIAZ`/…, `XPACLRI`, `RETAA`/`RETAB`, `BTI {c,j,jc}`. PAC as an environment-keyed function `pac k ptr mod` (the keys are a state field; theorems quantify over them); `AUT` gives the original pointer iff it was produced by `pac` with the same key and modifier, otherwise a non-canonical pointer (FEAT_FPAC: a fault). `BTI` as a `NOP` for binaries without the GNU BTI property (static Go binaries), recorded in SOUNDNESS.md | new `Janus/Arm64/PAuth.lean`, hook in `Janus/Arm64/Decode.lean`, `oracle/gen` `pauth` (qemu `-cpu max`), docs/SOUNDNESS.md | M | integ merge |
| **N4** | `Summary.inductionFamily`: strong induction over a measure for a finite family of entries `[(entry_i, pre_i, post_i)]`, `ih` providing every summary of the family at smaller measure; both ISAs; example: two mutually recursive Go functions | `Janus/Tactic/Recursion.lean`, `Janus/Amd64/Recursion.lean`, example | S | – |
| **N5** (**done**, agent/cover: `EnvReg.idreg`, `Kern.idregOK`, arbitrary result, examples `AESField` and `SVEField` with witnesses; arm64 oracle updated but not run: no arm64 host) | arm64 `MRS` of `ID_AA64ISAR0/1/2_EL1`, `ID_AA64PFR0/1_EL1`, `ID_AA64ZFR0_EL1`, `ID_AA64MMFR*_EL1` as environment values (kernel-emulated at EL0: the value is what the kernel reports, a theorem parameter), like integ/wave1's `MIDR_EL1` | the `MRS` part of `Janus/Arm64/Decode.lean`/`Exec.lean`, `Janus/Contracts/Misc.lean`, oracle | S | integ merge |
| **N6** | `GlobalInit`: the extractor records the initial bytes of each referenced writable `.data`/`.noptrdata` object (zero for `.bss`) as `Extracted.dataInit`; a precondition predicate and a `janus_run` lemma that resolves loads from it | `cmd/janus/extract.go` (data part), `Janus/Program.lean`, `Janus/Amd64/Program.lean`, docs/CLI.md | S | – |
| **N7** | Pin `makeslice`, `newobject`, `growslice` and its variants, `gcWriteBarrier1..8`, the `Slice.lean`/`String.lean` entry points: add them to `runtimeContractStubs`, regenerate `stubpins_gen.go` for go1.26.0/.5/.8/.10 | `cmd/janus/extract.go` (lists), `cmd/janus/stubpins_gen.go` | S | integ merge |
| **N8a** | `blockers` amd64 sweep: share the coverage tool's sweep (`VZEROUPPER` length fix, VEX/EVEX lengths, `0F 38`/`0F 3A` fallbacks), regression test on `memmove` and `addMulVVWW` | `cmd/janus/blockers.go` | S | – |
| **N8b** | Dynamic-target inference: restrict inferred function addresses to those whose `LEA`/`ADRP+ADD` result reaches a call or a stored funcval in the same function, or report why each target was added (`identity.json` `dynamicTargets[].reason`) | `cmd/janus/dynamic.go` | S | – |
| **N8c** | Coverage tool: (1) the `runtime` stage credits names written without `runtime.` in the contract files' tables and doc comments (and `gcWriteBarrierN`); (2) the `insn` stage handles externally linked cgo binaries (pclntab text base); (3) `coverage.sh` default `BRANCHES`, and a `-decode-set` option so main and a branch can be compared in one run | `scripts/coverage/*.go`, `scripts/coverage.sh` | S | – |
| **N8d** | Add the application corpus to `scripts/coverage.sh` (an optional `app` stage: a pinned third-party module built `CGO_ENABLED=0`, plus its cgo objects from `go build -work`), and re-baseline COVERAGE.md after the merge | `scripts/coverage.sh`, docs/COVERAGE.md | S | N8c, integ merge |
| R7 | Stack growth (unchanged from COVERAGE.md §6) | | XL | |
| R8 | `print`/`println` over the `write(2)` contract | `Janus/Contracts/Print.lean` | S–M | integ merge |
| R9′ (**done for** `KeepAlive`, `fadd64`, `fsub64`, `fmul64`, `fdiv64`: contracts on both ISAs, IEEE where the exact result is not tiny, tested against the real runtime, pinned, `_satisfiable`, examples `SoftAdd`/`SoftMul`/`SoftDiv`/`KeepAlive`; `morestackc` and `f64to32` open) | `KeepAlive`, `morestackc` (as a fault: `morestack` on the system stack), soft-float `f64to32`/`fadd64`/`fmul64`/`fdiv64` proofs against `Janus.Spec.SoftFloat` | `Janus/Contracts/Misc.lean`, `examples/rtmisc` | S | integ merge |

**Order.** Merge integ/wave1 first. Then, in parallel: N1b, N4, N6, N8a–c (no merge needed); N2,
N3, N5, N7, R8, R9′ (after the merge). N1a, N1c and N1d follow N1b. N8d comes last, to re-baseline.
After N2, N3 and N5, every function of every corpus measured here decodes on integ/wave1 + N, so
the decoder work is done for this corpus mix. The next coverage measurement should add more
hand-written-assembly libraries, which is where every new blocker in this round came from.

## 5. What did not change

Concurrency stays excluded: the 12 channel/select/goroutine entry points, `WaitGroup`, `Cond`, and
contended locks. With the store-exclusive model of integ/wave1, single-threaded `sync/atomic`
decodes everywhere. N1 adds contracts only for the uncontended, single-goroutine behaviour of
`sync`.

## 6. Reproducing

```sh
# decoders: main from this worktree, integ/wave1 copied from its build (read-only)
LEAN_NUM_THREADS=4 lake build janus-decode janus-oracle-amd64
(cd scripts/coverage && GOWORK=off go build -o "$T/covtool" .)

# std corpus (arm64; amd64-v1/-v3 likewise with CONFIGS)
CONFIGS=arm64 WORK="$T/stdwork" OUT="$T/out" JOBS=2 KEEP=1 scripts/coverage.sh build
for set in main integ; do
  "$T/covtool" insn -arch arm64 -j 2 -cache "$T/vcache-$set-arm64.txt" \
    -decode "$T/$set-bin/janus-decode" -model "$T/$set-bin/janus-oracle-amd64" \
    -json "$T/out/insn-arm64-$set.json" "$T/stdwork/arm64"/*.test
done

# runtime entry points against both branches
"$T/covtool" runtime -goroot "$(go env GOROOT)" -repo . -branches "origin/main integ/wave1" \
  -o "$T/out/runtime.tsv" -bins "arm64=$T/stdwork/arm64/*.test,amd64=$T/stdwork/amd64-v1/*.test"

# application: CGO_ENABLED=0 build per ISA, then `covtool insn` on the binary; its cgo objects:
CGO_ENABLED=1 CC=… go build -a -work <the cgo packages>   # copy $WORK/**/_x*.o, then `covtool insn -c`
```

The amd64 std passes take about 50 minutes per decoder set with `-j 2` (6.3 M distinct encodings
for v1, 10.6 M for v1 + v3); arm64 takes under a minute (1.04 M encodings). Measured 2026-10-26 on
a shared host (load 20–40).
