# The Sail (Arm ASL) oracle

`docs/ORACLE.md` tests `Janus.Arm64.step` against `qemu-aarch64`. qemu is an implementation,
not a specification. This second oracle runs the **same cases** on the **Sail arm-v9.4-a
model**, which rems-project translated automatically from Arm's official ASL (the 2023-03
Armv9.4-A release). It then reports three-way agreement: Janus vs Sail, qemu vs Sail, Janus vs qemu.

Nothing here re-implements the architecture. The instruction semantics, the EL0 state set-up
(each system register is written by stepping a real `MSR` in the model), the exception entry
and the page-table walk all come from Arm's pseudocode.

## Running it

```
scripts/oracle.sh full           # the qemu oracle: builds the corpus + qemu results (artifacts/oracle)
scripts/oracle-sail.sh run       # Sail driver + three-way report (artifacts/oracle-sail)
scripts/oracle-sail.sh smoke     # 18 hand-checked cases only
QEMU_OUT=artifacts/oracle-neon OUT=artifacts/oracle-sail-neon scripts/oracle-sail.sh run   # any qemu corpus, e.g. `oracle.sh neon`
scripts/oracle-sail.sh regen     # regenerate the Sail model from pinned sources (provenance)
scripts/oracle-sail.sh crosscheck  # regenerated model vs vendored model on the whole corpus
```

`run` copies `artifacts/oracle/{cases,hw}.jsonl`, runs the Sail model on every case (about 20 s
for 430k cases on 48 cores) and then uses the qemu oracle's own comparator three times. The whole
run takes about 2.5 minutes. The first build takes about 30 minutes, because the model is one 170 MB
C++ translation unit; later builds are incremental.

| file in `artifacts/oracle-sail/` | contents |
|---|---|
| `threeway.md` | pairwise tables, joint verdicts, **soundness section**, qemu-vs-Sail disagreements, fault-signal agreement |
| `soundness.jsonl` | every case where Janus succeeded with a result Sail does not produce (expected: empty) |
| `janus-vs-sail/` | `oracle run` output with hardware := Sail, model := Janus (`summary.md`, `verdicts.jsonl`, `repro.md` if any mismatch) |
| `qemu-vs-sail/` | hardware := qemu, model := Sail |
| `janus-vs-qemu/` | hardware := qemu, model := Janus (same corpus and Janus build, for the joint table) |
| `spalign/` | Sail-only corpus: SP-based loads/stores with a misaligned SP (qemu cannot check that) |
| `cases.jsonl`, `qemu.jsonl`, `janus.jsonl`, `sail.jsonl` | the frozen inputs and every side's raw results |

When `run` ends, the dumps are pruned (`scripts/lib/artifacts.sh`): the reports, `soundness.jsonl`,
each comparison's `summary.md`, `repro.*` and `mismatches.jsonl` stay; the four files above, every
`verdicts.jsonl` and `model.jsonl` are zstd-compressed (`.zst`); the comparisons' copies of the
corpus and the derived `sail-model.jsonl` / `cases.sail-dczid.jsonl` are removed (one full run
used to leave 8 GB). `KEEP=zst` compresses instead of removing, `KEEP=1` keeps everything raw.
`QEMU_OUT` may hold the compressed corpus of a pruned `scripts/oracle.sh` run; `crosscheck`
decompresses `cases.jsonl` and `sail.jsonl` for its comparison and removes the copies after.

Exit criterion: `soundness.jsonl` is empty, i.e. `janus-vs-sail` has 0 `MISMATCH`.

## What is reused

| piece | origin |
|---|---|
| ISA semantics | [rems-project/sail-arm](https://github.com/rems-project/sail-arm) `arm-v9.4-a`, Arm ASL translated to Sail (BSD-3-Clause-Clear) |
| single-step oracle around it | [yufengzjj/sail-aarch64-oracle](https://github.com/yufengzjj/sail-aarch64-oracle): Sail's C++ backend output of the model plus a harness (`step(opcode)` = `__DecodeExecute` + exception path, register/memory accessors) as a Rust crate with the generated model vendored |
| test cases, layout, result formats | the qemu oracle (`oracle/layout/layout.go`): `Case` in, `HW` out (plus extra fields Go ignores) |
| comparator, report, minimiser | the qemu oracle's `oracle run` / `oracle minimize` (`oracle/cmd/oracle`), run unchanged. The Sail driver is a drop-in `-runner`, or its results are replayed through `-reuse-native` / `-model` |
| Lean side | `janus-oracle` (`Oracle/Main.lean`); `State.dczid` comes from the case |

New code lives under `oracle-sail/` and in `scripts/oracle-sail.sh`. No file of the qemu oracle and
no Lean file is modified.

* `oracle-sail/src/main.rs`: the driver `janus-oracle-sail`. Supervisor plus worker processes; a
  Sail runtime assertion aborts only that case, which is reported as `status: error` with the
  assertion text.
* `oracle-sail/instrument_model.py`: adds two counters to the generated C++ (see
  "UNPREDICTABLE" below). It changes nothing else.
* `oracle-sail/threeway.py`: joins the three verdict files and tags known non-authoritative
  cases. `replay.py` serves precomputed results to `oracle run`. `smoke.py` holds the
  hand-checked cases. `spalign.py` generates the SP-misalignment corpus.

### Why this route

* **sail-aarch64-oracle** (chosen): it does exactly what is needed. It takes the full Sail
  arm-v9.4-a model and lets the caller set X0–X30/SP/PC/NZCV/PSTATE/memory, step one injected
  32-bit opcode through the model's own decoder, and read everything back, including the
  architectural exception path. It is self-contained (vendored model, patched Sail runtime), so
  it needs only Rust and a C++20 compiler. Execution is fast: about 20k cases/s on 48 cores.
* sail-arm's own C emulator (`elfmain.sail`) boots ELF images. It has no state-injection
  interface, so single-instruction cases would need a hand-written boot stub per case.
* **isla** executes the same Sail model, symbolically as well, but it is built for
  concurrency/litmus and symbolic traces. Concrete differential runs from an arbitrary
  register/memory state would need isla's snapshot build of the model plus a trace parser,
  which is more machinery with no extra authority. It stays the natural next step for
  *symbolic* checks: proving the Lean semantics of an instruction equal to the ASL for all
  inputs.

## Pinned versions

| dependency | pin |
|---|---|
| sail-aarch64-oracle | git `2dffc81de96705d087b72a57047dd4589c6fb548` (crate 0.2.0; `oracle-sail/Cargo.toml`, `Cargo.lock`) |
| vendored model | `vendor/model.cpp.gz` sha256 `64e3a929…a6ae5` (checked by the script); unpacked `model.cpp` sha256 `06e9a6e1…cdbc`, `model.h` `4f7cda2c…a5`, `model_missing.cpp` `88ad0c13…26`. The crate generated it with Sail 0.20.1 from sail-arm master (2026-06) |
| sail-arm (for `regen`) | `f5bf6c3a2b5df8c7f6f9d3572825ff074e0c6b7c`, the last `arm-v9.4-a` source change before the crate vendored its model. The only later source change (`7d05816`, `prelude.sail`) is a Lean-extraction annotation |
| Sail (for `regen`) | opam `sail.0.20.1`, OCaml `ocaml-base-compiler.5.2.1`, opam 2.5.0, z3 4.13.3 |
| Rust deps | `serde =1.0.228`, `serde_json =1.0.145`; full graph in `oracle-sail/Cargo.lock` (`cargo build --locked`) |
| toolchain used | rustc/cargo 1.99.0, g++ 15.2.0, libgmp 6.3.0 (`system-gmp` feature), Go 1.26.0, Lean 4.34.1; qemu reference 10.2.1 |

All external sources go to `DEPS` (default `/srv/janus-sail-deps`): the crate clone, the
sail-arm worktree, the opam root, and the unpacked and instrumented model copies.

## How to rebuild

```
scripts/oracle-sail.sh build                       # vendored model (default)
scripts/oracle-sail.sh regen && SAIL_MODEL=regen scripts/oracle-sail.sh build   # from source
```

`build` unpacks `vendor/model.cpp.gz` once to a stable path, instruments it, and builds with
`AARCH64_ORACLE_SAIL_MODEL_C` pointing there. The crate's default path re-unpacks the model
into `OUT_DIR` on every build-script run, and its `rerun-if-changed` on that fresh file makes
cargo recompile the 170 MB unit on every build. `regen` installs opam + Sail 0.20.1, checks out
sail-arm at the pin and runs the crate's README Step 2 command. It passes `--c-preserve` for *every*
function in `harness.sail`; the README lists only 8, but all of them are needed. It then runs
the crate's mandatory `fix_cpp_model.py`. `crosscheck` builds a second driver on the
regenerated model and diffs its results on the whole corpus.

Provenance status: the regenerated C++ is **not byte-identical** to the vendored copy. It is
244 MB vs 173 MB, the function count differs by 14, and some trivial bodies are emitted
differently, so the crate author's Sail build differed in detail. Semantic equality is checked
by `crosscheck` instead (result below).

## The EL0 state

Every case starts from the crate's reset state (EL3, AArch64). The driver steps `MSR`s through
the model, so their side effects are Arm's own, and then an `ERET` into EL0t at `TestPC`:

| register | value | why |
|---|---|---|
| `SCR_EL3` | NS, RW, APK, API, ATA, EnSCXT, HXEn, EnTP2; SMD = 0, HCE = 0, FGTEn = 0 | Non-secure, AArch64 below, PAuth/MTE/MOPS usable as on a Linux host. HVC is UNDEFINED. SMC is used to get back to EL3 between cases |
| `HCR_EL2` | RW, APK, API | EL1 AArch64, no stage 2, no traps (Linux not under a hypervisor) |
| `HCRX_EL2` | MSCEn | FEAT_MOPS usable at EL0 |
| `CPTR_EL2`, `MDCR_EL2`, `HSTR_EL2` | no traps | |
| `SCTLR_EL1` | Linux `INIT_SCTLR_EL1_MMU_ON` (M C SA **SA0** SED EOS I DZE UCT nTWE TSCXT IESB EIS SPAN UCI nTLSMD LSMAOE ITFSB EPAN), + EnIA/EnIB/EnDA/EnDB, ATA0, MSCEn; **A = 0**, nAA = 0, nTWI = 0 | Linux alignment rules: no general alignment checking, SP alignment checked at EL0, LSE2 16-byte rule for atomics/exclusives |
| `TCR_EL1` | T0SZ = T1SZ = 16, 4K granules, WBWA inner-shareable walks, IPS 48-bit, **TBI0 = 1**, TBI1 = 0, EPD1 = 1 | Linux 48-bit VA with top-byte-ignore for user addresses |
| `MAIR_EL1` | Attr0 = 0xFF (Normal WB) | |
| `TTBR0_EL1` | 4-level identity map of exactly two pages | see below |
| `CPACR_EL1` | FPEN = ZEN = SMEN = 3 | Linux enables FP/SVE/SME lazily, invisibly to the program |
| `ZCR_EL1.LEN` = 3, `SMCR_EL1.LEN` = 1 | VL 512, SVL 256 | Linux/qemu-user default vector lengths |
| `SPSR_EL3` | 0 (EL0t, DAIF clear) | |
| local monitor | `CLREX` | as the qemu runner does |

The MMU is **on**. With stage 1 off, EL0 data accesses are Device-nGnRnE and every unaligned
access faults, which is not what Linux user code sees. The identity map has the code page
(user RWX, as the runner's `mmap`) holding the word at `TestPC` with `UDF #0` everywhere else,
and the data buffer (user RW, UXN) holding `Pattern(seed, i)`. Nothing else is mapped.
Instruction fetch is not modelled: the crate injects the opcode.

A synchronous exception is taken to EL1 (vector base 0). The driver reads `ESR_EL1`, `FAR_EL1`,
`ELR_EL1`, `SPSR_EL1` and `SP_EL0` with `MRS` and maps them to the signal Linux would deliver,
which is what the qemu runner observes:

| ESR | signal / si_code / si_addr |
|---|---|
| EC 0x00 (UNDEFINED), 0x0E, 0x18, 0x0D (BTI), 0x0A (LS64), 0x27 (MOPS) | SIGILL / ILL_ILLOPC / pc |
| EC 0x1C (FPAC) | SIGILL / ILL_ILLOPN / pc |
| EC 0x24 translation / address-size | SIGSEGV / SEGV_MAPERR / untagged FAR |
| EC 0x24 access-flag / permission | SIGSEGV / SEGV_ACCERR / FAR |
| EC 0x24 alignment (DFSC 0x21) | SIGBUS / BUS_ADRALN / FAR |
| EC 0x26 SP alignment | SIGBUS / BUS_ADRALN / SP |
| EC 0x3C BRK | SIGTRAP / TRAP_BRKPT / pc |
| EC 0x01 WFI | not a fault: Linux's `wfi_handler` skips it, so status ok, pc + 4 |

Without an exception, the status is decided by the *next* fetch, exactly as in the runner:
`selfloop` (pc = `TestPC`), SIGILL in the code page, SIGBUS for a misaligned pc, otherwise
SIGSEGV at pc. Between cases the driver steps `SVC` (EL0 to EL1) and `SMC` (EL1 to EL3) and
re-runs the whole set-up. It zeroes FPCR/FPSR/TPIDR*/Z/P/FFR, then writes the case's `V0`–`V31`
into the low 128 bits of `Z0`–`Z31` (the rest stays zero, as after any Advanced SIMD write) and
its `TPIDR_EL0`, and reports `V0`–`V31` (the low 128 bits of `Z0`–`Z31`) after the step. A fresh model instance per case
(`SAIL_FRESH=1`) gives byte-identical results.

## What Sail does *not* settle (tags in `threeway.md`)

Some outcomes in the model are stubs or implementation choices, not Arm's ASL. They are tagged
and must not be read as "the architecture says so":

* **`sail-monitor-stub`**: sail-arm implements `IsExclusiveLocal/Global` as `true` and
  `ClearExclusiveLocal` as a no-op, so every store-exclusive *succeeds* (status 0, memory
  written). After `CLREX`, real hardware and qemu fail it (status 1, no store). For the same
  reason the model always performs the access, so alignment and translation faults on
  `STXR/STLXR/STXP` appear where qemu reports a failed store. The ASL order (alignment check
  first) is Arm's; whether aborts are detected before the monitor check is IMPLEMENTATION
  DEFINED.

  Since Janus models the store-exclusives (docs/SOUNDNESS.md), Janus-vs-Sail runs `janus-oracle
  --monitor-stub`: before each store-exclusive the model's monitor is set to mark exactly that
  store's bytes, which is the stub's view, so "pass" is among the model's outcomes (`alts`, see
  docs/ORACLE.md "Nondeterministic outcomes"), and the comparator requires Sail's result to be
  one of them. That checks the data path, the status register, register overlaps, alignment and
  faults of every store-exclusive against Arm's ASL. The parts the stub cannot judge (the Open
  Access state fails; a store-exclusive to the marked bytes opens the monitor) are checked against
  qemu only, where the corpus contains them deterministically (`gen/seq.excl`). Sequence-mode
  cases (field `words`) are stepped by the driver until the PC leaves the block, like the qemu
  runner.
* **`sail-unpredictable`**: sail-arm stubs `ConstrainUnpredictable*()` with
  `__UNKNOWN_*()`, which is deterministically the first enum value (`Constraint_NONE`), and the
  crate's `step_a64` turns `Error_Unpredictable` into UNDEFINED. `instrument_model.py` counts
  calls to `ConstrainUnpredictable{,Bits,Integer}` and `Error_Unpredictable` constructions while the
  instruction under test runs, and the driver emits `"unpredictable": n`. The Bool/Procedure
  variants are inlined by Sail's optimiser and cannot be counted; in A64 they occur only in
  SVE, debug and translation code. After such a case the instance is discarded.
* **uncaught model exceptions** (`status: error`): `Error_ConstrainedUnpredictable`,
  `Error_ImplementationDefined`, `Error_ReservedEncoding` and `Error_SError` are caught by no
  handler on the A64 path, so the step returns half-done. A second counter detects this. The
  case is reported as an error, never as a result, and the instance is discarded. Sail runtime
  assertions abort the worker (MOPS size stubs at `instrs64.sail:9007`/`9719`; `LDRAA` with
  writeback and `Rn == Rt`). Such a case is likewise an error.
* **`sbo-unpredictable`**: load/store-exclusive and ordered encodings whose "(1)"
  (should-be-one) Rs/Rt2 fields are not all ones. Arm: CONSTRAINED UNPREDICTABLE. sail-arm's
  decode patterns hard-code the ones, so these are UNDEFINED there (one permitted choice); qemu
  ignores the fields.
* **`mops-impdef`**: `CPY*`/`SET*`. The crate fixes the IMPLEMENTATION DEFINED options
  (option A; the prologue processes 0 bytes), and qemu chooses differently. Only the final
  memory state is comparable.
* **`impdef-dczid`**: `MRS Xt, DCZID_EL0`, `DC ZVA`, `DC GVA`, `DC GZVA`. `DCZID_EL0` is
  IMPLEMENTATION DEFINED (qemu `-cpu max` 7, the Sail model 8), so qemu and Sail legitimately
  differ. Janus is compared with each one using that reference's own value.
* **`sysreg-read`**: `MRS` of other system registers at EL0. Linux and qemu-user emulate reads
  of the ID registers; Sail applies the ASL trap rules for this EL0 configuration. Janus rejects
  these reads.
* **`pauth-keys`**: PAC/AUT/XPAC/PACGA/LDRA*/BRA*. The results depend on the keys (the model's reset
  values, random per process in qemu-user) and on FEAT_FPAC, which Sail implements: a
  failed `AUT*` faults (SIGILL/ILL_ILLOPN) where qemu returns a poisoned pointer.
* **`qemu-lacks-feature`**: Sail implements all of v9.4 (for example FEAT_THE `RCW*`,
  FEAT_LRCPC3 `LDIAPP`), while qemu 10.2's `max` CPU raises SIGILL on these.
* **`qemu-process-memory`**: the address is mapped in the qemu runner process (for example
  `0x10000`, the runner's text), so qemu loads from it. Sail maps only the two test pages.
* Fault *addresses*: Sail reports the exact faulting address (FAR, then Linux's
  `untagged_addr`: bits 63:56 := bit 55). qemu-user rounds si_addr down (for example
  `0x1000041003` becomes `0x1000041000`) and reports 0 for addresses outside its guest space.
  The comparator does not compare fault kinds or addresses; `threeway.md` lists the
  signal/si_code pairs separately.
* Not modelled: instruction fetch (so no instruction aborts and no BTI landing checks), the
  kernel half of the address space (EPD1), interrupts, and the global monitor. RNDR is
  nondeterministic.

None of these can hide a Janus soundness bug as an "agree". They only produce `model-gap`
or MISMATCH noise between qemu and Sail, or `error` cases, which are excluded.

## Results with the exclusive monitor (2026-10-25, 789,635 cases)

The full qemu corpus of `scripts/oracle.sh full` after the store-exclusives were modelled
(including the 20,000 `gen/seq.excl` blocks and the 1,752 cases of the harvested LL/SC loops, run
in sequence mode by the driver), Janus with `--monitor-stub`:

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| Sail (hw) vs Janus (model) | 755,121 | **0** | 34,501 | 13 | 0 |
| qemu (hw) vs Sail (model) | 773,667 | 14,837 | 1,118 | 1 | 12 |
| qemu (hw) vs Janus (model) | 749,746 | **0** | 39,888 | 1 | 0 |

`soundness.jsonl` is empty. The exclusive classes, Janus vs Sail: `gen/seq.excl` 19,369 agree
(17,329 of them with an alternative, i.e. a passing, outcome) and 631 model-gaps
(`unpredictable` and `unaligned`); `harvest/seq.excl` 1,752 agree (all through the passing
outcome); `gen/ls.excl` 3,823 agree, 177 model-gaps; `harvest/ls.excl` 1,938 agree, 120
model-gaps. The 11,696 qemu-vs-Sail MISMATCHes of the exclusive classes are the
`sail-monitor-stub` cases: qemu fails a store-exclusive with the monitor open, as the Arm ARM
requires, and the stub passes it. Janus agrees with both: with qemu on the failure (no
`--monitor-stub`), with Sail on the pass (`--monitor-stub`).

## Results with the Advanced SIMD classes of `NeonInstr` (2026-10-25, 653,793 cases)

`QEMU_OUT=artifacts/oracle-neon OUT=artifacts/oracle-sail-neon scripts/oracle-sail.sh run` on the
corpus of `scripts/oracle.sh neon` (targeted NEON classes, random groups, the C and Go harvests,
and 50,000 sequence-mode blocks). The driver now runs sequence-mode cases too: with `words`, it
lays the block out from `TestPC` and steps the model while the PC stays inside it at EL0 (one
step per word plus one), then reports like a single step.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| Sail (hw) vs Janus (model) | 638,122 | **0** | 15,637 | 34 | 0 |
| qemu (hw) vs Sail (model) | 652,740 | 231 | 788 | 0 | 34 |
| qemu (hw) vs Janus (model) | 637,430 | **0** | 16,363 | 0 | 0 |

`soundness.jsonl` is empty. The 34 unobserved cases are Sail errors on MOPS and PAuth words of
the random groups (tags `mops-impdef`, `pauth-keys`). The qemu-vs-Sail disagreements are the
known ones (store-exclusives with the monitor stub, MOPS, features qemu lacks, process memory)
plus one new: the vector `FABS`/`FNEG` under `FPCR.AH = 1` with a NaN lane (29 single-step cases
and 3 sequences), where Sail leaves the NaN unchanged, as the ASL `FPAbs`/`FPNeg` say, and qemu
10.2.1 changes its sign. Before the model faulted there, Janus followed the ASL and agreed with
Sail on all 33 cases that qemu disagreed on; it now faults (`trapped`) on that corner, so both
pairs are 0 MISMATCH. The Sail-only SP-misalignment corpus (2,680 cases) is 0 MISMATCH as well.

## Results with the crypto extension, CRC32 and permutes (2026-10-25, 389,440 cases)

The crypto corpus of `docs/ORACLE.md` (`scripts/oracle.sh crypto`, then
`QEMU_OUT=artifacts/oracle-crypto OUT=artifacts/oracle-sail-crypto JOBS=8 scripts/oracle-sail.sh run`):
the generated and harvested SHA-1/SHA-256/SHA-512/SHA-3, PMULL, CRC32, permute and scalar-DUP
classes and 150,000 sequence-mode blocks. The driver now runs sequence cases: a case's `words`
are laid out in the code page and injected one at a time at the model's PC
(`oracle-sail/src/main.rs`, the crate has no instruction fetch) until the PC leaves the block, an
exception is taken or a Sail exception escapes; the final state is reported as for one step.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 385,790 | **0** | 3,650 | 0 | 0 |
| qemu vs Sail | 389,440 | 0 | 0 | 0 | 0 |
| qemu vs Janus | 385,790 | 0 | 3,650 | 0 | 0 |

* **Soundness: 0 cases** (`soundness.jsonl` is empty). The 3,650 gaps are the SM3/SM4 words
  (`undecodable` in Janus), which qemu and Sail execute identically.
* **qemu and Sail agree on every case**, including all 150,000 multi-instruction blocks (chains of
  SHA256H/H2/SU0/SU1, SHA512H/H2/SU0/SU1, EOR3/RAX1/XAR/BCAX, PMULL/EXT/AESE, CRC32*, ZIP/UZP/TRN/TBL
  and windows of the real Go kernels), so the ASL these instructions are transcribed from and qemu's
  implementation agree on this corpus.

## Results with scalar floating point (2026-10-24, 1,131,099 cases)

The floating-point corpus of `docs/ORACLE.md` (`scripts/oracle.sh fp`, then
`QEMU_OUT=artifacts/oracle-fp OUT=artifacts/oracle-sail-fp scripts/oracle-sail.sh run`). The
driver now writes each case's `FPCR` and `FPSR` by stepping real `MSR FPCR`/`MSR FPSR`
instructions at EL0 (and refuses a case whose `FPCR` does not read back), and reports both after
the step; the comparator compares them with the registers. The model implements FEAT_AFP
(`FEAT_AFP_IMPLEMENTED = true`), so `FIZ`, `AH` and `NEP` are live, as on qemu.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 993,577 | **0** | 137,522 | 0 | 0 |
| qemu vs Sail | 1,131,099 | 0 | 0 | 0 | 0 |
| qemu vs Janus | 993,577 | 0 | 137,522 | 0 | 0 |

* **Soundness: 0 cases** (`soundness.jsonl` is empty). Every gap is `undecodable` (half
  precision, BFCVT, FRINT32/64, FJCVTZS, fixed-point conversions, the CONSTRAINED UNPREDICTABLE
  forms), and in each of them qemu and Sail agree with each other.
* **qemu and Sail agree on every case**, results, `NZCV`, `FPSR` and `FPCR` included, in all four
  rounding modes and with `FZ`, `DN`, `FIZ`, `AH`, `NEP` set and clear, so the Arm floating-point
  behaviour the model transcribes (NaN selection, `FMADD`'s addend-first NaN rule, `FPCR.AH`
  tininess and flushing, `FMAX`/`FMIN` with `AH`, saturating conversions, `NEP` merging) is
  confirmed by both references. The 137,015 cases where both fault agree on the signal
  (`SIGILL`/`ILL_ILLOPC`).

The regression corpus of `scripts/oracle.sh full` with the floating-point model (766,650 cases,
`fp.*` classes included):

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 731,764 | **0** | 34,872 | 14 | 0 |
| qemu vs Sail | 761,460 | 4,163 | 1,012 | 1 | 14 |
| qemu vs Janus | 730,803 | 0 | 35,846 | 1 | 0 |

Soundness: 0 cases. Every qemu-vs-Sail non-agreement carries one of the tags below
(`sail-monitor-stub`, `pauth-keys`, `sbo-unpredictable`, `qemu-process-memory`, `mops-impdef`,
`impdef-dczid`, ...); none is in an `fp.*` class.

## Results with Advanced SIMD (2026-10-23, 584,412 cases)

Corpus of `scripts/oracle.sh full` after the Advanced SIMD extension (cases carry `V0`–`V31` and
`TPIDR_EL0`; harvest includes the SIMD&FP words; new classes `vls.*`, `simd.*`). Janus against
Sail uses `State.dczid` = 8 as before.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 569,721 | **0** | 14,686 | 5 | 0 |
| qemu vs Sail | 579,343 | 4,071 | 990 | 3 | 5 |
| qemu vs Janus | 568,770 | 0 | 15,639 | 3 | 0 |
| Sail vs Janus, `spalign` (Sail-only) | 103,000 | **0** | 0 | 0 | 0 |

* **Soundness: 0 cases** (`soundness.jsonl` is empty). Janus's gaps against Sail: 14,235
  `undecodable`, 334 `unaligned`, 87 `noCode`, 30 `outsideAllocation`.
* The SIMD&FP classes against Sail (same grouping as in `docs/ORACLE.md`):

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
| vls.multi | 4517 | 369 | 3769 | 666 | 82 | 0 | 0 | 4227 |
| vls.pair | 6911 | 990 | 5292 | 1246 | 373 | 0 | 0 | 6251 |
| vls.regoff | 4419 | 306 | 2435 | 1984 | 0 | 0 | 0 | 4212 |
| vls.single | 4303 | 33 | 2324 | 1979 | 0 | 0 | 0 | 4268 |
| vls.uimm | 9265 | 4224 | 7138 | 2127 | 0 | 0 | 0 | 6447 |
| **total** | 86440 | 7857 | 62209 | 22170 | 2061 | 0 | 0 | 77413 |

* **qemu vs Sail**: every non-agreement carries one of the existing tags. In the modelled SIMD&FP
  classes the only non-agreements are 3 model-gaps (an `LD1`/`LDR` that qemu served from its own
  process memory); the rest are unmodelled `vls.other` words (`STLUR`/`LDAPUR` SIMD&FP, MOPS)
  under the existing tags. A first run
  showed 34 `WFI` cases where the driver did not report the vector registers on its "WFI
  trapped and skipped" path; fixed in `oracle-sail/src/main.rs`.

## Results with the atomics / DC ZVA extension (2026-10-23, 486,463 cases)

Corpus of `scripts/oracle.sh full` after the single-threaded atomics model was added (harvest
now includes `go test -c` of `sync/atomic` and `runtime`, and the classes `sys.mrs` and `sys.sys`).
`DCZID_EL0` is IMPLEMENTATION DEFINED and differs between the references (qemu 7, Sail 8):
`scripts/oracle-sail.sh` reads Sail's value with one `MRS` and runs Janus against Sail with
`State.dczid` = 8 (`cases.sail-dczid.jsonl`), and against qemu with 7.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 475,993 | **0** | 10,456 | 14 | 0 |
| qemu vs Sail | 480,628 | 4,815 | 1,005 | 1 | 14 |
| qemu vs Janus | 475,022 | 0 | 11,440 | 1 | 0 |
| Sail vs Janus, `spalign` (Sail-only) | 102,455 | **0** | 0 | 5 | 0 |

* **Soundness: 0 cases** (`soundness.jsonl` is empty). Janus's 10,456 gaps against Sail are
  9,935 `undecodable`, 385 `unaligned` (Sail implements FEAT_LSE2: misaligned ordered/atomic
  accesses inside 16 bytes succeed), 107 `noCode`, 29 `outsideAllocation`.
* The new instructions against Sail (same grouping as in `docs/ORACLE.md`):

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
| LDXP/STXP | 583 | 0 | 0 | 320 | 263 | 0 | 0 | 582 |
| LDXR/LDAXR | 1083 | 396 | 710 | 328 | 45 | 0 | 0 | 785 |
| MRS DCZID_EL0 | 1988 | 3 | 1988 | 0 | 0 | 0 | 0 | 32 |
| PRFM (literal) | 1169 | 0 | 1169 | 0 | 0 | 0 | 0 | 1153 |
| PRFM/PRFUM | 855 | 0 | 602 | 253 | 0 | 0 | 0 | 854 |
| STXR/STLXR | 1072 | 471 | 0 | 257 | 815 | 0 | 0 | 756 |
| SWP | 1051 | 78 | 898 | 112 | 41 | 0 | 0 | 999 |
| **total** | 18126 | 2640 | 13224 | 3397 | 1505 | 0 | 0 | 11771 |

  `MRS DCZID_EL0` and `DC ZVA` agree on every successful case with Sail's 1 KiB blocks, as they
  do with qemu's 512-byte blocks. Store-exclusives succeed in Sail (`sail-monitor-stub`) and
  fail on qemu; Janus rejects them, so both are gaps.
* **qemu vs Sail**: every non-agreement carries a tag. New ones: `impdef-dczid` (3,519: `MRS
  DCZID_EL0` returns 7 vs 8, and `DC ZVA`/`DC GVA`/`DC GZVA` zero 512 vs 1024 bytes) and
  `sysreg-read` (15: `MRS` of other registers, which Linux/qemu-user emulate and Sail traps; Janus
  rejects them all). The rest as before: `sail-monitor-stub`, `sbo-unpredictable`, `pauth-keys`,
  `qemu-process-memory`, `qemu-lacks-feature`, `mops-impdef`.

## Earlier results (2026-10-23, corpus of `scripts/oracle.sh full`: 427,845 cases)

Janus = `janus-oracle` built 13:55 (git `665fb69` + working tree); qemu = `artifacts/oracle/hw.jsonl`
(qemu 10.2.1, `-cpu max`); Sail = vendored model, instrumented.

| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |
|---|---:|---:|---:|---:|---:|
| **Sail vs Janus** | 409,378 | **0** | 18,460 | 7 | 0 |
| qemu vs Sail | 425,255 | 1,285 | 1,297 | 1 | 7 |
| qemu vs Janus | 408,119 | 0 | 19,725 | 1 | 0 |
| Sail vs Janus, `spalign` (Sail-only) | 90,190 | **0** | 260 | 0 | 0 |

* **Soundness: 0 cases** where Janus succeeds with a state Sail does not produce, over
  427,845 corpus cases and 90,450 misaligned-SP cases. Every one of Janus's 18,460 gaps is a
  conservative fault: 18,319 `undecodable`, 109 `noCode`, 32 `outsideAllocation`.
* **SP alignment is now confirmed, not just conservative**: in 83,200 `spalign` cases Sail
  takes an SP alignment fault (SIGBUS) exactly where Janus reports `spMisaligned`, and in none
  does Janus fault where Sail succeeds.
* **Joint verdicts**: 408,080 cases agree three ways. In 1,297, Janus and Sail both fault where
  qemu succeeds (should-be-one exclusives, PAC `AUT*` under FPAC, accesses to qemu process
  memory). In 1,285, Sail differs from qemu while Janus is conservative. No case has Janus and
  qemu agreeing on a success that Sail contradicts.
* **qemu vs Sail**: all 2,582 non-agreements carry a tag from the list above:
  `sail-monitor-stub` 1,334, `sbo-unpredictable` 824, `pauth-keys` 385, `qemu-lacks-feature` 17,
  `mops-impdef` 19, `qemu-process-memory` 10. The 7 model-errors are Sail assertion aborts
  (MOPS stubs, `LDRAA` writeback). The 1 unobserved is a qemu `escaped`. Signals agree on 40,378
  of 40,629 cases where both fault. The rest are the same tags (FPAC ILL_ILLOPN vs ILL_ILLOPC,
  SBO UNDEF vs qemu's alignment/translation fault, RCW alignment fault vs qemu SIGILL,
  qemu's read-only runner text giving SEGV_ACCERR vs MAPERR).
* **Provenance**: `crosscheck` gives byte-identical `sail.jsonl` from the model regenerated
  from sail-arm `f5bf6c3` with Sail 0.20.1 and from the crate's vendored model, on all 427,845
  cases.

## Found on the way

* qemu oracle comparator (`oracle/cmd/oracle/compare.go:142`): `d[:strings.IndexAny(d, ":[")]`
  panics on the `"... N more bytes"` line that is appended when more than 8 memory bytes
  differ. It never fires on Janus-vs-qemu, but does on qemu-vs-Sail. `scripts/oracle-sail.sh`
  builds the CLI from the unmodified sources with a `go build -overlay` replacement of that one
  line, applied only while the line is present. The proper fix belongs in `compare.go`.
* sail-aarch64-oracle: (1) the README's regeneration command preserves only 8 of the harness
  functions; (2) `build.rs` rebuilds the 170 MB model on every cargo invocation unless
  `AARCH64_ORACLE_SAIL_MODEL_C` is set; (3) `step_a64` does not catch
  `Error_ConstrainedUnpredictable` (301 throw sites in sail-arm), so such steps return
  half-executed with `have_exception` set; (4) `TCR_EL1.T1SZ = 0` (the reset value) makes
  `XPAC*` hit a model assertion. The EL0 set-up above avoids (4), and the driver detects (3).

## Split build (SAIL_SPLIT=1, the default)

The Sail model is one 170 MB C++ translation unit; g++ builds it serially (cold driver build 23-31 min wall, ~1450-1900 CPU s).
`scripts/oracle-sail.sh build` now cuts the instrumented model at top-level item boundaries into 48 translation units
(`oracle-sail/split_model.py`; every layout assumption is asserted, ghost temporaries stay with their users, the static type
helpers are replicated per unit) and builds them in parallel through a copy of the pinned crate whose only change is a
`build.rs` patch (`oracle-sail/build.rs.patch`, accepts `AARCH64_ORACLE_SAIL_MODEL_PARTS`; `oracle-sail/split_crate.py` makes
the copy, verifies it file by file against the pinned checkout and pins the original and patched `build.rs` SHA-256; the crate
is swapped in as a cargo directory source, so `Cargo.lock` and `--locked` are unchanged). Parsing the 40k-member `Model` class
costs g++ ~4 min (quadratic member lookup), so the patched `build.rs` precompiles it once (`-Werror=invalid-pch`: a PCH that is
not used is an error, not a silent slowdown) and compiles the units on `NUM_JOBS` threads (cc's `parallel` feature is off).
`SAIL_SPLIT=0` keeps the original single unit; `split_model.py`, `split_crate.py`, `build.rs.patch` and `SAIL_SPLIT` are in the
driver cache key. Measured (box load 20-40): cold build 8m14s wall / 2224 CPU s at 24 jobs, 8m57s / 1788 CPU s at 8 jobs, versus
31m10s / 1885 CPU s for `SAIL_SPLIT=0`. The split driver is bit-identical across job counts (sha256 d894a505...), differs from
the single-unit binary (as expected), and its output on the whole 486,460-case oracle corpus is byte-identical to the
single-unit driver's (sha256 78bb689b...).

Hardening (RTSAIL follow-up, `scripts/lib/test-splitcrate.sh`, `scripts/lib/test-cachecmp.sh`):

* `split_crate.py` compares the crate copy with the pinned checkout at every depth: `.git` and `target` are ignored only
  directly under the checkout's root (the copy has neither, so there they count), dotted names are compared, the
  executable bit is compared, directories are compared, and a symlink (file or directory) is an error.
* The model directories are re-hashed on every use, not only compared by mtime (`oracle-sail/dir_digest.py`): the
  instrumented `model.cpp`, `model.h` and `model_missing.cpp` carry `.inst-complete` (their SHA-256, the source model's and
  `instrument_model.py`'s); the parts directory carries `.complete` (SHA-256 of every part, `model.h`, `model_missing.cpp`,
  the instrumented model, `split_model.py`, the parts count). A mismatch regenerates from the source model; the unpacked
  vendored model is re-checked against the pinned archive and checkout. About 1 s per build. The patched `build.rs` also
  has `rerun-if-changed` on the parts directory, `model.h` and `model_missing.cpp` (patched `build.rs` pin changed).
* `artifact-hashes.json` records `config:SAIL_SPLIT` and `config:SAIL_SPLIT_PARTS`; `gate-cachecmp.py compare` reports a
  difference (or an unrecorded value) as a CONFIGURATION MISMATCH, exit 2, never as a P0 cache bug and never a pass;
  `nightly-cold-gate.sh` gives both runs the same explicit `SAIL_SPLIT`.
* The oracle corpus has almost no SVE, Advanced SIMD/FP or SIMD load/store words, so it says little about the Sail
  `__DecodeA64_SVE` and its neighbours. `oracle svegen` (oracle/gen/svesimd.go) draws, with a fixed seed, uniformly random
  words of the SVE, SME, SIMD&FP data-processing and SIMD load/store top-level groups; `scripts/oracle.sh quick|full` adds
  `SVESIMD_N` (default 800) per group, about 3.5k cases with ids from 30000000 (no existing case or expected output
  changes; Janus does not model SVE, so those are model-gaps; 0 MISMATCH on seeds 2, 3, 4, 5 against qemu). RTSAIL's
  131,100-case comparison of the split and single-unit drivers found them byte-identical.
