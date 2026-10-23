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
| `verdicts.jsonl` | one verdict per case (`agree` / `model-gap` / `MISMATCH` / ...) with diffs |
| `cases.jsonl`, `hw.jsonl`, `model.jsonl` | the inputs and both sides' raw outputs |

Knobs: `JOBS`, `N` (words per generated class), `K` (states per harvested word), `PER_CLASS`
(harvested distinct words per class), `SEED`, `QEMU` (set `QEMU=` on an arm64 host to run
the runner natively). After a model change you can skip the native side:
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
initial state: `X0`–`X30`, `SP`, `NZCV`, and a seed for the contents of a 4 KiB data
buffer. Everything is at fixed addresses, so a case is closed and deterministic:

| address | what |
|---|---|
| `0x10_0000_0800` (`TestPC`) | the instruction; every other word of its page is `0` (= `UDF #0`) |
| `0x10_0004_0000` (`DataBase`), 4096 bytes | the data buffer; byte `i` = `Pattern(seed, i)` |
| `0xF_F810_0000` / `0xF_F810_1000` | trampoline code / context page (127 MiB below, out of the way) |

everything else nearby is unmapped. The Lean side (`janus-oracle`) builds a `State` with
these registers, `pc = TestPC`, and `mem.regions = [⟨DataBase, 4096, writable⟩]` — exactly
the buffer, nothing else — and runs `Janus.Arm64.step word state`.

## How the native side observes one instruction

`oracle/cmd/runner` (Go, `GOARCH=arm64`) runs all cases of a shard in one process, without
landing pads or per-case subprocesses:

1. It writes the word at `TestPC`, refills the buffer, and calls a hand-assembled entry
   sequence that saves the host's callee-saved registers and SP, executes `CLREX`, loads
   `NZCV`, `SP`, `X0`–`X30` from the case and branches to `TestPC`.
2. Whatever the instruction does, the *next* thing that happens is a signal: falling
   through hits the `UDF` at `TestPC+4` (SIGILL); a branch lands on a `UDF` of the code page
   (SIGILL) or on an unmapped or non-executable page (SIGSEGV with `si_addr == pc`); a
   branch to a misaligned address raises SIGBUS/SIGSEGV at that address; an instruction that
   itself faults raises SIGILL/SIGSEGV/SIGBUS/SIGTRAP with `pc == TestPC`; a branch to itself
   spins until a watchdog thread sends SIGALRM (reported as `selfloop`, state = post-state).
3. A raw signal handler, installed with `rt_sigaction` (bypassing the Go runtime) and running
   on the thread's sigaltstack, copies `uc_mcontext` (`X0`–`X30`, `SP`, `PC`, `PSTATE`) into
   the context page and rewrites the saved PC to a resume sequence that restores the host
   registers and returns into Go.

So the captured state is precisely the architectural state after one instruction, and the
captured PC is where it went (fall-through, any branch target, or the instruction itself if
it faulted). The runner then reports registers, SP, NZCV, PC and the list of buffer bytes that
changed. `oracle selftest` checks this machinery against hand-computed answers (register and
flag preservation under all 16 NZCV values, loads, stores, guard faults, branches, self loops).

`GODEBUG=asyncpreemptoff=1` is required (the runner refuses to start without it): an
asynchronous-preemption signal arriving while the test instruction runs would enter the Go
handler with a foreign `g` register.

## Case generation

* **Harvested** (`harvest/<class>`): every distinct word of the executable sections of real Go
  arm64 binaries — a program using `math/big`, `crypto/sha256`, `sort`, `encoding/json`,
  `regexp`, `compress/flate`, ... (`oracle/harvest/bigprog`), `go test -c` binaries of
  `math/big strconv sort crypto/sha256 bytes strings`, and any `artifacts/*-arm64` — minus
  SIMD/FP and system encodings, capped per class (`PER_CLASS`) by uniform sampling, each under
  `K` random states.
* **Targeted** (`gen/<class>`): random encodings per class with fixed opcode bits and fields
  biased towards allocated encodings, plus a share of unallocated variants.
* **Group-random** (`rand/<class>`): fully random words inside each top-level encoding group
  (data-processing immediate / register, branches, loads/stores) — tests that the decoder
  rejects what it does not understand.

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
| succeeds | succeeds, identical `X0`–`X30`, `SP`, `NZCV`, `pc`, buffer bytes | **agree** |
| faults (any signal at `TestPC`) | faults (any `Fault`) | **agree** (fault kinds are not compared: `undecodable` vs SIGILL, `outsideAllocation` vs SIGSEGV, ...) |
| branches to a misaligned address | `pcMisaligned` | **agree** |
| succeeds | faults | **model-gap**: the model is conservative here. Fine when it is `undecodable` (not in the supported subset yet) or `outsideAllocation` for an access that hardware served from mapped non-buffer memory (e.g. a literal load from the code page) |
| succeeds | succeeds with any difference | **MISMATCH** — a soundness bug |
| faults | succeeds | **MISMATCH** — the model admits an execution hardware refuses |
| no clean observation (control escaped into other executable memory, harness error) | — | **unobserved** (excluded) |

MISMATCH is the headline number: a proof about Go code is only sound if the model never claims
a successful step that differs from the machine. Model gaps only cost coverage (a proof
would get stuck on a fault), never soundness.

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
  single `STXR` always fails (status 1, no store).
* **Memory outside the buffer.** The model only knows the buffer; the native process also has
  the code page and the Go runtime mapped. An access that lands on mapped non-buffer memory
  succeeds natively and faults in the model (model-gap), never the other way round.
* Only the 4 KiB buffer is compared byte by byte; a store that writes a byte equal to the
  pattern value already there is invisible (to both sides).
