# The amd64 differential oracle

The Lean x86-64 model (`Janus.Amd64.step`: decoder in `Janus/Amd64/Decode.lean`, semantics in
`Janus/Amd64/Exec.lean`) is in Janus's trusted base for amd64 proofs. The oracle tests it one
instruction at a time against the x86-64 host CPU itself. No emulator is involved.

## Results

For the final model (`Janus/Amd64/*`) on an Intel Xeon Gold 5412U host (Sapphire Rapids),
Linux with 5-level paging, Go 1.26.0:

| run | cases | agree | of which both fault | model-gap | **MISMATCH** | unobserved |
|---|---:|---:|---:|---:|---:|---:|
| `full`, `SEED=1` | 505,715 | 445,011 | 106,667 | 60,703 | **0** | 1 |
| `full`, `SEED=7` | 505,715 | 445,580 | 107,214 | 60,135 | **0** | 0 |
| **total** | **1,011,430** | 890,591 | | 120,838 | **0** | 1 |

`SEED=1`, broken down by case source:

| source | cases | agree | model-gap | MISMATCH |
|---|---:|---:|---:|---:|
| `harvest/*`: distinct instructions of real Go amd64 code, modelled classes | 154,209 | 154,121 | 88 | 0 |
| `harvest-other/*`: a sample of real instructions outside the subset (SSE arithmetic, AVX, AES, string ops, `CMPXCHG`, ...) | 3,906 | 1,297 | 2,609 | 0 |
| `gen/*`: targeted random encodings, about 90 classes | 253,200 | 209,013 | 44,187 | 0 |
| `edge/*`: hand-picked edge families (see below) | 54,400 | 50,594 | 3,806 | 0 |
| `rand/*`: random prefix/opcode/tail strings | 40,000 | 29,986 | 10,013 | 0 |

Model gaps by fault kind (`SEED=1`): `undecodable` 58,748 (encodings outside the subset, see below),
`undefinedResult` 1,103 (BSF/BSR of 0 at 16/32 bits, 16-bit SHLD/SHRD by more than 16),
`outsideAllocation` 667 (accesses the hardware served from mapped memory outside the buffer,
e.g. RIP-relative loads from the code page), `badTarget` 185 (branches to addresses `≥ 2^47`,
which are canonical on this 5-level-paging host). The per-class tables are in
`artifacts/oracle-amd64/summary.md` (and `summary-seed7.md`).

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
binaries, `GOAMD64=v1`) and `examples/basic`, `decode` accepts 99.60% of the 214,504 instruction
occurrences (99.21% of the 39,730 distinct encodings). The rest is scalar floating point
(`MOVSD/MOVSS/UCOMISD/CVT*`, ...), `MOVQ R14, FS:-8` (the TLS load in ABI wrappers: FS is never
modelled), `REP MOVSQ/STOSQ`, `XADD`/`CMPXCHG` and `RCR`. All of these fault as `undecodable`.

## Running it

```
scripts/oracle-amd64.sh selftest   # build, check the native harness on known answers (91 checks)
scripts/oracle-amd64.sh quick      # generated cases only (~100k)
scripts/oracle-amd64.sh full       # generated + edge + harvested from real Go binaries (default)
```

Knobs: `OUT` (default `artifacts/oracle-amd64`), `JOBS` (default 16, capped at 24), `N`
(encodings per targeted spec), `GROUP` (random strings), `K` (states per harvested
instruction), `PER_CLASS`, `SEED`, `MODEL` (`MODEL=oracle-amd64/bin/fakemodel` exercises the
pipeline without Lean). After a model change the native side can be reused:
`oracle-amd64/bin/oracle run -reuse-native -runner oracle-amd64/bin/runner -model .lake/build/bin/janus-oracle-amd64 -cases A,B -out DIR`.
`oracle minimize -out DIR` shrinks mismatching cases into `repro.md`/`repro.jsonl`. A full run
takes about 90 s, including the corpus build.

Pieces: `oracle-amd64/` (a separate Go module: `layout/` is the contract, `cmd/runner` the
native executor, `cmd/oracle` the gen/harvest/run/compare/minimize/selftest driver, `gen/` the
generators) and `Oracle/Amd64Main.lean` (the `janus-oracle-amd64` executable).

## What a case is

A case (`layout.Case`) holds the instruction bytes (1 to 15, hex) and a complete initial state:
the 16 GPRs, the six status flags, `XMM0`–`XMM15`, a seed for the 4 KiB data buffer, and
optional `init` byte overrides (used to plant return addresses and popped values). The
addresses are fixed:

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

1. The trampoline (`trampoline_amd64.s`) saves the host's callee state in the context page,
   loads `XMM0`–`XMM15` and the 16 GPRs, and enters `TestPC` with `IRETQ`. The `IRETQ` frame
   sets `RSP` and `RFLAGS` (the case's status flags plus **TF**) atomically with `RIP`.
2. With TF set, the CPU raises a single-step debug trap after **exactly one instruction**. That
   trap is a SIGTRAP with `si_code = TRAP_TRACE` and saved `RIP` = the next instruction:
   `TestPC + len` on fall-through, or the branch target on a taken branch, even an unmapped
   one, because the trap precedes the next fetch. An instruction that faults by itself raises
   SIGSEGV/SIGBUS/SIGILL/SIGFPE, or SIGTRAP for `INT3`/`INT1`, with saved `RIP` = `TestPC`
   (just after it for `INT3`). There is no fall-through-into-`INT3` guesswork and no watchdog:
   `JMP .` is observed as `ok` with `pc = TestPC`.
3. A raw signal handler is installed with `rt_sigaction`, bypassing the Go runtime, and runs
   on the thread's sigaltstack. It copies `uc_mcontext` (GPRs, `RIP`, `RFLAGS`) and the XMM
   registers from the signal frame's fxsave area into the context page. It then resets the
   frame's x87/SSE control state, clears TF/DF/AC and redirects the saved `RIP` to a resume
   sequence. That sequence restores the host registers (and `X15 = 0`, `R14 = g`) and returns
   into Go.

The runner reports `ok`, with every GPR, the status bits of `RFLAGS`, the XMM registers, `pc`
and the changed buffer bytes, or `fault`, or `escaped`/`error`. `oracle selftest` checks the
machinery against hand-computed answers: ALU flags, loads and stores, push/pop/call/ret,
branches, faults, `#DE`, `UD2`, self loops, SSE moves, and flag and register preservation under
all 64 combinations of the six status flags.

**Safety.** Random encodings run natively on a shared host, so the runner refuses case bytes
that contain system-call, segment-load, FP-environment-load or other system encodings
(`layout.Forbidden`: `SYSCALL`, `SYSENTER`, `INT n`, `MOV Sreg`, `POP FS/GS`, `LSS/LFS/LGS`,
`0F AE`, `0F 01`, `POPF`, `IRET`, `0F 00`, `0F 35`), and also every FS/GS-prefixed
instruction, because stores through FS corrupt the Go runtime's TLS. A seccomp-BPF filter on
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
  crypto/sha256 bytes strings math/bits encoding/binary`, and `artifacts/examples-amd64`.
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
* **Edge families** (`edge/<family>`): BSF/BSR with a zero source at 16, 32 and 64 bits; 32-bit
  `CMOV` with a false condition; MUL/IMUL/DIV/IDIV edge operands, including `IDIV` quotients of
  `-2^(w-1)` and every overflow; `AH`..`BH` versus `SPL`..`DIL` with and without REX;
  RIP-relative accesses (disp32 from `TestPC` reaches the buffer); `MOVAPS/MOVDQA/XORPS/PXOR`
  on misaligned memory; `XCHG mem, reg`; push/pop/call/ret/leave with `RSP` at and across the
  buffer ends.
* **Random** (`rand/*`): random prefix sequences (`66 67 F2 F3 F0 2E 3E 26 36 64 65`, REX),
  random one- and two-byte opcodes and random tails. These test that the decoder rejects what
  it does not understand and agrees on what it accepts, including instruction length.

## What agreement means

The comparator is `oracle-amd64/cmd/oracle/compare.go`.

| hardware | model | verdict |
|---|---|---|
| ok | ok, identical GPRs, defined status flags, `pc`, `XMM0`–`XMM15` and buffer bytes | **agree** |
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
* **FS/GS** are never executed natively (they would corrupt the runner's TLS). The decoder
  rejects `64`/`65` prefixes, and that rejection is checked only by `JanusTests/Amd64.lean`.
* **Canonical addresses.** This host has 5-level paging, so `2^47..2^56` is canonical: a jump
  there is a fetch fault (hw ok) and the model's `badTarget` is a gap. Non-canonical targets
  `#GP` at the branch itself, with `RSP` unchanged, and the model faults too.
* **Memory outside the buffer.** The model knows only the buffer. The native process also has
  the code page and its own mappings, so an access there succeeds natively and faults in the
  model (gap), never the other way round. Only the 4 KiB buffer is compared byte by byte.
* **No system state.** `RFLAGS` system bits, segment registers, MXCSR status bits, x87 state
  and YMM/ZMM upper halves are neither modelled nor compared.

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

Neither ACL2 X86isa itself, nor Remill or the K semantics, was tried: the Sail model ran on the
first attempt and exposes the undefined-flag masks directly. The bit-scan, population-count,
byte-swap and bit-modify classes are checked by the native oracle alone, because the formal
model does not implement them.
