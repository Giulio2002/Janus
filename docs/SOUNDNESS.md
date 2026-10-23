# Soundness: what a Janus theorem means

A verified Janus theorem is a Lean theorem about `Extracted.program`: the instruction words
copied out of the ELF binary, run by the Lean AArch64 model. The Lean kernel checks the proof;
nobody checks that the *statement* says what you meant. The guarantee is exactly the printed
statement, including its preconditions and quantifiers.

## Trusted computing base

These are trusted, not proved.

1. **The Lean AArch64 model** (`Janus/Arm64/Decode.lean`, `Exec.lean`, `State.lean`): the
   decoder, the instruction semantics and the checked memory. They are meant to agree with the
   Arm Architecture Reference Manual (ARM ARM) for the supported user-mode A64 subset. That
   agreement is differentially tested against qemu (`janus-oracle`), not proved. If the model
   is wrong about an instruction the program uses, a theorem can be true of the model and false
   of the hardware. Words outside the supported subset fault (`undecodable`). They are never
   given a guessed meaning.
2. **The ELF word copy** (`cmd/janus`: `binary.go`, `extract.go`, `identity.go`): finding the
   symbol's `[addr, addr+size)` in `.text` and copying its little-endian 32-bit words (trailing
   zero padding words are dropped). `janus verify` re-runs this copy against the binary
   (checked by SHA-256) and compares it byte for byte with `Extracted.lean`, so a stale or
   edited extraction is rejected. The copy itself and the symbol table lookup are trusted.
3. **Stub classification**: the extractor names runtime functions `runtime.panic*`,
   `runtime.goPanic*` and `runtime.gopanic` as `panic` stubs and `runtime.morestack*` as
   `morestack` stubs. Reaching a stub address ends the run with that outcome. This only affects
   theorems that mention stub outcomes (`Panics`, `NeverPanics`, `GrowsStack`). `Returns`
   cannot be established through a stub. Panics that Go raises from a hardware trap (a nil
   dereference is a `SIGSEGV`, turned into a panic by `runtime.sigpanic`) are not stub calls:
   the model reports them as faults, and `NeverPanics` excludes faults too.
4. **The Lean kernel**, plus the verifier's hashing, process execution and axiom audit. The
   audit allows only `propext`, `Quot.sound` and `Classical.choice`. It rejects `sorryAx`,
   `Lean.ofReduceBool` and `Lean.trustCompiler`, so `native_decide` and `bv_decide` cannot be
   used. `leanchecker` independently replays the environment (below).
5. **The Lean toolchain's own library** (`Init`, `Std`, `Lean`, `Lake`, shipped with the
   toolchain and read-only to every sandboxed process) and the **trusted framework build**: the
   framework's `.olean` files compiled by `janus` itself from the framework sources it carries,
   outside the sandbox, once per framework version (`janus verify --fresh` rebuilds them).

**What the kernel replay covers.** After the audit, `leanchecker` (shipped with the toolchain)
replays, through the kernel, **every module of the theorem's import closure that is not Lean
core**: every `Janus.*` framework module the theorem's environment imports, `Extracted`, the
independent `JanusTrusted` copy, every consumer module and every dependency module. Each module
is replayed against its imports as loaded from their `.olean` files, and since every non-core
import is itself replayed, no non-core declaration is taken on trust. Lean core is not replayed
by default; `--replay-fresh` additionally runs `leanchecker --fresh` on the theorem's module,
which re-adds every constant of its environment, core included, to an empty environment
(minutes: about 140 s for a closure that imports `Lean`). Passing replays are cached in the
trusted cache (`v1/replay`, never writable by a sandboxed process) under a key covering the
toolchain version, the module's `.olean` bytes (with its `.server`/`.private` parts) and,
recursively, the keys of its imports, so an unchanged framework module is not replayed again
while any byte change to it or to anything below it is. The cache is off with `--fresh` and
without a sandbox. Before replaying, every module of the closure must resolve from its home:
core modules from the toolchain library, `Janus.*` modules from the trusted framework build and
only modules the framework has a source for, `Extracted`/`JanusTrusted` from the trusted
directory.

**What the replay does not cover, and what does.** A replay checks that a module is
*well-typed*, not that it is the module its source describes: an `.olean` compiled from a
modified framework source (say `Ensures := True`) replays fine. That is why the framework
build is also **pinned**: the SHA-256 of every framework `.olean` (and of the trusted
`Extracted`/`JanusTrusted`) is recorded right after the trusted build and re-verified after
every untrusted step (the proof compile, the consumer's Lake build and `lake query`), after the
audit and after the replay; untrusted build outputs (consumer and dependency modules, the proof)
are pinned once they are final, so the replay checks exactly the bytes the audit read. In a
consumer workspace the framework package is additionally **mounted read-only** for every
sandboxed process (a mount point cannot be renamed or removed from inside), and the
workspace's framework build is replaced from the trusted cache whenever it differs from the
pins. A changed, corrupted, missing or extra framework module is rejected (`framework
integrity`). See finding R1 in [docs/AUDIT.md](AUDIT.md).

**Not trusted:**

* The Go compiler and linker. We reason about their output.
* Any source-level reasoning about the Go program.
* The extractor's reachability analysis (`branch.go`). It decides only *which* functions to
  copy, by following direct branches (`B`, `BL`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ`). It never
  decides what an instruction means: Lean decodes every word again. If it misses a callee (for
  example through an indirect `BLR`), that code is absent, and the model faults with `noCode`
  when control reaches it. A missed callee can make a theorem unprovable. It cannot make a
  false theorem provable.

## What a theorem about `Returns` / `Ensures` says

`GoABI.Ensures p entry args pre post` means: for **every** admissible return address `ret`
(`GoABI.RetAddr p ret`: `ret` is 4-aligned, below `2^48`, outside every extracted code segment
and not a stub address) and **every** state `s` with `pc = entry`, `R30 = ret`, `Ri = args[i]`,
and `pre s` (all other registers, flags, `SP` and memory arbitrary), there exist a finite fuel
and a state `s'` such that `(p.withExit ret).run fuel s` returns `s'` (reaches `pc = ret`),
`s'` restores `SP`, `R28` (g), `R29` (FP) and `R18`, and `post s s'` holds. This is total
correctness: termination is part of the claim. Running out of fuel is not success, and neither
is any fault.

`p.run` itself never reports undefined behaviour. Every step either produces a state or a named
`Fault`. So `Returns` also rules out out-of-bounds or read-only memory accesses, misaligned
`SP`-based accesses, branches to code outside the extracted program, and unsupported
instructions on the paths taken from states satisfying `pre`.

### Outcome predicates

| Predicate | Meaning |
|---|---|
| `Returns p s post` | the run reaches `p.exitAddr` (for a call: `ret`) in a state satisfying `post` |
| `Panics p s` | the run reaches a Go panic stub (bounds check, divide by zero, explicit `panic`) |
| `Faults p s` | the run stops with a fault other than `outOfFuel` (a nil or out-of-bounds access, a read-only store, misaligned `SP`, a jump outside the code, an unsupported instruction) |
| `NeverPanics p s` | for every fuel: no panic stub **and** no fault; only `outOfFuel` is allowed (`neverPanics_iff : NeverPanics ↔ ¬ Panics ∧ ¬ Faults`) |
| `GrowsStack p s` | the run reaches `runtime.morestack*` |

On real hardware every model fault is a crash or a Go panic: a memory fault is `SIGSEGV`, which
Go turns into `panic: runtime error: invalid memory address or nil pointer dereference`. So "never
panics" must exclude faults, and it does. `Returns` implies `NeverPanics`
(`Returns.neverPanics`), and `Faults`, `Panics` and `Returns` exclude each other.

`Faults` and `Panics` are positive claims about the model. A model fault means the code left the
memory, code and instruction subset the theorem grants; on hardware that access may hit another
mapping (memory the caller did not grant) rather than trap. Read `Faults` as "the function
needs more than the precondition provides", not as a guarantee of a hardware trap.

### The return address

A computed branch must never be mistaken for a return. The model ends a run when `pc` equals
`p.exitAddr`, and the extractor renders `exitAddr := 0`. If specifications used that fixed value,
any branch to 0 (a `BR` through a zero code pointer loaded from caller memory, a nil closure)
would "return", while on hardware it is a `SIGSEGV`. So specifications never use the extracted
value. `Ensures` (and every direct `Returns`/`Panics`/`NeverPanics` theorem in the examples)
quantifies over all `ret` with `RetAddr p ret` and runs `p.withExit ret` (`{ p with exitAddr :=
ret }`; the extracted `Program` itself is unchanged). The argument that this is sound:

* A real call is `BL entry` from a caller outside the extracted code. Its return address is the
  instruction after the `BL`, in the caller: 4-aligned, a user address below `2^48`, not inside
  an extracted segment, and not a runtime stub. So it satisfies `RetAddr`, and the theorem
  applies to it.
* The theorem holds for every such `ret`, with memory and registers otherwise as in `pre`. A
  path that reaches `ret` other than through the value the caller put in `X30` (a branch to a
  constant, or to a word loaded from memory that `pre` does not tie to `X30`) reaches it only for
  some values of `ret` and faults (`noCode`) for the others, so the theorem is not provable.
* Excluding the code ranges matters: if `ret` could be an address in the function, reaching that
  instruction in the normal course of execution would count as a return. Excluding stubs keeps
  `Panics` meaningful. The bound and the alignment are what `RET` itself needs (the model
  faults on misaligned or tagged branch targets).

Calls whose return address lies inside the extracted code (recursion, or a caller that was
extracted together with the callee) are not covered by the callee's theorem; they are covered by
the theorem about the outer function, which executes or summarises the inner call. Callee
summaries (`Tactic.Summary`) are stated on the extracted program and moved to `p.withExit ret`
by `Summary.withExit`, because their steps never touch `ret` (there is no code there).

## Assumptions and limits

A verified theorem is a statement about the following idealised execution. It says nothing
about executions outside it.

* **Single-threaded.** Memory changes only through the function's own stores. There are no
  other goroutines or OS threads, no concurrent writes and no weak-memory effects. Atomics and
  barriers mean only their sequential semantics: a load-acquire (`LDAR`, `LDAPR`, `LDAXR`) is
  an ordinary load, a store-release (`STLR`) an ordinary store, and the acquire/release
  variants of the LSE atomics behave like the plain ones. With one thread and no other
  observer these are equivalent; a theorem says nothing about what another thread would see.
  See "Atomics, exclusives and system registers" below.
* **No signals, no asynchronous preemption, no interrupts.** Go's signal-based async
  preemption, profiling signals and injected calls (`sigpanic`) are not modelled.
* **No runtime interaction.** No GC (write barriers, stack scanning, moving stacks), no
  scheduler, no stack growth. Reaching `runtime.morestack*` ends the run as a `morestack`
  outcome, and it is not a return. Calls into other runtime functions only work if they were
  extracted and their code is in the supported subset. They then run in the same idealised
  model. Functions with a stack-check prologue need `GoABI.StackGuardOK s k` (g readable,
  `stackguard0 + k < SP`) for the prologue to fall through.
* **User mode only (EL0).** There are no system registers beyond NZCV and the read-only
  `DCZID_EL0` (`State.dczid`, see below), no exceptions and no
  page tables. `SP` alignment checking (SCTLR_EL1.SA0, as Linux configures it) is modelled as a
  fault. Other alignment faults are not modelled, except where the instruction model says so.
* **Memory outside the listed regions faults.** Every load and store must lie entirely inside
  one `Region` of `s.mem.regions` that ends at or below `2^48` (and a writable one, for stores).
  A store also faults if any byte it touches lies in a read-only region, even if a writable
  region covers it too: permissions are per byte on hardware, so overlapping regions cannot
  make read-only data (`DataLoaded`) writable. Otherwise the run faults.
  The `2^48` bound is the Linux arm64 user address limit (48-bit VA; a kernel with 52-bit VA
  only hands out higher addresses to `mmap` calls that ask for them, which Go does not). Every
  real call state has its memory below it, so it is representable. In exchange no successful
  access wraps around `2^64`, and no tagged address (top byte non-zero) is accessible, so the
  top-byte-ignore aliasing of Linux EL0 (`x` and `x + 2^56` naming the same byte) cannot occur
  in a proof: two accessible ranges that are `Disjoint` as numbers are disjoint in hardware. The
  same bound is used for amd64, where it is also sound (user addresses are below `2^47`, and
  `[2^47, 2^48)` is non-canonical; see `docs/AMD64.md`).
  A theorem therefore holds only for callers whose memory layout satisfies the regions stated
  in its precondition: the stack window (`StackWritable`), the argument/spill area above `SP`,
  the `g` struct, and every heap object the function touches. Real memory can have more mapped
  pages than the model allows, so the model is conservative. A program that reads an unlisted
  but mapped address on real hardware cannot be proved to return.
* **Code is not memory.** Instructions are fetched from the extracted segments, not from
  `s.mem`. Read-only constants the code loads (`.rodata`, literal pools) are copied by the
  extractor into `Program.data`; a theorem that needs them assumes `Program.DataLoaded`
  (memory holds exactly those bytes in a read-only region). Writable globals (`.data`,
  `.bss`, `.noptrdata`, `.noptrbss`) are never copied, because their contents are not fixed
  by the binary: a proof that touches one must list it as an ordinary region in its
  precondition. Self-modifying code is not modelled, and stores never change the fetched code.
* **The return address.** Specifications quantify over every admissible return address (see
  "The return address" above), so the extracted placeholder `exitAddr := 0` never matters. A
  theorem stated directly on `Extracted.program` (without `withExit` and a universally
  quantified `ret`) uses the placeholder and counts any branch to `0` as a return; such a
  statement says much less, and is visible as such in the printed statement.
* **ABIInternal only.** `GoABI` covers integer arguments and results in `R0`–`R15` and
  stack-assigned words from `8(RSP)`. There are no floating-point or SIMD registers
  (`F0`–`F15`) and no FPCR/FPSR. A function whose arguments use them is outside the model.
  "`R29` is preserved" relies on Go's frame-pointer convention (`GoABI.FPConvention`:
  `R29 = SP - 8` at the call), because Go 1.26 leaf functions restore `R29` arithmetically.
* **64-bit addresses as naturals.** Addresses are `Nat` values below `2^64`, produced by the
  instruction model's wrap-around arithmetic. Region bounds are compared in `Nat`, and every
  accessible byte is below `2^48`.
* **Fixed binary.** A theorem is about one binary, identified by SHA-256. Rebuilding with
  another compiler version, other flags or another linker layout invalidates it. `janus check`
  detects this.

## Atomics, exclusives and system registers

`sync/atomic` and the runtime compile to load-acquire/store-release, LSE atomics and
load/store-exclusive loops; `runtime.memclrNoHeapPointers` uses `DC ZVA` after reading
`DCZID_EL0`. The model covers them as follows (`Janus/Arm64/Decode.lean`, `Exec.lean`).

* **Ordered accesses** (`LDAR`, `LDAPR`, `STLR`, all sizes) are ordinary loads and stores in
  the single-threaded model. `LDLAR`/`STLLR` (FEAT_LOR) are rejected.
* **LSE atomics** (`LD<op>` for ADD, CLR, EOR, SET, SMAX, SMIN, UMAX, UMIN; `SWP`; `CAS`;
  `CASP`; every size and A/L variant; the `ST<op>` aliases) are one-instruction
  read-modify-writes. Single-threaded, they are deterministic and are modelled exactly: read
  the old value, write the new one, put the old one in the destination register. The access
  needs write permission even when `CAS` does not store. `CASP` with an odd register is
  rejected (UNDEFINED).
* **Alignment.** Ordered, exclusive and atomic accesses fault (`Fault.unaligned`) unless naturally
  aligned (`CASP`: to the pair). Hardware without FEAT_LSE2 always faults there; with FEAT_LSE2
  some of them succeed when they stay inside 16 bytes. The model is conservative for both.
* **Feature assumptions.** Accepting an instruction means assuming the CPU implements it: the
  model is of a CPU with FEAT_LSE (`LD<op>`, `SWP`, `CAS`, `CASP`) and FEAT_LRCPC (`LDAPR`).
  On an Armv8.0 CPU they are UNDEFINED (`SIGILL`). Go code does not depend on this blindly: it
  runs LSE instructions only after testing `runtime.arm64HasATOMICS`, a byte the runtime sets
  at start-up from the CPU's capabilities (or, built with `GOARM64=v8.1`, it refuses to start
  without LSE). A proof through such a test assumes the flag in its precondition, as
  `examples/proofs/AtomicAdd.lean` does, and on a CPU without LSE that precondition is false,
  so the theorem is vacuous there rather than wrong. A proof about code that uses LSE
  unconditionally is a statement about LSE-capable CPUs.
* **Store-exclusives are rejected.** `STXR`, `STLXR`, `STXP` and `STLXP` decode to nothing
  (`undecodable`), so any run that reaches one faults. Reasoning: on real hardware a
  store-exclusive may fail *spuriously* (status 1, nothing stored) even with no other thread:
  an interrupt, a context switch, a cache eviction or an implementation-defined event clears
  the exclusive monitor. A deterministic "always succeeds" model would therefore claim
  behaviour hardware does not guarantee; it is sound only for code whose result does not
  depend on the number of failures (a correct retry loop), which is a property of the
  surrounding program, not of the instruction, and the model checks instructions one at a
  time. An "always fails" model is unsound in the other direction (the first attempt can
  succeed). A sound alternative would make the outcome an explicit nondeterministic input
  (an oracle stream in the state that theorems quantify over, plus a fairness assumption for
  termination); it is not needed for Go's LSE paths, so it is not implemented. The
  consequence is conservative: the `LDAXR`/`STLXR` fallback of `sync/atomic` (taken only when
  the CPU lacks LSE) cannot be proved, and a theorem through it is unprovable, never wrong.
* **Load-exclusives** (`LDXR`, `LDAXR`) are modelled as ordinary (aligned) loads. The exclusive
  monitor they would arm is observable only by a store-exclusive, which faults, so it is not
  part of the state; `CLREX` is a no-op for the same reason. Exclusive pairs (`LDXP`,
  `LDAXP`) are rejected.
* **PRFM/PRFUM** (all forms and prefetch operations) only advance `pc`: a prefetch never faults
  and has no architectural effect.
* **`DCZID_EL0` is a parameter, not a constant.** `MRS Xt, DCZID_EL0` (the only accepted system
  register read) returns `State.dczid`, the five meaningful bits (`DZP`, `BS`). The value is
  IMPLEMENTATION DEFINED (qemu `-cpu max` reports 7, i.e. 512-byte blocks; the Sail Armv9.4
  model 8; many Neoverse cores 4), so it lives in the state, execution never changes it, and a
  theorem about arbitrary initial states quantifies over all 32 values. A proof may restrict
  it by a visible precondition. `DC ZVA, Xt` zeroes the naturally aligned block of
  `4 << BS` bytes containing `Xt` (checked as a store of that many bytes) and faults
  (`Fault.trapped`, `SIGILL` on Linux) when `DZP = 1`. Other `DC`/`IC`/`SYS` operations are
  rejected. `examples/proofs/ClearWords.lean` proves `runtime.memclrNoHeapPointers` (through its
  `DC ZVA` path) for every value of `DCZID_EL0`.
* **No SIMD/FP registers.** `State` has no `V0`–`V31`. Go 1.26's `runtime.memmove` and
  `runtime.memclrNoHeapPointers` on arm64, and the compiler's inline copies and zeroing of
  fixed-size values, use general-purpose `LDP`/`STP` only (checked on the Go 1.26.0 binary: no
  `Q`/`D` loads or stores, `LD1`/`ST1`, `MOVI` or `DUP` in either routine), so no vector state
  is needed for them. The runtime routines that do use SIMD (`memequal`, `indexbyte`, `count`,
  the AES hash) also compute with it, which is outside this model.

**Coverage effect** (`janus blockers` on Go 1.26.0 `go test -c` binaries, every `T` symbol of
the package plus `runtime.memmove` and `runtime.memclrNoHeapPointers`, `--max-functions 3000`):

| binary (symbols) | fully decoded before | after | distinct rejected words before → after |
|---|---:|---:|---:|
| `sync/atomic` + `internal/runtime/atomic` (20) | 3 | 9 (+3 whose only rejected words are the LL/SC fallback `STLXR`) | 677 → 399 |
| `bytes` (61) | 26 | 27 | 681 → 406 |
| `strings` (70) | 15 | 16 | 694 → 414 |

`runtime.memmove` was already fully decoded; `runtime.memclrNoHeapPointers` now is. What still
blocks most `bytes`/`strings` functions is SIMD computation (`memequal`, `indexbyte`, `count`:
`LD1`, `CMEQ`, `ADDP`, `UADDLV`, ...), `MRS TPIDR_EL0`/`CNTVCT_EL0` and FP/AES code reached
through `mallocgc`.

## What the theorem does not say

* Nothing about callers other than those satisfying `CallSetup` and the stated precondition.
  If the precondition is unsatisfiable, the theorem is vacuous. Prefer preconditions that are
  shown satisfiable (`GoABI.setup_callSetup` builds a call state from any state).
* Nothing about timing, side channels, power, caches or speculative execution.
* Nothing about `NeverPanics` unless it is stated. `Returns` implies it
  (`GoABI.Returns.neverPanics`) only for the same initial state. `Panics` is only about panic
  stubs: a nil dereference is a `Fault`, and "never panics" means `NeverPanics` (no stub and no
  fault).
* Nothing about the Go source. If the compiler miscompiled it, the theorem is about the
  miscompiled code, which is the point.
