# Soundness: what a Janus theorem means

A verified Janus theorem is a Lean theorem about `Extracted.program`: the instruction words
copied out of the ELF binary, run by the Lean AArch64 model. The Lean kernel checks the proof;
nobody checks that the *statement* says what you meant. The guarantee is exactly the printed
statement, including its preconditions and quantifiers.

**The printed statement is the checked one.** `janus verify` prints the statement in a clean
environment (only `Janus` and `Extracted`, never the proof, so no proof-side notation,
unexpander or instance applies), and then checks that the text means what the kernel proved:
every argument in an instance-implicit position must be a registered instance of that trusted
environment or an instance binder of the theorem (no inline `⟨fun a b => a + b⟩` passed as the
`HMul` instance, which the default printer would show as `x * y`), and the printed text is
re-parsed and re-elaborated there and must be definitionally equal to the checked type (checked
by the elaborator at default transparency and confirmed by the kernel; definitionally equal
propositions are the same proposition, so the printed text, read with the canonical instances,
is exactly what was proved). `verified.json` also has `statementExplicit`, the statement with
every implicit and instance argument shown. The body of each plain proof-local `def` the
statement names (disclosed in `definitions`, and part of what the guarantee means) is held to the
same instance check, so a `def` whose displayed body reads as one operation while an inline
instance makes it compute another is rejected. See CRITICAL-1 in
[AUDIT-ROUND2.md](AUDIT-ROUND2.md) and R1 in [AUDIT-ROUND3.md](AUDIT-ROUND3.md).

## Trusted computing base

These are trusted, not proved.

1. **The Lean AArch64 model** (`Janus/Arm64/Decode.lean`, `Exec.lean`, `Vector.lean`,
   `State.lean`): the decoder, the instruction semantics and the checked memory. They are meant to agree with the
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
   `morestack` stubs, only in package `runtime` itself (no `/` in the symbol: an import path
   such as `runtime.panicky/lib` is not runtime, docs/AUDIT-ROUND6.md F3). Reaching a stub
   address ends the run with that outcome. This only affects
   theorems that mention stub outcomes (`Panics`, `NeverPanics`, `GrowsStack`). `Returns`
   cannot be established through a stub. Panics that Go raises from a hardware trap (a nil
   dereference is a `SIGSEGV`, turned into a panic by `runtime.sigpanic`) are not stub calls:
   the model reports them as faults, and `NeverPanics` excludes faults too.
4. **The Lean kernel**, plus the verifier's hashing, process execution, axiom audit and
   statement audit (`Janus/Tools/Audit.lean`, including Lean's parser, elaborator and
   pretty-printer as used by the round-trip check above). The auditor and `leanchecker` load
   `.olean` files written by the sandboxed (untrusted) compile; Lean's `.olean` loader does not
   validate the structure of the compacted region it maps, so its robustness against a
   malformed `.olean` is part of the trusted base too. The
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

## The ASL corollary (`janus verify --asl`)

`--asl` adds a second, separate guarantee: the verified `Ensures` theorem, transferred to Arm's
ASL as translated to Lean (the JanusASL package, [docs/ASL.md](ASL.md)). Its statement is recorded
under `asl` in `verified.json`; it says that from every ASL state related to the Go call state
(`Rel`) under the Linux EL0 configuration (`LinuxEL0Config`), the ASL run of the extracted words
returns to the caller in a state related to one satisfying the ABI and the postcondition.

It is a corollary, not a new proof obligation: `Ensures.toASL` (kernel-checked, in JanusASL)
applied to the verified theorem, with its three facts about the program (every word `StepOK`,
untagged code and stubs) obtained from `JanusASL.Classify.covered Extracted.program = true`, which
the kernel decides by evaluation on the identity-checked program. The trusted auditor checks the
corollary's type is exactly that derivation from the verified theorem; no untrusted module may
declare a JanusASL, ArmASL, Sail or generated-module name; the corollary's whole closure,
the ArmASL model included, is kernel-replayed and its compiled modules are pinned.

It additionally trusts what [docs/ASL.md](ASL.md#trust-story) lists: Arm's ASL to Sail
(sail-arm), Sail's Lean backend with JanusASL's patches (checked against qemu and the C++ build
of the same Sail on a 583,756-case corpus, not proved), the slice and splices, the `janus_step`
harness and lean-sail. The ASL run fetches instructions with the program's own `fetch`, not the
ASL's translated fetch, and only returning runs are transferred. Neither the trusted base nor the
meaning of the main theorem changes: the ASL stage runs after it and cannot alter its result.

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
  `DCZID_EL0` (`State.dczid`) and `TPIDR_EL0` (`State.tpidr`, see below), no exceptions and no
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
  stack-assigned words from `8(RSP)`. The SIMD&FP registers are in the state (`State.vregs`,
  arbitrary in every call state, not preserved by `ABIReturn`: Go's ABIInternal has no
  callee-saved SIMD&FP registers), but `GoABI` passes no floating-point arguments or results
  (`F0`–`F15`), and there is no FPCR/FPSR. A function whose arguments use them is outside the
  model.
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
* **The `arm64HasATOMICS` precondition trusts the kernel.** The runtime sets the flag from the
  `HWCAP_ATOMICS` bit Linux reports in the auxiliary vector, so the precondition is "the kernel
  says every core has LSE". A kernel that over-reports a feature on a heterogeneous
  (big.LITTLE) system — as happened with atomics, Go issue 28431 — makes the precondition true
  on a CPU where an LSE instruction can trap; the theorem is then about a machine that is not
  the one running. The same holds for any other HWCAP-derived flag a proof assumes.
* **FP/AdvSIMD.** FEAT_FP and FEAT_AdvSIMD are formally optional in Armv8-A, yet the model
  accepts Advanced SIMD instructions and SIMD&FP loads/stores and moves unconditionally (see
  "Advanced SIMD" below), and Go uses them unguarded (`memequal`, `IndexByte`, large copies).
  Accepting them assumes the CPU implements both; every system that runs Go's arm64 port does
  (the AArch64 procedure-call standard passes floating-point values in SIMD&FP registers).
  FEAT_AES, FEAT_LRCPC and FEAT_LSE are assumed in the same way where their instructions are
  accepted.
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
* **`DCZID_EL0` is assumed uniform across cores.** `State.dczid` is one value for the whole run,
  but the register is IMPLEMENTATION DEFINED *per core*. Go reads it once and caches the block
  size; a thread that migrates to a core with a different `BS` between that read and `DC ZVA`
  zeroes a different block size than the code planned for. A theorem that reads `DCZID_EL0`
  (ClearWords) is therefore about systems whose cores all report the same value; no shipping
  heterogeneous system is known to differ, but the architecture does not forbid it.
* **`TPIDR_EL0` is a parameter too.** `MRS Xt, TPIDR_EL0` (the thread pointer; Go's runtime reads
  it in `save_g`/`load_g` under cgo) returns `State.tpidr`. Linux gives each thread its own
  value and EL0 code may write it, but no instruction the model accepts does (`MSR TPIDR_EL0` is
  rejected), so within a run it is a constant of the state and theorems quantify over it.

## Advanced SIMD

`State.vregs` holds `V0`–`V31` (128 bits each); the Advanced SIMD operations are in
`Janus/Arm64/Vector.lean`, transcribed from the ASL `Operation` pseudocode (element loops become
`ofElems`, `Elem[x, e, esize]` is `elem x esize e`). Covered:

* **Loads and stores:** `LDR`/`STR`/`LDUR`/`STUR` (all addressing modes) and `LDR` (literal) of
  B/H/S/D/Q registers, `LDP`/`STP` of S/D/Q registers, `LD1`/`ST1` (multiple structures, 1–4
  registers), `LD1`–`LD4`/`ST1`–`ST4` (single structure) and `LD1R`–`LD4R`, with every
  post-index form. Rejected: `LD2`–`LD4`/`ST2`–`ST4` (multiple structures), `LDNP`/`STNP`,
  `LDAPUR`/`STLUR` and every reserved size. Each register (multiple structures, pairs) or element
  (single structure) is a checked access as in the pseudocode; a fault anywhere faults the whole
  instruction.
* **Integer data processing:** the three-same logical operations (`AND`, `BIC`, `ORR`, `ORN`,
  `EOR`, `BSL`, `BIT`, `BIF`), `ADD`/`SUB`, the compares (`CMEQ`, `CMTST`, `CMHI`, `CMHS`,
  `CMGT`, `CMGE`, and against zero `CMEQ`/`CMGE`/`CMGT`/`CMLE`/`CMLT`), `SMAX`/`UMAX`/`SMIN`/`UMIN`
  and their pairwise forms, `ADDP`; scalar `ADD`/`SUB`/compares on D registers; across lanes
  `ADDV`, `SADDLV`/`UADDLV`, `SMAXV`/`UMAXV`/`SMINV`/`UMINV`; `CNT`, `NOT`, `RBIT`,
  `REV16`/`REV32`/`REV64`, `ABS`, `NEG`, `XTN`; shifts by immediate `SSHR`/`USHR`, `SSRA`/`USRA`,
  `SHL`, `SLI`, `SRI`, `SHRN`, `SSHLL`/`USHLL`; `MOVI`/`MVNI`/`ORR`/`BIC` (immediate) and `FMOV`
  (vector, immediate: a fixed bit pattern); `EXT`, `TBL`/`TBX`.
* **Moves:** `DUP` (element, general), `INS` (element, general), `UMOV`, `SMOV`, and `FMOV`
  between general and SIMD&FP registers (`Wn`↔`Sd`, `Xn`↔`Dd`, `Xn`↔`Vd.D[1]`).
* **AES:** `AESE`, `AESD`, `AESMC`, `AESIMC`, with the S-boxes and row permutations copied from the
  ASL and GF(2^8) multiplication checked against the ASL tables (`JanusTests/Vector.lean`).
  Accepting them assumes FEAT_AES; Go only runs its AES hash after testing `cpu.ARM64.HasAES`
  (`runtime.useAeshash`), so a proof through it assumes that flag, as for LSE.

Not modelled, and rejected: all floating-point arithmetic, comparison and conversion (and with
them FPCR/FPSR: no accepted instruction reads or writes them, so they are not in the state),
saturating, rounding and widening/narrowing arithmetic other than the listed ones, permutes
(`ZIP`/`UZP`/`TRN`), SHA, polynomial multiply, SVE and SME. An Advanced SIMD write sets the whole
128-bit register (`V[d, n] = x` zero-extends); on a CPU with SVE the hardware also zeroes the
upper bits of `Z[d]`, which are not part of the model and not observable by the accepted
instructions.

Go 1.26's `runtime.memmove`, `runtime.memclrNoHeapPointers` and the compiler's inline copies of
small values use general-purpose `LDP`/`STP`; larger copies (`LDP`/`STP Q16, Q17`), the
`internal/bytealg` routines (`memequal`, `IndexByte`, `Count`, ...), `aeshashbody` and
`internal/chacha8rand.block` use the instructions above.

**Coverage effect** (`janus blockers` on Go 1.26.0 `go test -c` binaries, every `T` symbol of
the package plus `runtime.memmove`, `runtime.memclrNoHeapPointers`, `runtime.memequal` and
`internal/bytealg.{IndexByte,Count,Compare,IndexString}`, `--max-functions 3000`):

| binary (symbols) | fully decoded before | after | distinct rejected words before → after |
|---|---:|---:|---:|
| `sync/atomic` + `internal/runtime/atomic` (25) | 11 | 16 | 406 → 135 |
| `bytes` (66) | 29 | 42 | 406 → 135 |
| `strings` (76) | 18 | 28 | 414 → 137 |

(The previous round's table, with fewer symbols: `bytes` 26 → 27 of 61, `strings` 15 → 16 of 70.)
Now fully decoded: `runtime.memequal`, `internal/bytealg.IndexByte`/`IndexByteString`/`Count`/
`CountString`, `bytes.Equal`, `bytes.Index`, `bytes.IndexByte`, `bytes.IndexRune`,
`bytes.LastIndex`, `bytes.Cut`, `bytes.TrimPrefix`/`TrimSuffix`, `strings.Count`, `strings.Index`,
`strings.LastIndex`, `strings.TrimPrefix`/`TrimSuffix`, `sync/atomic.StorePointer`, and
`aeshashbody` and `internal/chacha8rand.block` as callees. Every remaining rejected word in these
binaries is floating point (`SCVTF`, `FCVTZS`, `FMUL`, `FMOV` (scalar immediate), ...; in the GC
pacer and heap profiling reached through `mallocgc`), a store-exclusive (`STLXR`, the LL/SC
fallbacks), `SVC` (system calls) or `MRS CNTVCT_EL0`/`CNTFRQ_EL0` (the generic timer in
`runtime.procyieldAsm`; the counter is not a constant, so it needs a nondeterministic model).
The other functions of `bytes`/`strings` reach `runtime.mallocgc` and stay blocked by these.

## Dynamic calls, closures and `defer`

An indirect call (`BLR`/`BR`; amd64 `CALL`/`JMP` through a register or memory) jumps to the value
the register holds, in the model as on hardware. Nothing about Go's type system is assumed:

* **Which code a dynamic call reaches is a hypothesis of the theorem when it is not computed
  by the code being proved.** `Janus.Spec.ItabIs ds m tab name` (the interface's itab word is the
  address of the static itab `name` of the extracted data, and memory holds its bytes
  read-only), `FuncvalIs m fv fn` (a funcval's code word) and `ClosureCtx m fv vars` (the captured
  variables after it) are ordinary propositions about the call state's memory and appear in the
  printed statement; the auditor treats them like any other part of the statement. A theorem
  says nothing about calls whose interface or func value is not the one stated. If the stated
  itab or funcval cannot be in memory as described, the theorem is vacuous for those callers,
  like any unsatisfiable precondition.
* **Itab contents come from the binary.** `ItabIs` names a data object of
  `Extracted.program.data`, copied byte for byte from `.rodata` (a static itab `go:itab.*T,I`)
  and re-checked by `janus check`. Dynamically built itabs (`runtime.getitab`, for type
  assertions to interfaces the compiler did not see) are heap objects, not covered by
  `ItabIs`; state their memory directly if needed.
* **Targets are untrusted extraction choices.** `janus extract --targets` and the extractor's
  inference (code addresses computed by user code, itabs and funcvals it loads) only decide
  which code is copied, like reachability. A target that is not copied makes the call fault
  (`noCode`), so no theorem through it can be proved; extra targets add code no theorem has to
  mention. What was added and why is recorded in `identity.json` (`targets`,
  `dynamicTargets`).
* **Open-coded defers are modelled as the code that implements them**: the deferred closure is
  an ordinary stack-allocated funcval called at each exit. `runtime.deferreturn`, which an
  open-coded function calls only from the block the runtime resumes at after a *recovered*
  panic, is not extracted (`omittedCalls` in `identity.json`): if a run reached it, it would
  fault, so a theorem that returns shows it is not reached.
* **Out of scope:** `recover`, and panics that unwind through deferred calls (a panic is a stub
  outcome: the run ends at `runtime.gopanic`/`runtime.panic*`, and the deferred calls the
  runtime would run while unwinding are not executed). Defers the compiler does not open-code
  (in loops, or more than 8 in a function) allocate defer records with `runtime.deferproc*` and
  call `runtime.deferreturn` at every exit; they are unsupported (the exit faults). Heap-allocated
  closures (`runtime.newobject`) are runtime calls like any other allocation.

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
