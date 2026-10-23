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
   cannot be established through a stub.
4. **The Lean kernel**, plus the verifier's hashing, process execution and axiom audit. The
   audit allows only `propext`, `Quot.sound` and `Classical.choice`. It rejects `sorryAx`,
   `Lean.ofReduceBool` and `Lean.trustCompiler`, so `native_decide` and `bv_decide` cannot be
   used. `leanchecker` independently replays the environment.

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

`GoABI.Ensures p entry args pre post` means: for **every** state `s` with `pc = entry`,
`R30 = p.exitAddr`, `Ri = args[i]`, and `pre s` (all other registers, flags, `SP` and memory
arbitrary), there exist a finite fuel and a state `s'` such that `p.run fuel s` returns `s'`,
`s'` restores `SP`, `R28` (g), `R29` (FP) and `R18`, and `post s s'` holds. This is total
correctness: termination is part of the claim. Running out of fuel is not success, and neither
is any fault.

`p.run` itself never reports undefined behaviour. Every step either produces a state or a named
`Fault`. So `Returns` also rules out out-of-bounds or read-only memory accesses, misaligned
`SP`-based accesses, branches to code outside the extracted program, and unsupported
instructions on the paths taken from states satisfying `pre`.

## Assumptions and limits

A verified theorem is a statement about the following idealised execution. It says nothing
about executions outside it.

* **Single-threaded.** Memory changes only through the function's own stores. There are no
  other goroutines or OS threads, no concurrent writes and no weak-memory effects. Atomics and
  barriers mean only their sequential semantics.
* **No signals, no asynchronous preemption, no interrupts.** Go's signal-based async
  preemption, profiling signals and injected calls (`sigpanic`) are not modelled.
* **No runtime interaction.** No GC (write barriers, stack scanning, moving stacks), no
  scheduler, no stack growth. Reaching `runtime.morestack*` ends the run as a `morestack`
  outcome, and it is not a return. Calls into other runtime functions only work if they were
  extracted and their code is in the supported subset. They then run in the same idealised
  model. Functions with a stack-check prologue need `GoABI.StackGuardOK s k` (g readable,
  `stackguard0 + k < SP`) for the prologue to fall through.
* **User mode only (EL0).** There are no system registers beyond NZCV, no exceptions and no
  page tables. `SP` alignment checking (SCTLR_EL1.SA0, as Linux configures it) is modelled as a
  fault. Other alignment faults are not modelled, except where the instruction model says so.
* **Memory outside the listed regions faults.** Every load and store must lie entirely inside
  one `Region` of `s.mem.regions` (and a writable one, for stores). Otherwise the run faults.
  A theorem therefore holds only for callers whose memory layout satisfies the regions stated
  in its precondition: the stack window (`StackWritable`), the argument/spill area above `SP`,
  the `g` struct, and every heap object the function touches. Real memory can have more mapped
  pages than the model allows, so the model is conservative. A program that reads an unlisted
  but mapped address on real hardware cannot be proved to return.
* **Code is not memory.** Instructions are fetched from the extracted segments, not from
  `s.mem`. Self-modifying code and loads from `.text`/`.rodata` are not modelled unless the
  precondition lists a region holding those bytes. Stores never change the fetched code.
* **The return sentinel.** The call "returns" when `pc` reaches `p.exitAddr`, the value
  planted in `R30` (the extractor currently renders `exitAddr := 0`). Reaching that address
  by *any* branch counts, not only `RET`. A real caller passes its own return address, not the
  sentinel. Transferring a theorem to a real call site assumes that the function treats `R30`
  opaquely (saves, restores and returns through it, but never computes with it). Go-generated
  code does this, but Janus does not prove it.
* **ABIInternal only.** `GoABI` covers integer arguments and results in `R0`–`R15` and
  stack-assigned words from `8(RSP)`. There are no floating-point or SIMD registers
  (`F0`–`F15`) and no FPCR/FPSR. A function whose arguments use them is outside the model.
  "`R29` is preserved" relies on Go's frame-pointer convention (`GoABI.FPConvention`:
  `R29 = SP - 8` at the call), because Go 1.26 leaf functions restore `R29` arithmetically.
* **64-bit addresses as naturals.** Addresses are `Nat` values below `2^64`, produced by the
  instruction model's wrap-around arithmetic. Region bounds are compared in `Nat`.
* **Fixed binary.** A theorem is about one binary, identified by SHA-256. Rebuilding with
  another compiler version, other flags or another linker layout invalidates it. `janus check`
  detects this.

## What the theorem does not say

* Nothing about callers other than those satisfying `CallSetup` and the stated precondition.
  If the precondition is unsatisfiable, the theorem is vacuous. Prefer preconditions that are
  shown satisfiable (`GoABI.setup_callSetup` builds a call state from any state).
* Nothing about timing, side channels, power, caches or speculative execution.
* Nothing about `NeverPanics` unless it is stated. `Returns` implies it
  (`GoABI.Returns.neverPanics`) only for the same initial state.
* Nothing about the Go source. If the compiler miscompiled it, the theorem is about the
  miscompiled code, which is the point.
