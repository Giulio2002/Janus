# Runtime contracts

Go code calls into its runtime: the allocator (`runtime.mallocgc`, `newobject`, `makeslice`,
`growslice`), the GC write barrier, map and interface helpers, cgo, … Most of that code is far
outside what a proof can execute (locks, system calls, the scheduler, the GC). Janus handles such
calls with **runtime contracts**: the function is not extracted, and the theorem states, as a
hypothesis, what it assumes the function does. Nothing is added to the trusted base: the
assumption is part of the printed statement, checked by the same auditor (round trip, instance
checks) as everything else.

This document describes the mechanism, which every kind of contract shares, and then each
contract library. Sections for further kinds are added under [Contract kinds](#contract-kinds).

## The mechanism

### 1. Extraction: `--contract`

```sh
janus extract <binary> <symbol> <outdir> --contract runtime.newobject --contract 'runtime.gcWriteBarrier*'
```

`--contract SYM` may be repeated; `SYM` is a glob pattern (`*` matches any run of characters,
including `.` and `/`; `?` one character; a name matches with or without its `.abi0` /
`.abiinternal` suffix). A direct branch (`BL`/`B`/`B.cond`/…, `CALL`/`JMP`/`Jcc`) to a function
whose name matches is **not followed**: its code is not copied, and the function is recorded as a
contract. Runtime stubs (`runtime.panic*`, `runtime.morestack*`) keep their stub meaning even if a
pattern matches them, and the entry function may not match a pattern.

The contracts appear in three places:

* `Extracted.lean`: `def contracts : List (String × Nat) := [("runtime.newobject", 0x28440)]` and
  `contracts := contracts` in `Extracted.program` (`Program.contracts`, a field with default `[]`
  on both `Janus.Program` and `Janus.Amd64.Program`, so artifacts without contracts are
  byte-identical to earlier ones);
* `identity.json`: `contractPatterns` (the patterns as given) and `contracts` (name, address);
  `janus check` / `janus verify` regenerate the extraction with the recorded patterns and compare
  both files byte for byte;
* `verified.json`: `contracts` (`"name @ address"`); `janus verify` prints
  `Runtime contracts assumed: …` and `janus explain` prints `runtime contracts assumed: …`.

The list does not change the run semantics. There is no code at a contract address in
`Extracted.program.segments`, so control reaching it faults with `noCode`, exactly as for a
missed callee. The list is metadata: it names the addresses (`Program.contractAddr p name`) and
tells the reader of a report which functions were left out.

### 2. The statement: linked code and a `Summary` hypothesis

A theorem that relies on a contract quantifies over the code at the contract addresses and assumes
the contract for it:

```lean
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (pre rt) post
```

* `Program.link p impl` is `p` with the segments `impl` appended after its own (`Janus.Program.link`,
  `Janus.Amd64.Program.link`). Every address where `p` has code still fetches `p`'s word
  (`Program.fetch_link`); stubs, data, contracts and the exit address are `p`'s.
* The contract is a `Tactic.Summary` (arm64: `Janus.Tactic.Summary`; amd64:
  `Janus.Amd64.Tactic.Summary`) of the linked program at the contract's address: from every state
  at that address satisfying the contract's precondition, ordinary steps of `p.link impl` reach the
  return address with the contract's postcondition. Named contracts (`NewobjectContract …`) are
  definitions that unfold to a `Summary`.
* The conclusion is about `p.link impl` for **every** `impl` satisfying the hypothesis. The real
  binary is one such program (its runtime code at those addresses), so the theorem applies to it
  exactly when the real runtime satisfies the contract. Nothing about `impl` can be used except
  the contract: the proof cannot run code it does not know.

Why not assume the summary about `Extracted.program` itself: there is no code at the contract
address in `Extracted.program`, so a `Summary` there with a non-trivial postcondition is false,
and a theorem assuming it would be vacuous.

### 3. The proof: `janus_run calls [h]`

The executors (`janus_run`, `janus64_run`) run programs of the form `p.link impl` with `impl` a
variable: the program facts (`stepOK`, `stubOK`, `exitOK`) are evaluated on the closed `p` and lifted
(`stepOK_link`, `stubOK_link`, `exitOK_link`); `withExit ret` on top works as before. At the call,
`calls [h]` uses the contract like any callee summary: the precondition is proved at the call
site, the postcondition is destructured into hypotheses (an equation `s' = …` is substituted) and
then simplified, and the run continues.

Tools for contract proofs (all untrusted automation, re-checked by the kernel):

* `Summary.mono` (both ISAs): specialise a contract to a call site, e.g. `hnew.pos` (the
  non-zero-size case of an allocation contract) is `Summary.mono hnew …`.
* `Outside a n rs` side conditions with a list `rs` that is not a literal (a variable `rt`) are
  proved from a hypothesis `Outside b k rt` with `[a, a+n) ⊆ [b, b+k)` (`Outside.of_sub`).
* `janus_frame` peels stores into an object known to lie in the ranges (`InRanges a n rt`,
  `MemFrame.writeLE_inRanges`), handles ranges of the form `rt ++ [ … ]`, and composes callee
  frames whose ranges mention `rt`.
* `InRanges.disjoint`: an object inside `rt` is disjoint from a range outside `rt`.

### 4. What a contract hypothesis means for trust

A verified theorem with a contract hypothesis says: *if* the runtime function behaves as the
contract says (in the model), *then* the function under proof meets its specification. It
says nothing about the runtime. Read the contract definition as part of the statement; it lives
in the framework (`Janus/Contracts/*.lean`), whose sources are pinned like every other framework
module, or in the proof file (then `janus verify` discloses its body under "Proof-local
definitions"). A contract that no code could satisfy makes the theorem vacuous, so contracts are
written to be satisfiable by the real runtime under the model's rules: for instance they never
add memory regions (instructions cannot), see below.

Which parts of the runtime are proved rather than assumed is listed per contract kind below and in
[SOUNDNESS.md](SOUNDNESS.md#runtime-contracts).

## Contract kinds

### Heap allocation (`Janus/Contracts/Alloc.lean`, `Janus/Contracts/AllocAmd64.lean`)

TBD: filled in by the allocation work (see the module docs of `Janus/Contracts/Alloc.lean`).

### FFI (cgo) (`Janus/FFI.lean`, `Janus/Amd64/FFI.lean`)

The Go → C boundary does not use the linked-code `Summary` mechanism above. The trusted part has
to run the C code in the model (the C wrapper and the C function are extracted and executed), and
it has to nest a second contract (`_cgo_topofstack`) inside that C run. So
`runtime.cgocall`, `_cgo_topofstack` and `runtime.cgoUse` are `external` stubs
(`Janus.StubKind.external`, classified by the extractor), and the theorem names a `Contract`
for them (`EnsuresC p C …`, semantics `ReturnsC`). See [FFI.md](FFI.md) for the full picture.

**Statement.** A Go-side theorem is stated under `CgoSpec fn G E`: "`cgocall` of the wrapper
`fn` in a state satisfying `G` returns with the Go state restored (`GoResume`) and memory `E s`
outside `cgoClobber s`". `CgoCall.refines` discharges it from a proved `CEnsuresC` of the C
wrapper, giving a theorem under `CgoCall p` alone. The end-to-end examples print
`EnsuresC Extracted.program (CgoCall Extracted.program) …`.

**What stays trusted.** Exactly the definitions `CgoCall`, `CgoEntry`, `CgoResumed`,
`GoResume`, `cgoClobber` and `TopOfStack`, both ISAs. As claims about the Go 1.26 runtime on
Linux:

1. *The C call.* `asmcgocall` calls the C code at `fn` with the C calling convention: `X0`/`RDI
   = arg`, return address outside the extracted code, `SP` 16-byte aligned (amd64: `RSP + 8`),
   `DF` clear. It runs on a system stack with at least `cgoCStack` (4096) bytes free below `SP`.
   That stack is not memory the Go state grants (`stackSep`), and the C code runs on the same
   thread (`TPIDR_EL0`/`FS`).
2. *Go memory during the call.* Between the Go state at `cgocall` and the C call, and between
   the C return and the Go resume, the runtime (`entersyscall`, `exitsyscall`, the scheduler,
   `asmcgocall`) changes no byte of the memory the theorem grants, except:
   * the goroutine stack below `SP` (`cgoStackScratch` = 1024 bytes; the linker bounds the
     nosplit chain at 800);
   * the spill slots of `cgocall`'s two register arguments (`[SP+8, SP+24)`);
   * the `g` struct (456 bytes in Go 1.26.0);
   * the TLS `g` slot.

   This assumes that the granted regions contain no runtime-internal memory (`m`, `p`, the
   scheduler, the `g0` stack). That holds for any caller whose precondition grants only its own
   stack frame, its arguments and its globals.
3. *The return.* The C code returns with its callee-saved registers restored (which `asmcgocall`
   relies on, and which the C proof establishes). `cgocall` then returns to the Go caller at its
   return address, with `SP` and `FP` restored and `g` the same goroutine. On amd64 also
   `X15 = 0`, `DF` clear, and `FS:-8 = g` for a possibly different thread's `FS`. All other
   registers, the flags and the vector registers are arbitrary. The goroutine may resume on
   another OS thread (`exitsyscall`'s slow path), so `TPIDR_EL0`/`FS` are arbitrary afterwards.
4. *`_cgo_topofstack`.* During one cgo call it returns the same value every time (no callback into
   Go moves the stack; callbacks are not modelled: the C code would have to reach `crosscall2`,
   which is not extracted, so such a run cannot be proved). It preserves every other register and
   writes only its frame (arm64: the 56 bytes below `SP`; amd64: nothing).
5. *No concurrency.* As everywhere in Janus: no other goroutine or thread writes the granted
   memory during the call. The garbage collector does not move or modify objects that are
   reachable from the arguments (cgo pins the Go memory it passes to C).

Everything else is executed by the model from the binary's bytes: the Go function, its cgo
`_Cfunc_` wrapper (including the stack check and the `_Cgo_always_false` test), the C wrapper,
and the C function.
