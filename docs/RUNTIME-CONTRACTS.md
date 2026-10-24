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

### Dynamic calls (interface methods, closures, method values, `defer`)

These are not contracts in the sense above (no code is left out): the call's possible targets are
extracted, and the theorem states which one the call reaches.

An interface method call, a call of a func value (a closure or a method value) and the call of a
deferred closure are indirect calls: the target is a word the code loads from memory (`Fun[k]`
of the interface's itab, word 0 of the funcval). Janus treats them as follows.

**The target is stated, not inferred from Go's types.** When the interface value or func value
comes from the caller, the theorem says which code the call reaches, as hypotheses on the call
state's memory (`Janus.Spec.Dynamic`, both ISAs):

| Hypothesis | Meaning |
|---|---|
| `ItabIs Extracted.program.data s.mem tab "go:itab.*T,I"` | The itab word `tab` is the address of the static itab of dynamic type `T` for interface `I`, copied from `.rodata` into `Program.data`, and memory holds its bytes read-only. Its `Fun[k]` slot is then the address of `T`'s `k`-th method of `I` (methods sorted by name). |
| `FuncvalIs s.mem f (segAddr Extracted.program "pkg.F.func1")` | The funcval at `f` holds the code address of that function. |
| `ClosureCtx s.mem f [v₀, v₁, …]` | The captured variables (pointers, for variables the closure modifies) follow at `f + 8`, `f + 16`, …; the closure reads them through the context register (`X26` on arm64, `RDX` on amd64). |

These are ordinary parts of the printed statement, so `janus verify` and the auditor show and
check them like the rest of the precondition. A theorem holds only for callers whose interface or
closure is the one stated; to cover several dynamic types, prove one conjunct per type
(`examples/proofs/HashWith.lean`).

When the code being proved builds the func value itself (a method value or closure passed to a
callee, an open-coded `defer`), the code word is read back from the code's own store and no
hypothesis is needed (`HashTwice`, `DeferAdd`).

**The target's code is extracted, untrusted.** `janus extract --targets SYM,…` copies the code a
dynamic call may reach: for an itab every method in it (and the itab as a data object named after
its symbol), for a static funcval `…·f` or a function name that function. The extractor also
infers targets from user code: function addresses it computes (closures and method-value
wrappers `T.M-fm` it builds) and the itabs and funcvals it loads from `.rodata`. Runtime-internal
indirect calls (`systemstack` closures and the like) are not inferred. Every added target is
recorded in `identity.json` (`dynamicTargets`, with `via` = `targets`, `itab`, `funcval` or
`code-address`), and `janus check` re-applies the recorded `--targets`. A missing target makes
the call fault (`noCode`), so it can only make a proof impossible.

**The callee is then a callee like any other.** Once the target register is a literal (after
`janus_dyn` has turned the hypotheses into equations), `janus_run` / `janus64_run` uses the
target's `Summary` from `calls [...]`, or executes it.

**Heap-allocated defer records.** A function whose defers the compiler cannot open-code calls
`runtime.deferprocStack`/`runtime.deferproc` and `runtime.deferreturn` (which itself runs the
deferred calls, dynamically). They can be left out with `--contract`
(`--contract 'runtime.deferproc*' --contract runtime.deferreturn`; a `--contract` pattern takes
precedence over the built-in omission of `deferreturn`), but no contract library describes them:
a theorem would have to state, as a `Summary` of the linked program, that `deferreturn` runs the
recorded closures. Such functions are unsupported for now.

**`defer`.** Open-coded defers (Go 1.26's default for up to 8 defers outside loops) are just code:
a funcval in the frame, a `deferBits` byte, and a call of the closure at each exit. The
`runtime.deferreturn` call such functions contain is reached only after a recovered panic; it is
not extracted (`omittedCalls` in `identity.json`). Defers that need a defer record
(`runtime.deferproc*`, with `runtime.deferreturn` at every exit) are not supported, and
`recover` and panics unwinding through deferred calls are out of scope (docs/SOUNDNESS.md).
