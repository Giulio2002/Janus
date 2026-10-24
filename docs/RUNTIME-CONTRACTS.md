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
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => … ∧ H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)) post
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
add memory regions (instructions cannot), see below. **Every contract needs a kernel-checked
satisfiability witness** (an implementation, its parameters, and a call state where the theorem
using it fires; `audit/round9/controls/NewPair_witness.lean`): before round 9 the allocation
contracts had none and were false for every implementation (round 9 C1,
`audit/round9/model/Unsat.lean`).

### 5. Readiness of the runtime (`RtReady`, round 9)

A `Summary` speaks about **every** state satisfying its precondition. A runtime function's
behaviour depends on the runtime's own state (the heap, the `mcache`, the current `g`, the free
stack below `SP`), which the caller does not control and the contract cannot describe in full.
So each contract takes a predicate `H : RtReady` (`List Nat → Nat → Nat → Memory → Prop`) and
requires `H args g sp (rtView rt s.mem)` at the call: the call's argument registers as numbers,
`g` (arm64 `R28`, amd64 `R14`), `SP` (amd64: `RSP` at the callee's entry) and the memory as the
runtime owns it (`rtView rt m`: `m`'s bytes inside `rt`, every other byte 0, and its regions).

* The theorem quantifies over `H` and assumes it **at its entry**, for the call it will make
  (`H [pairType] g (SP - 48) (rtView rt s.mem)` for NewPair, whose frame is 48 bytes). The
  caller's stores lie outside `rt`, which `rtView` cannot see (`rtView_writeLE`, a rewrite rule of
  the executors), so `janus_run` proves the call's readiness from the entry's.
* The real runtime meets the contract with `H args g sp v` := "from every call state with these
  arguments, this `g`, this `SP` and runtime memory `v` (whatever else memory holds) the
  runtime's code returns as the contract says". That is a function of what `H` sees, so the
  hypothesis is met by the real binary exactly at the calls the runtime serves as described:
  in the common case a free slot in the `mcache` span, enough heap, no stack growth, no GC
  assist that parks or shrinks the stack, no `mmap`. A call outside that (`make([]uint64, 1<<44)`
  throws `out of memory`, `audit/round9/probe`) is simply not one the theorem speaks about.

Which parts of the runtime are proved rather than assumed is listed per contract kind below and in
[SOUNDNESS.md](SOUNDNESS.md#runtime-contracts).

## Contract kinds

### Heap allocation (`Janus/Contracts/Alloc.lean`, `Janus/Contracts/AllocAmd64.lean`)

**Contracts.** `MallocgcContract`, `NewobjectContract`, `MakesliceContract` and
`GrowsliceContract` (arm64; the amd64 ones end in `64`: `NewobjectContract64`, …) state Go 1.26's
`runtime.mallocgc(size, typ, needzero)`, `newobject(typ)`, `makeslice(et, len, cap)` and
`growslice(oldPtr, newLen, oldCap, num, et)` as `Summary`s of the linked program. Each takes the
contract's address, the **runtime-owned ranges** `rt : List (Nat × Nat)` and the number of
stack bytes `stack` the runtime may use below `SP`. From any state at the entry with

* an admissible return address (arm64: `X30` 4-aligned, below `2^48`; amd64: `[RSP]` below
  `2^47`, a canonical address, since `RET` faults otherwise), an aligned `SP` and the window
  `[SP - stack, SP + 8 + 8·nargs)` writable (`CallOK`, `CallOK64`);
* a readable type descriptor (`TypeOK`: `Size_` at offset 0, `PtrBytes` at offset 8) and
  arguments that take no panic or throw path (`makeslice`: `len ≤ cap`, `Size_·cap ≤ maxAlloc`;
  `growslice`: `oldLen ≤ oldCap < newLen < 2^40`, element size 8 without pointers);

the function returns to the caller (`AllocRet`/`AllocRet64`: the ABI's preserved registers kept,
the results in the result registers, every other register, the flags and the vector registers
unspecified) with memory changed only inside `rt` and the callee's stack window
(`MemFrame s.mem m (rt ++ calleeStack s stack nargs)`), and, for a non-zero size, a **fresh**
object (`Fresh`):

* `[ptr, ptr + blockSize size noscan)` inside one of the ranges of `rt` (`InRanges`), below
  `2^48`, writable. `blockSize` is `roundupsize` (Go's size-class rounding, `msize.go`,
  transcribed with the class table `sizeClasses`), except for a tiny pointer-free allocation
  (`< 16` bytes), which shares a 16-byte block and owns only its own bytes;
* 8-aligned when `size ≥ 16` or a multiple of 8, 16-aligned when `size` is a multiple of 16
  (objects of a size class are laid out from a page-aligned span base; every class except 8 and
  24 is a multiple of 16; large objects are page-aligned), **except** a pointerful object of
  more than 512 bytes that is still small (`mallocHdr`): Go 1.26 stores an 8-byte malloc header
  in the slot and returns `slot + 8`, which is 8 mod 16 (round 9 C2; before, the contract
  promised 16-alignment for it, which the real runtime never gives);
* zero for its first `size` bytes when the call asks for zeroing (`newobject` and `makeslice`
  always do; `mallocgc` when `needzero` or the type has pointers).

`growslice` (8-byte pointer-free elements) also returns the new length and the new capacity
`growCap8 newLen oldCap` (`nextslicecap`, then `roundupsize`), copies the old elements and zeroes
the array from the new length on; the bytes of the appended elements are unspecified (the caller
writes them). `le_growCap8` proves the capacity holds the new length.

`.pos` (and `GrowsliceContract.withOld`/`.empty`) specialise a contract to a call site with
`Summary.mono`, e.g. to a non-zero size, so that the post has no implication.

**Runtime-owned memory.** `rt` is a parameter of every statement; a caller's precondition says
that its own data lies outside it (`Outside a n rt`). Freshness is then a theorem
(`InRanges.disjoint`): the object is inside `rt`, everything the caller holds is outside. The
contract does not shrink `rt` after an allocation, so two allocations under the same `rt` may
overlap as far as the contract says; the examples allocate once. Memory regions are never
added by a contract (no instruction can add one, so such a contract would be unsatisfiable and
the theorem vacuous): the arena memory is among the regions already, as Go's heap arenas are
reserved address space.

**Examples** (`examples/basic/zalloc.go`; arm64 `examples/proofs/`, amd64 `examples/proofs-amd64/`):

| Function | Contract | Guarantee |
|---|---|---|
| `NewPair(a, b) *Pair` | `newobject` | fresh 16-byte object in `rt`, 16-aligned, holding `a`, `b` |
| `MakeSlice(n) []uint64` | `makeslice` | `len = cap = n`; for `n > 0` a fresh, 8-aligned, all-zero array of `n` words |
| `AppendOne(s, x)` | `growslice` | room left: `x` stored in place; full (also nil): fresh array of capacity `growCap8 (len+1) cap` holding the old elements, `x`, then zeros |
| `SetNext(n, q)` | none (the barrier's flush, `wbBufFlush`, is a contract the precondition makes unreachable) | `n.Next = q`; with the write barrier on, `q` and the old value recorded in the P's write-barrier buffer, executed from the barrier's machine code |
| `MallocFast` (`runtime.mallocgc` itself, arm64) | none (every slow path is an unreachable contract) | the small pointer-free fast path, see below |

**What is proved about the allocator itself.** See `examples/proofs/MallocFast.lean` and
[SOUNDNESS.md](SOUNDNESS.md#runtime-contracts).

### Dynamic calls

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

**`defer`.** Open-coded defers (Go 1.26's default for up to 8 defers outside loops) are just code:
a funcval in the frame, a `deferBits` byte, and a call of the closure at each exit. The
`runtime.deferreturn` call such functions contain is reached only after a recovered panic; it is
not extracted (`omittedCalls` in `identity.json`). Defers that need a defer record
(`runtime.deferproc*`, with `runtime.deferreturn` at every exit) are not supported, and
`recover` and panics unwinding through deferred calls are out of scope (docs/SOUNDNESS.md).
