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

Every runtime function a framework contract describes is **pinned to its code** when
`--contract` names it (`runtimeContractStubs` in `cmd/janus/extract.go`, checked by
`checkContractPin`): the interface, equality, hashing, typed-memory and map runtime, and the
allocation, slice and write-barrier entries `runtime.mallocgc`, `newobject`, `makeslice`,
`growslice` and `gcWriteBarrier1`–`8` (`allocContractStubs`). Its normalized code must be one of
the hashes `scripts/gen-stubpins.sh` measured for the pinned toolchains, so the contract
hypothesis is about the Go runtime's own function, not about whatever code a binary placed under
that name. `audit/roundfw/run-roundfw.sh` (rows `P_*`) changes one byte of each of those five
functions on both ISAs and checks that the extraction is rejected, and that the unchanged binary
records `"pinned": true`. (`runtime.typehash` stays unpinned: its jump table makes its
normalized code differ between programs.)

A verified theorem with a contract hypothesis says: *if* the runtime function behaves as the
contract says (in the model), *then* the function under proof meets its specification. It
says nothing about the runtime. Read the contract definition as part of the statement; it lives
in the framework (`Janus/Contracts/*.lean`), whose sources are pinned like every other framework
module, or in the proof file (then `janus verify` discloses its body under "Proof-local
definitions"). A contract that no code could satisfy makes the theorem vacuous, so contracts are
written to be satisfiable by the real runtime under the model's rules: for instance they never
add memory regions (instructions cannot), see below. **Every contract needs a kernel-checked
satisfiability witness** `theorem <name>_satisfiable` in `Janus/Contracts/<File>Sat.lean`
(`<File>SatAmd64.lean`): an implementation, its parameters, and a call state satisfying the whole
precondition (`AllocSat.lean`; for a whole theorem, `audit/round9/controls/NewPair_witness.lean`).
`audit/round9/run-round9.sh` (row SAT) fails for any contract without one, except those listed as
open in `audit/round9/sat-pending.txt`: before round 9 the allocation
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

* **A satisfiable contract can still be instantiated into a vacuous one** (round 10 V1). The
  theorem must quantify the runtime: `janus verify` (the auditor) rejects a statement in which
  a contract (other than its whole conclusion) is applied to anything but variables of the
  statement for its runtime arguments (`impl` inside `Extracted.program.link impl`, `rt`, `H`, the models `R`/`M`), or in
  which another premise mentions such a variable (only the model laws `R.Laws`/`M.Laws` may).
  `H := fun _ _ _ _ => True` ("always ready") brought round 9 C1 back: the contract is false for
  every implementation and NewPair "returned 42" (`audit/round10/attacks/V1a_contract_H_true.lean`);
  likewise `rt := []`, `(hrt : rt = [])`, a contract about `Extracted.program` itself, or the toy
  model `R0`. What the rule does not catch: constraints inside the theorem's own precondition
  (the `Ensures … pre`) and the numeric parameters such as `stack`, which the reader checks as
  any precondition.
* **Readiness is not handed back.** A contract whose postcondition re-establishes everything its
  precondition needs can be chained without bound from one call state; when the call allocates
  memory it keeps or cannot free, no implementation (maps, round 10 V2) or no real-runtime
  implementation (interfaces, V3) meets it. Every allocating contract therefore takes its own
  `H`, required at the call and not given back.

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

<a id="dynamic-calls"></a>

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

**Heap-allocated defer records, `recover`, panics.** These go through the Go 1.26 panic runtime;
see [Panics, defer, recover](#panics-defer-recover) below. Open-coded defers (Go 1.26's default for
up to 8 defers outside loops) are just code: a funcval in the frame, a `deferBits` byte, and a call
of the closure at each exit, executed like any other code (`DeferAdd`, `DeferInc`). The
`runtime.deferreturn` call such functions contain is reached only after a recovered panic; without
`--contract runtime.deferreturn` it is not extracted (`omittedCalls` in `identity.json`).

### Maps (`Janus/Spec/Map.lean`, `Janus/Contracts/Map.lean`, `MapVar.lean`, `MapStr.lean` and their `…Amd64.lean` files)

Go 1.26 maps are Swiss tables (`internal/runtime/maps`). The compiler lowers map operations to
calls of linknamed runtime functions; a map theorem leaves those out with `--contract` and takes
their behaviour as hypotheses. The internal layout never appears in a statement.

**The abstract view (`Janus/Spec/Map.lean`).** A map's contents are `f : AMap K V := K → Option V`
(`AMap.empty`, `f.set k v`, `f.erase k`). `Keys f ks` says `ks` lists every key once (one
iteration order); `Keys.perm` makes any two listings permutations of each other, and
`sumValues_keys` says a sum of the values does not depend on the order. A theorem quantifies over
**every** `M : MapModel K V`:

| Field | Meaning |
| --- | --- |
| `M.Rep mem mp f` | the non-nil map with header at `mp` holds `f` in `mem` |
| `M.Iter mem it mp f ks` | the iterator struct at `it` still has to produce the keys `ks`, in that order |
| `M.Typ t` | `t` is the type descriptor (`abi.SwissMapType`) of the map type `M` is about |
| `M.Env mem g` | the runtime around the maps is usable (allocator has room, zero value is zero, ...) |
| `M.priv` | the runtime's private memory, as ranges: every header, directory, table, group, the zero value |
| `M.depth` | stack bytes below `SP` a map runtime call may use |

`IsMap M mem mp f` is the Go map value: `mp = 0` (nil) and `f` empty, or `M.Rep`. The only
properties of `M` a proof may use are the laws `M.Laws` (a hypothesis of every theorem) and the
contracts:

* `rep_frame`, `iter_frame`, `env_frame`: the representation lives in `M.priv` (an iterator also
  in its own struct): memory changes elsewhere, with the same accessible ranges (`Agrees`), keep it;
* `len`: a header's first word (`Map.used`, which `len(m)` loads inline) is the number of keys, and
  it is readable;
* `finite`: a represented map has finitely many keys.

Quantifying over `M` is what keeps `Rep` abstract: the theorem holds for the real runtime as soon
as *some* representation satisfies the laws and contracts for the real code, and a statement that
mentioned the Swiss layout would be wrong if our reading of the layout were. Applied to one
concrete execution, `M` can be chosen for it (`M.priv` = all memory except the objects the program
holds, `M.Env` = the allocator only hands out private memory), so the fixed `M.priv` is not a
restriction in practice.

**The contracts.** Each is `∀ f, Summary p addr pre post` (with `p = Extracted.program.link impl`
and `addr = Extracted.program.contractAddr "runtime.…"`):

| Go source | Runtime entry (Go 1.26) | arm64 / amd64 contract | Effect on `f` |
| --- | --- | --- | --- |
| `v := m[k]` (uint64 key) | `runtime.mapaccess1_fast64(t, m, k)` | `Access1` | none; returns a slot holding `(f k).getD 0` |
| `v, ok := m[k]` | `runtime.mapaccess2_fast64(t, m, k)` | `Access2` | as `Access1`, plus `ok` in the low byte of `X1` / `RBX` |
| `m[k] = v` | `runtime.mapassign_fast64(t, m, k)` + a store | `Assign` | a writable slot `p`: storing any `v` at `p` makes `f.set k v` |
| `delete(m, k)` | `runtime.mapdelete_fast64(t, m, k)` | `Delete` | `f.erase k` |
| `make(map[K]V)` | `runtime.makemap_small()` | `MakeSmall` | a fresh non-nil `AMap.empty` |
| `clear(m)` | `runtime.mapclear(t, m)` | `Clear` | `AMap.empty` |
| `for k, v := range m` | `runtime.mapIterStart(t, m, it)`, `runtime.mapIterNext(it)` | `IterStart`, `IterNext` | none; see below |
| `v, ok := m[*kp]` (`[16]byte` key) | `runtime.mapaccess2(t, m, kp)` | `Access2Ptr` | as `Access2`, key = the 16 bytes at `kp` |
| `make(map[K]V, n)` (`n` not a constant `≤ 8`) | `runtime.makemap(t, n, nil)` | `MakeMap` | a fresh non-nil `AMap.empty` |
| `v := m[*kp]`, other keys (e.g. `[24]byte`) | `runtime.mapaccess1(t, m, kp)` | `Access1G` | as `Access1`, key = `keyAt` of the `n` bytes at `kp` |
| `v, ok := m[*kp]` | `runtime.mapaccess2(t, m, kp)` | `Access2G` | as `Access2` |
| `m[*kp] = v` | `runtime.mapassign(t, m, kp)` + a store | `AssignG` | `AssignSlot`: storing `v` makes `f.set key v` |
| `delete(m, *kp)` | `runtime.mapdelete(t, m, kp)` | `DeleteG` | `f.erase key` |
| `v := m[k]`, `V` over 1024 bytes | `runtime.mapaccess1_fat(t, m, kp, zero)` | `Access1Fat` | the value's slot, or the caller's `zero` |
| `v, ok := m[k]`, `V` over 1024 bytes | `runtime.mapaccess2_fat(t, m, kp, zero)` | `Access2Fat` | as `Access1Fat`, plus `ok` |
| `v := m[k]` / `v, ok := m[k]` (4-byte key) | `runtime.mapaccess1_fast32`, `runtime.mapaccess2_fast32` | `Access1F32`, `Access2F32` | key = `W2` / `ECX` |
| `m[k] = v` (4-byte key) | `runtime.mapassign_fast32(t, m, k)` + a store | `AssignF32` | `AssignSlot` |
| `delete(m, k)` (4-byte key) | `runtime.mapdelete_fast32(t, m, k)` | `DeleteF32` | `f.erase k` |
| `m[p] = v` (pointer key) | `runtime.mapassign_fast64ptr(t, m, p)` + a store | `Assign64Ptr` | `AssignSlot`; lookups use `Access1`/`Access2` on the same model |
| `v := m[k]` (string key) | `runtime.mapaccess1_faststr(t, m, k)` | `Access1Str` (`Access1Str64`) | key = `strKey`: the string's length and bytes |
| `v, ok := m[k]` (string key) | `runtime.mapaccess2_faststr(t, m, k)` | `Access2Str` (`Access2Str64`) | as `Access2` |
| `m[k] = v` (string key) | `runtime.mapassign_faststr(t, m, k)` + a store | `AssignStr` (`AssignStr64`) | `AssignSlot`; the key's bytes must be the runtime's (`StrOwned`) |
| `delete(m, k)` (string key) | `runtime.mapdelete_faststr(t, m, k)` | `DeleteStr` (`DeleteStr64`) | `f.erase (strKey …)` |
| `len(m)` | inline load | `MapModel.Laws.len` | |

**One abstract map for every entry point.** All of them are stated on the same `M : MapModel K V`
for a map type, so a theorem that mixes entry points (`mapassign_fast64ptr` and
`mapaccess1_fast64` on a `map[*T]int`, `mapassign` and `mapaccess1` on a `map[[24]byte]int`)
uses one model. The new contracts take the value size `vs` (`V = BitVec (8 · vs)`, the slot's
little-endian contents: `vs = 1` for `bool`, `vs = 8` for `int`, so `BitVec (8 · 8)` is the
`BitVec 64` of the older contracts) and the key decoding of their entry point: `BitVec 64` for
`_fast64`/`_fast64ptr`, `BitVec 32` for `_fast32` (`key32`: the low half of the register),
`strKey` (length and bytes) for `_faststr`, `keyAt` (the `n` key bytes, little-endian) for the
generic entry points.

**Generic keys, through the key type's hash and equality.** `mapaccess1`/`mapaccess2`/`mapassign`/
`mapdelete` hash the key with `t.Hasher(key, m.seed)` and compare with `t.Key.Equal`, so which
keys are equal is decided by those functions. The generic contracts are stated for key types of
regular memory (`KeyRegular (rtView M.priv s.mem) t n`: the descriptor's key type has `Size_ = n`
and `TFlagRegularMemory`, read in the runtime's memory, where descriptors live). For them `Equal`
is `memequal` of the `n` bytes and the hash is the seeded byte hash of R4 (`HashModel.regHash`, an
uninterpreted function of the seed and the bytes; `HashModel.Laws.regular`), so equal keys are
exactly equal bytes and the abstract key is `keyAt`. Keys with floats, strings or interfaces
inside are not covered by these contracts (their abstract key is not their bytes).

**Readiness of allocating entry points (finding R3-C1).** `makemap_small`, `makemap` and every
`mapassign*` allocate. Before R3 `Assign` and `MakeSmall` promised to succeed from every state
satisfying `RTPre`, and `RTPre` comes back after every call (`M.Env` holds again): from one non-nil
map, `2^64` assignments of new keys would build a map whose count no header word holds
(`MapModel.Laws.len`), and `2^48 + 1` calls of `makemap_small` would need that many distinct map
addresses below `2^48`. `audit/maps/model/Unsat.lean` proves both old contracts false, on both
ISAs, for every call state whose guard word lies outside what the call may write
(`old_assign_unsat`, `old_makeSmall_unsat`, `…64`), and `old_*_vacuous` show that every theorem's
`CallerOK` provides that condition: `Insert`, `InsertGet` and `NewMap` were vacuous. The real
runtime throws `out of memory` long before. Now each allocating contract takes the round-9
readiness predicate `H : RtReady` and requires `Contracts.Ready H M.priv args s` (amd64:
`Ready64`): `H` sees the arguments (for `mapassign` also the key's value, for `mapassign_faststr`
its header), the goroutine, `SP` and the runtime's memory (`rtView M.priv`). A theorem assumes
`H` at its entry for the one allocating call it makes. The read-only entry points (lookups,
`delete`, `clear`, iteration) do not allocate and keep the perpetual `M.Env`.

**Other fixes of R3.** `Access2Ptr`, every generic and string access (`KeyIn`, `StrIn`) and
`IterStart`/`IterNext` require the key or the iterator struct outside the callee's stack window
(`calleeStack`): the runtime's frames overwrite that window, so a key there would be read after
it changed, and the pre-R3 `Access2Ptr`/`IterStart`/`IterNext` promised more than the runtime
does. On amd64 the iterator must also miss the return-address slot `[RSP, RSP + 8)` (`retSlot`),
which the callee's `RET` reads after storing into the iterator.

**Satisfiability.** Every map contract, old and new, on both ISAs, has a kernel-checked
`<contract>_satisfiable` (`Janus/Contracts/MapSat.lean`, `MapVarSat.lean`, `MapStrSat.lean` and
their `…Amd64` files; round 9's SAT row): toy models from `Janus/Contracts/MapModel0.lean` (`ME`:
one empty non-nil map; `MC`: one map of at most one entry, with readiness `HAssign`/`HMake`),
machine code proved to meet the contract for them, and a call state, with a non-nil map, that
satisfies the whole precondition. Two contracts constrain what a model can be: `IterNext` does not
say the iterator struct is writable (a model's `Iter` must imply it, `MapSat.MEI`), and
`AssignStr`'s key may lie anywhere in the runtime's memory, so a readiness predicate excludes keys
overlapping the map's own storage (`MapStrSat.HAssignS`), as the real runtime's readiness does.

The common shape, `RTPre` and `RTReturn`:

* **pre**: `M.Env` with the goroutine (`X28` / `R14`), for allocating calls the readiness `H`, the stack guard at least `M.depth` bytes
  below `SP`, the stack window `[SP - M.depth, SP + 8 + 8·nargs)` writable and outside `M.priv`,
  an admissible return address (`X30` 4-aligned below `2^48`; on amd64 the word at `[RSP]` below
  `2^47`, which `RET` needs, plus `X15 = 0` and `DF` clear), and
  `M.Typ` for the descriptor in the first argument register;
* **post**: the call returns to the caller with `SP`, `X18`/`X28`/`X29` (amd64: `RSP + 8`, `RBP`,
  `R14`, `X15`) preserved and everything else arbitrary; memory changes only in `M.priv`, at most
  `M.depth` bytes below `SP` (arm64: never the caller's saved frame pointer at `[SP-8, SP)`; amd64:
  never the return-address slot) and the argument spill slots (`MemFrame … (rtWrites M s nargs ++
  extra)`); `M.Env` holds again; every other map keeps its contents (`OthersKept`).

**Round 10 V2** found the same vacuity independently (`audit/round10/model/MapUnsat.lean` proves
it in the kernel; `audit/round10/attacks/V2a_map_assign_vacuous.lean` used it to "verify" that
Insert stores `v + 1`). It is closed by the R3-C1 readiness above (`Contracts.Ready H M.priv args
s`, not handed back by the call); witnesses: `Janus/Contracts/MapSat.lean`, `MapSatAmd64.lean`.

A theorem's caller-side precondition is `CallerOK M s frame above`: the environment, the stack
guard `M.depth + frame` below `SP`, the window `[SP - M.depth - frame, SP + above)` writable and
outside `M.priv`, and the guard word `16(g)` outside the window and `M.priv`. `RTPre.of_caller` and
`RTPre.of_parts` turn it into the contract precondition at a call site.

**Assignment precisely.** `mapassign` returns a pointer to the value slot and the compiled code
stores into it. The contract gives the slot as writable 8 bytes inside `M.priv` and, for every
value `v`, that the memory after the 8-byte store of `v` represents `f.set k v` (with `M.Env` and
the other maps intact). It says nothing about the memory before the store, so a theorem can only
use the map after the store, as the compiled code does.

**Iteration for every order.** `IterStart` promises some listing `ks` of the keys (`Keys f ks`)
and `M.Iter … ks`, plus what the compiled loop reads (`IterView`): the key pointer at `it + 0` is
`0` when no keys are left, otherwise it points to the current key and the element pointer at
`it + 8` points to its value. `IterNext` removes the head of the list. The contracts never say which
order, so `SumValues` is proved for an arbitrary `ks` and its statement quantifies over every listing:
the result equals `sumValues f ks % 2^64` for all of them. Modifying the map during the loop is
not covered (`IterNext` requires the map unchanged).

**Nil maps.** Access and iteration contracts accept `mp = 0` with `f` empty (access returns a
pointer to the zero value, iteration produces no keys; `len` is `0` by the inline nil test).
`mapassign` on a nil map panics (`panic(plainError("assignment to entry in nil map"))`) inside
the runtime; `Assign` requires a non-nil map, so no theorem here covers that call: the panic is
raised by code the extraction leaves out, not by a panic stub of the extracted program.

**Concurrency.** The runtime's detection of concurrent misuse (`fatal("concurrent map writes")`,
the `writing` flag) cannot trigger in the single-threaded model and is not part of any contract.

**What is proved rather than assumed.** `examples/proofs/MapAccess1Small.lean` (arm64) and
`examples/proofs-amd64/MapAccess1Small/Proof.lean` (amd64) verify the machine code of
`runtime.mapaccess1_fast64` against `Access1` for the concrete
representation `smallModel t zeroVal heap` (`Janus/Spec/SwissMap.lean`): nil maps, and small Swiss
maps (`SwissSmall`: `dirLen = 0`, `writing = 0`, one group of a control word and 8 key/value slots
of 16 bytes, control byte `< 0x80` = full, `used` = number of entries, all inside `heap`; the slot
size `16` at `t + 88` and `runtime.zeroVal` readable and zero). arm64 scans with the
`MVN`/`AND 0x8080…` byte mask (`maskFrom`, `mask_toNat`), amd64 with `PMOVMSKB`/`NOT` (`fullMask`).
`smallModel_laws` proves the laws
for it. So for small maps the `Access1` hypothesis is discharged by the real code. Still trusted:
every other contract, the large-map path of `mapaccess1_fast64` (hashing through the type's hasher
by an indirect `BLR`, directory and table probing), and the reading of Go 1.26's layout in
`SwissSmall` (a property of the maps the runtime builds that is not proved here). `H2` tags are not
part of `SwissSmall` because the small-map lookup does not read them.

**Examples** (`examples/basic/maps.go`, `maps2.go`; arm64 `examples/proofs/<Name>.lean`, amd64
`examples/proofs-amd64/<Name>/Proof.lean`): `Lookup`, `Insert`, `InsertGet` (two contracts; the
read-back returns `v`), `Delete`, `SumValues` (iteration, every order), `CountKeys` (no contract),
`LookupKey16` (generic `mapaccess2`), `NewMap`, `ClearMap`, and `MapAccess1Small` (the runtime
function itself, extracted as `runtime.mapaccess1_fast64`); R3: `LookupS`, `InsertS`, `DeleteS`
(`map[string]uint64`, `_faststr`), `LookupK24`, `InsertK24` (`map[[24]byte]uint64`, generic),
`Has32`, `Set32` (`map[uint32]bool`, `_fast32`, 1-byte values), `InsertPtr`, `LookupPtr`
(`map[*PNode]uint64`, `_fast64ptr` and `_fast64` on one model), `MakeHint` (`makemap` with a
hint). The R3 examples and `SumValues` each prove `Witness.nonvacuous`: a model, code meeting the
contracts, a readiness predicate where needed and a call state with a non-nil map satisfying the
whole precondition.

### String comparison (`Janus/Contracts/Cmpstring.lean`, `Janus/Contracts/CmpstringAmd64.lean`)

Go compares strings (`<`, `min`/`max` of strings through `runtime.strmin`/`runtime.strmax`) with
`runtime.cmpstring(a, b string) int`, assembly in `internal/bytealg/compare_*.s`. A theorem leaves it
out with `--contract runtime.cmpstring` and assumes `CmpstringContract` (arm64; amd64:
`CmpstringContract64`) at its address, with a stack allowance (`16` in the examples; the real
function uses none):

* **pre** (`CmpstringPre`, `CmpstringPre64`): the ABI conditions of the allocation contracts
  (`CallOK`/`CallOK64` with 4 arguments) and both strings readable (`StrOK m p n`: `n = 0`, or the
  `n` bytes at `p` in one region below `2^48`). Arguments: arm64 `a = (X0, X1)`, `b = (X2, X3)`;
  amd64 `a = (RAX, RBX)`, `b = (RCX, RDI)`.
* **post** (`CmpRet`, `CmpRet64`): the call returns to its caller (`retState`, `retState64`) with
  the result register holding the two's-complement `strCmp`, the bytewise lexicographic
  comparison (`-1`, `0`, `1`; a proper prefix is smaller), the ABI's preserved registers kept,
  everything else arbitrary, and memory changed at most in the callee's stack window
  (`calleeStack`, `calleeStack64`).

**Satisfiable.** `Janus.Contracts.CmpstringSat.cmpstring_satisfiable` and
`Janus.Contracts.CmpstringSatAmd64.cmpstring64_satisfiable`: a byte loop (A64, x86-64; machine code
in the files) placed in an otherwise empty program meets the contract for every call state,
proved by symbolic execution and induction on the remaining length, and a call state satisfying
the precondition exists. So a theorem assuming the contract is not vacuous.

**Not covered.** The real `cmpbody` (16-byte `LDP`/`REV` chunks on arm64, SSE/AVX2 loops on amd64)
is not executed; that it meets the contract is assumed. `strCmp` reads memory at the call, so the
caller's theorem keeps the string bytes outside the stack frames it writes before the call (the
`MinStr` preconditions).

**Example** (`examples/basic/zzconstructs2.go`): `MinStr(s, t) = min(s, t)` (`runtime.strmin`
executed): `t` when `strCmp t s < 0`, else `s`.

### Interfaces (`Janus/Spec/Type.lean`, `Janus/Contracts/Iface.lean`, `Janus/Contracts/IfaceAmd64.lean`)

Go 1.26 boxes values into interfaces with `runtime.convT*`, asserts and switches on dynamic
types with an inline probe of a per-site cache and, on a miss, `runtime.typeAssert` /
`runtime.interfaceSwitch` (`assertE2I(2)` from generic code), and compares interfaces with
`runtime.efaceeq` / `ifaceeq` (`runtime/iface.go`, `runtime/alg.go`). A theorem leaves these
functions out with `--contract` and takes their behaviour as hypotheses over an abstract model
of the runtime; the compiled code around them (type-word and hash compares, the cache probes,
the itab and data words) is executed from the binary.

**Layout and model (`Janus/Spec/Type.lean`).** The layouts the code and the runtime read
(`internal/abi`, Go 1.26, both ISAs): `abi.Type` (`Size_` 0, `PtrBytes` 8, `Hash` 16, `TFlag`
20 with `TFlagRegularMemory` 8 and `TFlagDirectIface` 32, `Kind_` 23, `Equal` 24),
`abi.InterfaceType` (`Methods` length at 64), `abi.ITab` (`Inter` 0, `Type` 8, `Hash` 16, `Fun`
24), `abi.TypeAssert` (`Cache` 0, `Inter` 8, `CanFail` 16) and its cache (`Mask`, then 16-byte
`Typ`/`Itab` entries), `abi.InterfaceSwitch` (`Cache` 0, `NCases` 8, `Cases` 16) and its cache
(24-byte `Typ`/`Case`/`Itab` entries). What the runtime computes from them is abstract: a theorem
quantifies over **every** `R : IfaceModel`:

| Field | Meaning |
| --- | --- |
| `R.itab inter typ` | `getitab(inter, typ, true)`: the itab of the pair (non-zero) or `none` if `typ` does not implement the non-empty interface `inter`; one value per pair for the whole run |
| `R.eq t m x y`, `R.Comparable t m x y` | `t.Equal(x, y)` on the values in memory `m`, and that it returns (no uncomparable type inside, stack within `R.depth`) |
| `R.IsType t`, `R.IsInter i` | a type descriptor; a non-empty interface type |
| `R.Env m g`, `R.priv`, `R.depth` | as for maps: the runtime usable; its memory (heap, `itabTable`, `zeroVal`, `staticuint64s`, the empty caches, every type descriptor and itab); stack bytes it may use |

The laws `R.Laws` are facts about the data: the environment lives in `R.priv`; descriptors are
readable, inside `R.priv`; an itab is never `0`; a `TFlagRegularMemory` type that is not direct
compares its `Size_` bytes and is always comparable (`regular`), a direct one too (`direct`).
`StaticItabs R ds` (a separate hypothesis, used only by the corollaries that name a static itab)
says `getitab` returns every static `go:itab.<T>,<I>` of the extracted data for its pair: the
linker lists every reachable itab in `runtime.itablink` (`cmd/link/internal/ld/typelink.go`),
`itabsinit` adds them to `itabTable` before any Go code runs, and `getitab` only creates an itab
for a pair it does not find, so this holds for a statically linked binary (no plugins).

**Caches.** `TACacheOK R m c inter` / `ISCacheOK R m c cs` state what `buildTypeAssertCache` /
`buildInterfaceSwitchCache` maintain: `Mask = 2^k - 1`, entries readable in `R.priv`, every used
entry holding the runtime's answer for its type (the itab or `0`; the case index of
`switchCase`), and an empty entry, so every probe ends. A descriptor starts with
`runtime.emptyTypeAssertCache` / `runtime.emptyInterfaceSwitchCache` (`TACacheOK.empty`,
`ISCacheOK.empty`). `TADescOK R m d` / `ISDescOK R m d cs` add the descriptor: readable, its
`Cache` word writable (the runtime replaces the cache about once in a thousand misses), a
non-empty interface (the cases `cs`), a well-formed cache. A theorem asks for a well-formed
descriptor, so it holds in every state the runtime can leave the cache in, not only the initial
one; the proofs of the probe loops (`AsHasher`, `Classify`) go by induction on the cyclic distance
to an empty entry (`probe_dist`, `probe_zero`).

**The contracts.** Each is a `Summary` at the function's address, with the frame of the map
contracts (`RTPre`/`RTReturn`, the same register and stack rules, memory changed only in
`R.priv`, the callee's stack window, the spill slots and, for `typeAssert`/`interfaceSwitch`,
the descriptor's `Cache` word; `R.Env` holds again):

| Go | Runtime entry | Contract (arm64 / amd64) | Result |
| --- | --- | --- | --- |
| `any(v)` | `convT(t, &v)` | `ConvT` | a readable box in `R.priv` holding a copy of `t.Size_` bytes (`BoxCopy`) |
| same, pointer-free `T` | `convTnoptr(t, &v)` | `ConvTnoptr` | the same; `t.PtrBytes = 0` required (`mallocgc` throws otherwise) |
| 2/4/8-byte `T` | `convT16/32/64(v)` | `ConvT16`, `ConvT32`, `ConvT64` | a box holding `v` (`BoxHolds`; `&staticuint64s[v]` for `v < 256`) |
| `string` | `convTstring(s)` | `ConvTstring` | a box holding `(ptr, len)`, `(0, 0)` for `""` (`&zeroVal`) |
| `[]T` | `convTslice(s)` | `ConvTslice` | a box holding the header, `(0, 0, 0)` for a nil slice |
| `x.(I)` (generic code) | `assertE2I(inter, t)` | `AssertE2I` | the itab (`ItabResult`); a nil or non-implementing `t` panics: excluded |
| `v, ok := x.(I)` (generic code) | `assertE2I2(inter, t)` | `AssertE2I2` | the itab or `0` |
| `x.(I)`, `v, ok := x.(I)` | cache probe, `typeAssert(desc, t)` | `TypeAssert` | the itab or `0` for `desc.Inter` (non-nil `t`); failing without `CanFail` excluded; the descriptor well formed again, same `Inter` and `CanFail` |
| `switch x.(type)` with interface cases | cache probe, `interfaceSwitch(desc, t)` | `InterfaceSwitch` | `switchCase R t cs`: the first case `t` implements and its itab, else `(len cs, 0)` |
| `a == b` on `any` | `efaceeq(t, x, y)` | `Efaceeq` | `efaceEqual`: true for `t = nil`; for a direct type the words; else `R.eq t` |
| `a == b`, non-empty interfaces | `ifaceeq(tab, x, y)` | `Ifaceeq` | `ifaceEqual`: the same with `t = tab.Type` |

**Allocating calls need readiness** (round 10 V3). `ConvT`, `ConvTnoptr`, `ConvT16/32/64`,
`ConvTstring`, `ConvTslice`, `TypeAssert` and `InterfaceSwitch` take a readiness predicate
`H : RtReady`, required at the call for its argument registers, `g`, `SP` and
`rtView R.priv mem`, and not handed back. Each of them may allocate (a box on every
`convT64(v)` with `v ≥ 256`: `audit/round10/probe` keeps 100000 boxes and gets 100000 distinct
addresses; a new cache when `typeAssert`/`interfaceSwitch` rebuild it), while every contract
hands `R.Env` back. Without `H` a contract demanded that, from any `R.Env` state, an unbounded
chain of such calls succeeds; in the model the regions are fixed and the collector cannot run,
so the real runtime meets no such `R.Env` and the theorems said nothing about the real binary
(a toy model meets them, so this is not refutable in the kernel; the map contracts, which keep
what they allocate, are: §Maps). `R.Env` remains the structural invariant; `H` is "this call's
allocation succeeds". `AssertE2I`/`AssertE2I2` (a new itab at most once per pair) and the
comparisons do not allocate without bound and are unchanged.

**`typeAssert` with a nil type** (round 10 I1). The contract used to admit a nil `t` with
`CanFail`, returning `0`. The runtime does return `nil` there, but then, about once in 1000 calls,
it rebuilds the cache with `buildTypeAssertCache(oldC, nil, nil)`, which reads `nil.Hash` and
faults (`audit/round10/probe tanil`: about 200 faults in 200000 calls, both ISAs). Compiled code
tests for nil before the call, so the contract now requires a non-nil `t`.

Every panic and throw path is excluded by a precondition, not specified: `TypeAssertionError`
(nil or non-implementing type in `assertE2I`, failing `typeAssert` without `CanFail`), comparing
an uncomparable type, `getitab` on an empty interface, a nil type in `interfaceSwitch` (the
compiled code tests for nil first). A box holds its value right after the call; nothing says it
keeps it across later runtime calls (they may change `R.priv`; reachability is not modelled).

A function that writes its frame before it calls `efaceeq` gets the comparison of the values at
its entry only if they do not depend on that frame: `EqFrame R t m x y ws`, a precondition
discharged for `TFlagRegularMemory` types whose values are outside the window by
`EqFrame.of_regular`.

**Pinned to the runtime's code.** The thirteen functions are `runtimeContractStubs` of
`cmd/janus/extract.go`: when `--contract` names one, the extractor checks it like a runtime stub
(the pclntab names it in package `runtime`, in the toolchain's file, and its normalized code is
one of the pinned hashes of `cmd/janus/stubpins_gen.go`, generated by `scripts/gen-stubpins.sh`
for go1.26.0, .5, .8, .10 in every build mode). A function of that name that is not the runtime's
is an extraction error; `identity.json` records `"pinned": true` and the reports print
`(pinned)`. So a theorem's contract hypothesis is about the Go runtime's own function. What that
function calls (`mallocgc`, `getitab`, `typedmemmove`, the types' `Equal` functions) is
identified by name only, as for the pinned helpers of the stubs.

**Non-vacuity.** `Janus/Contracts/IfaceSat.lean` and `IfaceSatAmd64.lean` prove, for every
contract on both ISAs, `<contract>_satisfiable`: a model `R0` (`Janus/Contracts/IfaceModel.lean`:
one ordinary type `TD`, one interface `ID` with the itab `TAB`, a box, two empty caches) whose
laws hold (`R0_laws`), machine code that satisfies the contract for `R0` (proved by symbolic
execution like any other code), and a call state (`wstate`, in the memory `wmem`) that satisfies
the contract's precondition. So no contract is contradictory, and the postcondition is reached.
Each example proof also proves, in `Proof.Witness`, that **all** hypotheses of its theorem hold
together for the binary it is about (`nonvacuous`: the laws of `R0`, the contract at the real
runtime function's address for the model code placed there, an admissible return address, and a
call state satisfying the theorem's precondition, with the descriptors at their real addresses
and, for `Classify`, the binary's read-only data loaded), and that the conclusion is then reached
(`returns`: `Box(42)` boxes `42`, `AsHasher` succeeds with the model's itab, `Classify` takes the
interface case, `Equal` of a box with itself is `true`). `scripts/verify-examples.sh` and
`scripts/verify-amd64-examples.sh` verify both theorems with `janus verify --theorem`.

**Examples** (`examples/basic/iface.go`; arm64 `examples/proofs/<Name>.lean`, amd64
`examples/proofs-amd64/<Name>/Proof.lean`):

| Function | Construct | Contract | Guarantee |
| --- | --- | --- | --- |
| `Box(x uint64) any` | boxing | `convT64` | `(type:uint64, ptr)` with a box holding `x` |
| `AsHasher(x any) (Hasher, bool)` | comma-ok assertion to an interface | `typeAssert` | the itab `getitab` gives (`0` for nil), the data word, `ok = itab ≠ 0`, for every well-formed cache; the static itab for `*MulHasher` |
| `Classify(x any) uint64` | type switch: `nil`, `uint64`, `string`, `Hasher`, default | `interfaceSwitch` | `0`/`1`/`2` by the type word (hash, then pointer), `3` iff `t` implements the case, else `4`; `3` for `*MulHasher` |
| `Equal(a, b any) bool` | `==` on interfaces | `efaceeq` | `false` for different type words, `true` for two nils, else `efaceeq`'s answer; for a `TFlagRegularMemory` type the byte equality of the values |

**What stays trusted.** Each contract, read as a claim about the Go 1.26 runtime, and the model
facts `R.Laws` and `StaticItabs`; the reading of the layouts above. None of the interface
runtime's own code is verified here: every path of `getitab` beyond the lock-free table lookup
takes the itab lock (whose arm64 LL/SC fallback the decoder rejects) and may allocate through
`persistentalloc`, and the cache rebuild allocates through `mallocgc`.

### Equality, hashing and typed memory (`Janus/Contracts/Mem.lean`, `Hash.lean`, `MapStr.lean`, `MemAmd64.lean`, `HashAmd64.lean`)

Go compares values with `runtime.memequal` (inline `==` on arrays and strings) and with the types'
equality functions (`Type.Equal`, used by the map and interface runtime and by compiler-generated
`type:.eq.T`), hashes map keys with the types' hash functions (`Type.Hasher`, `type:.hash.T`),
and copies or clears pointerful memory with `typedmemmove`, `typedmemclr` and
`memclrHasPointers`. A theorem leaves them out with `--contract` and takes their contract.

| Runtime function | arm64 / amd64 contract | Result |
| --- | --- | --- |
| `memequal(a, b, n)` | `Mem.Memequal`, `MemAmd64.Memequal` | `n` bytes at `a` and `b` agree |
| `memequal0/8/16/32/64/128(a, b)` | `MemequalN 0/1/2/4/8/16` | the `k` bytes agree |
| `memequal_varlen(a, b)` | `MemequalVarlen` | as `memequal`, size from the closure (`8(X26)` / `8(RDX)`) |
| `f32equal`, `f64equal` | `Fequal binary32 4`, `Fequal binary64 8` | `feq`: IEEE `==` (`NaN != NaN`, `+0 == -0`) |
| `c64equal`, `c128equal` | `Cequal …` | both parts `feq` |
| `strequal` | `Strequal` | `strEq`: equal lengths and bytes |
| `interequal`, `nilinterequal` | `Interequal`, `Nilinterequal` (over R2's `IfaceModel`) | equal first words and `ifaceeq`/`efaceeq` |
| `memhash(p, h, n)`, `memhash8/16/128`, `memhash_varlen` | `Hash.Memhash`, `MemhashN`, `MemhashVarlen` | `H.mem h n v` |
| `memhash0`, `memhash32`, `memhash64` | `Memhash0`, `Memhash32`, `Memhash64` | `h`; `H.mem32 h v`; `H.mem64 h v` |
| `strhash(p, h)` | `Strhash` | `H.mem h len bytes` |
| `f32hash`, `f64hash` | `Fhash …` | `FHashIs`: `±0 ↦ c1·(c0 ^ h)`, NaN ↦ `c1·(c0 ^ h ^ rand())`, else `H.mem h k x` |
| `c64hash`, `c128hash` | `Chash …` | real part, then imaginary part |
| `interhash`, `nilinterhash` | `Interhash`, `Nilinterhash` | `h` for nil, else `c1 · r`, `r` a `typehash` result |
| `typehash(t, p, h)` | `Typehash` | some `H.TypeHash t m p h r` |
| `rand()` | `Rand` | anything |
| `typedmemmove(typ, dst, src)` | `TypedMemmove` (write barrier off) | `dst` gets the `typ.Size_` bytes of `src` |
| `typedmemclr(typ, ptr)`, `memclrHasPointers(ptr, n)` | `TypedMemclr`, `MemclrHasPointers` (write barrier off) | zero bytes |
| `memmove`, `memclrNoHeapPointers`, `bulkBarrierPreWrite` | `Memmove`, `MemclrNoHeapPointers`, `BulkBarrierOff` | the callees of the typed-memory functions |
| `mapaccess2_faststr(t, m, key)` | `MapStr.Access2Str`, `Access2Str64` | `Map.Access2` keyed by the string's content `strKey` |

**The seeded hash is a model.** Every theorem quantifies over `H : HashModel`: the byte hashes are
uninterpreted functions of the seed and the bytes (the process's AES key schedule or `hashkey`,
fixed by `H.Env`), so a proof can only use what every hash satisfies. The laws are theorems
(`Janus/Contracts/HashLaws.lean`): equal floats have equal encodings unless both are zeros
(`feq_eq`), so they hash alike (`fhashIs_of_feq`, with `+0`/`-0` explicitly by `fhashIs_zeros`); a
NaN may hash to any value (`fhashIs_nan`: `c1` is odd, so `rand()` reaches every hash); equal
strings hash alike (`strhash_of_strEq`). `HashFKey` uses them to prove, for the compiler-generated
hash of a struct key, that keys equal under the generated `==` (`EqFKey`) have the same possible
hashes: the law a map lookup relies on.

**The frame.** As the map and interface contracts: the call returns to its return address with
the ABI's preserved registers (and `FPCR`, `MXCSR`'s control bits), memory changed only in the
callee's stack window `[SP - d, SP - 8)` (amd64 `[RSP - d, RSP)`), the argument spill slots, the
model's private memory (`M.priv`, `H.priv`, `R.priv`; never for the pure equality functions) and
the destination of a typed-memory call. Every precondition asks for the stack guard `d` below
`SP`, the window writable, the guard word `16(g)` outside the callee's window (and, with a
model, outside its private memory: a second runtime call after a first one must still find it),
and every input readable, below `2^48` and outside the callee's window (the callee writes its
frame before it reads). `memequal` has no spill slots (`nargs = 0`): the runtime's `memequal` is
`NOFRAME`, and its callers (`strequal`, `memequal_varlen`, compiled `==`) leave no room for them.
On amd64 a destination must also avoid the return-address slot.

**The write barrier is a parameter.** `TypedMemmove`, `TypedMemclr` and `MemclrHasPointers` take
the address `wb` of `runtime.writeBarrier` and require the flag off (`WriteBarrierOff`, the
negation of agent/rtstr's `WriteBarrierOn`); the flag-on behaviour (the barrier buffer) is work
package R5's.

**Pinning.** All these functions except `typehash` are in `runtimeContractStubs`: a `--contract`
naming one is checked to be the Go runtime's code (`checkContractPin`); `memequal` and
`memequal_varlen` live in `internal/bytealg`, `mapaccess2_faststr` in `internal/runtime/maps`
(`runtimeFuncDir`). `typehash` compiles a jump table whose normalized code differs between
programs, so it is identified by name only.

**Satisfiability.** `Janus/Contracts/MemSat.lean`, `HashSat.lean` (and `…Amd64.lean`) give, for
every contract, model code proved to satisfy it for the models `EqHashModel.M0` (typed memory),
`H0` (every hash is its seed), `IfaceModel.R0`, and a state satisfying the precondition;
`MapStr.access2Str_satisfiable` for the map lookup (model `MS0`, nil maps). The examples' witnesses
place that code behind a branch at the contract's address (`EqHashModel.branchWord`, `jmpBytes`,
`Summary.of_codeIn`).

**What is proved rather than assumed.** The runtime's own code of the equality, hash and
typed-memory functions is proved to meet these contracts, given the contracts of what it calls
(`examples/proofs/Alg*.lean`, `Mbar*.lean`; amd64 `examples/proofs-amd64/Alg*/`, `Mbar*/`), and on
arm64 `runtime.memequal` itself for every length (`AlgMemequal`). Still assumed: `memhash`,
`memhash32`, `memhash64`, `strhash` (assembly with an AES path), `typehash`, `rand`, `memmove`,
`memclrNoHeapPointers`, `bulkBarrierPreWrite`, `mapaccess2_faststr`, and on amd64 `memequal` and
`memequal_varlen` (both run `memeqbody`, which reads around short inputs).

**Examples** (`examples/basic/rteq.go`; both ISAs): `Eq32` (`[32]byte` `==`, `memequal` executed),
`StrEq` (`s == t`), `F64Eq` (`==` on `float64`, `+0 == -0`, NaN), `CopyTrees` (copy of a
pointerful array through `typedmemmove`, write barrier off), `ClearTrees` (`clear` of a `[]*T`
through `memclrHasPointers`), `LookupStr` (`map[string]uint64` lookup), `HashFKey` and `EqFKey`
(the compiler-generated hash and `==` of a struct key, with the equal-keys-equal-hashes law).
### Strings, slices and the write barrier (`Janus/Contracts/Rt.lean`, `String.lean`, `Slice.lean`, `WriteBarrier.lean`)

These contracts are written once, ISA-independently, as an `RtSpec` (`Janus.Contracts.Rt`): the
number of argument words `nargs`, a precondition `pre` on the argument words and the memory, the
ranges the function reads (`reads`, which must lie outside the callee's stack window) and writes
in the caller's memory (`writes`), whether it needs its stack check to fall through (`guard`), the
runtime's readiness (`ready`, round 9's `H`) and whether it writes runtime memory (`rtWrites`),
and a postcondition `post rt args m0 r0 r1 r2 m` on the three result words and the final
memory. `RtContract p addr rt stack H sp` (arm64; `X0`.. as the words) and `RtContract64` (amd64;
`RAX, RBX, RCX, RDI, RSI, R8`–`R11`, then stack words) turn a spec into a `Summary` with the
Go ABIInternal frame: callee-saved registers kept, memory changed only in `rt` (when
`rtWrites`), the callee's stack window `[SP - stack, SP)` and its argument spill slots, and the
spec's `writes`.

| Go source | runtime entry | spec |
| --- | --- | --- |
| `a + b + …` | `concatstring2..5`, `concatstrings` | `concatstringSpec k`, `concatstringsSpec` |
| `[]byte` concatenation | `concatbyte2..5`, `concatbytes` | `concatbyteSpec k`, `concatbytesSpec` |
| `string(b)` | `slicebytetostring`, `slicebytetostringtmp` | `slicebytetostringSpec`, `slicebytetostringtmpSpec` |
| `[]byte(s)`, `[]rune(s)`, `string(rs)`, `string(rune(v))` | `stringtoslicebyte`, `stringtoslicerune`, `slicerunetostring`, `intstring` | the corresponding `…Spec` |
| `for _, r := range s` (non-ASCII byte), `len([]rune(s))` | `decoderune`, `countrunes` | `decoderuneSpec`, `countrunesSpec` |
| C strings (cgo, syscalls) | `gostring`, `gostringn`, `gobytes` | `gostringSpec`, `gostringnSpec`, `gobytesSpec` |
| `append` past `cap`, any element type | `growslice`, `growsliceNoAlias`, `growsliceBuf*` | `growsliceSpec`, … |
| `make` + `copy`, escaping stack slices | `makeslicecopy`, `moveSlice*` | `makeslicecopySpec`, `moveSlice*Spec` |
| `copy` | `slicecopy`, `typedslicecopy` | `slicecopySpec`, `typedslicecopySpec` |
| pointer stores with the GC marking | `gcWriteBarrier1..8`; `wbZero`, `wbMove`; the `writeBarrier` flag | `WbContract`, `WbContract64`; `wbZeroSpec`, `wbMoveSpec`; `WriteBarrierOn` |

The UTF-8 decoder the specs use is `Janus.Spec.String.decodeRune`, a transcription of Go's
`decoderune` (U+FFFD and one byte for every invalid sequence, surrogates and overlong forms
rejected); `JanusTests/String.lean` checks it, `runesFrom`, `countRunes` and `intRune` against
about 16,000 vectors printed by the Go 1.26 runtime itself (`scripts/utf8vectors`).

**Satisfiability.** `Janus.Contracts.Sat` and `SatAmd64` prove `<spec>_satisfiable` for every
spec with a toy implementation (`constCode`/`constCode64`) at a concrete call state;
`Janus.Contracts.RtSat` (`rt_satisfiable`, `rt64_satisfiable`) and `WriteBarrierSat`
(`wb_satisfiable`, `wb64_satisfiable`) collect them for round 9's SAT row. `decoderuneSpec` and
`countrunesSpec` hold for every input without a readiness predicate, so no constant toy meets
them: their witness is the runtime's own code. `examples/proofs/SumRunes.lean` proves that the
machine code of `runtime.decoderune` meets `decoderuneSpec` (`decoderune_meets`), and
`examples/proofs/RuneLen.lean` that `runtime.countrunes` (with the `decoderune` it calls) meets
`countrunesSpec`; both then prove their example end to end with nothing assumed
(`correctness`; the contract-assuming layer is `correctness_of_contract`). `examples/proofs/WriteBarrier.lean` proves that the real
`gcWriteBarrier1..8` meet `WbContract` for the readiness `HRoom` (the P's buffer has room; the
flush `wbBufFlush` stays out as a contract and is never reached). The amd64 counterparts are in
`examples/proofs-amd64/`.

**Examples** (both ISAs): `Concat` (`concatstring2`), `ToBytes` (`stringtoslicebyte`),
`FromBytes` (`slicebytetostring`), `SumRunes` (for-range over a string, `decoderune`), `RuneLen`
(`countrunes`), `AppendPoint` (`growslice` with a 24-byte struct), `CopyNodes`
(`typedslicecopy`), `WriteBarrier`. Each has a `Witness` section (`nonvacuous`, `returns`).

**Probes of the real runtime** (`audit/rtstr/run.sh`, both ISAs, arm64 under qemu): every
string example agrees with Go's own builtins on 20,000 random inputs; the capacities the runtime
chooses for a full `[]Point` (`l ≤ 1200`) and for `[]byte(s)` (`len ≤ 3000`) are checked in Lean
against `growCap 24 true` and `roundupsize · true` by `decide +kernel`; and under gdb (amd64) the
write barrier's readiness `HRoom` holds at every real `gcWriteBarrier2` call that does not flush
(over 99% of the first 2,000 calls with the GC marking; the others are flushes).

**What stays trusted.** Each contract read as a claim about the Go 1.26 runtime, except
`decoderune`, `countrunes` and the write barrier's fast path, which are proved from the binary's
code.
<a id="panics-defer-recover"></a>

### Panics, defer, recover (`Janus/Spec/Panic.lean`, `Janus/Contracts/Panic.lean`, `Janus/Contracts/PanicAmd64.lean`)

**Go-level outcomes.** `Janus.GoABI.EnsuresGo` (and `Janus.Amd64.GoABI.EnsuresGo`) states both
outcomes of a call: it **returns** (with `ABIReturn` and a postcondition `ret s s'`) or it
**panics** with an interface value `v : Janus.Eface` (`pan s v s'`). A Go-level run (`GoReturns`)
is ordinary steps ending at the return address, at a panic stub (`runtime.gopanic`, the
`runtime.panic*` family), at a faulting instruction (a nil dereference or, on amd64, `#DE`, which
the signal handler turns into a panic via `runtime.sigpanic`), or at a point where a
deferred/recovered panic left the frame; a classification `GoClass` says which panic value each
of these is. `Ensures.toGo` turns every existing `Ensures` theorem into an `EnsuresGo` whose panic
outcome is impossible, so nothing earlier changes.

**The model.** A theorem quantifies over every `P : Janus.Spec.PanicRuntime` with `P.Laws`:

| Field | Meaning (Go 1.26 runtime) |
| --- | --- |
| `P.err k` | the `runtime.Error` value of kind `k : ErrKind` (`bounds`, `divide`, `shift`, `mem`, `dottype`, `rangeState`, …): a non-nil `error`, distinct per kind |
| `P.Env m`, `P.priv`, `P.depth` | the runtime usable; its memory (the `_panic`/`_defer` records, the deferpool, the error descriptors); the stack it may use |
| `P.Panicking m g v rp` | goroutine `g` runs an active, unrecovered panic with value `v`; its current deferred call returns to `rp` inside `gopanic` |
| `P.Calm m g` | no panic is active (`g._panic == nil`) |
| `P.Recovered m g` | the current panic was recovered |
| `P.wrapper pc` | `pc` is in a compiler wrapper (`abi.FuncIDWrapper`), which `recover` skips |

The laws: the error values are non-nil and injective; `Env`, `Panicking`, `Calm`, `Recovered`
live in `P.priv` (memory changes elsewhere keep them); a calm goroutine is not panicking.

**Classification (`goClass P`).** Reaching `runtime.gopanic` panics with the `any` the compiler put
in the argument registers (arm64 `X0`/`X1`, amd64 `RAX`/`RBX`). Reaching a `runtime.panic*` stub
panics with `P.err (panicStubErr name)`: `panicBounds`/`goPanicIndex*`/`goPanicSlice*` →
`bounds`, `panicdivide` → `divide`, `panicshift` → `shift`, `panicoverflow`, `panicfloat`,
`panicmem(Addr)` → `mem`, `panicSimdImm`, `panicdottypeE/I`/`panicnildottype` → `dottype`,
`panicmakeslicelen/cap`, `panicunsafe*`, `panicwrap`, `panicrangestate` → `rangeState`. A memory
fault at an address below `0x1000` (the signal handler's `sigcode1 < 0x1000` → `panicmem`) panics
with `P.err .mem`; on amd64 a `#DE` panics with `P.err .divide`.

**Contracts.** The control-flow runtime functions are left out with `--contract` and **pinned** to
the runtime's code (`runtimePanicContractStubs` in `cmd/janus`: `gopanic`, `gorecover`,
`deferproc`, `deferprocStack`, `deferreturn`, `deferprocat`, `deferrangefunc`, `sigpanic`; a
`--contract` on one of them takes precedence over its default stub/omit meaning). Each has a
satisfiability theorem in `Janus/Contracts/PanicSat.lean` (a model `P0` whose laws hold, model
code proved to meet the contract, and a call state in the precondition):

| Go | Runtime entry | Contract | Effect |
| --- | --- | --- | --- |
| `defer f()` in a loop | `deferproc(fn)` | `DeferprocContract` | returns; the record lives in `P.priv` |
| `defer` with a stack record | `deferprocStack(d)` | `DeferprocStackContract` | returns |
| `defer` in a range-over-func body | `deferprocat(fn, frame)`, `deferrangefunc()` | `DeferprocatContract`, `DeferrangefuncContract` | return |
| function exit with defer records | `deferreturn()` | `DeferreturnContract` | runs the frame's deferred calls and returns; effects confined to `P.priv` and the callee window |
| `recover()` | `gorecover()` | `GorecoverContract` | `nil` when `P.Calm`; the panic value (and `P.Recovered`) when called directly by the running deferred call: the caller is not a wrapper and its frame's saved return address, `[FP + 8]` on the frame-pointer chain, is that call's return point |
| `panic(v)` with a recovering open-coded defer | `gopanic(v)` | `GopanicRecoverContract` | calls the frame's deferred closure (funcval from the frame slot, `X26`, `P.Panicking`); for every state the closure may return in with the panic recovered, resumes the frame at its `deferreturn` site with `SP`/`X29` restored and `P.Calm` |
| range-over-func misuse | `panicrangestate(s)` | `panicrangestate_panics` (stub) | panics with `P.err .rangeState` |

Every returning contract has the frame of the other runtime contracts (`PanicPre`, `PanicRet`:
`SP`, `X18`, `X28`, `X29` kept, everything else arbitrary, memory changed only in `P.priv` and the
callee stack window, `P.Env` again). A caller states `PanicCallerOK P s frame above` (the
interface runtime's `CallerOK` for `P`); `PanicPre.of_caller` / `of_frame` give the contract's
precondition at a call site.

**`gopanic` is a continuation.** It is the one contract that hands control to user code: it says
the runtime reaches the closure's entry (a state the theorem continues from by running the
extracted closure), and that from **every** state the closure may return in — `SP`, `X18`, `X28`
restored, the runtime's stack between the closure's `SP` and the frame's kept, the panic recovered
— control reaches the frame's `deferreturn` site. A closure that does not recover gets no promise.
The frame's `deferBits` offset, slot offset and `deferreturn` site (funcdata
`FUNCDATA_OpenCodedDeferInfo` and `_func.deferreturn`) are parameters of the contract, i.e. part of
the printed statement.

**What is out of scope.** Nested panics (a panic while another is running), `Goexit`, frames with
several pending defers in the `gopanic` contract (one pending open-coded defer is covered), and
panics that propagate out of a frame with pending deferred calls (the panic outcome is stated for
frames whose deferred calls have run or that have none).

**Examples** (`examples/basic/rtpanic.go`; arm64 `examples/proofs/<Name>.lean`, amd64
`examples/proofs-amd64/<Name>/Proof.lean`):

| Function | Shows |
| --- | --- |
| `PanicIf(x, e any)` | returns `x + 1` for `x ≤ 10`, panics with exactly `e` otherwise (`panic(v) → .panicked v`) |
| `DeferInc(p, x)` | an open-coded deferred closure runs on the normal return (`*p` incremented) |
| `IndexAt(xs, i)` | out of range panics with `P.boundsError` (`runtime.panicBounds`) |
| `LoadField(c)` | a nil receiver faults, which is a panic with `P.err .mem` (the `sigpanic` path) |
| `DeferTwice()` | two heap `defer` records in a loop (`deferproc`, `deferreturn`); the call returns |
| `RecoverSet(x, e)` | `recover()` in a deferred closure turns `panic(e)` into a return of the named result `7` |
### Remaining runtime (`Janus/Contracts/Misc.lean`, `Instrument.lean`, `InstrumentCalls*.lean`, `MallocSC*.lean`; `Janus/Spec/{SoftFloat,Complex,ComplexMachine,PopCount}.lean`)

The entry points of COVERAGE.md §6 row 22 (R9), and how each enters a theorem. Examples:
`examples/rtmisc` (binaries `scripts/build-examples-rtmisc.sh`, proofs `examples/rtmisc/proofs/
{arm64,amd64}/`, checked by `scripts/verify-rtmisc-examples.sh`).

**Executed, not assumed.** These are ordinary Go code (or no code at all), so the proofs run the
runtime's machine code:

| entry | how | example (both ISAs unless noted) |
| --- | --- | --- |
| `complex128div` | executed: Smith's algorithm and the Annex G recovery, against `Janus.Float.cdiv` (IEEE operations, fused on arm64, unfused on amd64) | `Div` |
| `f32to64` (`-d=softfloat`) | executed (with `fpack64`), equal to IEEE `convertFormat` (`cvt binary32 binary64`) for every input | `Widen` |
| `KeepAlive` | an intrinsic: no call, the argument is only kept live | `LoadKeep` |
| `cgoNoCallback` | ordinary Go code (a store into `g`, a `panic` stub) | — |

**Read-only data with known contents** (`Janus.Contracts.Misc`):

* `runtime.staticuint64s` (`.rodata`, extracted with the code like every read-only object; the
  bytes are part of `Extracted.lean` and `Program.DataLoaded` loads them): `StaticUint64s m a`,
  proved from the extracted bytes (`StaticUint64s.of_loaded`), not assumed. `BoxByte`: boxing a
  `byte` returns `&staticuint64s[b]`, whose word is `b`.
* `runtime.zeroVal` (1024 zero bytes in `.noptrbss`), `runtime.inf` (the word `+∞`) and
  `runtime.cgoAlwaysFalse` (`false`): writable data the extractor does not copy, so a theorem
  states their contents as hypotheses (`ZeroVal`, `RuntimeInf`, `CgoAlwaysFalse`) at the address
  the code reads. Trusted: no Go code writes them (the runtime never assigns `zeroVal`, `inf` or
  `cgoAlwaysFalse` after initialisation). `ZeroBox`: boxing a zero array returns `&zeroVal`.

**CPU feature flags** (`Misc.CpuFlag m a b`: the flag byte at `a` holds `b`). `arm64HasATOMICS`,
`x86HasPOPCNT`, `x86HasFMA`, `x86HasAVX`, `x86HasSSE41`, … are set once by `internal/cpu` from
`CPUID`/`HWCAP` before user code runs. A theorem takes the flag's value as a parameter `b` and is
stated for every `b`. `Pop` (amd64, `GOAMD64=v1`): `bits.OnesCount64` tests `x86HasPOPCNT` and
takes `POPCNT` or the portable SWAR code; the theorem returns the population count for both values
of the flag. The model executes `POPCNT` on any CPU, so the `b = true` case means what it says when
the runtime sets the flag only on CPUs that have the instruction (trusted, docs/SOUNDNESS.md).

**Coverage counters (`-cover`, `Janus.Contracts.Instrument`).** No runtime call: the compiler
emits ordinary stores into the package's counter array. `CovBlock m ctr pkg fn cs` describes a
function's counter block (number of counters, package id, function index, counters), `bumped`
the counters after a run (each block that ran incremented modulo `2^32`). `Clamp`: `min(x, hi)`
and exactly the counters of the blocks that ran incremented, nothing else written.

**Contracts**, each pinned to the runtime's code (`rtmiscContractStubs`, regenerated by
`scripts/gen-stubpins.sh`) and satisfiable (`_satisfiable` in the `…Sat` / `…SatAmd64` module):

| entry | contract (arm64 / amd64) | condition of the return | example |
| --- | --- | --- | --- |
| `checkptrAlignment` (`-d=checkptr`) | `CheckptrAlignment` / `CheckptrAlignment64` | `AlignOK`: nil, or aligned and not straddling (the runtime's own test, over the abstract `checkptrBase`) | `CheckWord` |
| `checkptrArithmetic` | `CheckptrArithmetic` / `…64` | `ArithOK` | — |
| `cgoCheckPointer` | `CgoCheckPointer` / `…64` | the model's `ok` (the cgo pointer-passing rules; panic excluded) | — |
| `cgoCheckResult` | `CgoCheckResult` / `…64` | the model's `resOK` | — |
| `mallocgcSmallNoScanSC<n>`, `mallocgcSmallScanNoHeaderSC<n>`, `mallocgcTinySize<n>` (`GOEXPERIMENT=sizespecializedmalloc`) | `MallocgcSmallNoScanSCContract` & co. / `…64` | the `mallocgc` contract (`RtReady`, a fresh object of the class size) with the entry's fixed arguments | `NewPairSC` |

The checks return when the operation is valid and otherwise throw or panic; the contracts
describe the return and exclude the failure (a theorem therefore assumes the check passes). The
size-specialised entries reuse the `RtReady` allocation contracts of `Janus/Contracts/Alloc*.lean`
unchanged: each is `mallocgc` with a size, type and `needzero` that its size class fixes.

**External stubs.** `cgoUse` and `cgoKeepAlive` occur only on the dead `if cgoAlwaysFalse` branch of
cgo wrappers and throw when called; they are classified like `cgocall` (`.external`), and a proof
excludes the branch with `CgoAlwaysFalse`.

**Soft float (`-d=softfloat`).** The arithmetic helpers decode and run in the model, and
`f32to64` is proved equal to IEEE (`Widen`). The others are not given contracts:

* `fadd64`/`fsub64` are **not IEEE 754**: when the exact sum of two operands of opposite signs
  is subnormal, Go 1.26's `fadd64` returns a result off by a factor of two (65240 of 30M random
  pairs; every mismatch has a subnormal IEEE result; e.g. `0x802fa1d354c1e77c + 0x00329934086c3cdd`
  gives `0x00059094bc16923e`, IEEE `0x000b2129782d247c`; confirmed on the real runtime). A contract
  "fadd64 is IEEE addition" would be false, and Janus states none; a theorem about code built
  with `-d=softfloat` that adds floats must execute `fadd64` (it decodes) and can only conclude
  the IEEE sum under a hypothesis excluding subnormal results.
* `fmul64`, `fdiv64`, `f64to32` and the conversions matched IEEE on every tested input
  (random tests against the IEEE core) but have no proof; they run as code like any other runtime function.

**Build modes** (docs/CLI.md "Build modes"): `-race`, `-msan`, `-asan` and `-d=libfuzzer` are
rejected by `janus extract` with an error naming the mode (their instrumentation calls into the
sanitizer runtimes, outside the model, or is concurrency tooling); `-cover`, `-d=checkptr` and
`-spectre=ret` are accepted and recorded in `identity.json` (`buildModes`), with a note.

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
   thread (`TPIDR_EL0`/`FS`). On amd64 the C code sees the Go caller's x87 FPU state
   (`CgoEntry.x87`): the Go code, `cgocall`, `entersyscall` and `asmcgocall` execute no x87
   instruction, and a signal handler's x87 use is undone by the kernel's FPU save/restore.
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
   registers, the flags, the vector registers and (amd64) the x87 FPU state are arbitrary. The goroutine may resume on
   another OS thread (`exitsyscall`'s slow path), so `TPIDR_EL0`/`FS` are arbitrary afterwards.
4. *`_cgo_topofstack`.* During one cgo call it returns the same value every time. This excludes
   a callback into Go (`CgoCallback` below) that grows, and so moves, the goroutine stack during
   the call: a Go → C → Go composition that calls back is outside this claim (no example does). It preserves every other register and
   writes only its frame (arm64: the 56 bytes below `SP`; amd64: nothing).
5. *No concurrency.* As everywhere in Janus: no other goroutine or thread writes the granted
   memory during the call. The garbage collector does not move or modify objects that are
   reachable from the arguments (cgo pins the Go memory it passes to C).

Everything else is executed by the model from the binary's bytes: the Go function, its cgo
`_Cfunc_` wrapper (including the stack check and the `_Cgo_always_false` test), the C wrapper,
and the C function.

### The kernel: system calls, environment reads, vDSO clocks (`Janus/Contracts/Syscall.lean`, `Janus/Contracts/SyscallAmd64.lean`)

A Go function that talks to Linux is stated with `Kernel.EnsuresK p E entry args pre post`
(amd64: `Amd64.Kernel.EnsuresK`): the pre- and postconditions also take the **kernel state**
`Kern` (the I/O trace, the input oracle, the clock bounds, the IDs, the CPU features), and the run
is the kernel semantics `ReturnsK`, which gives each `.syscall` stub its contract
(`Kernel.SiteSafe`/`SiteNext` by site: `SVC #0`/`SYSCALL` by system call number, the environment
reads, the vDSO clocks). See [SOUNDNESS.md](SOUNDNESS.md#the-kernel-trust-boundary-system-calls-environment-reads-traps)
for what each contract allows and what is trusted.

| contract | what it states | used by |
|---|---|---|
| `Kernel.Safe`/`Kernel.Effect` per `Sys` | `read`, `write`, `openat`, `close`, `exit_group`, `clock_gettime`, `mmap`, `munmap`, `madvise`, `rt_sigprocmask`, `sigaltstack`, `sched_yield`, `nanosleep`, `getpid`, `gettid` | every `SVC #0`/`SYSCALL` stub (`internal/runtime/syscall/linux.Syscall6`, `syscall.rawSyscallNoError`, the `runtime` wrappers) |
| `Site.walltime`, `Site.nanotime` (arm64), `Site.timeNow`, `Site.nanotime` (amd64) | the vDSO clocks: a reading of the clock, recorded in the trace; the monotonic clock never goes back; only runtime-owned memory (`KEnv.rt`) and `KEnv.stack` bytes below `SP` change | `runtime.walltime`, `runtime.nanotime1`, `time.now` |
| environment reads | `CNTVCT_EL0` monotone, `CNTFRQ_EL0`/`XCR0` constants of `Kern`, `MIDR_EL1`/`CPUID`/`RDTSC(P)` arbitrary (feature-gated by `Kern` flags), `PSTATE.DIT` in `Kern` | `internal/cpu`, `runtime.cputicks`, `crypto/subtle` |
| `Kernel.SchedContract` / `Amd64.Kernel.SchedContract` | `runtime.entersyscall`/`exitsyscall` return with the Go ABI registers kept, memory changed only inside `rt` and their stack window (a `Summary`, `--contract`) | `syscall.Syscall`, `syscall.Syscall6` |
| `Kernel.ConvT64Contract` / `Amd64.Kernel.ConvT64Contract` | `runtime.convT64(v)` returns a pointer to 8 readable bytes holding `v` (a `Summary`, `--contract`) | `syscall.errnoErr` on the error path |

Witnesses: `Kernel.Effect.total`, `Kernel.SiteNext.total`, `Amd64.Kernel.SiteNext.total` (no
contract is stuck where its precondition holds), `write_full`, `read_some`, `clock_monotonic`,
`mmap_anon` (the interesting behaviour is allowed), and `JanusTests/Kernel.lean` (concrete code
meets `SchedContract` and `ConvT64Contract`). Examples: `examples/proofs-sys/{arm64,amd64}/`
(`WriteOut`: `syscall.Write`; `NowNano`: `time.Now().UnixNano()`; `Pid`: `syscall.Getpid`;
`MustNonNeg`: a path ending in a trap), run by `scripts/verify-sys-examples.sh`.
**Callbacks (C → Go, `CgoCallback`; K2).** `runtime.cgocallback` (`.abi0`, pinned by content)
is an external stub too. Trusted, both ISAs: `CgoCallback t p Cin R k`, `CallbackEntry`,
`CbResume`, `CbResumed`, `cbClobber`, `tlsGSlot`, `stackGuard` (amd64 also `CbStack`, `CbReady`;
arm64 `CbStack.Ready`). As claims about the Go 1.26 runtime (`runtime/asm_arm64.s`,
`runtime/asm_amd64.s`: `cgocallback`; `runtime/cgocall.go`: `cgocallbackg`, `cgocallbackg1`):

1. *The re-entry.* `cgocallback` loads `g` from the TLS `g` slot (`tlsGSlot t`: `runtime.tls_g` /
   `runtime.tlsg` of the extraction's `TLSImage`; `needm` borrows an extra `M` when it is nil),
   takes `m.curg`, points the TLS slot at it (`tlsG`), moves `X28`/`R14` to it (`gReg`: its
   struct readable Go memory, not C memory, `gSep`, and off its own stack, `gOff`), switches `SP`
   to the goroutine stack and, through `cgocallbackg` (`exitsyscall`) and `cgocallbackg1`, calls
   `fn(frame)` with the ABIInternal convention (`X0`/`RAX = frame`, `X15 = 0` and `DF` clear on
   amd64), returning to an address outside the extracted code, on the same thread, with the C
   side's `MXCSR` and x87 control word (amd64) / `FPCR` (arm64).
2. *The goroutine stack* (`goStack`, `stackSep`, `guard`). `k.size` writable bytes below the Go
   call's `SP` and the slots above it (arm64: the frame argument's spill slot, `[SP, SP+16)`;
   amd64: the return-address and spill slots, `[RSP, RSP+16)`), none of them C memory, and
   `g.stackguard0 + k.size ≤ SP + stackGuard` (`stackGuard = 928`, `stackguard0 = stack.lo +
   stackGuard`): the stack's low end is at least `k.size` bytes below `SP`, so the Go code's stack
   checks pass for frames up to about `k.size − 800` bytes (`CallbackEntry.guardOK`) and its
   frames fit. This is a claim only **under the readiness** `k.ready` (`CbStack`, round 9 C1
   style): the contract requires `k.ready [fn, k.size] g SP (rtView k.rt mem)` at the stub, with
   `g` the TLS slot's value. The real runtime meets it for `ready := "the goroutine
   `cgocallback` switches to has (or `morestack` can give it, up to `maxstacksize`) `k.size`
   bytes of stack below the entry, and no preemption request is pending"`; a goroutine whose
   stack is too small grows it on demand (`morestack` copies the stack and re-runs the
   function), which the model describes as the entry on the larger stack. A theorem quantifies
   over `ready` and assumes it at its entry.
3. *C memory.* Before and after the Go call, the runtime changes no byte of the C state's memory
   outside `cbClobber`: the C stack below `SP` (`cbStackScratch = 16384` bytes), the argument
   slots and the TLS `g` slot.
4. *The return.* `cgocallback` returns to `crosscall2` with `SP + 8`/`SP` restored, `DF` clear and
   the `MXCSR` control bits kept (amd64); every other register, the flags, the vector registers
   and (arm64) the exclusive monitor are arbitrary (ABI0), and the memory is the Go code's final
   memory on the C state's accessible bytes (`CbResumed`).
5. *Readiness of the Go code* (`R`). Facts the Go code needs of the runtime beyond the above (an
   allocator's readiness at its calls, Go read-only data such as a type descriptor) are the
   readiness predicate `R` on the Go call state: the theorem covers the executions in which `R`
   holds at the entry (`ECallBox`: `ROK`).

Witnesses: `cgoCallback_satisfiable` (for every `k`, given `CbRoom`: room for the goroutine stack
and the `g` struct outside the C memory) and `cgoCallback_satisfiable_of` (a readiness `R` that
holds at the witness entry), `callbackSpec_satisfiable` (`Janus.FFISat`, `Janus.Amd64.FFISat`).
`AVX-512`: the amd64 `CbResume` leaves `xmm`/`ymmHi` arbitrary; the `zmmHi`/`kreg` fields of
agent/avx512 are not in this tree, and must be added to its existentials when they are.

**libc (`Libc`, `SetJmp J`, `TlsGetAddr`; `Janus/Contracts/Libc.lean`, `LibcAmd64.lean`; K2).**
External stubs `sym@plt`; trusted as glibc's behaviour on Linux, one `Spec` per function
(FFI.md § 3.2–3.4): `memcpy`/`memmove`/`memset` (and `__*_chk`), `strlen`, `strcmp`, `malloc`,
`free`, `_setjmp`, `longjmp`/`_longjmp`/`__longjmp_chk`, `__tls_get_addr`. Each needs at most
`libcStack = 32768` bytes of stack below `SP` and keeps the callee-saved state, the thread
pointer and the regions (but `malloc`/`free`). Witnesses: `libc_satisfiable`,
`setJmp_satisfiable`, `jmpModel_satisfiable`, `tlsGetAddr_satisfiable` (`LibcSat`,
`LibcSatAmd64`).

### Stack growth (`Janus/Spec/Stack.lean`, `Janus/Contracts/Stack.lean`)

Every Go function that is not `NOSPLIT` begins with a stack-growth check (`Janus.GoABI`,
"Stack-growth prologue"): it compares `SP` with `g.stackguard0` and, when its frame does not
fit, calls `runtime.morestack_noctxt`. Until R7 every theorem assumed the check falls through
(`GuardOK`, `StackGuardOK`): the grown case — the `morestack` call — was excluded, and a run
that reached it stopped at the `.morestack` stub (`GoABI.GrowsStack`). R7 removes that
restriction. A theorem about `f` that holds "on any stack with room" (an ordinary `Summary`)
plus the `morestack` contract gives "`f` is correct, stack growth included".

**What `morestack`/`newstack`/`copystack` do** (Go 1.26 `runtime/stack.go`, `asm_arm64.s`,
`asm_amd64.s`). `morestack` saves the goroutine's context (`gobuf`: `pc` = the instruction after
the call, `sp`, `bp`, `lr`, `ctxt`) and calls `newstack` on the `g0` stack. `newstack` allocates
a stack of `newsize` bytes (`oldsize·2`, doubled until `newsize - used ≥ funcMaxSPDelta(f) +
stackGuard`; a request above `maxstacksize` throws `stack overflow`), and `copystack` copies the
used part of the old stack to the new one and **adjusts every pointer into the old stack**:
`adjustframe`/`adjustpointers` walk the frames with the unwinder (`traceback.go`) and, guided by
the stack maps (the pclntab's `FUNCDATA_LocalsPointerMaps`, `FUNCDATA_ArgsPointerMaps`,
`FUNCDATA_StackObjects`, selected by `PCDATA_StackMapIndex`), add `delta = new.hi - old.hi` to
each word the maps mark as a pointer whose value lies in `[old.lo, old.hi)`; `adjustctxt` does the
same for the saved frame pointer below `SP` on arm64. `g.stack`, `g.stackguard0`, `g.sched.sp`
are updated and `gogo` resumes at the saved `pc` — the prologue's glue after the `morestack`
call, which re-enters `f` on the larger stack. The whole goroutine stack moves, so the resumed
`SP` is the old one plus `delta`.

**The model** (`Janus/Spec/Stack.lean`, ISA-independent). `Moved cls pool lo hi hi' base ex m m'`
relates the memory before and after a copy of `[base, hi)` of the stack `[lo, hi)` to the top
`hi'`: a word `cls` marks as a pointer is adjusted by `hi' - hi` when its value is in the old
stack and copied otherwise (`adjustWord`), every other byte is copied, and the ranges `ex` are
left free. `Moved.trans` composes two moves into one — **the relocation invariance** that lets a
move compose with the resumed run. `FrameTable` is the stack maps (abstract: theorems quantify
over every table), `Chain` the unwinder's walk from the saved context, and `frameCls`/`framesCls`
the words a frame / a walk adjusts. The key lemmas `frameCls_mv`, `framesCls_mv`, `Chain.mv` and
`Chain.moved` prove the classification and the walk are relocation invariant, so the resumed run
reads the moved frame as the move left it.

**The contract** (`Janus/Contracts/Stack.lean`). `MorestackContract p FT pool rt H reloc`: from
every state at a prologue's `morestack` call satisfying `MorestackPre` (it is at a `.morestack`
stub; `g = X28`/`R14` runs on `[lo, hi)` inside the writable stack pools `pool`, above the first
page; the stack unwinds, `Chain`; the grown stack fits `maxstacksize`; the runtime is ready to
allocate, `H`, round 9's readiness predicate, on the runtime-owned memory `rt`; no word outside
the stacks points into a stack, `NoStackPtr`), the relation
`reloc` resumes in a `Grown` state: a larger stack inside the pools with room for the function's
own `funcMaxSPDelta + stackGuard` below the resumed `SP` (exactly `newstack`, not room for an
unbounded recursion), `SP`/`FP`/`g.stack`/`g.stackguard0` updated, the frames moved (`Moved`
along the `Chain`), `H` re-established, resumed at the glue. `morestack`/`morestack_noctxt` are
already **pinned** as `.morestack` stubs (`cmd/janus` `runtimeMorestackStubs`, `classifyStub`,
`stubpins_gen.go`), so the contract hypothesis is about the Go runtime's own `morestack`.

**The grown run.** `GrownReturns p reloc s post` is `Returns` through any number of `morestack`
resumes; `EnsuresGrow` is the grown `Ensures`, with the room precondition dropped. For a callee
that may grow, `GrownRet`/`GSummary` are the grown `ReachesRet`/`Summary` (with `bind`, `call`
and `GSummary.induction` for recursion). `grow_rec` is the well-founded recursion on the stack's
distance from `maxstacksize`: a growth makes the stack strictly larger, so after finitely many
it has room and the roomy `Summary` applies.

**Satisfiability** (`Janus/Contracts/StackSat.lean`). `morestack_satisfiable` exhibits a two-slot
toy stack allocator that meets `MorestackContract` for every program and frame table — it copies
the frames, adjusts every stack-map pointer into the old stack and rewrites `g.stack`/
`stackguard0` — and a call state satisfying the whole precondition (round 9's SAT row).

**amd64** (`Janus/Contracts/StackAmd64.lean`). The same model with `Arch.amd64` (`fp = sp +
spdelta + 8`, the return address at `fp - 8`, `varp = fp - 8`), and the amd64 call sequence:
the prologue's tail spills the register arguments to `8(SP)`, `16(SP)`, … (the caller's argument
area) and `CALL`s the stub, so at the stub `[RSP]` is the glue (`gobuf.pc`) and `RSP + 8` the
function's stack pointer (`gobuf.sp`). `MorestackContract64` resumes in a `Grown64` state: at the
glue, `RSP` moved, `RBP` adjusted (`adjustWord`, `adjustctxt` on `gobuf.bp`), `RDX = 0`
(`morestack_noctxt`), `R14` kept, `X15 = 0`, the direction flag clear, `MXCSR`'s control bits
kept; the copied region is `[RSP + 8, hi)` (the pushed glue address is not copied).
`GrownReturns64`/`GrownRet64`/`GSummary64`/`EnsuresGrow64`/`grow_rec64` are the grown run, and
`morestack64_satisfiable` (`Janus/Contracts/StackSatAmd64.lean`) reuses the toy allocator.

**The stack maps come from the binary.** `janus extract --frames` decodes, for every extracted
function, its pclntab record (`Extracted.frames : List FuncRec`: pc range, `FuncID`, flags,
`funcMaxSPDelta`, the `pcsp` and `PCDATA_StackMapIndex` tables as pc-value runs, the args and
locals pointer maps, the stack objects; `cmd/janus/frames.go`), and `janus check` re-derives it.
A grown theorem assumes its frame table **agrees** with these records (`FrameTable.Agrees
Extracted.frames`: at every pc inside an extracted function, the table's SP delta, largest frame,
maps and objects are the record's), so the maps a proof relies on are the binary's; the witnesses
build their table from the records (`FrameTable.ofRecs`), and `ofRecs_laws_arm64`/`_amd64` check
by evaluation that the records keep their words inside the frame (`FrameTable.InFrame`).

**What stays trusted** (see [SOUNDNESS.md](SOUNDNESS.md#stack-growth)): the `Moved`/`Chain`
relocation is what `newstack`/`copystack` do, and in particular **the stack maps are correct**
(the compiler's liveness information marks exactly the pointer slots; the tables are the binary's,
`FrameTable.Agrees Extracted.frames`). A precondition states that no pointer into the stack is
held in non-stack memory (`MorestackPre.noptr`, `NoStackPtr`; Go's escape analysis guarantees
it): `copystack` does not adjust such a word.

**Examples** (`examples/basic/zstack.go`; arm64 `examples/proofs/<Name>.lean`, amd64
`examples/proofs-amd64/<Name>/Proof.lean`; each with `Witness.nonvacuous` and `Witness.returns`):

| Function | Shows |
|---|---|
| `BigLocal(x, i)` | a large frame (176 bytes on arm64, 168 on amd64) whose prologue always grows on a small stack; returns `buf[0]` = `x` if `i&15 = 0` else `0`, on a stack of any size (`correctness`), with a witness whose frame does not fit (`Witness.no_room`) |
| `SumRec(n)` | recursion with growth at any depth: a grown callee summary (`GSummary.induction`) whose post states the move of the caller's frames, composed level by level (`Moved.trans'`, `mono_base`, `cls_congr`); the saved frame pointers adjusted, the spilled `n` copied; witness `SumRec(3)` from a stack where not even the first frame fits |
| `HoldPtr(x)` | a pointer into the function's own frame (`p = &a[x&1]`, kept in a locals-map slot) held across a call (`holdCallee(p, x)`) whose frame grows the stack: the callee's spilled `p` (its args map) and the caller's slot are both adjusted, so the callee's store reaches the moved array and the caller reads it back through the adjusted `p`; witness `HoldPtr(16) = 49` with the growth inside the callee (`Witness.callee_grows`) |
