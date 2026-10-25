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

### Maps (`Janus/Spec/Map.lean`, `Janus/Contracts/Map.lean`, `Janus/Contracts/MapAmd64.lean`)

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
| `len(m)` | inline load | `MapModel.Laws.len` | |

The common shape, `RTPre` and `RTReturn`:

* **pre**: `M.Env` with the goroutine (`X28` / `R14`), the stack guard at least `M.depth` bytes
  below `SP`, the stack window `[SP - M.depth, SP + 8 + 8·nargs)` writable and outside `M.priv`,
  an admissible return address (`X30` 4-aligned below `2^48`; on amd64 the word at `[RSP]` below
  `2^47`, which `RET` needs, plus `X15 = 0` and `DF` clear), and
  `M.Typ` for the descriptor in the first argument register;
* **post**: the call returns to the caller with `SP`, `X18`/`X28`/`X29` (amd64: `RSP + 8`, `RBP`,
  `R14`, `X15`) preserved and everything else arbitrary; memory changes only in `M.priv`, at most
  `M.depth` bytes below `SP` (arm64: never the caller's saved frame pointer at `[SP-8, SP)`; amd64:
  never the return-address slot) and the argument spill slots (`MemFrame … (rtWrites M s nargs ++
  extra)`); `M.Env` holds again; every other map keeps its contents (`OthersKept`).

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

**Examples** (`examples/basic/maps.go`; arm64 `examples/proofs/<Name>.lean`, amd64
`examples/proofs-amd64/<Name>/Proof.lean`): `Lookup`, `Insert`, `InsertGet` (two contracts; the
read-back returns `v`), `Delete`, `SumValues` (iteration, every order), `CountKeys` (no contract),
`LookupKey16` (generic `mapaccess2`), `NewMap`, `ClearMap`, and `MapAccess1Small` (the runtime
function itself, extracted as `runtime.mapaccess1_fast64`).

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
| `x.(I)`, `v, ok := x.(I)` | cache probe, `typeAssert(desc, t)` | `TypeAssert` | the itab or `0` for `desc.Inter`; failing without `CanFail` excluded; the descriptor well formed again, same `Inter` and `CanFail` |
| `switch x.(type)` with interface cases | cache probe, `interfaceSwitch(desc, t)` | `InterfaceSwitch` | `switchCase R t cs`: the first case `t` implements and its itab, else `(len cs, 0)` |
| `a == b` on `any` | `efaceeq(t, x, y)` | `Efaceeq` | `efaceEqual`: true for `t = nil`; for a direct type the words; else `R.eq t` |
| `a == b`, non-empty interfaces | `ifaceeq(tab, x, y)` | `Ifaceeq` | `ifaceEqual`: the same with `t = tab.Type` |

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
