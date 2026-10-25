# Audit round 9: runtime contracts against the real runtime

Branch `agent/redteam9`, based on `merge/b7` (main, round 8, agent/alloc, agent/stubpin,
agent/rt-fp), then merged with main (`987d96d`, then `73cae68`: maps, ffi/cgo contracts,
iface-alloc, rt-model's EX1 segment check). Scope: the runtime-contract layer added by
agent/alloc (allocation contracts, the proved `mallocgc` fast path, the write-barrier example),
the linked-program semantics, and leftovers from round 8 (memory-guard settings, the H1
lookalike table).

The lesson from AUDIT-FP.md (X64-MXCSR-STICKY) was the method: for every hypothesis, ask whether
a real call in a real process meets it, and check it on a running binary. Each check is a row of
`audit/round9/run-round9.sh`. The probes are `audit/round9/probe` (a Go program calling the
examples, built with go1.26.0), a gdb script for amd64 and an in-process reader for arm64 run
under qemu-aarch64. The host has no aarch64 gdb.

## Summary

| ID | Severity | Finding | Status | Rows |
|---|---|---|---|---|
| C1 | **critical** (vacuity) | **No code could meet the allocation contracts.** `NewobjectContract`, `MakesliceContract`, `GrowsliceContract` and `MallocgcContract`, on both ISAs, are `Summary`s over every state satisfying a precondition that said nothing about the runtime's own state. One such state has a 2^47-byte request (`≤ maxAlloc`) and no heap mapped. Regions never change, so no object can be returned there. The hypothesis was false for every implementation, address and `rt`, so the six NewPair/MakeSlice/AppendOne theorems were vacuous. The real runtime throws `out of memory` on such a request. | **BROKEN → fixed** | C1a–C1d, C1_ctl |
| SAT | high (process) | **No contract had to show it was satisfiable.** C1 went unnoticed because nothing required a witness. Row SAT (`audit/round9/sat_check.py`) now finds every runtime contract under `Janus/Contracts` (a `def … : Prop` whose body is a `Summary`) and requires `theorem <name>_satisfiable` in `Janus.Contracts.<File>Sat` (`…SatAmd64`), imported by `Janus.lean` so that `lake build` kernel-checks it: an implementation, its parameters, and a state satisfying the whole precondition. The 8 allocation contracts have one (`Janus/Contracts/AllocSat.lean`, `AllocSatAmd64.lean`). The 18 map contracts (arm64 + amd64) are listed as OPEN in `audit/round9/sat-pending.txt` (owner: agent/maps); any other contract without a witness fails the row, and a self-test row checks that removing a witness does. | **fixed** (maps open) | SAT, SAT_selftest |
| C2 | high (contract promises too much) | **16-alignment for header objects.** `Fresh` promised `ptr % 16 = 0` for every request whose size is a multiple of 16. A pointerful object of 513 to 32760 bytes follows an 8-byte malloc header (`mallocgcSmallScanHeader` returns `slot + 8`), so the real runtime returns `8 mod 16` for every one of them. | **BROKEN → fixed** | C2a, C2b |
| M1 | high (vacuity) | **MallocFast held for no call on `m0`.** `MCacheOK` required the six runtime globals, as one range `[globLo, globHi)`, to be separate from the `m`. `runtime.m0` lies in `.bss` inside that range, so the theorem said nothing about any allocation made on the main thread's `m`. Probe: 0 of 20000 real 64-byte requests met it. With each global on its own, 19682 do. | **BROKEN → fixed** | M1 |
| S1 | medium (gratuitous exclusion) | **SetNext's `BarrierOK` excluded most real calls.** It required one interval `[lo, hi)` holding `g.m`, `m.p`, `p.wbBuf` and the buffer slots, and missing `n.Next` and the stack. In the arena these interleave. Probe (amd64, barrier on): 82 of 300 real calls could meet it, against 300 of 300 with per-object separation. | **fixed** | S1 |
| H2 | **critical** (readability) | **Lookalike binders the H1 fold missed.** `ό` (U+03CC) vs `ό` (U+1F79), `K` (Kelvin sign) vs `K`, and `ι` (U+1FBE) vs `ι` (U+03B9) are Lean identifier letters that render identically and fold apart. `∀ K, K = K` read as a triviality and "Add returns x * y" verified (rows H2a–c), exactly like round 7's H1a. | **BROKEN → fixed** | H2a–c, controls |
| I1g | low (hardening) | `Program.contractAddr` falls back to 0 for a name that is not a recorded contract, and the round-8 name check did not cover it. A lookalike `"runtime.newobjеct"` read as the real contract. | **fixed** | I1g |
| D1 | medium (docs) | **The stubpin merge (`2bf7f35`) replaced `docs/SOUNDNESS.md` wholesale with agent/stubpin's copy.** That dropped the "Runtime contracts" section, round 8's cache sections (toolchain identity, private cache root, trusted-compile MAC) and the I1 "object names must resolve" item from the trust document. Restored by a three-way merge. | **fixed** | D1 |
| G1 | — | `growCap8` (`nextslicecap` + `roundupsize`) against the real runtime: all 43 growths of `[]uint64` up to 3·10^6 elements match, on both ISAs. | holds | G1 |
| MG | — | `JANUS_MEMGUARD` / `JANUS_MEM_MAX` change limits only. An attack stays blocked under every mechanism and limit, and a kill is an `Invalid`, never a pass. Hazard: a forced mechanism that is unavailable (`JANUS_MEMGUARD=cgroup` without a delegated cgroup, or a misspelt name) silently runs unguarded. | holds (hazard) | MG |
| MP | — | Map contracts (`Janus/Contracts/Map.lean`, `MapAmd64.lean`) already take the abstract runtime model `M : MapModel` (`Env`, `Rep`, `priv`), the readiness design C1 adds to allocation. `MapAccess1Small` discharges `Access1` for `smallModel`, whose single `heap` interval must hold a map's header and its group and miss the stack window. Probe (amd64 gdb, `probe9 maps`): 400 of 400 real small-map lookups, on the main goroutine and on 8 others, admit such an interval. | holds | MP |
| FF | — | cgo contracts (`Janus/FFI.lean`, `Amd64/FFI.lean`, `CABI`): the X64-MXCSR-STICKY lesson is applied (only the control bits of MXCSR/FPCR are kept, the sticky status flags are arbitrary). `TPIDR`/`FS` are arbitrary after the call. `g` is 456 bytes in go1.26.0 (`runtime.g0` symbol size `0x1c8`). Stack shrinking is unsafe while `syscallsp ≠ 0`, which `exitsyscall`'s slow path clears only after rescheduling, so the "stack does not move across cgocall" claim matches the runtime. No vacuous hypothesis found. | holds | (reviewed) |
| L1 | — | Linked-program semantics: `--contract` wins over `--targets` (no code is copied at a contract address), stubs keep their stub meaning, the entry cannot be a contract, and `impl` is universally quantified. No way was found for a proof to choose its `impl`. | holds | (round-8 rows) |

**Safe to merge: yes**, with the full regression below. The fixes change the statements of 11
example theorems (the six allocation theorems take `H : RtReady` and assume `H` at entry;
MallocFast's `MCacheOK` and both SetNext `BarrierOK`s are restated). Every changed theorem verifies.

## C1 (CRITICAL, BROKEN → fixed): the allocation contracts were unsatisfiable

**What a contract is.** `NewobjectContract p addr rt stack` unfolded to
`Summary p addr (NewobjectPre stack) post`, which means: for **every** state at `addr` with
`CallOK`, a readable type descriptor and `typSize ≤ maxAlloc`, the code returns with a fresh
object `[ptr, ptr + blockSize)` that is inside `rt`, writable, zeroed and aligned. `MemFrame`
keeps every region's accessibility, and the docs rightly note that no instruction adds a region.

**Why nothing meets it.** Take the state whose only regions are the 4112-byte stack window and
the 16-byte descriptor, with `Size_ = 2^47`. It satisfies the precondition. A post state would
need `2^47` writable bytes that exist in no region. So the contract is false whatever `impl`,
`addr` and `rt` are. `audit/round9/model/Unsat.lean` proves this in the kernel
(`newobject_unsat : ¬ OldNewobjectContract p addr rt 4096`), with the pre-round-9 definition
copied verbatim. The other three contracts fall the same way: each admits sizes up to `maxAlloc`
and says nothing about the heap.

So `NewPair`, `MakeSlice` and `AppendOne`, on arm64 and amd64, were vacuous. Each held because
its hypothesis `hnew` / `hmk` / `hg` could never hold, while the docstrings said "the theorem
holds for the real binary exactly when the real runtime meets the contract". The real runtime
meets it least of all. `probe9 big 44` calls `MakeSlice(1<<44)` (`8·2^44 = 2^47 ≤ maxAlloc`,
admitted), and it dies with `fatal error: out of memory` (row C1d). The runtime also reads its
own data structures (`mcache`, `mspan`, `g`), which a universally quantified state fills with
garbage.

**Fix.** Every allocation contract now takes a readiness predicate `H : RtReady`
(`Janus/Contracts/Alloc.lean`, "The runtime's own state at a call"). Its precondition also
requires `H args g sp (rtView rt s.mem)`:

* `args` are the call's argument registers as numbers;
* `g` is arm64 `R28` or amd64 `R14`;
* `sp` is the stack pointer at the callee's entry;
* `rtView rt m` is memory as the runtime owns it: the bytes inside `rt`, every other byte 0, and
  the regions.

Theorems quantify over `H` and assume it at entry, for the call they make. For example, NewPair
assumes `H [pairType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)`, where `pairType`
is recomputed from the `ADRP`+`ADD` pair (amd64: the extraction's data object). The caller's own
stores lie outside `rt` and do not change `rtView` (`rtView_writeLE`, a rewrite rule of both
executors), so `janus_run` carries `H` to the call.

`Janus/Tactic/Common.lean`'s `Outside` discharger had to handle a bare `Outside a n rt` with a
variable `rt`: `simp only` failed with "no progress", now `failIfUnchanged := false`. This only
lets the discharger close more goals.

* **The real runtime meets the fixed contract** with `H args g sp v` := "from every call state
  with these arguments, `g`, `SP` and runtime memory `v` (whatever the rest of memory holds),
  the runtime's code returns as the contract says". That is a function of exactly what `H`
  sees. It holds at the calls the runtime serves without a system call, a throw or a stack
  move: a free `mcache` slot, enough heap, no GC assist that parks or shrinks the stack.
* **Each fixed contract is satisfiable in the kernel** (`Janus/Contracts/AllocSat.lean`,
  `AllocSatAmd64.lean`: `newobject_satisfiable`, `mallocgc_satisfiable`, `makeslice_satisfiable`,
  `growslice_satisfiable` and their `…64` versions; toy code that returns a zeroed heap, an `H`,
  and a call state meeting the whole precondition for a non-zero size). The theorem built on the
  contract fires too: `audit/round9/controls/NewPair_witness.lean`
  places a two-instruction allocator (`MOVZ X0, #0x10000; RET`) at `runtime.newobject`. It
  chooses `rt` = a 64 KiB heap plus `Pair`'s descriptor, and `H` = "the argument is a
  descriptor inside `rt` of at most 32 KiB and the heap is writable and zero", and proves
  `NewobjectContract` for them by running the code. It then builds a concrete NewPair call
  state that satisfies the whole precondition, `H` included, and instantiates
  `Proof.correctness`, so the theorem fires (row C1c).
* Row C1b: the pre-fix argument, restated against the fixed contract
  (`audit/round9/model/UnsatFixed.lean`), does not compile. The fixed contract holds for
  `H := fun _ _ _ _ => False`, so its negation is false.

Remaining scope, now stated in SOUNDNESS.md: one allocation per theorem; stack moves (growth,
or a self-scan in GC assist that shrinks the stack) are calls `H` excludes; the model is
single-threaded, so `H` is a property of the call state, and other threads are not covered.

## C2 (HIGH, BROKEN → fixed): malloc-header objects are not 16-aligned

Go 1.26 `mallocgc` serves a small pointerful object of more than 512 bytes with
`mallocgcSmallScanHeader`, which stores the type pointer in the slot and returns
`x = add(x, gc.MallocHeaderSize)`. Slots of the classes involved (576 bytes and up, all
multiples of 16) start 16-aligned, so `x ≡ 8 (mod 16)`. `Fresh` promised `ptr % 16 = 0` whenever
`size % 16 = 0`, for example for `newobject` of a 528-byte type with pointers. Row C2a: 50 such
objects on each ISA, all at `8 mod 16`. A contract the real runtime breaks for one type is false
for the real runtime as a whole (it is a single `∀`), so this alone already kept the old
contracts from describing the real binary.

Fix: `Fresh` takes `hdr` (`mallocHdr size noscan`: pointerful, `512 < size ≤ 32760`). Such an
object is promised 8-alignment only. `newobjectObj`, `makesliceObj` and `mallocgcObj` pass it on
both ISAs. Row C2b checks the boundaries.

## M1 (HIGH, BROKEN → fixed): `MallocFast` said nothing about calls on `m0`

`MCacheOK` listed `(globLo, globHi - globLo)`, the hull of `debug.malloc`, `gcBlackenEnabled`,
`SizeToSizeClass8`, `SizeClassToSize`, `writeBarrier` and `MemProfileRate`, in a `Spread` with the
`m`'s fields. In the example binary the hull is `[0x160448, 0x1907ed)` in `.noptrdata`/`.bss`, and
`runtime.m0` is at `0x16a880`, inside it. Every goroutine running on the main thread's `m`, which
includes the main goroutine of nearly every program, violates `MCacheOK`.

The in-process probe (`probe9 mcache`, arm64 under qemu) reads every conjunct of `MCacheOK` just
before 20000 real `mallocgc(64, nil, false)` calls (string concatenation), at the offsets the
proof uses:

| | holds |
|---|---|
| shipped `MCacheOK` | 0 / 20000 (the globals hull: 20000 failures; everything else as below) |
| round-9 `MCacheOK` | 19682 / 20000 (the 318 others: the slot is the last of a 64-slot `allocCache` block, the refill path) |

`span.needzero = 0`, a zero slot, `elemsize` = class size, GC and profiling off, and `p ≠ 0`
held at every sampled call. The other `MCacheOK` facts are therefore satisfiable in practice.
Under a constantly running GC (`probe9 loopgc`), every sampled span was `emptymspan`: GC start
flushes the mcaches. That is the refill slow path, correctly excluded.

Fix: each global is its own entry of the `Spread` (13 objects). The `Obj` fact for the hull
stays, since all six globals lie in one RW segment. `zero_of_run`, `fast_path` and
`fresh_of_fastPost` (which also follows C2's `Fresh`) are updated, and MallocFast verifies.

## S1 (MEDIUM, fixed): SetNext's `BarrierOK` interval

The gdb probe (`setnext_amd64.py`, `probe9 loopgc`) stops at 300 real `SetNext` calls with the
write barrier on. It computes the tightest `[lo, hi)` (the hull of `g.m`, `m.p`, `p.wbBuf` and
the slots): only 82 calls admit an interval missing `n.Next` and the stack window. The goroutine
stack, `g`, `p` and the heap objects interleave in the arena. Fix (both ISAs): `BarrierOK s n`
states that each of the four runtime objects is `Apart` from `n.Next` and the stack, and the
slots are `Apart` from the cursor. 300 of 300 calls meet it. The `lo`/`hi` parameters are gone.

## H2 (CRITICAL readability, BROKEN → fixed): lookalike binders beyond the fold table

Round 7 rejected binders that fold to the same Latin text and binders with non-identifier
characters. Lean's identifier letters (`isLetterLike`) also include polytonic Greek
(U+1F00–U+1FFE), the accented and Coptic range U+03CA–U+03FB, and the whole letterlike block.
These contain exact visual duplicates the fold did not map:

* **H2a:** `ό` U+03CC vs `ό` U+1F79 (canonically equivalent);
* **H2b:** `K` U+212A KELVIN SIGN vs `K`;
* **H2c:** `ι` U+1FBE vs `ι` U+03B9. The fold maps the latter to `i` and not the former, so the
  two fold *apart*.

Each verified "Add returns `x * y`" from `(h : ∀ K, K = K)`. Fix (`Janus/Tools/Audit.lean`):
binders may use ASCII, subscripts, basic Greek (`greekBinderChar`), the mathematical
script/fraktur/double-struck letters (which the fold maps to Latin) and only the letterlike
symbols the fold maps. The fold also maps `γ → y` and `σ → o`. Combining marks and zero-width
characters were already rejected. Binders in `let`, `match` alternatives and `fun` inside
proof-local definitions go through the same check (`binderNames` walks the definition bodies);
constant names must be plain ASCII (round 6 F1). No shipped statement uses a newly rejected
letter. Round 7's honest-Greek control H1b still verifies.

## I1g (LOW, fixed): contract names

`Janus.Program.contractAddr` and `Janus.Amd64.Program.contractAddr` join round 8's name-lookup
list: the name must be a literal naming one of `Extracted.program.contracts`.

## D1 (MEDIUM, fixed): `docs/SOUNDNESS.md` lost three rounds of text in a merge

`git diff 971be53 2bf7f35 -- docs/SOUNDNESS.md` is empty: the merge took agent/stubpin's file and
discarded the 205 lines agent/redteam8 and agent/alloc had added. The restoration is
`git merge-file` of base `139f774`, ours `a679ee8` and theirs `971be53`, with the one conflict (the
G3 paragraph) taken from stubpin, then agent/rt-fp's change re-applied. No other file of that
merge lost content (each file was checked against both parents). Row D1 checks that the sections
are present.

## Not findings (checked)

* **growslice capacities** (G1): exact for every growth observed. `roundupsize 0` is 8 in the
  model and 0 in Go, which no contract reaches (`newLen > oldCap ≥ 0`).
* **Zeroing**: tiny blocks are zeroed when the block is fresh, small spans clear when
  `span.needzero` is set and `needzero` asked, and large objects clear before return (pointerful
  ones always). The `needzero = false` + pointers case throws in Go and is excluded.
* **The `[SP-8, SP)` slot** (the caller's saved frame pointer) is preserved by Go's arm64
  prologue (`STP` at the callee's new `SP - 8`).
* **Memory guard** (MG): every mechanism and limit keeps H1a blocked, and a memory kill is
  `Invalid: … exceeded the memory limit`.
* **`--contract` and stubs** (L1): see the table.

## Regression status

Run on the merged tree, one heavy job at a time:

| Suite | Result |
|---|---|
| `audit/round9/run-round9.sh` | all rows as expected |
| `scripts/verify-all-examples.sh -j 1` | all examples Verified (MallocFast included) |
| `go test ./cmd/...` | ok |
| `audit/run-all.sh`, `audit/round{2..8}` runners | all rows as expected |

(See the commit message for timings.)
