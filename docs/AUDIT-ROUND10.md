# Audit round 10: features merged since round 9

Branch `agent/redteam10`, based on `merge/b23` (main `f84051a` + round 9). Scope: what was
merged while round 9 ran or after it: round 9's own fix (the readiness predicate `H : RtReady`),
the cache collector, Go assembly (ABI0), the interface contracts, the amd64 `GOAMD64=v3` and SSE
packed models, the arm64 crypto model, the regenerated ASL slice (agent/asl), and a sweep for
contracts and example theorems that nothing shows satisfiable.

The method is round 9's: for every hypothesis, ask whether a real call in a real process meets it,
and also whether the statement or the contract can be **chained or instantiated** into something no
implementation meets. Each finding is a row of `audit/round10/run-round10.sh`. The probes are
`audit/round10/probe` (go1.26.0, both ISAs, arm64 under qemu-aarch64), kernel-checked models in
`audit/round10/model`, attack proofs in `audit/round10/attacks`, and differential runs against
this host's CPU (amd64 oracle) and the sail-arm v9.4 decode clauses (arm64).

## Summary

| ID | Severity | Finding | Status | Rows |
|---|---|---|---|---|
| V2 | **critical** (vacuity, kernel-checked) | **The map contracts `Assign` and `MakeSmall` contradicted `MapModel.Laws`.** Their precondition is `M.Env` and their postcondition hands `M.Env` back, so from one call state the contract chains: `2^64` inserts of distinct keys (or `2^48 + 1` distinct new maps), all kept in the fixed private memory. The law `len` says the header's first word (below `2^64`) is the key count. `audit/round10/model/MapUnsat.lean` proves `M.Laws ∧ Assign … ∧ (one call state) → False` and the same for `MakeSmall`. So **Insert, InsertGet and NewMap, on both ISAs, were vacuous**: `V2a` "verified" with Insert's exact hypotheses that `m[k] = v` stores `v + 1`. Round 9 had listed the map contracts as "not unsatisfiable the way C1's were". | **BROKEN → fixed** | V2_model…, V2a, V2_ctl, SAT |
| V1 | **critical** (vacuity by the statement) | **A theorem could instantiate a satisfiable contract into an unsatisfiable one.** Nothing required the readiness predicate, the runtime ranges, the model or the code of a contract hypothesis to be quantified. `H := fun _ _ _ _ => True` ("the runtime is always ready") is round 9's false contract again: `V1a` "verified" that NewPair returns 42, with a statement that reads as a stronger, unconditional claim. Likewise `rt := []`, `rt` pinned by a premise `rt = []`, a contract about `Extracted.program` itself (no code there), or the toy model `R0`. | **BROKEN → fixed** (auditor rule) | V1a–f, V1_ctl |
| V3 | high (vacuous for the real binary) | **The allocating interface contracts could not be met by the real runtime.** `convT*` allocate a box per call (`convT64(v)`, `v ≥ 256`: 100000 calls, 100000 distinct boxes, both ISAs) and `typeAssert`/`interfaceSwitch` allocate when they rebuild a cache; each contract hands `R.Env` back. So a contract demanded an unbounded chain of allocations from any `R.Env` state; in the model (fixed regions, no system calls, so no `mmap` and no collector) the real runtime meets no such `R.Env`, and Box, AsHasher, Classify said nothing about the real binary. A toy model meets them, so unlike V2 this is not refutable in the kernel. | **fixed** | V3a, V2_V3_…take_H, V3_ctl |
| I1 | high (contract promises more than the runtime) | **`TypeAssert` admitted a nil type.** With `CanFail` the runtime returns `nil`, but about once in 1000 calls it then rebuilds the cache with `buildTypeAssertCache(oldC, nil, nil)`, which reads `nil.Hash` and faults: 202 faults in 200000 calls (amd64), 203 (arm64). Compiled code tests for nil first, so no example was affected. | **BROKEN → fixed** | I1a, I1b |
| SAT2 | medium (process) | **The SAT row checked witness names only.** `theorem assign_satisfiable : True` would have counted. It now requires the witness statement to name its contract and exhibit a state. | **fixed** | SAT, SAT_selftest… |
| F1 | medium (framework identity) | **An in-place framework build could be stamped for sources it was not built from.** A `--janus-root` checkout is built in place, and the ready stamp recorded the SHA-256 of the sources janus read *before* Lake ran. If the checkout changed during the build (a `git checkout` in another terminal), the modules of the other commit were stamped as this framework's; after the checkout went back, the next run found the stamp ready and verified against modules compiled from the other commit while reporting the first commit's framework SHA-256. `TestFrameworkSourcesChangeDuringBuild` reproduces it with a fake Lake. Shared caches between clones at different commits hold (below). | **BROKEN → fixed** | F1 |
| A1 | low (informational) | **The ABI convention warning missed linked programs.** It matched only `Ensures… Extracted.program Extracted.entry`, so no theorem with runtime contracts (`(Extracted.program.link impl)`) and none with `.withExit` was ever checked. | **fixed** | A1 |
| G | — | Cache eviction: planted symbolic links in result, trusted, consumer and tmp are removed, never their targets; a collection that deletes the run trees of a running verification (no grace, 36 ms age) leaves an attack blocked and a good proof with a verdict, and a later run verifies. Every reader re-verifies (HMAC, pins, stamps). | holds | G1, G2 |
| X | — | amd64 v3 + SSE packed: about 2.24 M cases (legacy-prefix and VEX field sweeps, boundary encodings, FMA at the underflow and overflow boundaries under 17 MXCSR settings, packed FP with mixed trapping lanes): 0 MISMATCH. The decoder is stricter than hardware where it differs (rejects REX-before-`66`, `66`+`F3`, `2E` before VEX, `VZEROALL`). | holds | X1 |
| C | — | arm64 crypto/CRC32/permutes: the Lean decoder against the sail-arm v9.4 decode clauses on all 2,097,152 words of the SIMD/FP and register groups: 0 reserved words accepted, 0 valid words missed. 241,000 qemu executions: 0 mismatches. The stated feature set (AES, SHA1/2/512, SHA3, PMULL, CRC32; SM3/SM4 rejected) is exactly what the decoder accepts. | holds | C1 |
| R1 | — | Round 9's `H : RtReady` itself: `H` is quantified, so a proof cannot choose it, and the contract's `H`-arguments are exactly the call's (a statement that assumes `H` for other arguments does not prove). What it could not stop was a *statement* choosing `H` (V1) or a contract chaining (V2/V3). | holds (with V1) | V1_ctl |

The ASL `sqrt_real` substitution (agent/asl) holds; it is reported in its own section below.

**Statements changed** by the fixes: Insert, InsertGet, NewMap, Box, AsHasher, Classify on both
ISAs take `H : RtReady` and assume it at entry for their one allocating call; their
`Proof.Witness` sections supply `H := Htrue`. Every changed theorem verifies.

## V2 (CRITICAL, BROKEN → fixed): the map contracts that allocate were unsatisfiable

`Assign p addr M := ∀ f, Summary p addr pre post` with
`pre s := RTPre M 3 s ∧ M.Typ t ∧ m ≠ 0 ∧ M.Rep s.mem m f` and a postcondition that, for every value
`v` stored into the returned slot, gives `M.Rep (m'.writeLE slot 8 v) m (f.set k v)` **and
`M.Env` of that memory**. `RTPre` asks for `M.Env`, the stack window and an admissible return
address, none of which the call consumes. So from one call state `s` the contract applies again
to `s` with the new memory and key `k + 1`, and so on: after `2^64` inserts the map at `m` holds
every 64-bit key. `MapModel.Laws.len` says the header's first word is the number of keys, and an
8-byte word is below `2^64`. `MakeSmall` falls the same way by pigeonhole: each call returns a map
distinct from every represented one and keeps the others (`OthersKept`), and each header is
below `2^48` (`Laws.len`), so `2^48 + 1` calls are impossible.

`audit/round10/model/MapUnsat.lean` proves both in the kernel (`assign_unsat`,
`makeSmall_unsat`) with the merge/b23 definitions copied verbatim. The only extra assumption is
that the stack-guard word is outside what the call may write, which `CallerOK` (the examples'
precondition) gives. `V2a` turns it into a verified false theorem about the real binary:
Insert's exact hypotheses, conclusion `M.Rep s'.mem m (f.set k (v + 1))`.

**Fix.** `Assign` and `MakeSmall` take a readiness predicate `H : RtReady` and require
`H [t, m, k] g SP (rtView M.priv mem)` (`MakeSmall`: `H []`) at the call, like the allocation
contracts of round 9. The postcondition does not give `H` back, so the chain stops after one
call. `M.Env` keeps its meaning, the runtime's structural invariant, which the real runtime does
preserve. The six theorems assume `H` at their entry; the caller's stores are outside `M.priv`,
so `rtView_writeLE` carries it to the call. `Janus/Contracts/MapSat.lean` and `MapSatAmd64.lean`
prove both fixed contracts satisfiable with their laws: a one-header toy model `M0` (count 0 or 1,
key 5), machine code, `H`, and a call state meeting the whole precondition. Row
`V2_model_fixed_contracts_unsat_attempt`: the same argument against the fixed contracts does not
compile.

Still open (owner agent/maps): `_satisfiable` witnesses for the 14 non-allocating map contracts
(`Access1/2`, `Delete`, `Clear`, `IterStart`, `IterNext`, `Access2Ptr`, both ISAs), listed in
`audit/round9/sat-pending.txt`. They do not chain into growth (no contract among them adds keys
or maps), and `MapAccess1Small` proves `Access1` from the real runtime code for small maps.

## V1 (CRITICAL, BROKEN → fixed): a statement could choose the runtime

Round 9 made each allocation contract satisfiable by giving it a readiness predicate `H` that
"the theorem quantifies over". Nothing enforced that. A statement can pass a closed term:

* `V1a`: NewPair with `NewobjectContract … rt 4096 (fun _ _ _ _ => True)`. That contract is
  round 9's unsatisfiable one, so the proof derives `False` from it and concludes `X0 = 42`. The
  printed statement shows `fun x x_1 x_2 x_3 => True`, which reads as "the runtime is always ready".
* `V1b`: `rt := []`: no object can be inside `[]`, so every call state meeting `H` refutes the
  contract (an attack proof, not just a statement: it runs NewPair to the call).
* `V1c`: `rt` a variable but `(hrt : rt = [])` a premise. `V1d`: a contract about
  `Extracted.program` (no code at the contract address). `V1e`: the toy model `R0` of the
  witnesses as the interface model. `V1f`: V1a's closed contract moved into the theorem's own
  `Ensures` precondition instead of a premise.

**Fix** (`Janus/Tools/Audit.lean`, `checkContractHyps`). Everywhere in the statement (after
proof-local definitions are expanded; only a conclusion that is itself a contract, a theorem
*proving* one, is exempt), each application of a runtime contract (a definition in
`Janus.Contracts` whose body is a `Summary`) must pass, for each parameter of type `RtReady`,
`List (Nat × Nat)`, `IfaceModel` or `MapModel K V`, a variable bound by the statement, and for its
program `Extracted.program.link impl` with `impl` such a variable. No other premise may mention
those variables, except the model laws (`R.Laws`, `M.Laws`). A dependency definition used by
the statement may not apply a contract (it would hide it from the check). A theorem whose
conclusion is a contract (MapAccess1Small proves `Access1` for `smallModel`) is not affected
(`V1_ctl_contract_in_conclusion`).

Not covered by the rule, and left to the reader as for any precondition: constraints the
theorem's own precondition (`Ensures … pre`) puts on these variables, and the numeric parameters
(`stack`; a contract with too small a stack is satisfiable by a toy and not by the runtime).

## V3 (HIGH, fixed): allocating interface contracts and the real runtime

Every interface contract has the map contracts' frame: `R.Env` before, `R.Env` after. For
`convT64(v)` with `v ≥ 256` the runtime allocates a fresh 8-byte box each time (row V3a); for
`typeAssert`/`interfaceSwitch` a cache rebuild allocates a new cache. A contract therefore
claims that from any `R.Env` state an unbounded sequence of allocations succeeds. In the model
the regions are fixed and no system call executes (no `mmap`, no futex, so no collector cycle),
so the real runtime's code eventually takes a path the model faults on; the largest `R.Env` it
preserves is empty, and the theorems assuming these contracts held for the real binary only
vacuously. Toy models meet the contracts (boxes may be reused, since nothing says a box keeps
its value), so the kernel cannot refute them: this is a property of the real runtime, argued from
its source and the model, not a proof.

**Fix.** `ConvT`, `ConvTnoptr`, `ConvT16/32/64`, `ConvTstring`, `ConvTslice`, `TypeAssert` and
`InterfaceSwitch` (both ISAs) take `H : RtReady`, required at the call (argument registers, `g`,
`SP`, `rtView R.priv`) and not handed back. The witnesses (`IfaceSat`, `IfaceSatAmd64`) use
`Htrue`; Box, AsHasher and Classify assume `H` at entry. `AssertE2I`, `AssertE2I2` (a new itab
at most once per type pair, bounded) and `efaceeq`/`ifaceeq` are unchanged.

The other interface questions, measured against go1.26.0 on both ISAs, hold: every law of
`R.Laws` (7,338 types walked on amd64, 4,291 with `TFlagRegularMemory`, none with a float,
string, interface or padding; byte equality agrees with `==` on all bit flips), `StaticItabs`
(148 of 148 static itabs returned by `getitab`), `TACacheOK`/`ISCacheOK` (3,000,000 AsHasher and
Classify calls over 261 dynamic types, every cache entry correct, also after 6 GCs). Two
documentation slips in `Janus/Spec/Type.lean` were noted (a dynamically built itab's `Hash` is 0,
not a copy of the type's; `Equal` is a funcval pointer, not a code address); no contract uses them.

## I1 (HIGH, BROKEN → fixed): `typeAssert` with a nil type

The contract admitted `t = 0` when `desc.CanFail` (returning itab 0). `runtime.typeAssert`
returns `nil` there, then goes on to the cache update: `cheaprand()&1023 == 0` and
`cheaprand()&Mask == 0` (always, for the empty cache) lead to
`buildTypeAssertCache(oldC, nil, nil)`, whose `addEntry` reads `typ.Hash`, a nil dereference.
`audit/round10/probe tanil`: 202 of 200000 calls fault on amd64, 203 under qemu-aarch64. The
compiler emits the nil test before the call, so the contract now requires `t ≠ 0`
(`model/TypeAssertNil.lean`). The AsHasher proofs already called it only with a non-nil type.

## F1 (MEDIUM, BROKEN → fixed): the framework build stamp and a changing checkout

Lead from the coordinator: could the real cache make `janus verify` check against a different
framework checkout, or a stale one, than the one it runs with (two clones of Janus at different
commits sharing `~/.cache/janus`)?

* **Consumer packages: holds.** The consumer's `janus` dependency (`git` in `.lake/packages`, or a
  `path`) is byte-compared with the running framework (`compareFramework`); a different checkout
  is an `Invalid: framework identity`. The workspace's framework package is synchronised from the
  running framework's own files, its library is copied from the cached base
  `v1/framework/<SHA-256 of the running framework>` (rebuilt if its stamp, sources or module pins
  differ), and the workspace family is keyed by that SHA-256 and the package root. Two clones with
  different framework files get different bases and families; clones with identical framework
  files share them and are the same framework. The go-test symptom (tests resolving `janus` to
  another worktree) is test-side.
* **A `--janus-root` checkout built in place: broken.** For it, `ready` cannot compare sources
  with a copy (the checkout *is* the sources), so it relies on the stamp, which `build` wrote with
  `fw.Sha256`, the hash of the sources read when janus started. Lake compiles whatever is on disk
  while it runs. A checkout that changes during the build therefore gets a stamp naming the old
  sources over modules of the new ones, and once the checkout returns to the old sources, every
  later run is "ready" and uses the other commit's modules (the kernel replay checks them, but
  against their own definitions), while reports name the old framework. Fix
  (`cmd/janus/framework.go`, `build`): after Lake, the sources are read again and must hash to
  `fw.Sha256` (with the same manifest), else nothing is stamped and the run fails; for a cache copy
  the copy is compared with `fw.Files` again. Residual: sources that change and change back
  within one build are not detected (it takes a concurrent writer of the checkout).

## A1 (LOW, fixed): the convention warning

`janus verify` warns when a statement applies the other calling convention's contract to
`Extracted.entry` (docs/ABI0.md). Its regular expression required the program argument to be
`Extracted.program`, so it never fired for `(Extracted.program.link impl)` or `.withExit`. It now
accepts both (and a parenthesised entry); `TestABIMismatch` has the cases. The classification
stays informational: a theorem stated in the other convention verifies and is about calls laid
out that way, which real callers do not make; an entry passed through a proof-local definition is
still not recognised.

The ABI0 vocabulary was otherwise reviewed: `CallSetup0` (frame word `i` at `RSP + 8 + 8i`, the
return address, `DF` clear; arm64 16-aligned `RSP`) matches what go1.26.0 emits, `ABIReturn0`
obligations are proved, `TlsG` is a precondition, and the wrapper theorems execute the wrappers.

## G (holds): cache eviction

Probed beyond `TestCacheGCRedTeam`/`TestCacheGCConcurrentVerify`: symbolic links planted in
`v1/result`, `v1/trusted`, `v1/consumer/<family>` and `v1/tmp` (row G1) are removed by
`janus cache gc --max 0 --grace 0s --all`, their targets untouched. A collector run every 0.2 s
with `JANUS_CACHE_TMP_HOURS=0.00001 --grace 0s` deletes the trusted, work and audit directories of
a running verification; the pins (`pinnedLib.diff` reports a missing file), the nonce-marked
audit output and the HMAC'd result entries turn that into an error, never a pass: the attack stays
blocked and the control ends with a verdict (G2). No path was found where a missing file is read as
success. Hazard (unchanged, documented): `--grace 0s` and a tiny `JANUS_CACHE_TMP_HOURS` let a
collection break a running verification.

## X (holds): amd64 v3 and SSE packed

A sub-agent ran about 2.24 M targeted cases on this Sapphire Rapids host (`-j 8`): random legacy
prefix sequences on the `0F`/`0F38`/`0F3A` maps (REX before and after the mandatory prefix), every
VEX map, `pp`, `L`, `W`, `vvvv` and stray prefixes, 143 hand-picked boundary encodings, scalar FMA
on the underflow-after-rounding and overflow boundaries under 17 MXCSR settings (all `RC`, `FTZ`,
`DAZ`, unmasked `UE/OE/PE/IE`), packed FP with trapping and non-trapping lanes, and the repo's
generators with new seeds: 0 MISMATCH. Row X1 regenerates the boundary, FMA and packed sets. One
open point that a single Intel host cannot settle: `MIN`/`MAX` with `DAZ = 1` return the operand
as `DAZ` read it (a denormal as zero), as this CPU does; if AMD returns the original denormal the
result is vendor-dependent. Go's ABI keeps `DAZ` off, and it only matters to a theorem that
allows `DAZ = 1`. The FMA model faults (`undefinedResult`) for two or more NaN operands and for
`0 × ∞ + NaN`, so it does not commit to Intel's NaN order.

## C (holds): arm64 crypto

Row C1 compares `janus-decode` with the first matching sail-arm v9.4 `__DecodeA64` clause and
its UNDEFINED conditions on all 2,097,152 words with bits 27:25 = 111 or 101 (`crypto/clauses.json`,
from `crypto/sailclauses.py`): 0 accepted reserved words, 0 missed. Execution against qemu
(241,000 cases, aliased registers, TBL tables wrapping past `V31`, XAR rotations 0..63): 0
mismatches. On Linux Go runs SHA3 instructions only on darwin (`useSHA3`), a detail the feature
note could add.

## The ASL slice regeneration (agent/asl): holds

`JanusASL/sail/fakereal_sqrt.py` replaces the one `sqrt_real` of the generated `FakeReal.lean`
(the regex matches exactly one definition; the vendored slice has no other). The replacement,
with `K = 1100`, computes `m = Nat.sqrt ⌊num·4^K/den⌋` and returns `m/2^K` when `m²·den = num·4^K`
(exact), else `(2m+1)/2^(K+1)`: round-to-odd at `2^-1100`, strictly inside the interval of the
true root. Its single call site is `FPSqrt` → `FPRound(sqrt_real value, fpcr, N)` with
`N ∈ {16, 32, 64}`; the slice has no estimate (`FRSQRTE`/`FRECPE`), BFloat16 or FP8 rounding
path. The root of a positive finite input is normal in every format, and every boundary
`FPRound` tests is a multiple of `2^-590` or coarser, so the substituted value always rounds
like the true root, with the same IXC/UFC/OFC. A sub-agent's model (a transliteration of
`FPRoundBase` deciding on the true root by exact integer comparisons, checked against hardware
`sqrt` on 19,984 doubles) compares it under 16 FPCR settings (FZ, FZ16, AH, UFE) and 5 rounding
modes: half precision exhaustively, 2,539,440 comparisons, 0 mismatches; single precision
5,288,960 comparisons (66,192 samples: random, every exponent with edge mantissas, subnormals,
exact squares, near-ties) and double precision 6,600,160 (82,515 samples, same design): 14,428,560
comparisons in all, 0 mismatches. `docs/AUDIT-ASL.md` row A5 still probes
`sqrt_real` at `2^80`, not the `2^1100` the code uses.

## Open items

* `_satisfiable` witnesses for the 14 non-allocating map contracts (agent/maps); `MapSat.M0` is a
  starting point.
* Whole-theorem non-vacuity witnesses (`Proof.Witness.nonvacuous`) exist for the interface
  examples and for NewPair (round 9 C1c); MakeSlice, AppendOne, MakeAdder (both ISAs), NewPair
  (amd64) and the map examples have none. V1 and the contract witnesses rule out the patterns
  found this round, not every joint unsatisfiability of a hand-written precondition.
* Satisfiable by a toy is weaker than satisfiable by the real runtime (V3): the witnesses do not
  show the latter, and cannot in the model.
* `MIN`/`MAX` under `DAZ = 1` on AMD (X), unconfirmed.

## Regression status

On `agent/redteam10` (merge/b23 + this round), one heavy job at a time (`LEAN_NUM_THREADS=4`,
`JANUS_JOBS=2` once the coordinator asked for it):

| Suite | Result |
|---|---|
| `audit/round10/run-round10.sh` | all rows as expected (V1a–f, V1_ctl×2, V2×5, V3_ctl, SAT×2, I1a–b, V3a, A1, F1, G1–G2, X1, C1, ASL1), 74 min |
| `scripts/verify-all-examples.sh -j 1` | all ok: 78 arm64 items, 80 amd64 functions, 10 assembly items (6264 s) |
| `go test -count=1 -parallel 2 -timeout 7000s ./cmd/...` | ok (1269 s) |
| `audit/run-all.sh -j 1` | ok (670 s) |
| `audit/round{2,…,9}` runners, `audit/rt-model/run.sh` | all rows as expected |

The double-precision `sqrt_real` sample (`audit/round10/asl/sqrt_model.py`) takes hours and is not
a row; its result is the one quoted above.
