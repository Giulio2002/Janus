# Changelog

## v0.3.2 (2026-11-13)

Bug fix (PR #3): janus's own compile of a consumer package's modules (olean provenance) could reuse a stale
stored olean. The trusted olean store key of a module covered its source and its direct imports' olean bytes
only. An olean does not cover its own imports, so a change deep in the import closure (the body of a reducible
definition) could leave an intermediate olean byte-identical while a module above it elaborated against the old
body. The stale olean was then reused, and the kernel replay rejected it: **fail closed, never a wrong
verdict**, but such rows failed in warm caches until the store was wiped.

- The key now also covers each import's own key, hence the whole closure (`cmd/janus/provenance.go`). Key
  format `janus-own-olean-v3`: existing store entries are rebuilt once.
- `TestOleanStoreKeyTransitive`: Deep → Mid → Add, where Mid's olean is byte-identical across a change of Deep's
  body; all three must recompile (fails before the fix: only Deep and Mid did).

## v0.3.1 (2026-11-12)

`lakefile.toml` still says version 0.3.0: it is embedded in `janus` (verifier identity), and the release ships
the exact gated tree.

### BREAKING: the allocation contracts keep the type descriptor out of the callee's stack window
**BREAKING (runtime-contract preconditions; consumers must re-discharge).** The allocation contracts'
preconditions (`NewobjectPre`, `MakeslicePre`, `MallocgcPre` for `typ ≠ 0`, `GrowsliceArgs`, and their amd64
twins `…Pre64`, `GrowsliceArgs64`) now also require the type descriptor to lie outside the callee's stack
window: `Outside (s.regs 0).toNat 16 (calleeStack s stack 1|3)` (arm64; `s.regs 1` for `mallocgc`, `s.regs 4`
for `growslice`; amd64 `RAX`/`RBX`/`RSI`, `calleeStack64`). `GrowsliceOld`/`GrowsliceOld64` now take the stack
bound and require the old elements outside the window.
Why: the pinned go1.26.10 `runtime.makeslice` pushes its frame before it reads `et.Size_` (arm64
`MOVD.W R30,-48(RSP)`, `MOVD R29,-8(RSP)`; amd64 `PUSHQ BP`), so for a state with the descriptor inside
`[SP-56, SP-40)` the real runtime does not do what the contract says. The old contracts held there, so every
theorem assuming them was vacuous for the real binary in those states (no real caller passes such a descriptor).
The change reaches the non-live contracts (`NewobjectContract`, `MakesliceContract`, `MallocgcContract`,
`GrowsliceContract`) and the live ones (`…LiveContract`, the SC variants) through their shared `…Pre`.
`TypedMemmove`/`TypedMemclr` (+Live, +RtPre64 reads) already had this conjunct.
Migration: at a call site, prove `Outside et 16 (calleeStack s stack n)` for the descriptor. A real descriptor
is `.rodata`, which is not writable: with `janus_data hd [hw]` (the call window `hw`) the context has
`a + n ≤ base ∨ base + len ≤ a` per data object, and `simp only [calleeStack, outside_cons, outside_nil,
and_true]; omega` closes it (arm64 and, with `calleeStack64`, amd64). For a concrete witness state: `by simp only
[calleeStack, outside_cons, outside_nil]; decide` (`Outside` has no `Decidable` instance; the fv-uint256 call-site
modules define a scoped one). `growslice`: also the old array (a live object, `hL2W`-style fact) outside the window.
Tests: red-team round `test/redteam/rounds/roundalloc` (the descriptor-in-window state satisfied the old
precondition, falsifies the new one; ten drop-the-conjunct mutants flip; rodata control passes);
`LiveSat*`/`AllocSat*`/`MallocSCSat*` witnesses carry the conjunct.

### Additive: zero-byte `memmove` and `makeslice` contracts (PR #2)
New runtime contracts for zero-byte runtime calls, `memmove` and `makeslice` (additive: no existing statement, proof
or auditor rule changes).

- `MakesliceZeroLive` (arm64, `Janus/Contracts/Live.lean`) and `MakesliceZeroLive64` (amd64, `LiveAmd64.lean`): a call
  of `runtime.makeslice(et, len, cap)` with `et.Size_ · cap = 0` returns with the live set and the budget unchanged
  (`ZeroAllocRet` / `ZeroAllocRet64`; the result pointer is unconstrained). `MakesliceLiveContract` appends an empty
  range at an unconstrained pointer to the live set in that case, after which a caller can state neither `LiveExt`
  nor a later call's `LiveSep`. The precondition is `MakesliceLiveContract`'s with cost `0`, the zero size, and the
  type descriptor outside the callee's window. `MakesliceZeroLive(64).of_codeIn`.
- Justification: the pinned `makeslice` calls `mallocgc(0, …)`, which returns `&runtime.zerobase` first thing
  (`malloc.go:1075`). `LiveSat.makesliceZeroLive_pinned` / `LiveSatAmd64.makesliceZeroLive64_pinned` run the pinned
  go1.26.10 `makeslice` and `mallocgc` themselves in the model, for every runtime hypothesis.
- `zeroAllocRet_of_frame` (`LiveCall.lean`), `zeroAllocRet64_of_frame`, `MakesliceZeroLive.of_live` /
  `MakesliceZeroLive64.of_live` (a live-contract stub is a zero-byte witness when the invariant ignores empty live
  ranges), `LiveSat.toyR_dropEmpty`, `inRs_append_empty`, `view_append_empty`; SAT witnesses
  `makesliceZeroLive(64)_satisfiable` (both makeslice contracts on one stub).
- Both contracts are on the auditor's pinned-contract list. JanusTests.MakesliceZero (incl. a red team: a stub that
  charges the budget for a zero-byte request is refuted, `¬ MakesliceZeroLive …`, both ISAs). docs/RUNTIME-CONTRACTS.md:
  "Zero-byte allocations".

New runtime contract for `memmove` of zero bytes:

- `MemmoveZeroLive` (arm64, `Janus/Contracts/Live.lean`) and `MemmoveZeroLive64` (amd64, `LiveAmd64.lean`): a call of
  `runtime.memmove(dst, src, 0)` returns as a `MemmoveLive` call does, with an empty written range, under only the ABI
  and live parts of the precondition (nothing about `dst` or `src`). Go's `copy` calls `memmove` with `n = 0` and a nil or
  `zerobase` pointer, which `MemmoveLive`'s precondition cannot accept.
- `MemmoveLive.withZero` / `MemmoveLive64.withZero`: the two contracts give the `memmove` summary whose precondition is
  `n = 0 ∨` the destination and source facts. `LiveMemRet.of_nil`, `LiveMemRet64.of_nil`, `liveMemRet_none`,
  `liveMemRet_none64`, `MemmoveZeroLive(64).of_codeIn`.
- Justification: the pinned runtime's `memmove` returns before any memory access for `n = 0` (arm64 `CBZ R2, copy0`;
  amd64 `TESTQ BX, BX; JEQ move_0`). `LiveSat.memmoveZeroLive_pinned` / `LiveSatAmd64.memmoveZeroLive64_pinned` run the
  pinned go1.26 code in the model and prove the contract for every runtime hypothesis; they are the SAT witnesses.
  `MemmoveUptoSat(Amd64).memmoveUptoWithZero(64)_satisfiable`: both premises of `withZero` hold of one stub.
- Tactics `janus_live_memmove_zero` / `janus64_live_memmove_zero` prove the contract for a stub that returns without a
  memory access when `n = 0` (e.g. `LiveStub.memmoveUptoSeg`).
- Both contracts are on the auditor's pinned-contract list (`Janus/Tools/Audit.lean`, round 9 SAT row).
- docs/RUNTIME-CONTRACTS.md: "Copies of zero bytes".

## v0.3.0 (2026-11-12)

Instruction-count bounds. **Auditor change** (new accepted statement shapes and one new rule; every existing
rule is unchanged), so the result and framework caches rebuild once.

- `GoABI.ReturnsWithin`, `RunsAtLeast`, `EnsuresWithin`, `RunsAtLeastOnCall` (arm64 `Janus/GoABI.lean`,
  amd64 `Janus/Amd64/GoABI.lean`): at most `n` / at least `m` instructions executed by the model
  (`Program.run` fuel; not CPU cycles; runtime-call stubs are not counted). Kernel-checked lemmas
  (no axiom, `sorry` or `native_decide`): `ReturnsWithin.returns`, `.mono`, `.post_mono`, `Returns.within`,
  `RunsAtLeast.mono`, `RunsAtLeast.le_of_returnsWithin`, `exact_count`, `EnsuresWithin.ensures`,
  `.mono_bound`, `.mono`, `RunsAtLeastOnCall.mono`.
- `janus_run` / `janus64_run` prove `ReturnsWithin n` and `RunsAtLeast m` goals by fuel-counted stepping
  (`ReachesW`, `Going`; a bound one too small or too large is not provable and the tactic says so).
- Auditor: `EnsuresWithin` is an Ensures-family main (same Extracted.program mention, contract, call-site,
  binder and `[RSP]`-word rules; through def-wrapped statements too); `ReturnsWithin`/`RunsAtLeast` are run
  claims; the tied witness of an `EnsuresWithin` main may use `Returns` or `ReturnsWithin`; a
  `RunsAtLeastOnCall` witness must also contain a returning run from the same state; the instruction bound
  may not mention the execution of the program (U-BOUND-PURE).
- Examples: `Max` (arm64, amd64) gets `within` (N = 4) and `atLeast` (M = 3) with witnesses; `JanusTests.Within`;
  red-team round `test/redteam/rounds/roundwithin`.
- `lakefile.toml` version 0.3.0 (it still said 0.1.0).
- Includes everything in v0.2.1 below (PR #1: module-system consumer dependencies, olean store v2,
  and the `import all` parser fix).
- Disclosed (pre-existing since v0.1.0, fixed in v0.3.1): the live allocation contracts (makeslice, newobject,
  mallocgc with a type, growslice; both ISAs) do not keep the type descriptor outside the callee's stack
  window, so the pinned runtime does not meet them for a descriptor in the slots `makeslice` pushes before
  reading it. See docs/RUNTIME-CONTRACTS.md ("Known gap").
- Known limitations: `janus verify --asl` transfers `Ensures` theorems only; an `EnsuresWithin` theorem is
  rejected there ("not `Janus.GoABI.Ensures`"); derive the plain `Ensures` with `EnsuresWithin.ensures` and
  transfer that. `janus_run` proves numeral bounds only (no state-dependent budget from a loop invariant), and
  has no `calls`/`join` in bound goals. A def-wrapped `EnsuresWithin` statement is rejected like a def-wrapped
  `Ensures` (the statement must mention `Extracted.program`).

## v0.2.1 (2026-11-12, maintenance release, tagged separately on branch release/v0.2.1)

Bug fix for consumer packages whose dependencies use Lean's module system (`module` header,
`public import`), such as ethereum/EthLib. Before, `janus verify --proof-root` failed at
"Stage: olean provenance" for them; it never produced a wrong verdict.

- janus's own compile of the consumer closure keeps every module-data part `lean -o` writes
  (`.olean`, `.olean.server`, `.olean.private`, `.ir`), not only the `.olean`.
- The trusted olean store records and authenticates each part (entry format v2; v0.2.0 entries are
  rebuilt once). A module's identity covers all its parts; olean-only modules keep their keys.
- The import-header parser accepts the module system's modifiers before `import`
  (`public import`, `public meta import`, `private import`) and `all` after it.
- `import all` is always read as the modifier, as Lean 4.34.1 reads it: the module name follows,
  across newlines and comments, and `import all` without a module is refused. Found by red-teaming
  this release: an intermediate version of the parser read `import all` followed by a newline as an
  import of a module named `all`, which would have left the real import out of a module's key. The
  incremental item keys' header parser (`incr.go`) is fixed the same way, and no longer treats
  `runtime` as a modifier.

## v0.2.0 (2026-11-10)

Repository restructure and an arm64 host-build fix. **No Lean API, auditor rule, gate, red-team
expectation or safety check changed.** Lean module names (`Janus.*`, `JanusTests.*`, `Oracle.*`) are
unchanged; consumers need no source edits. See `docs/MIGRATION.md` ("v0.1 to v0.2") and
`Structure/README.md`.

- New layout: `models/{asl,x86}` (was `JanusASL/`, `JanusX86/`), `validation/` (was `oracle*/` and
  `Oracle/`, organised as `hardware-comparison/`, `reference-models/`, `model-runner/`),
  `test/lean` (was `JanusTests*`), `test/redteam` (was `audit/`, rounds under `rounds/`),
  `scripts/{gate,build,verify,validation,dev,archive}`, `docs/{design,audit,validation,dev-notes,assets}`.
  History is preserved (`git mv`). One-shot generators (`jx1_*`, `jx2_*`, `break-demo.sh`,
  `incr-sample.py`) moved to `scripts/archive/`.
- `Janus.lean`, `Janus/`, `framework.go`, `identity_sentinel.*`, `go.mod`, `go.sum`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` stay at the root (Lake modules and `go:embed`).
- `janus` now builds for linux/arm64 hosts: `blockers_amd64.go` / `sweep_amd64_test.go` lost their
  `_amd64` file-name suffix (now `blockers_x86.go`, `sweep_x86_test.go`).
- The verifier identity changes (embedded sources moved), so result and framework caches rebuild once.
- The validation Go modules are renamed to their directories
  (`github.com/Giulio2002/Janus/validation/hardware-comparison/{arm64,amd64}`).
- Added `Structure/README.md` (repository map) and this changelog. Removed the stray `.x1` / `.x2`.

## v0.1.0

First tagged release (tag `v0.1.0`, commit `77054be0`): Lean framework and `janus` CLI for formally
verifying compiled Go machine code (arm64, amd64).

- Mandatory non-vacuity witnesses: a returning run from a state satisfying the precondition, a
  call-site state for every runtime-contract hypothesis, strict by-name pairing, anchoring for
  Panics/Faults/Traps conclusions; narrow, labelled exemptions for refutations and run-free statements.
- Hermetic proof sandbox: allowlist root, environment allowlist, hidden cache keys, fds above 2 closed.
- `verify-batch` with witness companions and stale-report withdrawal; speed batch 14; provenance fix.
- ~840 pinned red-team expectations; trust model in `docs/SOUNDNESS.md`.
- Known limitations: a witness shows some run returns, not that every contract call site is reachable
  on it (KA1); main theorems with class-typed binders cannot be witnessed; red-team controls N45/N53
  are rejected conservatively; accepted sandbox nondeterminism: clock, random bytes, uid, host
  `/proc/{cpuinfo,meminfo,loadavg}`.
- Not shipped: linux/arm64 host binaries (fixed in v0.2.0).
