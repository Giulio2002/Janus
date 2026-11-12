# Changelog

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

## v0.2.1 (maintenance release, tagged separately on branch release/v0.2.1)

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
