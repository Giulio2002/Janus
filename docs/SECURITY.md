# Trusted base, meaning of Verified, and security posture

Moved out of the top-level README. See also [SOUNDNESS.md](SOUNDNESS.md).

## Trusted computing base

| Trusted | Why it is trusted, and how it is checked |
|---|---|
| Lean ISA models: `Janus/Arm64/{Decode,Exec,State}.lean`, `Janus/Amd64/{Decode,Exec,State}.lean` | Meant to match the ARM ARM / Intel SDM on the supported subset. Differentially tested (above), not proved. |
| ELF byte copy: `cmd/janus` `binary.go`, `extract.go`, `identity.go`, `amd64.go` | Finds the symbol and copies its bytes. `janus verify` re-runs the copy against the SHA-256-checked binary and byte-compares `Extracted.lean`. |
| Stub classification | `runtime.panic*`, `runtime.goPanic*`, `runtime.gopanic` are panic stubs; `runtime.morestack*` is stack growth. Affects only theorems that mention those outcomes. |
| Lean kernel, `leanchecker`, and the verifier | Hashing, process execution, the sandbox, and the `janus-audit` routine (axiom allow-list, statement rules and printing). |

**Not trusted:** the Go compiler and linker; any reasoning about the Go source; the extractor's
reachability and data-reference analysis; every tactic (`janus_run` and friends only build proof
terms that the kernel re-checks); and your proof file.

## What a Verified theorem does and does not mean

A `Verified:` line means the printed statement, with its hypotheses and quantifiers, holds for the
extracted bytes under the Lean model. The kernel checks the proof, **not whether the statement says
what you meant**: read the statement.

| It does mean | It does not mean |
|---|---|
| The exact bytes in *this* binary (SHA-256) satisfy the statement | Anything about another build, compiler version, flag set or linker layout |
| `Ensures`/`Returns`: the code terminates and returns to the caller; no fault, no panic on the way | Anything for callers outside the precondition. An unsatisfiable precondition makes the theorem vacuous |
| Every memory access stays inside the regions the precondition grants | That an access outside them would trap on hardware (it may hit another mapping) |
| `NeverPanics`: no panic stub **and** no fault (a nil dereference is a fault, as on hardware it is a `SIGSEGV` that Go turns into a panic) | Anything about timing, side channels, caches or speculation |
| Callee-saved state (`SP`, `g`, frame pointer, …) is restored per Go ABIInternal | Concurrency: the model is single-threaded, with no signals, preemption, GC or scheduler |
| | Vector floating point, half precision, and SIMD arithmetic outside the modelled subset (on arm64 the Advanced SIMD integer and move instructions, see [docs/SOUNDNESS.md](SOUNDNESS.md#advanced-simd); scalar floating point is modelled, see [docs/SOUNDNESS.md](SOUNDNESS.md#floating-point)): these fault as `undecodable` |

The full list is in [docs/SOUNDNESS.md](SOUNDNESS.md) (and [docs/AMD64.md](AMD64.md) for the
x86-64 differences).

## Security posture: the proof is untrusted code

A Lean proof file is a program: `#eval`, `initialize`, macros and tactics all run while it compiles.
Janus assumes the proof is **hostile** and still guarantees that `Verified` means the printed
statement holds. `janus verify`:

* runs **every Lean process that loads the proof in a sandbox** (bubblewrap, else an `unshare`
  namespace): no network, read-only filesystem except one private build directory, private `/tmp`.
  Without a sandbox it refuses unless you pass `--unsafe-no-sandbox`, and the mode is recorded in
  `verified.json`;
* audits the theorem with the **trusted `janus-audit` routine** ([`Janus/Tools/Audit.lean`](../Janus/Tools/Audit.lean)),
  which loads the compiled proof as data and never runs its initializers, so a proof cannot forge
  the audit record;
* checks the imported `Extracted` is **kernel-defeq to an independently compiled trusted copy**, so a
  planted or shadowing module is rejected;
* **prints the statement in a clean environment** that imports only `Janus` and `Extracted`, so the
  proof's notations, unexpanders and instances cannot make it read differently;
* allows only the axioms `propext`, `Quot.sound`, `Classical.choice` (so no `sorry`, `native_decide`
  or `bv_decide`), and replays with `leanchecker` every module of the theorem's import closure
  outside Lean core (every `Janus.*` module, `Extracted`, consumer and dependency modules), caching
  passing replays by content hash;
* pins the SHA-256 of every compiled framework `.olean` after the trusted build and re-checks it
  after every untrusted step, the audit and the replay (in a consumer workspace the framework build
  is also read-only to the sandboxed Lake build), and hashes every other compiled `.olean` once it is
  final.

These defences answer an internal red-team audit, [docs/audit/AUDIT.md](audit/AUDIT.md), which records the
attacks as found (a forged audit via `initialize`, IO from `#eval`, a shadowed `Extracted`, misleading
unexpanders, and others) together with the fixes. Each attack has a regression test in
[`cmd/janus/hardening_test.go`](../cmd/janus/hardening_test.go), and `test/redteam/run-all.sh` replays them all.
For example, the audit's file-writing attack now dies inside the sandbox:

```text
Invalid: Lean rejected the proof test/redteam/attacks/A6_eval_io.lean.
Lean errors (2):
  test/redteam/attacks/A6_eval_io.lean:7:0: error: read-only file system (error code: 30)
      file: /srv/janus/test/redteam/work/A6-written-during-verify.txt
```

<!-- TODO(coordinator): docs/audit/AUDIT.md's summary table still shows the original "BROKEN" status of
each finding (the snapshot before the fixes). The fixes F1–F6 are present in the code (sandbox.go,
Janus/Tools/Audit.lean, GoABI.NeverPanics/RetAddr, the 2^48 bound in Memory.accessible, PIE
rejection in binary.go), but the audit doc should get a "Status after fixes" column before release. -->

