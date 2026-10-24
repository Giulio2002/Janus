# Testing Janus: what runs, where the time and memory go

This page describes the test suites of Janus itself, how long they take, how much memory they
use, and the changes that made them faster and bounded in memory **without weakening any
check**: every proof is still compiled and kernel-checked, every sandbox, pin, audit, round-trip,
instance check and kernel replay still runs with the same strength.

## The suites

| Suite | Command | What it checks |
|---|---|---|
| arm64 examples | `scripts/verify-examples.sh [-j N] [Name …]` | the 20 arm64 example proofs and the WrongAdd demo, through `janus verify` |
| amd64 examples | `scripts/verify-amd64-examples.sh [-j N]` | the 25 amd64 theorems |
| all examples | `scripts/verify-all-examples.sh [-j N]` | both of the above in one pool, longest first |
| soundness audit | `audit/run-all.sh [-j N]`, `audit/round{2,3,4,5,7}/run-round*.sh [-j N]`, `audit/round6/run-round6.sh` | every documented attack is rejected, every control verifies (round 7: the result cache) |
| Go tests | `go test -timeout 50m ./cmd/...` (`-short`: no Lake builds) | the CLI, the extractor, the verifier end to end |
| JanusASL | `scripts/asl.sh prove` | the Arm-ASL equivalence theorems (39) and their axiom audit |
| ASL build cache | `JanusASL/tools/test_asl_cache.sh [--e2e CACHE]` | the `ASL_CACHE` key ignores lakefile edits that cannot reach the ArmASL build and changes on every input that can (31 cases, seconds); with `--e2e`, a restore into a copy with an edited JanusASL lakefile leaves `lake build ArmASL` nothing to do (docs/ASL.md "Build cache") |

`-j N` runs up to `N` independent rows/proofs at once (`scripts/lib/parallel.sh`); output is
printed in the original order, and a failure in any block fails the run. The default is
**bounded by memory, not cores**: `min(cores/4, (MemAvailable − 40 GiB)/20 GiB, 2)`, at least 1,
and before each block starts `MemAvailable` is checked again (a block waits for a running one
while less than 20 GiB is free above the 40 GiB headroom). `JANUS_JOBS` or `-j` override it;
`-j 1` is the plain serial run. When `scripts/lib/memguard.sh` is loaded, every block runs under
a cgroup memory limit of `$JANUS_JOB_MEM` (default 20G) that janus' own per-process limits nest
in (see "Memory guard" below). `go test` uses the same formula as its `-parallel` default.

Tools for measuring:

* `JANUS_TIMINGS=1 janus verify …` prints the duration of every verification stage on stderr.
* `scripts/peak-mem.sh CMD …` runs `CMD` in a transient cgroup and reports its peak memory
  (cgroup `memory.peak`, the peak sum of the resident sets of all its processes, and the largest
  single process).

## Where the time went (profile, before)

Measured on the 48-core, 251 GB development host while other agents were running (load average
30–90); absolute numbers move with the load, the ratios do not.

### One `janus verify` (Add, warm cache): 16.5–19.3 s, of which the audit was 13.5–15.8 s

| Stage | before | after |
|---|---:|---:|
| extraction check | 0.005 s | 0.005 s |
| sandbox self-test | 0.01 s | 0.01 s |
| framework build check (`lake build` no-op, then a ready stamp) | 0.15 s | 0.07–0.21 s |
| toolchain lookup (two `lake env lean` calls) | 0.17 s | 0.09 s (concurrent) |
| framework pins (hash ~70 MB of oleans; done 6 times) | 0.07 s each | 0.013 s each (parallel hashing) |
| compile Extracted + JanusTrusted | 0.7 + 0.7 s (sequential) | 0.67 s (concurrent), 0 s on a trusted-cache hit |
| proof compile (sandboxed) | 0.9 s | 0.9 s |
| **audit** | **13.5–15.8 s** | **1.35 s** |
| kernel replay of Extracted/JanusTrusted/Proof (when not cached) | 2.6 s after the audit | ~0.8 s, concurrent with the audit |
| total, warm | 16.5–19.3 s | 2.7–3.0 s |
| total, new extraction (replay not cached) | 18.8 s | 3.7–4.4 s |

Why the audit took 14 s: it ran as `#eval JanusAudit.run …` in a Lean file whose header already
imported `Janus` and `Lean`. Two things were slow:

1. **A quadratic loop.** `EnvironmentHeader.moduleNames` is not a field but a function that
   rebuilds the array of all ~2400 module names; the shadowing check called it once per
   constant of the audited environment (~300k). `perf` put about half of the audit's time there.
2. **Re-reading mapped files.** An `.olean` is mapped at a fixed address; when a process has
   already mapped it (the file header imported `Janus` and `Lean`), a second `importModules` of
   the same module copies and relocates the whole file instead (~2.3 s, 2 GB per import). The
   audit imported the audited environment and then the clean environment, each re-reading every
   core and framework module.

Kernel replay: `leanchecker A B C` imports a separate environment for every target inside one
process, so after the first every import takes the copy-and-relocate path: three small modules
took 2.1 s together but 0.75 s each in separate processes. The cold replay of the framework is a
single target (`Janus` is a name prefix of every framework module), for which leanchecker started
one task per module, all at once.

### Slow proofs

| Proof | before | after | why |
|---|---:|---:|---|
| ClearWords (17 theorems) | 428–454 s | 206–217 s | its theorems were elaborated **one after the other**, see below |
| A64IndexByte | 56.6 s | 10.8 s | one `omega` took 45 s matching 16 atoms against a differently associated sum |
| AddLimbs, CopyBlock | 13–15 s | (unchanged) | they were 30–60 s only under load |

ClearWords: Lean elaborates the proofs of a file's theorems in parallel, but two things in the
executor made each theorem wait for every theorem before it:

* the executor evaluates closed terms (addresses like `retPC`, the `until` stops, `janus_eval_nat`)
  with the compiled evaluator (`evalExpr`); a term that mentions a definition **of the proof file**
  must be compiled against the compiled environment of the whole file so far, which waits for all
  earlier declarations to be checked. Now these terms are delta-unfolded to imported constants
  first (`Common.unfoldLocalDefs`, definitional), so the evaluation uses the imported environment
  and does not wait; if the unfolded term cannot be compiled, the original is evaluated as before;
* closed side conditions were closed with `decide +kernel`, whose auxiliary lemma is added with
  `Elab.async` off, i.e. after the kernel checks of all earlier declarations. They now try plain
  `decide` first (the proof term `of_decide_eq_true rfl` is the same; the kernel checks it with
  the theorem) and fall back to `decide +kernel` (`Common.decideClosed`).

A64IndexByte: a lemma `maskSum_eight` states `maskSum f 8` written out the way the quick test's
hypothesis has it, and two `omega` calls became rewrites. No existing statement changed (every
declaration header of every example proof is byte-identical to `main`).

### Go tests (before: 34.8 min on the loaded host; 19–22 min quiet)

The slowest tests were TestVerify (492 s), TestInlineInstanceRejected (264 s), TestConsumerVerify
(197 s), TestHardeningAttacks (162 s), TestBoundInstanceRejected (157 s), TestSandboxRecorded
(139 s, unsandboxed: no replay cache, so a full framework replay), TestVerifyBatch (139 s). Every
one of them is a sequence of `janus verify` runs, so the per-verify speed-ups apply to all; in
addition the independent tests and the subtests of TestVerify/TestHardeningAttacks (each on its
own extraction) are marked parallel, and `-short` now keeps the fast real-Lean tests (honest
proofs, axiom/kernel/statement rejections, hardening attacks) and skips only the Lake-building
ones (consumer packages, dependencies, Mathlib, install, concurrency, framework copies).

## Where the memory went (before / after)

Peak memory is measured with `scripts/peak-mem.sh`: cgroup = `memory.peak` of the whole process
tree (anonymous memory plus the page cache it brings in), RSS-sum = peak sum of the resident
sets of its processes (shared mapped pages counted once per process), and the largest single
process.

Before, a cold or unsandboxed verify peaked at 36–37 GB in one leanchecker process (the replay of
the framework: one task per module, each importing that module's whole environment, all at
once), and the warm audit held 5.7 GB (two re-read copies of the core library). Now leanchecker
runs with `LEAN_NUM_THREADS=2` (`JANUS_REPLAY_THREADS`): the same modules are replayed, two at a
time (framework replay on a quiet host: 1 thread 19 s / 1.5 GB, 2 threads 15 s / 5.1 GB,
4 threads 11 s / 7.4 GB; a thread per core 30–37 GB). The compiled auditor maps each module once
(1.7 GB). At most two replay targets run at once in one verify (plus the three small per-proof
modules while the audit runs), and concurrent verifications replaying the same bytes take a
lock, so they replay them once.

### Per verify, final numbers

| Verify | before: time, peak cgroup / RSS-sum | after: time, peak cgroup / RSS-sum |
|---|---|---|
| Add, cold cache (framework built and replayed) | 55.0 s, 36.1 / 36.0 GB | 41.9 s, 3.0 / 8.2 GB (24 s of it build the framework) |
| Add, unchanged re-verify | 17.1 s, 4.2 / 5.7 GB | **0.5 s** (result-cache hit), 0.1 / 0.1 GB |
| Add, warm, result cache off | 17.1 s, 4.2 / 5.7 GB | 3.0 s, 0.3 / 1.8 GB |
| Max, new extraction | 20.5 s, 4.2 / 5.7 GB | 4.0 s, 0.6 / 5.3 GB |
| Add, `--unsafe-no-sandbox` | 30.3 s, 37.3 / 37.3 GB | 15.2 s, 3.4 / 6.0 GB |
| A64IndexByte, warm | 30.7 s, 4.2 / 5.7 GB | 15.0 s, 0.6 / 5.7 GB |
| ClearWords, warm | 427.9 s, 4.3 / 5.8 GB | 207.0 s, 5.0 / 5.8 GB |

Stages of one verification (`JANUS_TIMINGS=1`, after):

| Stage | cold (first run of a framework version) | warm (proof edited) | unchanged (cache hit) |
|---|---:|---:|---:|
| extraction check, sandbox self-test | 0.02 s | 0.02 s | 0.02 s |
| framework build check | 24.1 s (the build) | 0.21 s | 0.21 s |
| toolchain lookup, framework pins | 0.13 s | 0.10 s | 0.10 s |
| result-cache lookup | 0.01 s (miss) | 0.01 s (miss) | 0.01 s (hit, done) |
| trusted compile | 0.73 s | 0 s (trusted cache) or 0.7 s | |
| proof compile | 0.9 s + the proof | 0.9 s + the proof | |
| audit | 1.4 s | 1.35 s | |
| kernel replay (overlapped) | 11.7 s waited for the framework replay | ~0.1 s waited | |
| **total for Add** | **39 s** | **2.7–3.0 s** | **0.34 s** |

So the per-verify overhead is ~2 s on top of the proof's own elaboration (warm), ~0.35 s for an
unchanged re-verify, and ~15 s (the framework's kernel replay, which overlaps the other stages)
plus the framework build itself for the first verification of a framework version. The build
(`lake build` of the 48 framework modules and the auditor, ~24 s on this host) happens once
per framework version and cannot overlap anything, because every later stage needs it.

### Per suite (fresh cache each; before = main, serial; after = the default -j, 2 here)

Measured with `scripts/peak-mem.sh` around the whole suite. The host was shared with other agents
(load average 10–40), so the times are indicative; the memory numbers are not affected.

| Suite | before: time, peak cgroup / RSS-sum | after: time, peak cgroup / RSS-sum |
|---|---|---|
| `scripts/verify-examples.sh` | 1295 s, 29.8 / 29.7 GB | 321 s, 6.2 / 14.3 GB |
| `scripts/verify-amd64-examples.sh` | 1113 s, 29.3 / 29.6 GB | 312 s, 5.9 / 10.8 GB |
| `scripts/verify-all-examples.sh` (both, one pool), cold | 2408 s (the two above, in sequence) | 357 s, 8.5 / 16.1 GB |
| the same, warm, result cache off | | **282 s**, 5.2 / 7.6 GB |
| the same, nothing changed | | **12 s**, 0.3 / 1.8 GB |
| `audit/run-all.sh` | 602 s, 43.2 / 42.7 GB | 190 s, 7.5 / 11.3 GB |
| `audit/round2…6`, `round7` (new) | (serial; minutes each) | 92, 31, 31, 209, 158, 64 s; peak ≤ 7.6 / 14.8 GB |
| `go test -timeout 50m ./cmd/...` | 1251 s (34.8 min under heavier load), 43.4 / 42.0 GB | **360 s**, 14.3 / 19.4 GB |

**Maximum total for a whole suite at the default -j: 14.3 GB** (cgroup peak of `go test`; 19.4 GB
summed RSS, which counts shared mapped pages once per process). Before: 43.4 GB, from a single
leanchecker process. No suite now has a process above 5.7 GB.

`go test` also keeps every assertion: the parallelism comes from marking independent tests and
subtests parallel (each on its own extraction), not from removing checks; the one assertion that
encoded the old replay batching (TestReplayPlanKeys: one leanchecker call for three targets) now
asserts one call per target. `go test -short` runs the fast real-Lean tests (TestVerify,
TestHardening*, TestSandboxRecorded, the round 2/5 instance tests, TestResultCache) and skips only
those that build consumer packages or dependencies with Lake, install janus, copy a framework or
run the concurrency tests.

### A verification daemon (`janus serve`): evaluated, not built

A long-lived trusted process could keep the framework environment and the auditor loaded. What
it could save per warm verify, from the stage table: the framework build check (0.21 s, which it
would still have to re-establish, since the build can change between requests), the toolchain
lookup (0.09 s) and the auditor's process start and imports (~0.4 s of its 1.35 s). The proof
compile (0.9 s plus the proof) must stay a fresh sandboxed process, and the kernel replay of the
proof's modules must read the new oleans either way. So at most ~0.7 s of ~3 s, while it would add
a long-lived trusted component holding state across verifications (a stale framework, a reused
environment) that every request would have to re-validate, and whose own threat model would
include every client. The result cache gives an unchanged re-verify in 0.34 s without a resident
process. Not worth it.

## What changed, and why every check is as strong as before

* **Compiled auditor (`janus-audit`).** `lean_exe janus-audit` (root `Janus.Tools.AuditMain`)
  runs exactly `JanusAudit.runImpl`, the function the `Audit.lean` script calls through
  `JanusAudit.run`, with the same arguments; the record was compared byte for byte. It is part of
  every framework build, its SHA-256 is in the build's ready stamp (a changed executable makes the
  build "not ready", and it is relinked), and it is hashed again right before it runs (nothing
  untrusted runs between that check and its start). It runs sandboxed with the verification's
  `LEAN_PATH`. `Janus.Tools.Audit` now imports only `Lean` (the auditor reads `Janus` and
  `Extracted` as data), so the executable links no framework code. The consumer path uses it too
  (except with `--fresh`, whose temporary base is gone by audit time: then the script runs).
* **Auditor reads each module once** (the clean environment's module data is read first and the
  audited environment's state grown from it). This is a fresh import of the audited modules when
  the imported `Extracted` imports `Janus`, which is checked on the result; otherwise the audited
  environment is imported separately. Same constants, same order.
* **Trusted-compile cache.** The compiled `Extracted`/`JanusTrusted` are reused from
  `<cache>/v1/trusted/<key>` when the toolchain, the framework build's pins and both sources are
  byte-identical; the files are re-hashed against the entry's manifest and pinned as before. Like
  the replay cache it lives where sandboxed processes cannot write, and it is used only with a
  sandbox and without `--fresh`.
* **Replay alongside the other stages.** `Extracted`, `JanusTrusted` and `Proof` are replayed
  (one leanchecker each) as soon as `Proof.olean` is pinned, while the audit runs, and the
  framework (when its replay is not cached) as soon as the framework build is pinned. The result counts
  only for modules that the audited closure then contains, under the same cache keys; the pins
  are re-checked after it as before; a failure is not reported early: the regular replay runs
  those modules again and reports it after the audit, as before.
* **One leanchecker process per replay target**, at most two at once, two threads each, with a
  lock per target. leanchecker's targets are name prefixes, so a target replays exactly what it
  did when several targets shared a process.
* **Parallel pin hashing**, concurrent toolchain queries, concurrent trusted compiles.
* **Result cache** (docs/SOUNDNESS.md "Verification-result cache", audit round 7): an unchanged
  re-verify prints the recorded report (plus `Cached:`) in ~0.35 s.
* **Tactics**: `Common.unfoldLocalDefs` before compiled evaluation, `Common.decideClosed` for
  closed side conditions (see ClearWords above). Neither changes a proof term the kernel checks
  except that a closed side condition may now be checked inside the theorem instead of in an
  auxiliary lemma.

## JanusASL

The generated model (`ArmASL`, 24 modules that import each other in a chain) takes about 42 min
of the ~54 min cold build. The declarations are in dependency order (Sail emits them that way)
and the large ones depend on nearly everything before them, so splitting the chain differently
at the same cut points would gain about 5% (critical path 2384 s of 2520 s). The large
modules are dominated by code generation, not elaboration: one declaration,
`AArch64_AutoGen_ArchitectureReset`, spends 820 s in the compiler (630 s in its LCNF `simp`
pass).

`scripts/asl.sh` therefore gets a **shared build cache** (`ASL_CACHE=<dir>`): the ArmASL build
and the lean-sail package are copied from `<dir>/<key>` before building and stored there after a
build (key: SHA-256 of the vendored tarball, the toolchain, the lean-sail manifest entry, the
splitter and the lakefile settings that reach ArmASL's modules; docs/ASL.md "Build cache"). Entries carry a SHA-256 manifest that is checked after every copy and are
published atomically under a lock; `ASL_CACHE_READONLY=1` only reads. With an entry,
`scripts/asl.sh prove` takes 3 min 56 s (Lake replays the copied modules; only the proofs
build) instead of ~54 min; "audited 39 theorems: only propext, Classical.choice, Quot.sound".
The cache must be writable only by trusted users: its oleans are what the JanusASL proofs are
checked against.

## CI

* The example jobs verify against the checkout's Janus build (`JANUS_ROOT`) instead of building
  the embedded copy of the same sources a second time in `~/.cache/janus`; the embedded path is
  covered by `go test` (TestEmbeddedFramework, TestInstallOutsideRepo).
* On a 4-core, 16 GB runner the memory-bounded defaults give 1 job, so CI runs serially; the
  speed-up comes from the per-verify changes (a verify is about 5x faster).

CI estimate (GitHub-hosted 4-core, 16 GB runner; not measured there, scaled from the local
ratios above, which are dominated by per-verify work that is the same on any machine):

| Job | before | after (estimate) |
|---|---|---|
| go-test (Lean build, vet, `go test`) | ~30–40 min (45 min timeout) | ~10–15 min |
| arm64 (examples, decoder coverage, qemu oracle, `audit/run-all.sh`) | ~35–45 min | ~12–18 min |
| amd64 (examples, native oracle) | ~25–35 min | ~10–15 min |
| ASL equivalence (cache miss / hit) | ~60 min / ~10 min | unchanged on GitHub (its .lake cache already reuses ArmASL); locally `ASL_CACHE` gives ~4 min |

The per-runner peak memory drops from ~30–43 GB (more than a hosted runner has, which made the
cold replay swap or be killed) to under 15 GB.

## Memory guard

Lean jobs are memory-hungry and occasionally runaway: a kernel replay of the framework holds
several environments at once, a proof can elaborate a huge term, a lake build compiles many
modules in parallel. On a shared host an unbounded job ends in the *global* OOM killer, which
picks whatever is largest on the machine (or takes the machine down). So every Lean-family job
janus or a script starts runs inside a **cgroup v2 memory limit** (`memory.max`, `memory.swap.max
= 0`): a runaway job is killed on its own by the cgroup's OOM killer, and the diagnostic says so.

### janus

`cmd/janus/memguard.go`. Every process janus starts that runs Lean (lean, leanchecker, lake,
`janus-audit`, `janus-decode`) goes through `guardRun`, which enters the limit *before* the
sandbox starts, so the cgroup contains the whole bwrap/unshare tree.

| mechanism | when | how | peak |
|---|---|---|---|
| `cgroup` | `$JANUS_MEMGUARD_CGROUP` is a delegated cgroup (set by `scripts/lib/memguard.sh`), or janus's own cgroup is delegated | a child cgroup per job (`memory.max`, `memory.swap.max=0`, `memory.oom.group=1`), entered with clone3 `CLONE_INTO_CGROUP` | the child's `memory.peak` |
| `systemd-user` | a user systemd manager is reachable | `systemd-run --user --scope --collect -p MemoryMax=… -p MemorySwapMax=0 -p OOMPolicy=continue`; janus re-runs itself in the scope as a supervisor that starts the job, waits, and writes the scope's `memory.peak` and OOM-kill count for its parent | the scope's `memory.peak` |
| `systemd-system` | root, no user manager | the same with the system manager | same |
| `prlimit` | no cgroup mechanism | `prlimit --as=limit+16G` per process | max RSS (`wait4`) |
| `none` | nothing works | unguarded, with a warning | — |

Each mechanism is probed once per process: the cgroup one by starting a process in a limited
child, the systemd ones by running the supervisor's probe in a transient scope and checking
that it sees `memory.max` equal to the limit. `JANUS_MEMGUARD=<mechanism>` forces one.

`prlimit` is a last resort. Lean reserves about 10 GiB of address space before it allocates
anything (measured: `VmPeak` 10.1 GiB for a 3-line file, with 4 threads or 48), and a virtual-memory
limit below ~11 GiB makes it fail with `failed to create thread`. So the virtual limit is the
memory limit plus 16 GiB, per process. janus recognises Lean's out-of-memory messages under it.

**Limit.** `JANUS_MEM_MAX` (`16G`, `1500M`, `off`); default min(24 GiB, 40% of MemTotal), which is
24 GiB on the 251 GiB development host and 6.4 GiB on a 16 GiB CI runner. CI sets 12G: one job
runs at a time there, and the ArmASL build (10.7 GiB with 8 lake jobs) and the ClearWords proof
(4.8 GiB) need more than 6.4 GiB. `lake build` (the framework,
`janus-decode`, consumer packages) gets `LEAN_NUM_THREADS` = limit / `JANUS_LAKE_JOB_MEM` (3G),
at most the CPU count. That is lake's job count: measured with 8 independent slow modules,
`LEAN_NUM_THREADS=2` ran 2 lean processes at once and `=6` ran 6.

**Diagnostic.** A job killed for memory (or one the guard could not start) turns the whole
verification into

```
Invalid: lean Proof.lean Proof.olean exceeded the memory limit and was killed (limit 1.0 GiB, measured peak 1.0 GiB, mechanism systemd-user). This is not a verdict on the proof.
  Stage: resource limit
  Next: Raise the per-job limit with JANUS_MEM_MAX (e.g. JANUS_MEM_MAX=32G; default min(24G, 40% of RAM)) if the host has the memory, or make the proof (or what it imports) need less memory.
Details:
The killed job interrupted the stage: proof checking
```

whatever error the killed process caused, and no `verified.json` is written. This holds for
`janus verify`, batches (per request group) and the other commands. A success records the
guard in `verified.json`:

```json
"memoryGuard": {"mechanism": "cgroup", "limit": "24.0 GiB", "limitBytes": 25769803776,
                "source": "default", "peakBytes": 7000084480, "peak": "6.5 GiB", "jobs": 11}
```

`janus memguard` prints the mechanism (and why stronger ones were skipped). `janus memguard --
CMD…` runs any command under it. A verification prints `janus: memory guard: …` on stderr only
when there is no mechanism (a warning) or with `JANUS_MEMGUARD_VERBOSE=1`, because stderr starts
with the verdict. `JANUS_MEMGUARD_LOG=1` also prints each job's label and peak.

### Scripts

`scripts/lib/memguard.sh`, sourced by verify-examples, verify-amd64-examples, the build
scripts, the oracle scripts, asl.sh, bench.sh, break-demo.sh, audit/run-all.sh and every
audit round runner.

* `memguard_self "$@"` (right after sourcing) re-runs the script once under a script-wide
  guard of max(limit, MemAvailable − 40 GiB), `JANUS_SCRIPT_MEM_MAX` to override. Everything the
  script starts is bounded, and the host keeps 40 GiB.
* `memguard_run [-l LIMIT] [-n LABEL] -- CMD…` runs one command under a limit. It prints
  `memguard[LABEL]: peak X / limit Y (mechanism)`, with `OOM-KILLED` added when its own limit
  killed something, and returns 137 then.
* `memguard_lake ARGS…` is `lake ARGS…` with `LEAN_NUM_THREADS` from the budget
  (`memguard_jobs 3G`). Every `lake build` in the scripts (the framework, the oracles, ArmASL,
  JanusASL) uses it, and the go test rows use `memguard_run`.
* `bash scripts/lib/memguard.sh run|lake|mechanism …` is the same from outside a script (used by
  CI).

**Nesting.** The outer guard is a systemd scope with `Delegate=yes`. Its command runs in a leaf
`leader` cgroup, +memory is enabled on the scope, and `JANUS_MEMGUARD_CGROUP` names the guard.
An inner `memguard_run`, and janus itself, then create limited children of that cgroup instead
of new systemd scopes, which would be siblings outside the outer limit. So the layers are:

```
script guard  (max(24G, MemAvailable − 40G))          memguard_self
└─ parallel slot  (JANUS_JOB_MEM, 20G)               scripts/lib/parallel.sh par_run → memguard_run
   └─ janus job  (JANUS_MEM_MAX, 24G → effective 20G) cmd/janus guardRun, one per lean/leanchecker/lake
```

The effective limit of a job is the smallest `memory.max` on its path, and that is the one
janus reports. A kill caused by an inner limit is reported by the inner guard, through janus's
diagnostic. The outer guards see it only in their hierarchical `memory.events`, print "a nested
guard killed one of its jobs", and return the command's own status. parallel.sh admits a new
slot only while MemAvailable ≥ 40 GiB headroom + 20 GiB, so slots × slot limit stays within
MemAvailable.

Without a user systemd manager (or root) and without a delegated cgroup, both sides fall back to
prlimit, then to none. `janus memguard` and the scripts' first `memguard: …` line name the
mechanism, and janus warns on every verification when there is none. Checked as an unprivileged user with no user manager: janus picks `prlimit` and
lists why `cgroup` (mkdir permission denied), `systemd-user` (no bus) and `systemd-system` (needs
root) were skipped.

**CI** (`.github/workflows/ci.yml`, `asl.yml`). Each job enables lingering for the runner user
(`loginctl enable-linger`), which starts its user manager, then exports `XDG_RUNTIME_DIR` and
`JANUS_MEM_MAX=12G`. It logs `memguard mechanism: …` (the scripts' detection) and `janus memguard` (janus's),
and runs a 1G probe. The lake builds and
`go test` run under `scripts/lib/memguard.sh`. If the user manager does not come up, the guard
degrades as above and the log says which mechanism is active.

### Tests

`cmd/janus/memguard_test.go`:

* `TestMemGuardKillsHungryProof`: a proof whose `#eval` builds a list of 10⁸ naturals,
  verified by a separate janus process under `JANUS_MEM_MAX=1G`. It is run directly (the detected
  mechanism, `systemd-user` here) and nested in a 4G `scripts/lib/memguard.sh` job guard (janus
  then uses `cgroup` children of it). Both must print `Invalid:`, `Stage: resource limit`,
  `limit 1.0 GiB` and the measured peak, no proof/audit error, and leave no `verified.json`. In
  the nested case the job guard's summary must not claim the kill. The test skips when there is no
  cgroup mechanism, so the host is never at risk. Each run takes about 2 s; the peak is the
  limit, 1.0 GiB.
* `TestMemGuardNormalVerify`: Add and Max verify under the default limit, and `memoryGuard` in
  `verified.json` records the mechanism, the limit, the job count and a peak below the limit.
* `TestParseMemSize`, `TestDefaultMemLimit`, `TestJobLabel`, `TestMemLimitDiag`,
  `TestMemGuardFailureDiag` (a job the guard could not run is a resource-limit failure),
  `TestMemGuardBadLimit` (an unparsable `JANUS_MEM_MAX` is refused before anything runs).

Manual checks of the shell side (python allocating 1000 MiB): a 300M limit kills it (137, peak
299 MiB). An outer 2G guard with an inner 200M guard: the inner one kills it, and the outer one
reports the nested kill and passes the status through. An outer 300M guard around janus at 2G:
janus reports the effective 300 MiB limit and stays alive to print its diagnostic. No `mg-*` or
`janus-*` cgroups are left behind.

### Measured peaks

`memory.peak` of each guarded job, from `verified.json` (`memoryGuard.peak`, the largest job)
and `JANUS_MEMGUARD_LOG=1`. 48-core host, Lean 4.34.1, LEAN_NUM_THREADS=4 for leanchecker,
2026-10-24. "Warm" means the framework is built and its kernel replay is cached (the usual
case): only the proof's own modules are compiled, audited and replayed. Shared, already-cached
olean pages are charged to the cgroup that first read them, so a warm job's peak is mostly its
own heap.

**Cold** (fresh `JANUS_CACHE_DIR`, Add): 11 jobs. `lake build Janus` (framework, 8 jobs) 1.3 GiB;
the kernel replay `leanchecker Janus` (every framework module) **3.0 GiB** with the default 2
replay threads (6.5 GiB with 4), the verification's peak; every other job ≤ 222 MiB. A cold `lake build Janus Janus.Tools.Audit` alone peaks at
538 MiB with 1 job (62 s) and 1.0 GiB with 8 jobs (23 s), so 3 GiB per lake job is a generous
budget for the framework.

**ArmASL / JanusASL** (`scripts/asl.sh build`, 8 lake jobs from the 24 GiB budget): the cold
ArmASL build (41 jobs, 42.5 min) peaked at **10.7 GiB** for the whole lake tree (its largest
modules, Part17/Part24, take ~9 min each). The JanusASL + janus-asl-check build on top (199 jobs,
16 min) peaked at 7.3 GiB.

**Warm, arm64** (`scripts/verify-examples.sh -j 1`, peak per verification, heaviest job):

| example | peak | heaviest job |
|---|---|---|
| Add | 209 MiB | janus-audit |
| Max | 209 MiB | janus-audit |
| Add128 | 223 MiB | janus-audit |
| Mul64 | 223 MiB | janus-audit |
| Add256 | 313 MiB | lean Proof.lean |
| Div | 222 MiB | janus-audit |
| Get | 235 MiB | lean Proof.lean |
| AddThree | 233 MiB | lean Proof.lean |
| Sum | 222 MiB | janus-audit |
| SetOne256 | 222 MiB | janus-audit |
| HexDigit | 223 MiB | janus-audit |
| AddLimbs | 496 MiB | lean Proof.lean |
| CopyWords | 239 MiB | lean Proof.lean |
| SumSquares | 243 MiB | lean Proof.lean |
| AtomicAdd | 222 MiB | janus-audit |
| AtomicMax | 223 MiB | janus-audit |
| CopyBlock | 462 MiB | lean Proof.lean |
| ClearWords | **4.8 GiB** | lean Proof.lean (213 s) |
| A64Equal64 | 325 MiB | lean Proof.lean |
| A64IndexByte | 503 MiB | lean Proof.lean |
| WrongAdd (break demo) | 223 MiB | |

The whole run (21 verifications, one at a time) peaked at 4.9 GiB in its script guard.

**Warm, amd64** (`scripts/verify-amd64-examples.sh -j 1`, peak per function):

| example | peak | example | peak |
|---|---|---|---|
| Add | 222 MiB | CopyWords | 233 MiB |
| Add128 | 209 MiB | Div | 223 MiB |
| Add256 | 264 MiB | Equal64 | 487 MiB |
| AddLimbs | 323 MiB | Get | 223 MiB |
| AddThree | 239 MiB | GlobalTable | 221 MiB |
| AtomicAdd | 222 MiB | HexDigit | 222 MiB |
| AtomicMax | 223 MiB | Max | 222 MiB |
| Bump | 223 MiB | Mul64 | 222 MiB |
| ClearWords | **2.3 GiB** | SetOne256 | 222 MiB |
| CopyBlock | 366 MiB | Sum | 227 MiB |
| CopyBlock512 | 1.5 GiB | SumSquares | 251 MiB |
| Table | 295 MiB | | |

Every example is far below the 24 GiB default. The largest jobs are the ClearWords proof
(4.8 GiB) and the cold framework replay (3.0 GiB), so the default leaves about 5x headroom. A 20G parallel slot holds a cold
verify with room to spare.
