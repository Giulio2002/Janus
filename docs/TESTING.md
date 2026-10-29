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
| all examples | `scripts/verify-all-examples.sh [-j N] [--changed]` | the arm64, amd64 and assembly examples in one pool, longest first by measured time (`--changed`: development only, unchanged items skipped) |
| soundness audit | `audit/run-rounds.sh [-j LANES]` (all of them as parallel lanes), or each: `audit/run-all.sh [-j N]`, `audit/round{2,3,4,5,7,8}/run-round*.sh [-j N]`, `audit/round6/run-round6.sh` | every documented attack is rejected, every control verifies (round 7: the result cache) |
| Go tests | `go test -timeout 60m ./cmd/...` (`-short`: no Lake builds) | the CLI, the extractor, the verifier end to end, the cache collector |
| JanusASL | `scripts/asl.sh prove` | the Arm-ASL equivalence theorems (39) and their axiom audit |
| ASL build cache | `JanusASL/tools/test_asl_cache.sh [--e2e CACHE]` | the `ASL_CACHE` key ignores lakefile edits that cannot reach the ArmASL build and changes on every input that can (31 cases, seconds); with `--e2e`, a restore into a copy with an edited JanusASL lakefile leaves `lake build ArmASL` nothing to do (docs/ASL.md "Build cache") |

`-j N` runs up to `N` independent rows/proofs at once (`scripts/lib/parallel.sh`); output is
printed in the original order, and a failure in any block fails the run. The default is
**bounded by memory and cores**: `min(cores/6, (MemAvailable − 40 GiB)/10 GiB, 8)`, at least 1
(8 on the 48-core development host, 1 on a 4-core 16 GiB CI runner), and before each block starts
`MemAvailable` is checked again (a block waits for a running one while less than 10 GiB is free
above the 40 GiB headroom). The 10 GiB per block is twice the largest measured verification
(ClearWords, 4.8 GiB; a cold framework replay 3.0 GiB; "Measured peaks" below). `JANUS_JOBS` or
`-j` override it; `-j 1` is the plain serial run. When `scripts/lib/memguard.sh` is loaded, every
block runs under a cgroup memory limit of `$JANUS_JOB_MEM` (default 10G) that janus' own
per-process limits nest in (see "Memory guard" below). `go test` uses the same formula for its
number of test slots (see "Gate speed" below).

Tools for measuring:

* `JANUS_TIMINGS=1 janus verify …` prints the duration of every verification stage on stderr.
* `scripts/peak-mem.sh CMD …` runs `CMD` in a transient cgroup and reports its peak memory
  (cgroup `memory.peak`, the peak sum of the resident sets of all its processes, and the largest
  single process).

## The gate driver (`scripts/gate.sh`)

One command runs every check of the gate: `scripts/gate.sh [-j N] [--lanes N]` (under `memcap`). It
prebuilds once, then runs every stage as a parallel lane that reads the prebuilt outputs.

**Phase 1, prebuild (once).** `go build bin/janus` (and `audit/bin/janus-rounds`, the audit lanes'
copy), `lake build` plus `lake build Janus Janus.Tools.Audit janus-audit`, the example binaries of every
suite (`scripts/build-examples{,-amd64,-asm,-sys,-rtmisc,-print,-cgo}.sh`, in parallel), and the
framework build and replay verdict (a first verification of the Add example). The later stages run with
`JANUS_EXAMPLES_PREBUILT=1` / `JANUS_GATE_PREBUILT=1` and rebuild nothing.

**Phase 2, lanes.** Queued longest first by their time in the last run (`artifacts/gate/lane-times`;
built-in estimates before the first run), at most `--lanes` at once (default `-j + 1`: the verify pool
and `-j` others):

| lane | what it runs |
|---|---|
| `verify` | `scripts/verify-all-examples.sh --cgo`: ONE queue (`scripts/lib/pool.sh`) of every arm64, amd64, asm, rtmisc, sys, print and cgo item, longest first by the recorded `.times` (unknown items first) |
| `gotest` | `scripts/gotest-shards.sh`: `go test -count=1 -timeout 7000s ./cmd/...` in duration-balanced shards |
| `rounds` | `audit/run-rounds.sh` (all audit rounds) |
| `axiom` | `scripts/ci-axiom-guard.sh` |
| `x86` | `scripts/x86formal.sh prove` |
| `asl-build`, `sail-build` | `scripts/asl.sh build` (set `ASL_CACHE`), `scripts/oracle-sail.sh build` |
| `rtasl-prove`, `-rel`, `-strict`, `-replay`, `-btf`, `-probes`, `-fsqrt`, `-go` | `audit/rt-asl/run.sh GROUP`: the red-team round ASL, one lane per group (`run.sh` without arguments still runs them all, in order) |

**Automatic sizing.** Without `-j` / `--lanes` (and without `JANUS_JOBS` / `JANUS_LANES`), `gate.sh` chooses them
from the host (`scripts/lib/autojobs.sh`, tested by `scripts/lib/test-autojobs.sh` with fake nproc / MemAvailable /
load inputs): `jobs = min(cap, (free cores - 16 reserved for the other lanes) / 2.1 cores per item, (MemAvailable -
30 GiB floor - 40 GiB reserved) / item GiB)`, at least 2, where free cores = nproc - 1-minute load and item GiB = the
largest recorded per-item peak of `scripts/speed-baseline.tsv` (6.1 without one) x 1.5, at least 4; `lanes =
min(jobs + 3, 15)`. An idle 48-core / 170 GiB box gets `-j 10`, 13 lanes. Fewer than 8 free cores or a 1-minute
load of 60 or more (RULES.md) falls back to `-j 2`. `JANUS_GATE_MAX_JOBS` (default 12), `JANUS_GATE_MEM_FLOOR_GIB`,
`JANUS_GATE_LANE_CORES`, `JANUS_GATE_LANE_GIB`, `JANUS_GATE_CORES_PER_ITEM` tune it. The choice and its reason are
printed and recorded in the timeline's `gate` line (`auto`, `why`, `roundsLanes`). The audit-round lane count (`JANUS_ROUNDS_LANES`, read by `audit/run-rounds.sh` where it supports it, exported to the rounds lane only) is min(6, free cores / 8, (MemAvailable - 40 GiB) / 15 GiB), at least 2, and 2 on a busy host. Admission: every pool (`pool.sh`) starts no new
item while MemAvailable is below the floor plus one item's estimate. An explicit `-j` or `JANUS_JOBS` (the shared-box
rule of RULES.md) is used as given; memguard's per-job limits are unchanged.

**Concurrency.** `-j N` / `JANUS_JOBS` (default **2**, the shared-box rule; `auto` uses the formula of
`scripts/lib/parallel.sh`) is the number of verify items at once; the go test shards (`max(2, N)`, one
test slot each) and the audit lanes (`N`) scale with it. `--lanes` / `JANUS_LANES` caps the lanes.
`LEAN_NUM_THREADS` is capped at 4. The gate refuses to start at load >= 70, MemAvailable < 40 GiB or
< 60 GiB free (`JANUS_GATE_FORCE=1` overrides). `--only/--skip` and `--changed` give a PARTIAL run.

**One queue.** `verify-all-examples.sh` queues arm64, amd64, asm, rtmisc, sys, print (and with `--cgo`
the cgo) items in one pool; the cgo, sys and print scripts take `-j` and `--list` and still run
standalone. Their theorems go through `verify_theorems` (`scripts/lib/theorems.sh`), like arm64/amd64.

**Streamed output.** Each item prints `[done/total] PASS|FAIL|TIMEOUT|SKIP|BLOCKED  id  wall` the moment it
finishes (with the last 30 log lines on a failure), a `-- pool ...: done/total, running [id elapsed, ...]`
line every minute, and the verify lane's lines are echoed live. Every item's full log is kept (verify:
`<out>/verify/<id>.log`; lanes: `<out>/lanes/<name>.log`).

**Verdict.** A failed, timed-out, blocked or missing item or lane fails the gate (exit 1), exactly as
before; item timeouts (`JANUS_ITEM_TIMEOUT`), the audit, kernel replay, pins and sandbox are those of the
scripts being run.

**go test shards.** `scripts/gotest-shards.sh` lists every test (`go test -list`), deals them to the shards
longest first using `testDurations` in `cmd/janus/order_test.go`, and checks that the shards partition the
list (fails if a test is unassigned or twice); afterwards it checks from the `-v` output that each
shard reported a result for exactly its tests.

**Lane memory limits.** memguard's per-job default (24G) applies inside the outer `memcap` unless
`JANUS_MEM_MAX` is set, and the ASL build OOM'd at 24 GiB once, so `gate.sh` sets an explicit per-lane limit
(`JANUS_GATE_MEM_<LANE>`, e.g. `JANUS_GATE_MEM_ASL_BUILD=64G`, overrides it):

| lane | per-job limit | measured peak (acc1 timelines, `-j 2`) |
|---|---|---|
| `asl-build`, `sail-build`, `rtasl-*` | 48G | asl-build 11.2 GiB in its logged jobs, one cold build job OOM'd at 24 GiB (FpSame.ExecC) |
| `x86` | 24G | 11.2 GiB |
| `rounds` | 24G (its lanes have their own 20G cgroups) | 1.2 GiB per job |
| `gotest`, `axiom` | 24G | 14.3 GiB (profile) / negligible |
| `verify` | none set: each item bounds itself (10G slots; print rows 24G) | items 0.2-6.1 GiB, print 10-14 GiB |

These are per-job ceilings, not reservations. The outer cap is `memguard_self`'s `max(limit, MemAvailable - 40 GiB)`;
the simultaneous peaks are what count: measured asl-build + x86 + rounds + verify pool at `-j 2` ~ 30-45 GiB, far
inside it. At a higher `-j` the verify pool adds ~10 GiB per slot (the admission check in `parallel.sh` keeps
40 GiB free).

**Kept trees.** The isolated lake-lane trees are `artifacts/gate/trees/<hash of HEAD tree + uncommitted diff>/{x86,asl}`.
They are removed when the gate passes, kept (path reported) when it fails or is cancelled, and reused by a
rerun of the same sources (`scripts/lib/test-gatelanes.sh` tests limits, keep, reuse, removal). A second run on the
same sources waits (flock). `ASL_CACHE`, or `JANUS_ASL_CACHE` as an alias, is forwarded to `scripts/asl.sh`; the
content-addressed cache of `agent/speed-asl` is not final, so this is only the hook.

**Cancel.** A gate run is its own process group (`setsid`); `<out>/pgid` holds the id. Cancel one run with
`kill -- -$(cat <out>/pgid)` (or stop its memcap scope) and nothing else; never kill by name or pattern, other
gates share the host (`scripts/lib/test-pgcancel.sh`). The Lake-writing lanes (x86, asl, oracle, rt-asl) work in
private source copies (`artifacts/gate/trees/<hash>/x86` and `/asl`, about 0.85 GiB each, see "Kept trees"),
because a `lake` in JanusX86/JanusASL replays the framework's `.olean` files it depends on by path; the verify,
go test and audit lanes read the prebuilt framework build, which is never written after the prebuild.

**Speed baseline.** `scripts/speed-baseline.tsv` (id, wall seconds, peak GiB per verify item and lane) is recorded
by a green full gate: `scripts/gate.sh --speed-baseline record` (only items that PASSED; header has commit, -j, host
load), reviewed and committed. Enforced by default (`--speed-baseline enforce`): an item that PASSED but took more
than max(1.5 x baseline, baseline + 10 s), or a total pool work above 1.5 x, fails the gate with the item,
baseline, measured time and ratio; new items are listed, not failed; peak-memory growth is a warning. The host
load is printed with the verdict but never excuses a regression. Without the file the summary says
`speed check NOT enforced: no baseline`. `python3 -I scripts/gate-speedcheck.py seed artifacts/verify-all-examples.times OUT`
derives a provisional file from a times file (not enforced). Update procedure: after an intended speed change,
re-record on a green full gate and say why in the commit message.

**Old gate vs new gate (nothing dropped).**

| old check (pgate.sh / pg3.sh / RULES.md) | new gate |
|---|---|
| `lake build` | prebuild `lake` (`lake build`, then `lake build Janus Janus.Tools.Audit janus-audit`) |
| `go test -timeout 7000s -parallel 2 ./cmd/...` | lane `gotest`: same tests, `-count=1 -timeout 7000s`, sharded; partition checked before and after |
| `scripts/ci-axiom-guard.sh` | lane `axiom` |
| `scripts/verify-all-examples.sh` (arm64, amd64, asm, rtmisc, sys, print) | lane `verify` (same items, same theorems, same Witness theorems) |
| `scripts/verify-cgo-examples.sh` (64 rows, correctness and Witness) | lane `verify`, `--cgo` items |
| `scripts/verify-sys-examples.sh` (10 rows) | lane `verify`, sys items (the full default list, 2 more rows than the old verify-all had) |
| `scripts/verify-print-examples.sh` | lane `verify`, print items |
| `audit/run-rounds.sh` | lane `rounds` |
| `audit/rt-asl/run.sh` (asl prove, A1-A3, A6, A7, A8, A5/C2, fsqrt, C1) | lanes `asl-build` + `rtasl-*` (one per group; same rows, same expectations) |
| `scripts/x86formal.sh prove` | lane `x86` |
| item timeouts (`JANUS_ITEM_TIMEOUT`), audit, kernel replay, pins, sandbox, Witness theorems | unchanged: the same scripts and `janus verify` run them |
| `x86formal.sh prove` "twice" (profile A.1) | pgate.sh and pg3.sh contain ONE `x86formal.sh prove` step (the profile's two entries are two runs of it, not two targets; there is no x86b step in either script) |
| anything else in pgate.sh / pg3.sh (oracle.sh, oracle-sail.sh as a step, `asl.sh` check/oracle, coverage.sh, cabi-probe.sh, build-examples checks) | not steps of either script. Their builds that the covered checks need are in the prebuild (`oracle-sail.sh build` for `rtasl-fsqrt`, `asl.sh build`); the standalone corpora checks (`oracle*.sh full`, `asl.sh check`, `coverage.sh`, `cabi-probe.sh`) were not in the old gate and are not added |
| (new) speed regression check, timeline, streamed results | on top of the above |
| CI `lake build Janus JanusTests` and `... janus-oracle-amd64` (not default Lake targets) | prebuild `lake`: `lake build JanusTests janus-oracle-amd64` |
| CI `go vet ./...` | lane `govet` |
| CI `JanusASL/tools/test_asl_cache.sh`, `test_asl_mod_cache.sh` | lane `cachekeys` |
| CI decoder coverage of the arm64 examples (`janus blockers`) | lane `decoder` (`scripts/decoder-coverage.sh`, also called by ci.yml) |
| CI `scripts/oracle.sh quick` (qemu) and `scripts/oracle-amd64.sh quick` (native), MISMATCH check | lane `oracle` (in the lake tree, after `rtasl-prove`) |
| asl.yml `scripts/asl.sh verify` (4 ASL corollaries) | lane `asl-verify` (after `rtasl-prove`) |
| CI `audit/run-all.sh`, `verify-examples.sh`, `verify-amd64-examples.sh`, `ci-axiom-guard.sh`, `x86formal.sh` build/prove, `asl.sh build/prove` | already covered: lanes `rounds`, `verify`, `axiom`, `x86`, `asl-build`, `rtasl-prove` |

**Timeline.** `<out>/timeline.jsonl` (default `artifacts/gate/<UTC time>/`, linked as `artifacts/gate/latest`)
has one JSON object per prebuild step, stage, pool, lane and item (start/end epoch seconds, wall, status);
`python3 -I scripts/gate-report.py <timeline>` prints the stages, pool utilisation, lanes and critical path.

## Red team of the caches (`cmd/janus/*_rt_test.go`, `scripts/lib/test-rt-incr.sh`)

An authorized audit of the result cache, the incremental records, the framework verdict store and the build-cache
key. Every attack is a test that must end in a miss or a refusal: stale edits with restored mtimes, deep and
auditor-only framework modules (every `import` spelling, the `module` header), toolchain/checker/auditor swaps,
environment and script changes, key framing and symlinks, record tampering at every truncation length and every
flipped byte, key-file handling, build inputs of the verifier identity (assembly files, overlays), a hostile proof
reading or writing the caches from both sandbox modes, concurrent writers, verdict-store forgeries and failed or
timed-out runs. The shell side (`test-rt-incr.sh`, run by `TestRTIncrScripts`) covers `JANUS_INCR_EXPLAIN` in the
environment, the clean-tree pin that a record requires, the go configuration in lane keys and the scripts each item
kind runs. Findings fixed on the way: see `git log agent/speed-rt`.

## Incremental gate (`--incremental`)

**The default is a FULL run.** `scripts/gate.sh` and `scripts/verify-all-examples.sh` skip nothing unless asked; the
full cold gate stays **mandatory before every push to main and nightly**. `scripts/gate.sh --incremental` (or
`JANUS_GATE_INCREMENTAL=1`; `verify-all-examples.sh --incremental`, `--changed` is an alias) is for the merge gate of a
branch: it skips an item or lane only on the record of a PASS whose key is identical. Every item that runs is checked
in full, and the prebuild, the build lanes and the axiom guard always run. Every full run (and every incremental run)
records the passes it sees, so a full gate feeds the next incremental one. Design and trust argument:
docs/SOUNDNESS.md "Incremental gate records"; code: `cmd/janus/incr.go` (`janus incr check|record|explain`),
`scripts/lib/incr.sh`.

**What an item's key hashes** (all by content): the item and its arguments; the relevant environment
(`JANUS_*` except output/parallelism variables, `LEAN*`, `LAKE*`, `GO*`, `CGO_*`, memory limits, ...); the verifier
identity (Go-only variant, `cmd/janus/verifierid.go`); the Lean toolchain; the framework configuration and the
**transitive import closure** of the item's modules (sources and compiled module data of every framework module it
imports, found by following the real `import` lines); the auditor (sources, compiled modules, `janus-audit`) and
`leanchecker`; the proof file(s), package and extraction (`Extracted.lean`, `identity.json`, the binary); the pins; the
gate scripts and libraries. Lanes (`gotest`, `rounds`, `x86`, `rtasl-*`) hash the whole working tree except `docs/`,
`assets/` and `*.md` (docs/SOUNDNESS.md is hashed, an audit row reads it), plus the machine.

**Reading the result.** Every item prints `skipped (unchanged: incremental; recorded PASS of <time> on <host> at <commit>,
<s>s then; key <hash>)` or its usual result line. The verify lane prints an `incremental report` (RAN or SKIPPED for
every item, totals) and the gate report prints `RAN / SKIPPED` for every item and lane. The verdict says `GATE PASS
(INCREMENTAL: ...)`.

**Debugging a miss.** `scripts/gate.sh --explain arm64:Add` (also `cgo:amd64/CAdd`, `lane:gotest`) prints every key
component with its hash, the key, and whether a record exists; run it before and after a change and diff the two
outputs (`bin/janus incr explain ... --verbose` also lists the closure module by module). It reads the state of an
earlier run and runs and records nothing.

**What the tests attack** (`cmd/janus/incr_test.go`, `go test -run Incr ./cmd/janus`): an edit of each input class
(proof, an imported module one and three levels deep, its compiled data, the toolchain string and binaries, the
verifier identity, the auditor's source/module/executable, the pins, the scripts, each relevant environment
variable, the extraction and its binary, the item's arguments) is a miss; an edit of a framework module the item
does not import, of the verifier's own output files or of documentation is a skip; a tampered, truncated,
re-keyed, copied, foreign-key, wrong-domain, symlinked or trailing-garbage record is a miss; a record from a
failed run is never written and withdraws an older one; inputs that change during the run are not recorded; an
input that cannot be hashed makes the item always run; key framings do not collide.

## Gate speed (2026-10-25): profile, changes, before/after

The merge gate and every agent's regression run are `go test ./cmd/...`,
`scripts/verify-all-examples.sh` and the audit rounds, often run by several agents at once on the
same host. Measured on the 48-core, 251 GB development host under the usual load of other agents
(load average 35–60), `LEAN_NUM_THREADS=4`, Lean 4.34.1. Every number is one run; the host's load
moves absolute times by ±30%, not the ratios.

### Profile (before)

**`go test`** (`go test -json`, per-test elapsed; `cold` = fresh test cache and no `.lake` in the
checkout, `warm` = the same cache and checkout again, `-count=1`):

| | cold | warm |
|---|---:|---:|
| wall | 1135 s | 954 s |
| sequential (non-parallel) tests, one after the other | 722 s | 612 s |
| parallel phase (at `-parallel 2`) | ~530 s | ~430 s |

* **Most of the time was sequential.** A test that does not call `t.Parallel` runs alone, before
  any parallel test starts. The sequential ones included the heaviest: `TestCacheGCConcurrentVerify`
  (199–253 s), `TestForeignFrameworkWriteDetected` (168–185 s), `TestConcurrentVerify` (86–151 s),
  `TestAmd64Blockers` (79 s cold: it built the checkout's framework), `TestR1FrameworkTamper`
  (46–64 s), `TestRound6StatementNames`, the memguard tests. They were sequential because they
  set environment variables (`t.Setenv`) or because they **damage or empty the shared test
  cache**: the collector test ran `janus cache gc --max 0 --grace 0s` in a loop on
  `~/.cache/janus-test` (removing every replay marker, trusted-compile and result entry, of this
  run and of every other agent's run sharing that cache), the concurrency test deleted the
  shared framework build's stamp and decoder module, and the foreign-write test appended to the
  shared build's `Janus/Tools/Audit.olean`.
* **Redundant framework replays.** The kernel replay of the whole framework (`leanchecker
  Janus`, 15–40 s and ~3 GB each) ran again and again: the collector loop removed its markers as
  soon as they were written, the early framework replay took no lock (six verifications started
  together each ran their own: the 6–8 concurrent `leanchecker Janus` processes in
  `~/.cache/janus-test/v1/run/replay-*`), and every `--unsafe-no-sandbox` verification replayed
  the framework unconditionally (no replay cache without a sandbox): TestSandboxRecorded,
  TestR1FrameworkTamper's four unsandboxed rows, TestForeignFrameworkWriteDetected's three runs.
* **Low parallelism, random order.** `-parallel` defaulted to 2, and the testing package starts
  released parallel tests in no particular order, so a 2–4 minute test could start last.

**`scripts/verify-all-examples.sh`** (166 items) and the audit rounds: see the tables below.

### Changes

* **Framework replay verdict** (`cmd/janus/replaymark.go`; docs/SOUNDNESS.md "The framework replay
  verdict"): one HMAC-authenticated verdict per (toolchain, framework pins), looked up before any
  untrusted step; concurrent verifications of a new framework build replay it once (replay lock),
  a verdict in use is protected from the collector (use lock), and it is read (never written)
  without a sandbox. Every per-module replay marker is now HMAC-authenticated too. The proof's own
  modules (`Extracted`, `JanusTrusted`, `Proof`, consumer and dependency modules) are never
  covered by it.
* **Consumer workspaces keep the framework base's lease** until they close (the
  TestConsumerLakefileLean/TestVerifyBatch flake, below).
* **Tests that damage or empty their cache get a private one** (`seededCache`, `seed_test.go`): a
  copy of the test cache's framework build, accepted only if `framework.ready` holds for the copy
  (sources byte-identical to the embedded framework, every module-data file and the auditor
  hashing as stamped), plus the framework verdict, carried over only if its HMAC verifies under
  the source cache's key (it is then re-recorded under the private cache's key). The copy lives
  on disk under the test cache's `v1/tmp`, not in `/tmp`. The collector, concurrency and
  foreign-write tests use it, so they no longer disturb anything else, and they are parallel.
* **The test cache is seeded** in `TestMain` from the user's cache (`~/.cache/janus`, or
  `$JANUS_TEST_SEED_CACHE`; `off` disables it) when that has a ready build of the same framework
  and the test cache has none, with the same hash check and verdict rule.
* **Every Lean test is parallel** except `TestUnshareFallbackSelect` (it sets `JANUS_SANDBOX` for
  an in-process sandbox check; the verification half, `TestUnshareFallbackVerifies`, runs a janus
  process and is parallel). Tests that needed an environment variable for janus now pass it to a
  janus subprocess (`TestR1FrameworkTamper`: `JANUS_R1_MODE`; its rows are parallel subtests).
* **Longest first** (`order_test.go`): every parallel test starts with `defer parallel(t)()`,
  which waits for a slot of the package's own scheduler; a free slot goes to the waiting test
  with the longest measured duration (`testDurations`). The number of slots is
  `min(GOMAXPROCS/6, (MemAvailable − 40 GiB)/10 GiB, 8)` (8 here, 1 on a 4-core 16 GiB runner) or
  `-parallel N`; testing's own limit is raised so that it does not bind first.

No assertion was removed or relaxed. Added: `TestFrameworkVerdictKey`,
`TestFrameworkVerdictAuthentic`, `TestModuleMarkerPlanted`, `TestFrameworkReplayOnce` (six
concurrent verifications run `leanchecker Janus` once; a failing replay records nothing; a verdict
in use survives `gc --max 0 --grace 0`), `TestSeedFramework`, `TestConsumerAuditorLease`, and a
planted verdict (well-formed, MAC under another key) for the forged framework build in
`TestR1ForgedFrameworkLemma`, which must still be rejected by the kernel replay.

### go test, before / after

| | before | after |
|---|---:|---:|
| cold (fresh test cache, no `.lake`, seeding off) | 1135 s | 671 s |
| warm (`-count=1`, same cache and checkout) | 954 s | **202–212 s** (final run, all tests including the new ones: 202 s) |
| sequential tests | 612–722 s | 10 s |

After, the critical path is `TestCacheGCConcurrentVerify` (199 s warm), which the scheduler
starts first; cold, the first ~4 minutes are the two framework builds (the checkout's and the
cache's, which every Lean test needs).

### Go tests, 2026-10-29: per-run cache, prebuilt fixture (no check removed)

* **A cache of its own per run.** `TestMain` creates `<cache dir>/janus-test-run-*` (on disk, never a RAM
  `/tmp`) as the test cache and removes it when the run ends; `scripts/gotest-shards.sh` gives every shard one
  and removes them in a trap. `JANUS_TEST_CACHE_DIR=<dir>` names one explicitly (kept), `=shared` selects the old
  shared `~/.cache/janus-test` (which every run had refilled, 22-32 GB). A run killed by `go test -timeout`
  leaves its directory behind; `rm -rf ~/.cache/janus-test-run-*` when no test is running.
* **A prebuilt framework fixture** (`fixture_test.go`). The first run for a framework version builds, under a lock, a
  cache of its own in `<cache dir>/janus-test-fixture` (outside `~/.cache/janus`, so no collector evicts it): the
  embedded framework's Lake build and the sandboxed `leanchecker Janus` verdicts of the embedded build AND of this
  checkout's own build (`--janus-root` verifications use that one; its bytes, so its verdict key, differ). Every
  later run copies the ready build and the authentic verdicts into its per-run cache (`seedFramework`,
  `seedCheckoutVerdict`; the copy must hash as stamped, a verdict counts only if its MAC verifies under the
  fixture's key) and `seededCache` carries both to the private caches of the tests that damage or empty their cache.
  Before, every run had to replay the checkout's framework (3-5 min per replay on a loaded host, 500 s of waiting
  at the start of the suite) or find it in a shared cache. `JANUS_TEST_FIXTURE_DIR=off` goes back to seeding from the
  user's cache. A test that checks the cold path (`TestSeedFramework`, `TestFrameworkReplayOnce`, the forged-framework
  tests) still builds or replays what it tests; nothing is skipped.
* **`TestCacheGCLRUOrder` flake.** The collector's clock is injected: the fixture's `gc` passes the fixture's own
  reference time (plus one second, so "just now" entries are older than a zero grace) as `gcOptions.Now`, so the
  priorities (age / weight) depend only on the ages the fixture set, never on how long the test has been running.
  No retry, no sleep.
* **Measured** (go test -json -parallel 8 on the 48-core host while other agents' gates ran, load 30-60; one run
  each): 3070 s (`-parallel 4`, no `.lake` in the checkout, nothing seeded) -> 889 s (checkout built, per-run cache,
  seeded from the user's cache) -> 764-786 s with the fixture warm (three green runs in a row: 2534 s with the one-time
  fixture build, 764 s, 786 s). The remainder is the host's load: the suite uses 1085 s user + 439 s system CPU in
  total, and its longest tests (`TestCacheGCConcurrentVerify`, `TestR1ForgedFrameworkLemma`) are two full
  framework replays each, which take 3-5 min on this loaded host and 15-40 s on an idle one.
* The list of tests is unchanged (185 names before and after, diffed: `go test -list '.*' ./cmd/...`).

### The TestConsumerLakefileLean / TestVerifyBatch flake

Both failed together now and then with `the auditor executable …/v1/framework/<key>/.lake/build/bin/janus-audit
changed after it was built`, and each passed alone. Root cause: the consumer path
(`verify --proof-root`, `verify-batch`) held the shared lock on the cached framework base only
while preparing its workspace, but runs the base's compiled auditor much later. Any writer that
took the exclusive lock in between (a rebuild for another target such as `janus blockers`' decoder,
the repair of a damaged build, or the cache collector, all of which the old tests did on the
shared test cache) could replace or remove the executable, and the (correct) check rejected the
honest run. The workspace now holds the lease until `ws.close`; the check is unchanged.
`TestConsumerAuditorLease` reproduces it deterministically: a writer repeatedly takes the
exclusive lock and moves the auditor away and back while four consumer verifications run. Before
the fix all four failed with exactly that message (12 s); after, all verify. `go test -count=5
-parallel 4 -run 'TestConsumerLakefileLean$|TestVerifyBatch$|TestConsumerAuditorLease$'` passes
(164 s).

### Two more test-suite bugs

* **Consumer workspaces shared across checkouts.** A consumer workspace family was keyed by the
  framework's content hash and the package root only. Two byte-identical janus checkouts (agents'
  worktrees sharing `~/.cache/janus-test`) therefore shared workspaces and seeded each other's
  builds whenever the package root matched, and a package that switched to another checkout at
  the same path reused the first checkout's workspace. This was not a soundness hole (the
  dependency is still byte-compared with the verifier's framework, `compareFramework`, the
  workspace's framework is copied from the content-keyed trusted base and pinned, and the report
  records the checkout the package resolved), but it coupled worktrees. The family key now also
  covers the framework's source and directory and the resolved janus dependency (type, checkout
  directory, URL, revision). `TestConsumerTwoCheckouts` (two checkouts, one package path switching
  between them, a second package) fails with the old key and passes with the new one. (The exact
  path the M1 agent saw could not be reproduced with two copies of this tree sharing one test
  cache; the cache-damaging tests that used to run on the shared test cache are the other way
  worktrees interfered, and they now use private caches.)
* **`TestR1FrameworkTamper` on a cold cache**: janus prints `Building the Janus framework (…)` before
  the verdict when it builds the framework; the test now skips exactly those leading notices
  (`withoutProgress`, unit-tested) and still requires `Invalid:` to be the first other line.

### Example suite (`scripts/verify-all-examples.sh`, 166 items)

Profile (before, fresh private cache, the default `-j 2`): **2800 s**. The per-item times (now
printed for every item and kept in `artifacts/verify-all-examples.times`) are dominated by a few
proofs: ClearWords 345 s, MallocFast 344 s, A64Crc32 209 s, Classify 167 s, then a long tail of
10–65 s items. Peak memory per verification (`memoryGuard.peak` in every `verified.json`): at most
3.9 GiB (ClearWords; MallocFast 3.7, the amd64 assembly items 3.5–3.6, Classify 2.6–3.0), so the
old 20 GiB budget per job (and the cap of 2 jobs) left the host's memory and cores mostly idle.
The examples' binaries and the framework are built once per run already (`JANUS_EXAMPLES_PREBUILT`),
and every item uses the same janus cache, so the framework build and its replay happen once.
A second, smaller waste: the further theorems of one proof file (the non-vacuity witnesses, Div's
and Get's `panics`, F64ToU64's `exact`/`saturation`) ran one after the other, each compiling the
same proof again (Classify: 3 x ~170 s).

Changes:

* default `-j`: `min(cores/6, (MemAvailable − 40 GiB)/10 GiB, 8)` with a 10 GiB slot limit
  (`scripts/lib/parallel.sh`; 8 here, unchanged 1 on a CI runner);
* the pool is ordered **longest first by the last run's measured times** (an item without a time
  goes first; the built-in order before the first run);
* **one compile per proof file** (`scripts/lib/theorems.sh`): all theorems of a proof file (correctness,
  the extra ones, the non-vacuity witnesses) are verified by ONE `janus verify --theorem A --theorem B ...`
  run. The proof is compiled once (before, once per theorem: 654 compiles for 332 files), and the extraction check,
  the trusted compile, the pins and the framework replay verdict are done once; each theorem still gets
  its own audit (statement, kind, axiom allow-list), kernel replay of its closure, result-cache entry and
  report (`verified/<Theorem>.json`; the first theorem's is also `verified.json`). Per-theorem status
  and log (`STATUSDIR/<i>.rc`, `.log`) come from the run's `--results` file, so a failing theorem fails alone
  and cannot be masked by (or mask) the others; a timeout or crash of the run fails all of them. Nothing is
  weakened: the same checks run for the same theorem, minus the repeated compile and fixed costs. The split
  rtmisc packages (Three, Chain) build their module chain once in one workspace and check
  `Main:correctness`, `Witness:nonvacuous` and `Witness:returns` from it (`--proof-root` with
  `--theorem PROOF.lean::NAME`), instead of three runs rebuilding the chain;
* `--changed` (development only, never the gate): skips every item whose inputs (its extraction,
  proof file and extraction arguments, the framework sources and the toolchain) are byte-identical
  to its last passing run in this checkout (`artifacts/verify-all-examples.manifest`, written by
  every run). The janus executable is deliberately not an input: after a change to `cmd/janus` the
  result cache misses everywhere, while `--changed` re-verifies only the items whose extraction
  changed; CI and the merge gate run the full suite. WrongAdd (the break demo) always runs.

| run | before | after |
|---|---:|---:|
| fresh cache (framework built and replayed), first run (built-in order) | 2800 s (`-j 2`) | 1001 s (`-j 8`) |
| fresh cache, with the measured order and two theorems at once | | **715 s** |
| warm caches, result cache off (`JANUS_RESULT_CACHE=off`: a janus change) | 23–35 min (reported) | **552 s** |
| nothing changed (result cache) | 12 s | 8 s |
| `--changed`, nothing changed | | 8 s (4 s pool) |
| `--changed`, one proof edited (Add made false) | | 61 s: Add re-verified (FAILED, as it must), WrongAdd, 165 skipped |

On a fresh cache about 2–3 minutes of the 715 s are the framework build (every item waits for it)
and its first replay; after that the critical path is the longest proof under an 8-wide load
(Classify's pair, ClearWords, MallocFast: 390–430 s under the host's load of 50–60).

### Audit rounds

Profile (before; each script after the other, warm caches): `audit/run-all.sh` 270 s, round 2
133 s, round 3 9 s, round 4 9 s, round 5 467 s, round 6 60 s, round 7 1233 s, round 8 781 s:
**2962 s** (rounds 7 and 8 overlapped some of the measurements above, so they are high). Rounds 7
and 8 are long because every attack row runs `janus verify --fresh` (deliberately the cold path:
no result, trusted-compile or replay cache, so each row replays the whole framework), one after
the other; round 7 also runs its cache attacks (`run-cache.sh`, a `--janus-root` copy with an
edited framework that must be rebuilt). Every script also built janus and ran `lake build` again.

Changes: `audit/run-rounds.sh [-j LANES] [round …]` builds janus, the checkout's framework and
the example binaries once (`JANUS_AUDIT_BIN`, `JANUS_AUDIT_PREBUILT=1`, which the round scripts
honour instead of building again) and runs `run-all.sh` and rounds 2–8 as parallel lanes,
longest first (default `min(cores/12, (MemAvailable − 40 GiB)/20 GiB, 4)` lanes of `-j 2` rows);
each lane's output is printed whole, and a lane that fails fails the run. The rounds are
independent (each writes only its own `audit/<round>/work` and temporary caches). Inside rounds 7
and 8, the `--fresh` rows run as parallel blocks after the fixtures are built (each on its own
copy of the extraction it verifies when it writes a `verified.json`); the lists of rows are
unchanged (compared mechanically). The `--fresh` rows still replay the framework every time.

| | before | after |
|---|---:|---:|
| all audits (serial / `audit/run-rounds.sh`) | 2962 s | **983 s** (load average 70–77) |
| longest lane (round 7, including `run-cache.sh`) | 1233 s | 981 s |

### Fault injection (after the changes)

On a scratch copy of the tree with its own warm cache (`JANUS_RESULT_CACHE=off`):

| fault | result |
|---|---|
| control: `examples/proofs/Add.lean` | Verified; every framework module reused (verdict), the per-verification modules by their own markers |
| wrong proof (`% 2 ^ 64` → `% 2 ^ 63` in Add's statement) | `Invalid: Lean rejected the proof … unsolved goals` |
| the same, through `verify-all-examples.sh --changed` | Add re-verified and FAILED, run exit 1; the 165 unchanged items skipped |
| framework source edit (a theorem appended to `Janus/GoABI.lean`, janus rebuilt) | framework rebuilt (new key), verdict miss: `leanchecker Janus` ran, 0 framework modules reused; the second run reused all 80 |
| tampered verdict (one MAC byte flipped) | a miss: the framework was replayed again and the verdict re-recorded |
| planted per-module markers (every marker overwritten in the pre-HMAC format) and the verdict deleted | every planted marker rejected: `leanchecker Janus` replayed the framework (40 s), Extracted/JanusTrusted/Proof replayed; `cached: none` |
| planted, well-formed verdict (MAC under another key) for a framework olean carrying an unchecked `False` lemma (`TestR1ForgedFrameworkLemma`) | still `Stage: kernel replay … Janus.GoABI.forged`, and no verdict recorded |
| tampered trusted-compile manifest, result entry, cache permissions | unchanged checks: `TestRound8TrustedManifestMAC`, `TestResultCache`, round 8 M1/C1 rows, round 7 cache rows, all passing |

## Where the time went (earlier profile, before the 2026-10-24 changes)

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

## Build cache policy

The ASL/Sail build outputs (the ArmASL model, the JanusASL and Janus module builds, the Sail oracle
driver) are served from a content-addressed, HMAC-signed, hash-checked cache (docs/SOUNDNESS.md
"Build caches"; `scripts/asl.sh`, `scripts/oracle-sail.sh`). It caches build outputs only: every
check still runs. The policy:

* **Merge gates and pre-push gates may use the cache** (it is on by default; entries that fail
  their HMAC or a file hash are rebuilt, never used).
* **A nightly gate runs truly cold**: `JANUS_ASL_CACHE=0` (neither reads nor writes the cache; also
  `off`/`no`/`false`; `ASL_CACHE=off` is the older spelling) in a fresh worktree with no builds,
  to catch any gap in the key coverage. `scripts/nightly-cold-gate.sh` does it and compares the
  result with a cached run of the same commit.
* **A disagreement is a P0 cache bug.** If a cold run and a cached run of the same commit differ in
  any lane's pass/fail, or in any ASL/Sail artifact hash (`scripts/gate-cachecmp.py`: every
  ArmASL/JanusASL `.olean` and the Sail driver), the cache served something its inputs do not
  determine, or a key misses an input. Treat every cached result since the last agreeing nightly as
  unproven, fix the key (`JanusASL/tools/asl_cache_key.py`, `asl_mod_cache.py`,
  `oracle-sail/cache_key.py`), and add a case to `scripts/lib/test-bcache.sh`. (If a build step is
  not reproducible bit for bit, the artifact comparison will say so on the first nightly: fix the
  non-determinism or drop that artifact from `gate-cachecmp.py hashes`, with a note here; never
  loosen the lane comparison.)
* **Owner: the main session.**

```
scripts/nightly-cold-gate.sh [--commit REV] [--cached-out DIR] [-- gate.sh args]
# example crontab line (not installed): 02:30 every night, on the commit main points to
# 30 2 * * *  cd /srv/janus && scripts/nightly-cold-gate.sh --commit main -- -j 2 >> /srv/janus-ops/nightly-cold.log 2>&1
```

It makes a cached gate run and a cold gate run (each `memcap -m 80G scripts/gate.sh`, in its own
fresh worktree) unless `--cached-out` names the output of an earlier cached run of that commit,
and exits 1 with a `P0 CACHE BUG` report on any disagreement, 2 if the runs cannot be compared.
The comparison logic is tested with fake results by `scripts/lib/test-cachecmp.sh`; the cache's
integrity and key tests are `scripts/lib/test-bcache.sh`.

## Disk use

On the development host the caches and the oracle dumps once filled the 874 GB disk and put
123 GB into `/tmp`, a RAM tmpfs: one consumer workspace per test (625 of them, 77 GB) in the Go
test cache under `/tmp/janus-test-cache`, 48 GB in `~/.cache/janus`, stale framework and
JanusASL builds, and multi-GB JSON-lines dumps in every worktree's `artifacts/` (one finished
worktree held 69 GB). Three changes bound them:

* **The cache collector** (`janus cache gc`, automatic after `verify`, `verify-batch` and
  `blockers`; docs/CLI.md "Cache"): an LRU over every cache entry with a budget of min(40 GiB,
  10% of the disk) by default (`$JANUS_CACHE_MAX`), min(8 GiB, 5%) on a tmpfs, shrinking when the
  disk is nearly full; entries in use or used in the last 10 minutes are never removed.
  `janus cache du` shows the usage. Soundness: docs/SOUNDNESS.md "Cache eviction".
* **The Go test cache is on disk**: `$JANUS_TEST_CACHE_DIR`, else `~/.cache/janus-test`, else
  `/var/tmp/janus-test-cache-<uid>` (never `os.TempDir()`), separate from the user's cache and
  bounded by the collector like it. `TestMain` seeds it from `~/.cache/janus`
  (`$JANUS_TEST_SEED_CACHE`) when that has a ready build of the same framework (hash-checked, see
  "Gate speed"); `JANUS_TEST_ASL_SEED` seeds the JanusASL build.
* **The ASL build cache is bounded** (`ASL_CACHE`, `asl_mod_cache.py gc`, run by `scripts/asl.sh`
  after every publish with `ASL_CACHE_MAX`, default 15G; docs/ASL.md "Build cache", "Eviction").
* **Oracle dumps are pruned** when a driver ends (`scripts/lib/artifacts.sh`, used by
  `scripts/oracle.sh`, `oracle-amd64.sh`, `oracle-sail.sh`, `asl.sh check`, `x86formal.sh check`
  and `audit/round5/model/run-model.sh`): summaries, reproductions and `mismatches.jsonl` stay,
  the corpus, results and verdicts are zstd-compressed (about 5x, verdicts 15x), duplicates and
  cheaply derived dumps are removed. `KEEP=zst` compresses everything, `KEEP=1` keeps it all raw.
  `scripts/lib/test-artifacts.sh` (run by `go test`, `TestArtifactsLib`) tests the pruning.

Tests of the collector (`cmd/janus/cachegc_test.go`, on private fixture caches; seconds):

| test | checks |
|---|---|
| `TestCacheGCLRUOrder` | eviction order by age / weight, stopping as soon as the cache fits, dry run |
| `TestCacheGCRespectsLocks` | a held workspace (exclusive), framework (shared) or JanusASL (`.use`, `.lock`) lock keeps the entry; released, it goes with its lock and stamp files |
| `TestCacheGCGraceAndPins` | grace period, a use restarting it, in-process pins, `--all` |
| `TestCacheGCRetentionAndTemporary` | retention days, temporary trees by their newest file, trash, orphaned locks and stamps, empty families, the result key never touched, shard directories kept |
| `TestCacheGCLowDisk` | the budget shrinks with the free space, even with `JANUS_CACHE_MAX=off` |
| `TestCacheGCRedTeam` | symbolic links not followed, planted entries removed, a forged entry stays rejected, nothing created, a dry run changes nothing, a non-private cache is refused |
| `TestCacheGCConcurrentHolders` | a collector looping with no budget and no grace while goroutines take and use entries the way janus does: no entry disappears while held |
| `TestCacheCLI`, `TestAutoCollect` | `janus cache du/gc` output and errors, the automatic collection and its rate limit |
| `TestCacheGCConcurrentVerify` (Lean) | verifications in separate processes (single files and a consumer package) while `janus cache gc --max 0 --grace 0s` loops; all verify, and from an emptied cache the re-verification gives the same theorem, statement and axioms |
| `TestTestCacheOffTmpfs` | the test cache is not on a RAM filesystem and passes the round-8 check |

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
└─ parallel slot  (JANUS_JOB_MEM, 10G)               scripts/lib/parallel.sh par_run → memguard_run
   └─ janus job  (JANUS_MEM_MAX, 24G → effective 10G) cmd/janus guardRun, one per lean/leanchecker/lake
```

The effective limit of a job is the smallest `memory.max` on its path, and that is the one
janus reports. A kill caused by an inner limit is reported by the inner guard, through janus's
diagnostic. The outer guards see it only in their hierarchical `memory.events`, print "a nested
guard killed one of its jobs", and return the command's own status. parallel.sh admits a new
slot only while MemAvailable ≥ 40 GiB headroom + 10 GiB, so slots × slot limit stays within
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
(4.8 GiB) and the cold framework replay (3.0 GiB), so the default leaves about 5x headroom. A 10G parallel slot holds a cold
verify with room to spare.

## Per-item time limit

The verify-* scripts run every `janus verify` through `jv` (scripts/lib/itemtimeout.sh) under `JANUS_ITEM_TIMEOUT` seconds (default 2700; 0 disables). A hung proof is killed, reported as `TIMEOUT:` in its log, and counts as a failure; the run continues.
