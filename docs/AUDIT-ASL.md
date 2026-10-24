# Janus audit, round ASL: JanusASL's claims, and concurrent `janus verify`

This round reviews two pieces that no earlier round examined.

* **JanusASL** (`docs/ASL.md`, `JanusASL/**`). It claims that the Janus arm64 model equals Arm's
  ASL (sail-arm v9.4-a, translated to Lean by Sail's Lean backend) for every integer
  data-processing class and every branch. `run_agree` and `Ensures.toASL` then carry the shipped
  example theorems over to the ASL. This round attacks what those statements **mean**: the state
  relation, the configuration predicate, the generated model and its patches, the run-level
  hypotheses and the audit.
* **A known bug.** Concurrent `janus verify` runs on one machine interfered with each other.

The rows are in `audit/rt-asl/`: `run.sh` (the runner), `RelMeaning.lean`, `AuditStrict.lean`
with `asl-statements.golden`, and `sail/` (Sail backend probes). The Go tests are in
`cmd/janus/concurrency_test.go`.

Severity: **medium** = a claim or a workflow is wrong, but no false `Verified` and no false
theorem results; **low** = a latent defect or an overclaim in prose; **info** = scope that should
be stated.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| C1 | **medium** (availability; fails closed) | concurrent `janus verify` failed with "framework integrity … unexpected Janus/Tools/Decode.olean" while `janus blockers` (or any writer) used the same framework build | **BROKEN → fixed** (shared/exclusive locking, ready stamp, regression tests) |
| A6 | medium (assurance) | `JanusASL/Audit.lean` selects theorems by name suffix and checks only axioms: a missing or renamed theorem, or a weakened statement, passes | open → stricter audit + reviewed statements added as a row; sent to the ASL agent |
| C2 | low (latent) | Sail's Lean backend (with JanusASL's patches) silently drops assignments made inside a block that initializes a `let`/`var` | latent: not reached (0 such shapes in the sources); row added; sent to the ASL agent |
| A4 | low | `Ensures.toASL` is described as "the same statement about the ASL", but `Rel` ignores memory and V registers, so a postcondition about those carries nothing over | open (doc); the 4 examples are register-only and are not affected |
| A1 | — | `Rel` is too weak or degenerate | blocked: `Rel` is a function onto X0–X30, SP, PC, NZCV (kernel-checked) |
| A2 | — | `Rel ∧ LinuxEL0Config` is contradictory (vacuous theorems) | blocked: a witness exists for **every** Janus state (kernel-checked) |
| A3 | — | the example corollaries are vacuous or only about Janus | blocked: `Add` restated over Sail states alone (kernel-checked) |
| A5 | — | the backend patches change semantics beyond the documented fixes | blocked: the patched constructs match Sail's C backend on 2,058 concrete inputs |
| A7 | — | the JanusASL proofs are accepted only by the elaborator | blocked: `leanchecker JanusASL.Proofs` replays them |
| A8 | info | `LinuxEL0Config` describes nVHE or guest Linux (HCR_EL2.E2H = TGE = 0), not a VHE host | faithful otherwise (see A8); doc note sent |
| A9 | — | slicing or the harness removes behaviour on a proved path | blocked (see A9) |

**One item was BROKEN: C1, the concurrent-verify race. It failed closed, so it was never
unsound. It is fixed, with regression tests. The JanusASL theorems hold and mean what
docs/ASL.md says. The open items are an audit gap (A6), a latent backend defect that is not
reached (C2), and a prose overclaim (A4).** The runner passes: `audit/rt-asl/run.sh` prints "all
rows as expected".

---

## C1 (BROKEN → fixed): concurrent `janus verify` runs interfered

### Mechanism

A verification uses one framework build, shared by every janus process on the machine: the
cached base `~/.cache/janus/v1/framework/<sha>` for the embedded framework, or the checkout
for `--janus-root`. `frameworkBase` held the cache lock only while it synced the sources and ran
`lake build`. It returned with the lock **released**. `verify` then pinned the build's
`Janus.*` module data (`frameworkPins`) and re-checked the pins after every untrusted step
(R1). Any process that wrote to the build in that window failed the pins. The concrete writer
is `janus blockers`. It ran `lake build janus-decode` in the same base, with no lock at all, and
that compiles `Janus.Tools.Decode`, a framework module that `Janus`/`Janus.Tools.Audit` do not
build. On this host, 12 of the 46 cached bases contain `Janus/Tools/Decode.olean`. A
verification running at that moment failed with:

```
Invalid: the Janus framework build (…/framework/fc4502a1…/.lake/build/lib/lean) changed after the audit;
its compiled modules no longer match the pinned SHA-256 hashes:
  unexpected Janus/Tools/Decode.olean
  Stage: framework integrity
```

This is the reported break-demo failure: other agents running `janus blockers` or tests on the same main-based
framework sha, which share one base. Reproduction on the old code, with a private cache:
remove `Decode.*` from the base, start `janus verify artifacts/Add …`, and 8 s later start
`janus blockers artifacts/examples-arm64 example.com/basic.Add`. The verify exits 1 with the
message above. The `--janus-root` path had no lock at all: concurrent runs ran `lake build`
in the checkout at the same time.

Three smaller races in the same code:

* `evictStale` deleted a lock file while holding its flock. A process already blocked on the old
  inode then held a lock that no one else could see.
* `newestSibling` checked that a sibling workspace was unlocked, released the lock and only then
  copied the sibling's build. The sibling could be rebuilt during the copy.
* Lake does not re-hash its outputs. A damaged framework olean was therefore never rebuilt, even though
  the diagnostic says "janus rebuilds the trusted framework on the next run".

### Fix (`cmd/janus/framework.go`, `lock_unix.go`, `lock_other.go`, `verify.go`, `blockers.go`, `consumer.go`, `batch.go`)

* **Readers hold a shared lock for the whole use.** A verification takes `LOCK_SH` on the
  build's lock file and keeps it until its last pin check (`libraryRoot`'s cleanup). A consumer
  workspace keeps it until the base has been copied and compared. Every **writer** (the sync
  plus `lake build`, `blockers`' decoder build, eviction) takes `LOCK_EX`. Nothing therefore
  writes to a build while a verification uses it.
* **A ready stamp, so that readers never write and never wait for each other.** A writer
  records the framework sha, the manifest hash, the Lake targets it built and the pins of the
  result in `<base>.ready` (`<checkout>/.lake/janus-framework.ready` for a directory framework),
  written atomically. A reader whose sources equal the framework byte for byte (embedded
  framework), whose stamp matches and whose current pins equal the stamped ones uses the build
  under `LOCK_SH` alone. Otherwise it upgrades to `LOCK_EX`, repairs and rebuilds, re-stamps,
  and goes back to `LOCK_SH`. This repeats up to 3 times, then fails with a clear message.
  Builds only grow their target set (`janus-decode` stays stamped).
* **Repair actually repairs.** Before Lake runs, the writer removes every framework module whose data no
  longer matches the previous stamp (`changedModules`, `removeModuleOutputs`), so Lake compiles
  it again from source.
* **The lock is re-checked by inode** (`lockFileMode`). After the flock is granted, the path must
  still name the locked file, otherwise the lock is taken again. Eviction can therefore delete lock
  files safely. A base in use is share-locked, so eviction's non-blocking `LOCK_EX` fails and the
  base is kept.
* `newestSibling` returns the sibling **locked**, and the copy runs under that lock.
* `janus blockers` gets its decoder via `findJanusRoot(…, "janus-decode")`. The decoder is built
  under `LOCK_EX` and run under `LOCK_SH`.

Processes running a janus binary from before this fix take no shared lock. They can still be
disturbed by a writer, but they never disturb a new reader, because their builds take the
exclusive lock. They fail closed as before.

### Regression rows

* `TestConcurrentVerify` runs real, separate janus processes. It drops the base's stamp and
  `Janus.Tools.Decode`, then runs 6 verifies (Add ×3 on one artifact, Max, Mul64, Add128) with
  staggered starts, `janus blockers` (which must rebuild the decoder in the base), and 2 late
  verifies, all at once. Then 4 verifies plus blockers on a `--janus-root` checkout. All must
  succeed, and the stamp must list `janus-decode`. With the shared lock disabled
  (`libraryRoot` releasing at once), the test fails with exactly the reported error ("verify#0
  Add failed … unexpected Janus/Tools/Decode.olean", 4 of 6). With the fix it passes (160 s).
* `TestForeignFrameworkWriteDetected` checks that a write which bypasses the lock is still
  detected. A proof compiled with `--unsafe-no-sandbox` appends to the base's
  `Janus/Tools/Audit.olean` from `#eval`. The run must fail with "Stage: framework integrity …
  modified Janus/Tools/Audit.olean". The next verification must succeed, and it rebuilds the
  olean to its original bytes (the repair path).
* `audit/rt-asl/run.sh` row C1 runs both tests.

---

## A1 (blocked): `Rel` is a function onto X0–X30, SP, PC, NZCV

`Rel js s` means `gprVal s i = some (js.regs i)` for i < 31, `SP_EL0 = some js.sp`,
`_PC = some js.pc`, and a PSTATE with `SP = 0`, `EL = 0`, `nRW = 0` and N/Z/C/V equal to Janus'
flags. `RelMeaning.lean` proves the following:

* `Rel.unique`: `Rel js s → Rel js' s →` the two agree on every register below 31, SP, PC and
  flags. So `Rel` is a (partial) function from Sail states to that part of the Janus state, in
  the direction the transfers need: a statement about `js'` with `Rel js' s'` is a statement
  about `s'`.
* `Rel.no_two_regs`, `no_two_sp`, `no_two_pc`, `no_two_flags`: no Sail state relates two Janus
  states that differ in one of these.
* `Rel.ignores_mem`: what `Rel` does not see. Any memory, V registers, TPIDR_EL0 and DCZID
  relate to the same `s`. This is right for the proved classes, which touch none of them, and it
  is the source of A4.

## A2 (blocked): the hypotheses are satisfiable for every state

`rel_cfg_satisfiable : ∀ js, ∃ s, Rel js s ∧ LinuxEL0Config s` holds with an explicit witness
`wit js`. It is the empty Sail state with the 24 configuration registers at `janus_init`'s
values (the `FeatureImpl` vector built from `cfgFeaturesOff`, proved to agree with `cfgFeat` for
all 259 features by kernel evaluation), Janus' GPRs, SP_EL0, PC, and PSTATE at EL0t with Janus'
NZCV. The predicate's conjuncts are therefore not contradictory. No `*_agree`, `run_agree` or
`correctness_asl` holds vacuously. This complements the compiled `cfgOk` check of
`janus-asl-check`, which is a test and not a proof.

## A3 (blocked): the example transfers say something about the ASL alone

`Add_pure_asl` restates `JanusASL.Examples.Add.correctness_asl` with no Janus state anywhere.
Take any Sail state with `LinuxEL0Config` in which every GPR and SP_EL0 is present, X0 = x,
X1 = y, X30 = ret (an admissible return address) and PC = the entry of Add. Then `aslRun`
returns to `ret` with X0 = (x + y) mod 2^64. The proof constructs the Janus state from the Sail
state (`ofSail`, `ofSail_rel`). The corollaries are thus genuine statements about the generated
ASL, under exactly the stated hypotheses. Remaining scope, as documented in docs/ASL.md: words
come from the program's `fetch`, not from the ASL's translated instruction fetch, and Janus
faults (`.error`) are not covered.

## A4 (low, open): `Ensures.toASL` and postconditions about memory

`Ensures.toASL` concludes `∃ js', Rel js' s' ∧ … ∧ post js js'`. `Rel` relates only registers,
SP, PC and NZCV (A1). A postcondition about `js'.mem` or `js'.vregs` therefore constrains
nothing in `s'`, yet the docstring calls the result "the same statement about the ASL". All four
shipped examples have register-only postconditions, so their corollaries are faithful. Suggested
fix (sent to the ASL agent): restrict the corollary to postconditions that depend only on
X0–X30/SP/PC/NZCV, or say so in the docstring and in docs/ASL.md.

## A5 (blocked): the Sail backend patches against Sail's C backend

`audit/rt-asl/sail/patches.sail` exercises each JanusASL fix. The same functions are compiled by
Sail 0.20.3 with both patches, once with the C backend (gcc + gmp) and once with the Lean
backend (built against the pinned lean-sail), and run on the same inputs:

| probe | patch | inputs | Lean = C |
|---|---|---:|---|
| effectful `int` let whose first branch is `unsigned` (the `asl_Int` shape) | 5 (integer lets) | 256 | yes |
| one-bit and two-bit vector literals `[v[3]]`, `[v[7], v[0]]` | 1 | 256 | yes |
| `(hi @ lo) = v` as a statement, in a block, in an `if`, in a `foreach` | 4 (`rewrite_var_updates`) | 4 × 256 | yes |
| assignments in `if`/`match` branches bound by `let` | (pre-existing case) | 2 × 256 | yes |
| `RoundTowardsZero(Real(a)/Real(b))` for 64-bit and 80-bit operands, negative cases, `INT_MIN/-1` | 6 (`Rat`) | 7 | yes |
| `pow_real` with negative and positive exponents, negative base | 6 | 3 | yes |

`FakeReal.lean` was also read line by line. `round_down`/`round_up` are `Rat.floor`/`Rat.ceil`
(Sail C: `mpq` floor/ceil). `abs`, comparisons and `to_real` are exact. `real_power x n` is
`x ^ n` over `Rat` (checked: `2^-3 = 1/8`, `(-2)^3 = -8`). Only `sqrt_real` is inexact, and it
is not reached (it does not occur in the generated model). `real_power` is reached, by the FP
helpers (`FPRound`, `FPUnpack`, `2^1000000` for infinities), which are outside the proved
subset. Patches 1–3 only change printing (a one-bit vector is its bit; parenthesised `do`
branches; `(← do e)` fields). None of them changes a bit-vector operation.

## C2 (low, latent): block-initialized `let`/`var` loses its assignments

The probes found one construct that the patched Lean backend still translates wrongly:

```sail
var hi : bits(4) = 0x0;
let t : int = { hi = v[7 .. 4]; unsigned(hi) };   // also: var t : int = { hi = …; 3 }
t * 1000 + unsigned(hi)                          // C: hi updated; Lean: hi still 0x0
```

The generated Lean rebinds `hi` inside the initializer, and the update never escapes:

```lean
let t : Int :=
  let hi : (BitVec 4) := (Sail.BitVec.extractLsb v 7 4)
  (BitVec.toNatInt hi)
((t *i 1000) +i (BitVec.toNatInt hi))
```

Fix 4 handles only a `let` whose binding *and* body both update variables. In this shape only
the binding does, and the Lean pipeline omits `letbind_effects`. A first attempt at a fix (a
`rewrite_var_updates` case for "only the binding updates") had no effect. The update is lost in
an earlier rewrite, so no patch is proposed here.

**Not reached.** Neither sail-arm's sources nor JanusASL's splices and harness contain a
`let`/`var` whose initializer is a block (`run.sh` greps them: 0). The constructs that Sail's own
rewrites produce from sail-arm (concatenation assignments as statements, in branches, in loops)
are translated correctly (A5). A future splice or harness change in this shape would compile and
compute wrong values, as bugs 4–6 did. The row keeps the reproduction live and reports "fixed"
once the backend translates it correctly. Sent to the ASL agent.

## A6 (medium, open): the JanusASL audit does not pin what it audits

`scripts/asl.sh prove` runs `JanusASL/Audit.lean`. It walks the environment and checks the
axioms of every `JanusASL.*` constant whose name ends in `_agree`, `_asl` or `toASL`. The
JanusASL theorems do **not** go through `janus verify`'s trusted auditor: there is no
statement identity, no sandbox and no olean pins. Gaps:

* a documented theorem that is deleted or renamed only lowers the printed count ("audited 39"),
  and nothing fails;
* the statements are never looked at. An extra hypothesis, a weaker conclusion or a new
  `trivial_agree : True` passes and counts;
* the selection is by suffix, so the documented set and the audited set can drift apart.

None of this is exploited today. All 39 theorems are present, are theorems, use only `propext`,
`Classical.choice` and `Quot.sound`, and their statements (reviewed for this round, and the
branch hypotheses checked for satisfiability via A2) are the ones docs/ASL.md describes.
`audit/rt-asl/AuditStrict.lean` closes the gap as a row. It takes an explicit list of the 39
names, each must be a `theorem` with standard axioms, any unlisted `JanusASL.*` declaration with
those suffixes fails, and every statement is printed. `run.sh` compares the statements with the
reviewed copy `audit/rt-asl/asl-statements.golden`, so any change to a statement must be
reviewed again. Suggested to the ASL agent: adopt it as `JanusASL/Audit.lean`.

## A7 (blocked): kernel replay

`lake env leanchecker JanusASL.Proofs` replays every proof module against the kernel (about 75 s,
50 s of it `Bitmask.lean`'s `decide +kernel`). It passes. Note: `leanchecker JanusASL` also scans
stale oleans on the search path. In a build directory reused from the aslverify branch, it fails
on that branch's `JanusASL.Verify` ("unknown constant JanusAudit.aslCorollary"). The runner
therefore replays the `JanusASL.Proofs` prefix, and the ASL agent was told about it.

## A8 (info): is `LinuxEL0Config` faithful to Linux EL0?

Values pinned (decoded from `janus_init`) compared with Linux 6.x arm64:

| item | config | Linux 6.x EL0 | effect on the proofs |
|---|---|---|---|
| TCR_EL1.TBI0 / TBI1 / TBID0 | 1 / 0 / 0 | TBI0 = 1 always (tagged-address ABI), TBI1 only with KASAN SW tags, TBID0 = 0 | faithful. `AArch64_BranchAddr` keeps an untagged target unchanged (bit 55 = 1 selects TBI1 = 0); tagged targets are excluded and Janus faults on them |
| HCR_EL2.E2H / TGE | 0 / 0 | VHE hosts run EL0 with E2H = TGE = 1 (EL2&0 regime, TCR_EL2); nVHE hosts and KVM guests as here | **scope**: the theorems cover nVHE/guest Linux. A VHE host state does not satisfy the predicate (no claim is made about it, so nothing is false). docs/ASL.md should say so |
| SCTLR_EL1 | M C I SA SA0 UCT DZE UCI nTWE EnIA/IB/DA/DB EPAN ATA0 …, BT0 = 0, TCF0 = 0 | the same family (`INIT_SCTLR_EL1_MMU_ON`); BT0 = 0 as Linux; TCF0 per process (MTE off by default) | none on integer/branch results |
| PSTATE.BTYPE / PAN / UAO / DIT / TCO / SSBS | 0 | ERET from the kernel; DIT/SSBS per process | not read by the proved classes |
| `InGuardedPage = false` | — | a page is guarded only with `PROT_BTI`, which the loader sets for ELF files with the GNU_PROPERTY_AARCH64_FEATURE_1_BTI note. Go's linker emits no BTI landing pads and no such note: `artifacts/examples-arm64` has only `.note.go.buildid` and `.note.gnu.build-id`, and no `PT_GNU_PROPERTY` (row A8) | faithful for Go binaries. `BranchTargetCheck` needs `InGuardedPage` |
| features off | AArch32 EL1–3, DoubleLock, ETMv4, CONSTPACFIELD, EPAC, PACIMP, PACQARMA3, #258 | mutually exclusive PAC algorithm choices and AArch32 | the rest is on (BTI, GCS, SPE, BRBE, MTE …). The branch path runs **more** ASL than on a minimal CPU, not less: no feature check is short-cut by disabling it |
| SPE / BRBE / GCS registers | 0 | off for a normal process (GCS only after `prctl`, which Go does not use) | the bookkeeping proved not to touch GPRs/SP/PSTATE |

## A9 (blocked): slicing and the harness

* **Slicing** keeps every decode-clause pattern and guard verbatim. A clause outside `keep.txt`
  keeps its `SEE` line and gets an `ImplementationDefined("janus-excluded …")` body. Sail's own
  callgraph slice then removes only unreachable definitions, which cannot change the meaning of
  what remains. The proofs are about the generated functions themselves, and `chain.py`'s
  dispatch lemmas refute every earlier clause's pattern. A proved word therefore reaches its own
  clause in the generated model, and the model's clause order is Arm's. The 22 literal patterns
  are rewritten MSB-first to bit lists, the convention of every other clause. The `sys` class
  agrees on 8,792 corpus cases.
* **Splices.** `AArch64_TakeException` is not on any `Janus_OK` path. The PAC nibble helpers are
  reachable only for the PAC branch variants. The sysreg dispatch is not read by a proved class.
* **Harness compared with sail-arm's `__InstructionExecute`.** `janus_step` omits `__FetchInstr`,
  `PMUEvent`, `SPEPreExecution`/`SPEPostExecution`, `InGuardedPage := false`,
  `PSTATE.BTYPE := BTypeNext`, `AArch32_ITAdvance` and `SSAdvance`. None of these writes X0–X30,
  SP, PC or NZCV on a completed EL0 A64 instruction with SPE and MDSCR_EL1.SS off. The BTYPE update matters only
  together with `InGuardedPage` (A8). `aslRun`'s use of the program's `fetch` is documented.

---

## Follow-up by the ASL agent (branch agent/asl, not yet merged here)

The findings were sent to the ASL agent. It reports the following:

* A6: `JanusASL/Audit.lean` now takes an explicit list of 41 names (the 39 above plus the new
  `ldstUImm_agree` and `ldstImm9_agree`). Each must exist as a theorem, unlisted names fail, and
  the statements are printed.
* A4 and A8: docs/ASL.md now says that `Rel` is register-only (so `Ensures.toASL` transfers
  only the register part of a postcondition) and that the predicate describes nVHE or guest
  Linux.
* C2: there will be no let/var-bound blocks in new splice code. The patch set is unchanged.

**When agent/asl is merged**, `LinuxEL0Config` has the fields this round's witness already
sets (`mpam3`, `mpam2`, `tstate`), and the load/store theorems add `MemRel`/`UserMapped`
hypotheses. Extend `expected` in `audit/rt-asl/AuditStrict.lean` with the two new theorems,
review their statements (in particular that `MemRel ∧ UserMapped` is satisfiable, as A2 does for
`Rel ∧ LinuxEL0Config`) and regenerate `asl-statements.golden`. The A6 row fails until then,
on purpose.

## Running

```
audit/rt-asl/run.sh            # every row (~10 min; the Go concurrency tests take ~6)
RT_ASL_SKIP_GO=1 audit/rt-asl/run.sh
```

The Sail rows need the pinned toolchain (`scripts/asl.sh deps`, `DEPS`). Without it they are
skipped.
