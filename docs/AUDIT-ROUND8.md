# Janus soundness audit, round 8

Round 8 attacks the residuals that round 7 listed (§6 of docs/AUDIT-ROUND7.md: the toolchain
part of the cache keys, the unauthenticated trusted-compile cache) and two directions nobody had
tried: object names inside a statement, and a cache directory that another user can write. It
also keeps a regression row for kernel native reduction.

Guarantee under review, as before: *if `janus verify` (or `verify-batch`, or consumer
`--proof-root`) prints `Verified`, everything it reports (the statement, the definitions,
`janus explain`, verified.json) is an exact and honest account of a theorem that holds for the
actual bytes of the binary under the documented semantics.*

The rows are in `audit/round8/` (`attacks/`, `govers/`, `run-round8.sh`), plus
`TestRound8ToolchainCacheID`, `TestRound8TrustedManifestMAC` and `TestRound8CacheRootPrivate` in
`cmd/janus/round8_test.go`. Severities are as in earlier rounds. **Critical** means a misleading
account prints `Verified`. **High** means a false claim about the binary, or a forged result,
prints `Verified`. **Low** means hygiene.

| # | Severity | Finding | Status | Rows |
|---|----------|---------|--------|------|
| I1 | **critical** (readability) | **Object names that resolve to nothing.** `ItabIs`, `segAddr` and the other name lookups default to `False` or `0` when no object has the name. A lookalike (`MulHаsher`, Cyrillic `а`), absent or misspelt name, or a lookup in another list than `Extracted.program.data`, makes a statement vacuous or about address 0 while it reads as a claim about that object. | **fixed** (auditor check) | I1a–I1f, 3 controls |
| C1 | **high** (multi-user) | **The cache root was not required to be private.** A `JANUS_CACHE_DIR` (or shared `XDG_CACHE_HOME`) that another user can write, or one they created first, lets them choose the result-cache key and forge `Cached: Verified`, or plant a framework build or a trusted compile. A readable key leaks the same power. | **fixed** | C1a–C1c, control, unit rows |
| L1 | low | **The toolchain part of the cache keys was the version string and the paths of `lean`/`leanchecker`.** The elaborator and the kernel live in `lib/lean/libleanshared.so`; a toolchain rebuilt in place under the same version gave stale hits in every cache. | **fixed** | unit row |
| M1 | low (hardening) | **Trusted-compile manifests had SHA-256s but no MAC.** A same-user write outside the sandbox could plant an entry. Out of the threat model like the replay cache, but the result cache already had a key. | **hardened** | M1 rows, unit row |
| N1 | none | `Lean.reduceBool` with `@[implemented_by]` proves `False`. It depends on `Lean.ofReduceBool`/`Lean.trustCompiler`, which the axiom allow-list rejects. | **no issue** (regression row) | N1a |
| G3 | **high** | **A go1.25 binary labelled go1.26** defines the go1.26-only stub name `runtime.panicSimdImm` itself, and round 7's stub gate (which reads the Go version from build info) takes it for the runtime's panic stub: "every call of Add panics" verifies for an Add that returns `x + y`. | **fixed**: stubs pinned to the runtime's normalized code plus pclntab package/file (`cmd/janus/stubpin.go`, SOUNDNESS.md item 3) | G3a (must be rejected at extraction); audit/round7 G3a rows |

**This round found one critical readability item (I1) and one high item (C1), both fixed here,
and one high binary-side item (G3), fixed by pinning stubs to the runtime's code.** L1 and M1 close round 7's
residuals.

---

## I1 (CRITICAL readability, fixed): object names that resolve to nothing

The framework's name lookups (`Janus.Spec.ItabIs ds m tab name`, `dataNamed`, `dataAddr`,
`dataLen`, `dataWord`, `itabFun`, `segWord`, `Janus.Tactic.segAddr`, `Janus.Amd64.Tactic.segAddr`,
and amd64 `dataBase p i` by index) fall back to a default when no object matches: `ItabIs` is
`False`, an address is `0`. The statement still round-trips exactly, since Lean reads the
name the same way, and it reads as a claim about the named object.

* **I1a** `ItabIs Extracted.program.data s.mem tab "go:itab.*example.com/basic.MulHаsher,…"`
  (Cyrillic `а`, U+0430) as the precondition of HashWith. No data object has that name, so the
  precondition is `False` and "HashWith(MulHasher) returns 0" is vacuous. The proof is three
  lines (`dataNamed … = none := by rfl`).
* **I1b** the ASCII value-receiver itab `go:itab.example.com/basic.MulHasher,…` (no `*`), which
  the binary does not have. Same effect.
* **I1c** `segAddr Extracted.program "example.com/basic.Mul"` in Add's postcondition. The
  extraction of Add has no such function, so the address is 0 and "Add returns x + y + &Mul"
  holds.
* **I1d** the real itab name, looked up in `[]` instead of `Extracted.program.data`.
* **I1e** the lookalike name passed through the parameter of a proof-local `def IsHasher`.
* **I1f** (amd64) `dataBase Extracted.program 3` in Add's postcondition; amd64 Add has no data
  object, so it is 0.

Each attack's proof compiles (the audit runs only after it does); the rows require the I1
diagnostic, so none of them is blocked for an unrelated reason.

**Fix** (`Janus/Tools/Audit.lean`, `checkSymbolRefs`, run by `cleanEnvAndPrint`). After the
statement's proof-local definitions are expanded (`expandLocals`, beta-reducing their
applications, so a name passed through an `abbrev` or a parameter is seen at its use), every
application of one of the lookups above must have

* its program or data argument definitionally equal to `Extracted.program` (or
  `Extracted.program.data`); for the program-taking lookups both `segments` and `data` are
  compared;
* its name argument a closed term that reduces to a string literal naming a data object (for
  `segAddr`/`segWord`: a code segment) of `Extracted.program`, read from the extraction itself
  (`symTable`); an `ItabIs` name must also be a static itab (`go:itab.`);
* for `dataBase`, a numeral index below the number of data objects.

An unapplied or under-applied lookup is rejected. Every dependency definition the statement uses
is checked the same way. The diagnostic names the lookup and the offending name, for example:
`the statement uses Janus.Spec.ItabIs with the name "go:itab.*example.com/basic.MulHаsher,…",
but the extracted program has no data object of that name, so the lookup silently defaults`.

**Controls** (must verify): `examples/proofs/HashWith.lean` (the itab names through
`abbrev mulItab`/`rotItab`), `Proof.add_summary` of `examples/proofs/AddThree.lean` (`segAddr` of
a real callee in the statement) and amd64 `HexDigit` (`dataBase Extracted.program 0`). Every
shipped example verifies with the check (`scripts/verify-all-examples.sh`, below).

**verify-all-examples.sh gap.** Its arm64 list predated the dynamic-call examples and omitted
`HashWith`, `HashTwice`, `MapSum` and `DeferAdd`, the four arm64 examples whose statements use
`ItabIs`/`FuncvalIs`. They are now in the list, so the suite covers the check on arm64 too.

## C1 (HIGH, fixed): the cache root must be private

The result cache, the trusted-compile and replay caches and the framework build are trusted
state. Their protection against sandboxed code is that sandboxes see them read-only or not at
all, and the result-cache key is hidden by a tmpfs. Neither helps against another *user* who can
write the directory: a cache under a shared `HOME`/`XDG_CACHE_HOME`, a group-writable directory,
or a `JANUS_CACHE_DIR` in a world-writable place that someone else created first lets that user
choose the HMAC key and forge any `Cached: Verified` report. A key readable by others gives the
same power.

**Fix** (`cmd/janus/cachesafety.go`, `checkCacheRoot` and `readPrivateFile`; called by
`libraryRoot`, `openWorkspace` and `resultHMACKey`). Before the cache is used:

* the cache root (after resolving symbolic links; it is created 0700 if missing) is a directory
  owned by the user, not writable by group or others;
* each directory janus uses below it (`v1`, `v1/result`, `v1/trusted`, `v1/replay`,
  `v1/framework`, `v1/consumer`, `v1/tmp`, `v1/run`), if present, is a real directory (not a
  symbolic link) with the same owner and mode restriction;
* every ancestor of the root is owned by the user or root and is not group- or other-writable
  unless it has the sticky bit (as `/tmp`: others cannot rename or remove our entries);
* `v1/result` is 0700, and its `.key` is a regular file owned by the user, of mode 0600 or
  stricter, of 32 bytes, not a link;
* cache entries, manifests and the key are opened with `O_NOFOLLOW` and must be regular files
  owned by the user.

A violation is an `Invalid` diagnostic (stage `cache safety`) that names the path and the
problem, with a hint (`Set JANUS_CACHE_DIR to a directory only you can write …`). An unsafe key
used to make the result cache silently miss; it now stops the verification, since a key others
could read may already have been used to forge entries.

Rows: **C1a** group-writable root (`mode 770`), **C1b** `v1/trusted` a symbolic link, **C1c**
the key chmod 0644, each with the CLI; **C1_ctl** the same cache once private again verifies.
`TestRound8CacheRootPrivate` also covers an other-writable root, a group-writable parent without
the sticky bit (refused) and with it (accepted), a root reached through a symbolic link
(accepted), a group-writable or non-directory subdirectory, a symlinked key, a short key and a
0755 result directory.

**Tests and exceptions.** The Go test suite's caches are `t.TempDir()` directories (0700 under
the sticky `/tmp`) or `/tmp/janus-test-cache` (owned by the user, 0755); all pass the check, so
no test needed a weaker rule and **no exception was added**.

## L1 (low, fixed): the toolchain's identity in the cache keys

Round 7 §6: the result key and `trustedCacheKey` covered the toolchain version string and the
*paths* of `lean`/`leanchecker`, the replay and early-replay keys only the version. `bin/lean` is
a 9 KB launcher; the elaborator and the kernel are in `lib/lean/libleanshared.so` (233 MB) and
the core library's `.olean` files.

**Fix** (`cmd/janus/leanjob.go`, `toolchain.cacheID`, used by every key: trusted compile, replay,
early replay, result). The identity is the version, the SHA-256 of `bin/lean` and
`bin/leanchecker`, and for every file under `bin/` and `lib/lean/` its path, size, modification
and change times, inode, device and mode (a symbolic link also by its target and the file it
names). Stat data keeps it cheap for 15 000 files; a rewrite changes the change time, which the
writer cannot set back (`touch -d` and `cp -p` restore only the modification time). It is
computed once per run. A toolchain that cannot be walked gets a random identity, so its caches
always miss.

Row: `TestRound8ToolchainCacheID`: the identity and the trusted-compile key change when
`libleanshared.so` is rewritten in place with the same size and its modification time restored,
when a core `.olean` is replaced, when a library or `bin/` file is added, and when a library file
becomes a symbolic link; they are reproducible otherwise.

## M1 (hardening): trusted-compile manifests carry a MAC

**Fix** (`cmd/janus/speed.go`). A manifest now holds `mac`, HMAC-SHA256 of the key and the
pins of its files under the result cache's private key (which no sandboxed process can read).
`readTrustedManifest` accepts an entry only if the MAC verifies; a missing, empty or wrong MAC,
the MAC of another key, or files swapped under an old MAC is a miss. Since a pre-round-8 or
planted entry would otherwise make its key miss forever, `storeTrustedCache` moves an
unauthentic entry aside (atomically) and records the new one.

Rows: **M1_authentic_hit** (a second run reports `trusted compile (cached)`), **M1_missing_mac**
and **M1_bad_mac** (every manifest edited: the next run compiles again and verifies),
**M1_*_replaced** (the run after that hits again). `TestRound8TrustedManifestMAC` adds the
empty MAC, a MAC for another key, swapped file pins, a self-consistent planted manifest without a
MAC, and a changed cache key.

## N1 (no issue): kernel native reduction

`audit/round8/attacks/N1a_reducebool_implemented_by.lean`: `f` unfolds to `false` but is compiled
as `true` (`@[implemented_by g]`). `Lean.reduceBool f = true` by `rfl` (the kernel runs the
compiled code), `Lean.ofReduceBool` turns it into `f = true`, and `f = false` by `rfl`, so
`False`, hence "Add returns x * y". The axiom audit rejects it:
`depends on disallowed axioms: Lean.ofReduceBool, Lean.trustCompiler`. Kept as a regression row
so the reflective tactics (`janus_carry`, `janus_ring`) stay kernel-checked.

## G3 (HIGH, fixed): a go1.25 binary labelled go1.26

Fixture `audit/round8/govers`: package `lib` defines, in assembly, `TEXT runtime·panicSimdImm(SB)`
returning 0, and `main.Add` returns `x + y + lib.Zero()` through it (qemu prints 3). Linked by
go1.25.5, whose runtime has no `panicSimdImm`, the name is the binary's only definition and is
not mangled; `-ldflags=-X=runtime.buildVersion=go1.26.0` labels the binary go1.26. Round 7's G1
gate (exact go1.26 name, go1.26 build info, symbol table, unique name) accepts it as the
runtime's panic stub, and `G3a_spoofed_goversion_stub.lean` (`Panics` for every call of Add)
verifies. This is the residual round 7 recorded under G1 ("Check 2 reads the Go version from
build info"), now demonstrated.

**Fix.** The build-info version plays no part any more: a listed name is a stub only if its
normalized code matches a pin measured from the real go1.26.x runtimes and the pclntab places it
in package `runtime` at the pinned source file (docs/SOUNDNESS.md item 3, `cmd/janus/stubpin.go`,
`scripts/gen-stubpins.sh`). The fixture's `runtime.panicSimdImm` sits in
`example.com/govers/lib/zero_arm64.s` and its hash is not pinned, so extraction fails;
`run-round8.sh` requires that, and audit/round7 has rows for the committed extraction and qemu.

## Regression status

Run one suite at a time on this branch (host shared with other agents):

| Suite | Result |
|---|---|
| `audit/round8/run-round8.sh` | all rows as expected (I1a–f, N1a blocked; controls, M1, C1 and unit rows ok; G3a open at the time; blocked since the stub-pin merge), 368 s |
| `scripts/verify-all-examples.sh` | all ok: 25 arm64 items (with HashWith, HashTwice, MapSum, DeferAdd) and 27 amd64 functions, 590 s at -j 2 |
| `audit/run-all.sh` | no BROKEN row, 282 s |
| `audit/round2…7` | all as expected: 68, 11, 10, 225, 81, 639 s (round 7 with its cache rows) |
| `go vet ./...`, `go test -timeout 60m ./cmd/...` | clean; `ok github.com/Giulio2002/Janus/cmd/janus` 622 s |

## Reproduce

```
audit/round8/run-round8.sh                      # I1, N1, G3, L1/M1/C1
cd cmd/janus && go test -run 'TestRound8' -v .  # the unit rows only
```

The runner builds `audit/round8/bin/janus`, writes under `audit/round8/work/rows/` and uses
private temporary caches under `$TMPDIR` (removed at the end). G3a needs the go1.25.5 toolchain
(`GOTOOLCHAIN=go1.25.5`); without it the row is reported as skipped.
