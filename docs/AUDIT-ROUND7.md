# Janus soundness audit, round 7

This is the seventh independent review. Round 6 closed the instance and round-trip family and
listed some residual risks next to it. This round attacks those residuals and other directions
nobody had tested yet, with live attempts: the binary side beyond stubs (assembly, `//go:linkname`,
build info), bound-variable names, operations whose standard Lean meaning surprises readers, and
dependency definitions.

Guarantee under review: *if `janus verify` (or `verify-batch`, or consumer `--proof-root`)
prints `Verified`, everything it reports (the statement, the definitions, `janus explain`,
verified.json) is an exact and honest account of a theorem that holds for the actual bytes of
the binary under the documented semantics.*

The rows are in `audit/round7/` (`attacks/`, `asmstub/`, `dep/`, `run-round7.sh`), plus
`TestStubKind`, `TestClassifyStub` and `TestTermSafe` in `cmd/janus`. Severities are as in
earlier rounds. **Critical** means a misleading account prints `Verified`. **High** means a false
claim about the binary prints `Verified`. **Low** means hygiene.

| # | Severity | Finding | Status |
|---|----------|---------|--------|
| G1 | **high** | **Stubs by name, in a normally built binary.** Any package can define a Go-assembly `TEXT runtime·panicX(SB)`, or push a Go function with `//go:linkname f runtime.panicX`. Neither needs `-checklinkname=0`. Round 6 classified every `runtime.panic*`/`runtime.morestack*` name without `/` as a stub. So "Add panics on every call" verified for an Add that returns `x + y`. Worse, "Inc never panics" verified for an Inc that panics on every call: its callee was named `runtime.morestack…`, and `NeverPanics` allows reaching `morestack`. | **BROKEN → fixed** |
| H1 | **critical** (readability) | **Bound-variable lookalikes.** `(h : ∀ ο : BitVec 64, ο = o)`, with a Greek omicron, reads as the triviality `∀ o, o = o`. It actually says every value equals the parameter `o`, which is false, so the theorem is vacuous. "Add returns `x * y`" verified with this statement. `«о»` (Cyrillic) and `«o​»` (zero-width space) binders did the same. | **BROKEN → fixed** |
| J1 | high (readability) | **Dependency definition bodies were not shown.** A pinned dependency's `MisLib.mul` is documented as "the product" but its body is `a + b`. The statement `s'.regs 0 = MisLib.mul x y` verified, and the report listed only the name. | **hazard → fixed** (bodies disclosed) |
| K1 | hazard | **Standard operations that read misleadingly.** One true statement reads "Add's result is 0 and equals `x`": `r * 2 ^ 64 = 0`, `r.toNat / 0 = 0` and `(x + y) % 2^64 - r.toNat = 0`. It verifies, and that is correct Lean. | **hazard → mitigated** (notes in the report) |
| G2 | low (documented) | **The entry symbol and build info are labels the binary carries.** A `//go:linkname` push names a function of another module `example.com/basic.Add`. `-ldflags=-X runtime.modinfo=…` or `-X runtime.buildVersion=…` rewrites the module path, its version and the Go version that `debug/buildinfo` reports. | documented |
| T1 | low | `termSafe` escaped only the bidi overrides and isolates. It now escapes every format (Cf) character, including LRE/RLE/PDF, LRM/RLM and zero-width characters. | hardened |
| D* | none | `.rodata` copied as data, data labels, reachability, `withExit` | no issue (§5) |

**This round found BROKEN items: G1 (high) and H1 (critical, readability). Both are fixed and
have regression rows. J1 and K1 are hazards under the stated guarantee and are mitigated.**

---

## G1 (HIGH, BROKEN → fixed): runtime stubs named by any package

Fixture: `audit/round7/asmstub`, a module built with plain `go build -trimpath` (go1.26.0,
linux/arm64). Its package `lib` has an assembly file `zero_arm64.s` with:

* `TEXT runtime·panicJanusR7(SB)`: `MOVD $0, R0; RET`. `lib.Zero` calls it, and `main.Add(x, y)`
  returns `x + y + lib.Zero()`.
* `TEXT runtime·morestackJanusR7(SB)`: calls the Go function `lib.boom`, which does
  `panic("boom")`. `lib.Boom` calls it, and `main.Inc(x)` returns `x + 1 + lib.Boom()`.

The linker accepts both. Their ELF symbols are `runtime.panicJanusR7` and
`runtime.morestackJanusR7`, with no `/`. On qemu-aarch64, `Add(1, 2)` prints 3 and `Inc` prints
`panic: boom`. Before the fix, `janus extract` printed `stub … panic runtime.panicJanusR7` and
`stub … morestack runtime.morestackJanusR7`, and:

* **G1a**, `Panics (Extracted.program.withExit ret) s` for every call of Add, verified.
* **G1b**, `NeverPanics (Extracted.program.withExit ret) s` for every call of Inc, verified.
  Hardware panics on every call. This is a false "never panics" claim, the strongest kind
  `NeverPanics` makes.

Other routes I tried to the same effect:

* `//go:linkname f runtime.panicIndex` with a Go body. The name is absent from the go1.26
  runtime, so it links unmangled.
* An assembly function with a real stub's name, such as `runtime·panicdivide`. It links as
  ABI0 beside the runtime's ABIInternal one, under the mangled name `runtime.panicdivide.abi0`.
  Before the fix, `stubKind` stripped `.abi0` and accepted it.
* `//go:linkname f runtime.morestack_noctxt.abi0`. This gives a **second** symbol with exactly
  the real stub's name.
* `-ldflags=-s`. The pclntab carries no ABI suffix, so the ABI0 `runtime.panicSimdImm` from
  `lib` appears unmangled.

Routes the toolchain rejects: a second ABIInternal definition of a runtime function
(`//go:linkname f runtime.panicdivide`, or `runtime.gopanic`, `runtime.panicBounds`), and a
second ABI0 `runtime·morestack_noctxt`. Each fails with "duplicated definition of symbol".

**Fix** (`cmd/janus/extract.go`, `classifyStub`, shared by arm64 and amd64). A branch target
is a stub only when all of these hold:

1. Its ELF name is on an **exact** list. The list holds the go1.26 runtime's
   `panic*`/`goPanic*`/`gopanic` functions (from `go tool nm` on the runtime archive for go1.26.0
   and go1.26.10, linux/arm64 and linux/amd64; the two architectures and releases agree), minus
   `panicCheck1/2` (they return) and `morestackc` (a throw that only runtime code calls). It also
   holds `runtime.morestack.abi0` and `runtime.morestack_noctxt.abi0`, with their ABI0 suffix.
   No suffix is stripped.
2. The binary was built with go1.26 (`go1.26`, `go1.26.N` or `go1.26rcN`).
3. Its names come from the ELF symbol table, not from the pclntab.
4. No other function has the same name.

Under these conditions the runtime defines every listed name itself. Another definition with
the same ABI is therefore a link error, and one with the other ABI gets a mangled name that is
not on the list. A listed name that fails check 2, 3 or 4 is an extraction error, with a "Next"
hint. An unlisted name that looks like a stub in a pclntab-only binary is also an error.
Extracting the runtime function as code would silently give a different, much larger program.
After the fix, `runtime.panicJanusR7` and `runtime.morestackJanusR7` are extracted as code, and
Inc reaches the real `runtime.gopanic` stub. G1a and G1b no longer check. **G1c**
(`Returns … s'.regs 0 = x + y` for Add) verifies on the new extraction. **G1d** (a
`janusdup` build with the duplicate `runtime.morestack_noctxt.abi0`) and **G1e** (`-ldflags=-s`)
are rejected at extraction.

**Residual.** Check 2 reads the Go version from build info, and `-X runtime.buildVersion=go1.26.0`
rewrites it (G2). To exploit that, an attacker would need a binary linked by a *different* release,
labelled go1.26, whose runtime lacks a listed name, plus a definition of that name. A
cross-check would need data `-X` cannot reach. The DWARF producer string is one candidate, but
`-w` removes it. Out of the threat model (docs/AUDIT.md §4: the binary is the subject), but
recorded here.

## H1 (CRITICAL readability, BROKEN → fixed): bound-variable lookalikes

Round 6 A5 called bound-variable lookalikes low, because "each binder is printed where it is
introduced, with its type". The live row shows that seeing the binder is not enough:

```
Verified: Proof.correctness
  Statement:
    Proof.correctness (o x y : BitVec 64) (h : ∀ (ο : BitVec 64), ο = o) : Janus.GoABI.Ensures Extracted.program Extracted.entry [x, y] (fun x => True) fun x_1 s' => s'.regs 0 = x * y
```

The text reads "for any `o`, given the trivial `∀ o, o = o`, Add returns `x * y`". The
hypothesis is false, so the claim is vacuous. Add adds. The text round-trips exactly, since Lean
reads it the same way. `«о»` (Cyrillic U+043E, allowed only between guillemets) and `«o​»`
(U+200B) verified the same way (rows H1c and H1d).

**Fix** (`Janus/Tools/Audit.lean`, `checkBinderNames`). It runs on the statement and on every
disclosed proof-local type and value, and rejects:

* a binder name with characters other than Lean identifier letters (`isLetterLike`, which
  covers Greek and letterlike symbols), ASCII digits and `_ ' ! ?` and subscripts. This rejects
  Cyrillic, zero-width, combining and bidi characters in `«…»` binders;
* two **distinct** binder names of one term that are equal once lookalike letters are folded
  to Latin (`latinLookalike` from round 6). This rejects `o` and `ο`, and `x` and `χ`.

Greek binders that imitate nothing in scope, such as `(α β : BitVec 64) … fun x σ => …`, still
verify (row **H1b**). No shipped example or test is affected.

**String literals.** No statement in the examples uses one. Round 6 already escapes the bidi
overrides in report text, and this round's T1 escapes every format character, so an RLO or a
zero-width character inside a literal prints as `\u{…}`.

## J1 (hazard → fixed): dependency definition bodies

Fixture: `audit/round7/dep`, a pinned local git dependency `MisLib` with
`/-- The product a * b … -/ def mul (a b : BitVec 64) : BitVec 64 := a + b`, and a consumer
theorem `s'.regs 0 = MisLib.mul x y` about Add. Before the fix, the report said only
`Dependency constants in the statement: MisLib.mul (def, MisLib)`. A reader trusting the name
reads "Add returns x * y". The guarantee asks the reader to read "dependency notation", but
nothing showed what the dependency's definition says.

**Fix.** The auditor now prints every dependency `def` the statement reaches, with its body, in
the clean environment, where the dependency's notation and delaborators do not apply. The new
record field is `externalDefinitions`. `verify`, `verify-batch` (through the consumer report) and
`explain` show it as "Dependency definitions used by the statement (pinned source; part of its
meaning)", and verified.json carries `dependencyDefinitions`. The bodies are shown, not
round-tripped. Round 5's instance rules for dependency constants are unchanged, and a dependency
body may use instances. Row **J1a**:

```
  Dependency definitions used by the statement (pinned source; part of its meaning):
    MisLib.mul : BitVec (64 : Nat) → BitVec (64 : Nat) → BitVec (64 : Nat) := fun (a b : BitVec (64 : Nat)) => a + b
```

## K1 (hazard → mitigated): operations that read misleadingly

The most misleading true statement I could build from standard operations, for Add (row **K1a**):

```
Ensures … fun x_1 s' => s'.regs 0 * 2 ^ 64 = 0 ∧ BitVec.toNat (s'.regs 0) / 0 = 0 ∧ (x.toNat + y.toNat) % 2 ^ 64 - BitVec.toNat (s'.regs 0) = 0
```

As school arithmetic, it reads "the result is 0" and "the result equals x + y and is at most
it" (the conclusion would be the opposite if `-` meant integer subtraction). In Lean, `2 ^ 64` is
`0` at `BitVec 64`, `/ 0` is `0`, and `Nat` subtraction truncates. The statement is true, it
round-trips, and it is "Lean's standard meaning". So this is not BROKEN, but the report did not
help the reader.

**Mitigation.** The auditor scans the statement and every disclosed body, and returns notes.
They are warnings, never rejections, so honest examples are unaffected. Notes are printed under
"Notes (standard Lean meaning that may read unexpectedly; not errors)" in `verify`, under "Read
with care" in `explain`, and as `notes` in verified.json. Flagged operations:

* `-` at `Nat` (and `Nat.sub`, `Nat.pred`): truncates at 0;
* `/` and `%` at `Nat`, `Int` or a fixed-width type, when the divisor is not syntactically
  nonzero (a nonzero numeral, or a power or product of such): `a / 0 = 0`;
* `^` at a wrapping type (`BitVec w`, `Fin n`, `UIntN`, `IntN`): `(2 : BitVec 64) ^ 64 = 0`;
* `xs[i]!`: `default` when out of bounds;
* `Int.toNat`: negative values map to 0.

Wrapping `+` and `*` at `BitVec` are not flagged, because they are the meaning of almost every
honest arm64 statement. Unsigned `<` is not flagged either. `K1b` checks that the shipped Add
proof gets no notes. The full example suites run with notes enabled. Proposed next steps, not
implemented: a `janus explain --lint` that also flags wrapping `+`/`*` at `BitVec` in
*hypotheses*, where wrapping more often hides a weaker condition.

## G2 (low, documented): entry symbol and build info are binary-carried labels

* **Entry label.** `lib.fakeAdd` is pushed with `//go:linkname fakeAdd example.com/basic.Add`.
  The module `example.com/basic` is not in the binary. `janus extract … example.com/basic.Add`
  works, and **G2a** ("returns 42") verifies with `Entry: example.com/basic.Add` and
  `Module: example.com/asmstub`.
* **Build info.** `-ldflags=-X runtime.modinfo=…` (16 bytes of padding, the text, 16 bytes of
  padding) makes `debug/buildinfo` and `go version -m` report any main module path, version and
  sum, and `-X runtime.buildVersion=…` any Go version. With a fake `GOOS`/`GOARCH` the binary is
  still rejected by the ELF machine check.

So could the reported `Entry: example.com/basic.Add` be wrong about which code was proved? The
code proved is always exactly the bytes at that symbol's address, in the binary whose SHA-256 the
report records. The symbol name, the module path and the Go version are what the binary says
about itself. They are not authenticated, and the binary is the subject, not the adversary
(docs/AUDIT.md §4). They matter for soundness only through G1's Go-version gate (see its
residual).

## 5. Probes with no issue

* **`.rodata` as data overlapping code.** Data is never executable: `fetch` reads only
  `segments`. A literal-pool word copied from `.text` as data (`ldr-literal`) is a read-only
  copy of the same bytes, so code and data may overlap without changing either.
* **Mislabelled data.** A `DataSegment`'s `name` is display only. `DataLoaded` uses `base` and
  `bytes`, both copied by the trusted copier from a non-writable section.
* **Reachability and `withExit`.** A branch outside every known function is unresolved, and
  reaching it is `noCode`, a fault. That makes `Returns` and `NeverPanics` false, never true.
  `RetAddr` excludes code and stub addresses, so `withExit ret` cannot turn an omitted callee
  into a return. A missed *stub* is now an extraction error (G1), never a silent reclassification.
* **Duplicate and aliased symbols.** `lookup` requires a unique entry name. Stubs now require a
  unique name too. Assembly TEXT sizes are computed by the assembler. A function with size 0
  extends to the next symbol, which only makes its segment longer, and those bytes are real code.

## 6. Review of main 1d0b147 (testinfra + memguard): the result cache, the compiled audit and the memory guard

This is a code review, now of the merged tree (main 1d0b147). agent/memguard already ships live rows for the cache
(RC1–RC6 in its own `docs/AUDIT-ROUND7.md`: proof and lakefile probes, a tampered entry, a
stale framework, `--fresh`, `--unsafe-no-sandbox`). This review does not repeat them. It found
**no BROKEN item**.

* **Key coverage (stale hits).** The `verify` options that affect the outcome are `theorem`,
  `proof`, `binary`, `janus-root`, `replay-fresh`, `fresh` and `unsafe-no-sandbox`. Each is
  either in the key or disables the cache. The janus executable's SHA-256 is in the key, so
  any change to the verifier, the auditor rules (this round's G1/H1/J1/K1 included) or the
  embedded framework is a miss. The binary is covered through the recorded SHA-256, after the
  same `check` that re-hashes the binary. After a hit, the extraction, the proof bytes and
  identity.json are read again and compared. Proof-path swaps between hashing and use are covered
  by that comparison.
* **Toolchain (low, doc).** The key and `trustedCacheKey` cover the toolchain's version string
  and the *paths* of `lean`/`leanchecker`. SOUNDNESS.md says "the toolchain version and
  binaries". `bin/lean` is a 9 KB launcher, and the elaborator and kernel live in
  `lib/lean/libleanshared.so` (233 MB), which is not hashed. Rebuilding a toolchain in place
  under the same version would give a stale hit. The toolchain is trusted and read-only to
  sandboxes, so this is in line with the replay cache. Fix: change the wording to "version and
  paths", or add the size, mtime and inode of `libleanshared.so` (cheap) to both keys.
* **Trusted-compile cache.** Entries are protected by location only: the cache is read-only
  to sandboxes, and the manifest holds SHA-256s, not a MAC. A planted entry would need a
  same-user write outside the sandbox, which is out of the threat model, the same as for the
  replay cache. Extracted, JanusTrusted and Proof are still kernel-replayed. For consistency
  with the result cache, a MAC under the same key is recommended.
* **Early replay.** A marker only *skips* the early run (`ran = false`), and `apply` then
  credits nothing. Credit is given only when every early `leanchecker` exited 0, and only to
  modules that a target name-prefixes in the plan. The framework pins are re-checked after
  it. No path was found where a failed or skipped early replay counts as passed.
* **Memory guard: can a kill become "verified"?** No. Every mechanism (cgroup, systemd scope
  with an in-scope supervisor, prlimit) returns a non-nil error for a killed job. The supervisor
  maps a signal to `128+sig`, and a supervisor that writes no stats is a guard error.
  `memOutcome` also turns *any* kill recorded during the run into the resource-limit
  diagnostic, even if a later step passed. `Verified` is printed only after `memOutcome`.
  The prlimit text heuristic can at most relabel a failure as a resource failure.
* **Merge note.** agent/memguard also brought a `docs/AUDIT-ROUND7.md` and
  `audit/round7/run-round7.sh` (the cache rows). After merging main 1d0b147, those rows are
  §7 below, and their runner is `audit/round7/run-cache.sh`, which `run-round7.sh` runs last.
  Every other round-7 row passes `--fresh`, so it takes the cold path.
* **Interim main bug (now moot).** Between the two merges, consumer (`--proof-root`) runs with
  a `--janus-root` checkout failed with "no default toolchain configured". The cached base got
  no sources. c386fa7 fixed this, and main 1d0b147 contains it.

## 7. The verification-result cache (agent/testinfra rows, merged)

`janus verify` records the result of a successful sandboxed verification and prints it again,
marked `Cached:`, when every input is the same (docs/SOUNDNESS.md, "Verification-result cache").
That makes the cache a trusted component: a forged or stale entry would print `Verified` for a
proof that was never checked. This round attacks it. Runner: `audit/round7/run-cache.sh`, run by `audit/round7/run-round7.sh`
(attack files in `audit/round7/attacks/`, the lakefile attack is the `resultcache` mode of
`audit/attacks/R1_pkg`).

| Row | Attack | Expected | Result |
|---|---|---|---|
| RC1_proof_probe_bwrap | a proof's `#eval` reads `$JANUS_CACHE_DIR/v1/result/.key`, lists the entries, writes `planted-by-proof` (bubblewrap) | blocked: the directory is an empty tmpfs inside the sandbox (the proof compiles and verifies, sees nothing), nothing reaches the host | blocked |
| RC1_proof_probe_unshare | the same under the unshare fallback | blocked (the script mounts the same tmpfs, strictly) | blocked |
| RC2_lakefile_probe | a consumer lakefile does the same while Lake elaborates it | blocked: Lake runs sandboxed, sees an empty directory | blocked |
| RC3_tampered_entry | a recorded entry is edited on disk so its statement reads `x * y` | blocked: the HMAC does not verify, the entry is ignored, the verification runs and prints `x + y` | blocked |
| RC4_stale_framework | an entry recorded with a `--janus-root` framework is looked up after a framework source changes | blocked: the framework's hash (and its rebuilt pins) are part of the key | blocked |
| RC5_fresh_bypasses | `--fresh` | never uses the cache | blocked |
| RC6_unsandboxed_bypasses | `--unsafe-no-sandbox` | never uses the cache | blocked |

`TestResultCache` (cmd/janus) checks the same properties in `go test`: a hit prints exactly the
fresh output plus `Cached:`, an edited proof misses, a tampered entry is ignored, `--fresh` and
`--unsafe-no-sandbox` bypass the cache.

Not attacked here, because they are outside the threat model (docs/SOUNDNESS.md): a user who
can write `~/.cache/janus` directly (they can equally replace the framework build), and a proof
run with `--unsafe-no-sandbox` (it runs with the user's privileges).

There is no verification daemon, so there is no row for one (docs/TESTING.md explains why).

## Residual risks (honest list)

* G1 relies on the build-info Go version, which a lying `-X runtime.buildVersion` can set.
* The K1 notes are heuristics on the statement's syntax: they flag operations, not intent.
* Dependency bodies are disclosed, not round-tripped (J1). The tagged-def residual of round 6 §3
  is unchanged.
* Entry and module names are binary labels (G2).

## Regression status

On this branch, merged with main 1d0b147, all of these pass: `audit/round7/run-round7.sh` (with
the cache rows of `run-cache.sh`), `scripts/verify-all-examples.sh` (21 arm64 items and 27 amd64
functions), `audit/run-all.sh`, `audit/round2/run-round2.sh` through
`audit/round6/run-round6.sh`, and `go test -timeout 50m ./cmd/...`.

## Reproduce

```
audit/round7/run-round7.sh
```
