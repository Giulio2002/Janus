# Consumer packages and batch verification

The [README](../README.md) and [docs/CLI.md](CLI.md#verify) introduce `janus verify`. This page
covers verifying proofs that live in **your own Lake package**, verifying **many** of them in one
session, scaffolding a package with `janus init`, and what is trusted versus sandboxed.

## Threat model

A proof file, a `lakefile.lean` and any Lean elaborator they import are arbitrary code that
`janus` runs while Lean elaborates them. Janus treats all of it as **untrusted** and confines it
(see [docs/CLI.md § Threat model](CLI.md#threat-model-the-proof-is-untrusted-code)): every Lean
process that loads consumer code runs under a sandbox (bubblewrap, else `unshare`) with no
network and a read-only filesystem except one private build directory, the theorem is audited by
the trusted compiled `janus-audit` without running the package's initializers, the imported
`Extracted` is checked definitionally against the bytes extracted from the binary, and the
statement is pretty-printed in a clean environment that never imports the consumer's modules.
The framework package in the workspace is mounted read-only for every sandboxed process, its
compiled modules are pinned by SHA-256 to the trusted framework build and re-checked after the
Lake build, the audit and the replay, and the kernel replay covers every non-core module the
theorem imports, so a lakefile or a dependency's build step cannot replace a framework module
(or the auditor). What is trusted is the Janus Lean framework the `janus` binary carries (compiled
by `janus` itself, outside the sandbox), the Lean toolchain, the Lean kernel and `leanchecker`, and
the ELF byte copy. Verification refuses to run without a sandbox unless
`--unsafe-no-sandbox` is passed; the mode is recorded in `verified.json`.

Use consumer verification only with packages you are willing to execute under that sandbox.

## Consumer proof packages

For proofs split across your own Lean modules, pass the Lake package root:

```sh
janus verify artifacts/Add --proof proofs/Add.lean --proof-root . --theorem MyProof.correctness
```

The package must:

* depend on **`janus`**, as a resolved git dependency pinned to a **full 40-hex revision** (the
  standard `.lake/packages` layout) or a local path dependency;
* depend on other packages only as described in [Extra dependencies](#extra-dependencies):
  every one, transitively, a git dependency pinned to a full revision and checked out clean at
  it (or, with `--allow-path-deps`, a recorded local path);
* use the **same Lean toolchain** as the Janus framework (its `lean-toolchain`);
* have a resolved `lake-manifest.json` (run `lake update`). Both `lakefile.toml` and
  `lakefile.lean` work.

The checked-out `janus` sources must match the framework the verifier carries **byte for byte**,
allowing LF/CRLF differences; otherwise verification fails with `Stage: framework identity` and
prints the differing files and the revision to pin. `janus framework` prints that revision, and
`janus init` writes it into a new package's lakefile.

Verification takes a snapshot of the package's `.lean`, `.toml`, `.json` and `lean-toolchain`
files (excluding `.lake`, `.git`, `artifacts`, `generated`, `bin`, `obj`, the selected output
directory, and any dotfiles), copies it into a workspace together with the framework and the
selected `Extracted` module, and builds and checks it there — it never trusts the package's own
compiled caches. Shared consumer modules can themselves `import Extracted`. The report binds every
snapshot file's hash and the dependency revision. `Extracted.lean` is reserved for the selected
artifact: a consumer package may not contain a file or module named `Extracted`, and no consumer
module may declare a name under the `Extracted` namespace.

The statement may mention Lean/Std core, `Janus.*`, `Extracted.*` and plain `def`s from your
package (their bodies are disclosed in the report's `definitions`); proof-local or shared-module
instances, class values, `opaque`s, axioms and `Extracted`-shadowing names are rejected, so a
consumer module's notation or unexpander cannot change what the statement means. Constants from
[extra dependencies](#extra-dependencies) follow their own rule, below.

See [examples/consumer](../examples/consumer) for a tiny package: a shared lemma module
(`ConsumerExample.Spec`) plus two theorem modules (`ConsumerExample.Add`, `ConsumerExample.Max`).

## Extra dependencies

A consumer package may depend on other Lean projects — a spec library, Mathlib — next to janus.
`janus verify --proof-root` (and `verify-batch`) accepts the package when **every** entry of its
`lake-manifest.json` other than janus, transitively (Mathlib's own `batteries`, `aesop`, `Qq`,
`plausible`, `proofwidgets`, `LeanSearchClient`, `importGraph`, …, which the root manifest lists
as `"inherited": true`), is

* a **git** dependency whose manifest `rev` is a **full 40-hex commit**; a dependency you
  require directly must also be *asked for* by that commit in the lakefile (`rev = "<commit>"`,
  not a branch or tag, so `lake update` cannot move it). A dependency's own requirements may
  name a branch; the root manifest's `rev` pins them;
* **checked out at exactly that commit with no local modifications**: `git rev-parse HEAD` in
  `.lake/packages/<name>` equals the pin, `git status --porcelain` is empty (the package's own
  `.lake` build directory aside), and every file of the pinned tree hashes to its git blob id
  (which also catches edits hidden from `git status`, e.g. by `--assume-unchanged`).

Anything else fails with `Stage: consumer manifest` naming the dependency and what to run. Path
dependencies other than janus are rejected unless you pass **`--allow-path-deps`**; then their
source snapshot (the same file rules as the consumer's) is used as it is and recorded as
`"type": "path"` with its tree hash — it is not pinned, so prefer git for anything you publish.
git runs with hooks, fsmonitor and your global/system git configuration disabled, under the
sandbox when one is available.

**What happens to them.** Exactly the pinned files are copied into the verification workspace
(`deps/<name>`) and given to Lake as path packages; Lake builds the modules the proof needs
**under the sandbox**, like the consumer's own modules. Their build outputs are untrusted: the
kernel replay re-checks every dependency module the theorem's environment imports (for a Mathlib
import that is thousands of modules, so expect minutes the first time; passing replays are cached
by content hash, so unchanged modules are not replayed again). A new extraction's workspace starts
from a sibling workspace's dependency builds. The first build of a large dependency is a full
source build (no `lake exe cache get`: downloaded oleans would be unverified build outputs), so
the first Mathlib verification takes as long as building the imported part of Mathlib.

Module identity is checked after the build: no consumer or dependency module may use a root
reserved for the framework or the toolchain (`Init`, `Std`, `Lean`, `Lake`, `Janus`,
`Extracted`, `JanusTrusted`), no module name may come from two places, and no module root may be
shared between the consumer and a dependency (`Stage: module identity`).

**What a statement may use from a dependency.** Its plain `def`s and theorems, and the inductive
types and structures they are built from, with their constructors and recursors. Its
**instances** (wherever the `instance` attribute was attached), classes and class-valued defs,
`opaque`s, axioms and unsafe declarations are rejected (`Stage: statement identity`): an
instance can make `a * b` mean addition, and a reader of the statement would not see it. So
write the operation by name — `UInt256.add a b`, not `a + b`. A dependency def's body is *not*
unfolded or vetted: its meaning is the pinned dependency's, and the report lists every
dependency constant the statement (or a proof-local def it uses) mentions in
`dependencyConstants` as `"<name> (<kind>, <module>)"`. The axiom rule is unchanged: everything
the theorem depends on, dependency lemmas included, may use only `propext`, `Quot.sound` and
`Classical.choice`, and `native_decide` (`Lean.ofReduceBool`) anywhere in that closure is
rejected.

The auditor reads instance and class information from the imported modules' raw environment
extension data, so **no dependency code runs in the trusted auditor**. The statement is still
pretty-printed in a clean environment of the trusted modules only: the dependency constants it
reaches are added there as type-only declarations, so neither the proof's nor the dependency's
notations, unexpanders or delaborators apply. (Generalized field notation still applies:
`WordLib.Word.add a b` prints as `a.add b`; `dependencyConstants` names the full constants.)

**The record.** `verified.json` has `consumer.dependencies`: for each dependency its `name`,
`type`, `url`, `rev`, `inputRev`, `inherited`, `subDir`, the checkout `dir`, the number of files
copied and their tree `sha256`; `consumer.allowPathDeps` is set when `--allow-path-deps` was
given. `janus verify` prints one `Dependency:` line per entry and `janus explain` lists them with
the dependency constants used.

### Using an external spec

Suppose you want the specification of `Add256` (see `examples/proofs/Add256.lean`) to be the
EVM's 256-bit addition from a Lean port of
[NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean), where

```lean
structure UInt256 where
  val : Fin (2 ^ 256)

def UInt256.add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
```

(the names below follow that shape; adjust them to the port you pin). Require it and Mathlib
next to janus, each by commit:

```toml
[[require]]
name = "janus"
git = "https://github.com/Giulio2002/Janus"
rev = "<janus framework prints this>"

[[require]]
name = "evmyul"
git = "https://github.com/<you>/EVMYulLean-port"
rev = "<40-hex commit>"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"   # tag v4.34.1, matching the framework's toolchain
```

Run `lake update` once (set `MATHLIB_NO_CACHE_ON_UPDATE=1` to skip Mathlib's cache download,
which verification does not use). Janus states memory contents with its own vocabulary:
`Janus.Spec.val256 m p : Nat` is the 32 little-endian bytes at `p`, with `val256_lt : val256 m p
< 2 ^ 256`. The **bridge** is a plain proof-local def from that vocabulary to the external type,
plus the lemma that connects the two arithmetic views:

```lean
import Extracted
import EvmYul.UInt256

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace MyProofs.Add256

/-- The bridge: the 256-bit value at `p` as the external spec's word. -/
def word (m : Memory) (p : Nat) : EvmYul.UInt256 := ⟨⟨val256 m p, val256_lt m p⟩⟩

/-- Janus's arithmetic statement is the external addition, read through the bridge. -/
theorem word_add {m m₁ m₂ : Memory} {z x y : Nat}
    (h : val256 m z = (val256 m₁ x + val256 m₂ y) % 2 ^ 256) :
    word m z = EvmYul.UInt256.add (word m₁ x) (word m₂ y) := by
  -- rewrite rather than unfold: `%` by the literal `2 ^ 256` must not be evaluated
  have hv : (word m z).val = (word m₁ x).val + (word m₂ y).val := by
    apply Fin.ext
    rw [Fin.val_add]
    exact h
  unfold EvmYul.UInt256.add
  rw [← hv]

/-- The Janus-native theorem (proved exactly as examples/proofs/Add256.lean). -/
theorem native (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' => val256 s'.mem z.toNat = (val256 s.mem x.toNat + val256 s.mem y.toNat) % 2 ^ 256 ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; janus_arith)

/-- The published theorem: `Add256` computes `EvmYul.UInt256.add`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' => word s'.mem z.toNat = EvmYul.UInt256.add (word s.mem x.toNat) (word s.mem y.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) :=
  (native z x y).mono (fun _ h => h) (fun _ _ _ ⟨h, hw⟩ => ⟨word_add h, hw⟩)

end MyProofs.Add256
```

The pattern:

* prove the theorem in Janus's own vocabulary first (`native`), where the tactics work;
* state the published theorem through a **bridge def** (`word`) into the external type and the
  **external operation by name** (`EvmYul.UInt256.add`), and derive it with `Ensures.mono` and
  one **bridge lemma** (`word_add`) that equates the two arithmetic readings;
* keep instances out of the statement: `word … = word … + word …` would elaborate to the
  dependency's `HAdd` instance and be rejected. Inside proofs, instances are fine.

`janus verify` then reports `MyProofs.Add256.word` (with its body) under `definitions`, and
`EvmYul.UInt256 (inductive, …)`, `EvmYul.UInt256.mk (constructor, …)` and
`EvmYul.UInt256.add (def, …)` under `dependencyConstants`, alongside the pinned `evmyul`,
`mathlib` and Mathlib's dependencies under `consumer.dependencies`. A reviewer checks the
statement, the bridge's body and that the pinned `UInt256.add` is the EVM's `ADD`.

The tests carry a small, runnable version of this pattern: `cmd/janus/deps_test.go` builds a
word library in a local git repository (`structure Word where val : BitVec 64`, `Word.add`,
`Word.add_val`), requires it by its `file://` URL and commit, and verifies
`example.com/basic.Add` against `(Word.add (toWord x) (toWord y)).val` through the bridge
`toWord`; it also checks that the library's `Mul` instance, an `opaque` and an axiom are
rejected, as are an unpinned requirement and a dirty checkout. `TestConsumerMathlib`
(`JANUS_TEST_MATHLIB=1`) verifies a statement that uses Mathlib's `Function.Bijective` with
Mathlib pinned at `v4.34.1`.

## `janus init`

```sh
janus init my-proofs            # requires janus at the current binary's revision, runs lake update
janus init my-proofs --janus-path /path/to/Janus   # local path dependency instead
janus init my-proofs --rev <40-hex> --no-update     # pin a specific revision, skip lake update
```

Scaffolds a ready-to-build consumer package: `lakefile.toml` requiring `janus` (at the revision
the binary carries, from `janus framework`), a matching `lean-toolchain`, a shared `Spec` module,
an example theorem module, a small Go program to extract from, and a `README`. Unless
`--no-update` is given it runs `lake update` to resolve the manifest. `--name` sets the library
name (a capitalised identifier, not `Janus` or `Extracted`).

## Batch verification

```sh
janus verify-batch requests.json [--results FILE] [--json] [--fresh] [--unsafe-no-sandbox] [--allow-path-deps] [--asl]
```

```json
{
  "schema": 1,
  "proofRoot": ".",
  "requests": [
    { "outdir": "artifacts/Add", "proof": "ConsumerExample/Add.lean", "theorem": "ConsumerExample.Add.correctness" },
    { "outdir": "artifacts/Max", "proof": "ConsumerExample/Max.lean", "theorem": "ConsumerExample.Max.correctness" }
  ]
}
```

Paths are relative to the manifest. Each request names an `outdir` (an extraction directory), a
`proof` and a `theorem`, and optionally its own `proofRoot` (overriding the top-level one) and
`binary`. A request **without** a `proofRoot` is a single-file verification.

**What is shared, what is per request.** Requests that share one `proofRoot` take **one snapshot**
of that package. Requests whose extraction (`Extracted.lean`) is byte-identical share **one Lake
build** of their proof modules in one workspace, so a shared lemma module is built once;
requests with different extractions use separate workspaces (because `Extracted` is a single
module name), and the first workspace's build seeds the others. **Each request is audited and
kernel-replayed on its own** and gets its **own `verified.json`**: a failure in one request's
proof or axioms does not affect the others. Each request prints `PASS`/`FAIL` with its module or
stage; `--results FILE` writes every outcome as JSON in request order, each with a classified
`failure` (or `null`). The exit code is `0` only when every request verified. Every request first
withdraws its previous `verified.json`; a failed request leaves none.

With `--asl` every verified request also gets its ASL corollary ([docs/ASL.md](ASL.md#janus-verify---asl-the-corollary-of-a-verified-theorem));
`janus verify --proof-root … --asl` does the same for one request. The JanusASL build is shared
by the whole batch. A result's `asl` is `"verified"` or `"invalid"` (with `aslFailure`), printed
as an `ASL:` line under its `PASS`; an ASL failure does not make the request fail (its
`verified.json` keeps the theorem), but the batch exits 1 and reports `aslFailed`. A consumer
theorem stated through its own definition (`Computes Extracted.program Extracted.entry spec`) is
accepted when that definition unfolds to `Janus.GoABI.Ensures`. No consumer or dependency module
may live under the `JanusASL`, `ArmASL`, `Sail`, `JanusASLWords` or `JanusASLCorollary` roots.

## Support cache

Successful runs keep a local cache under `$JANUS_CACHE_DIR` (default `~/.cache/janus`):

* the framework build (`v1/framework/<hash>`), built once per framework version and reused by
  every verification;
* the JanusASL build for `--asl` (`v1/asl/<key>`), keyed by the framework, the JanusASL sources
  with the vendored model, the toolchain and the framework build it requires; about an hour and
  1 GB to build, kept for `$JANUS_ASL_RETENTION_DAYS` (default 30) after its last use;
* consumer workspaces (`v1/consumer/<package+framework>/<extraction>`), keyed by the framework
  hash, the package root and the extraction. A second run with unchanged inputs rebuilds nothing;
  Lake decides reuse from its own traces, and a new extraction starts from a sibling workspace's
  build so the extraction-independent modules are not rebuilt.

Workspaces are locked while in use (concurrent runs are safe) and evicted after
`$JANUS_CACHE_RETENTION_DAYS` (default 7), or earlier, least recently used first, when the cache
exceeds its budget (`$JANUS_CACHE_MAX`, default min(40 GiB, 10% of the disk); `janus cache du`
and `janus cache gc`, docs/CLI.md "Cache"). `--fresh` bypasses the caches and builds in a throwaway
directory. The report's `consumer.rebuilt` lists which modules were (re)built; `consumer.workspace`
names the workspace, or `(temporary, --fresh)`.

## Limits

Consumer packages must be pure Lean source packages: a `janus` dependency (git pinned to a full
revision, or a local path), other dependencies only pinned and clean (or local paths with
`--allow-path-deps`), the framework's toolchain, no symlinked sources, no `Extracted` module of
their own. Dependencies whose build needs more than Lean (ProofWidgets' JavaScript bundle needs
`npm` or a release download, which the network-less sandbox cannot do) work only for modules that
do not import those parts; most of Mathlib below its widget-using tactics is fine. Lake configuration and Lean elaborators are
executable code and run under the sandbox; verify only packages you trust enough to execute
confined.
