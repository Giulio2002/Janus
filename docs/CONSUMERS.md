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
What is trusted is the Janus Lean framework the `janus` binary carries, the Lean kernel and
`leanchecker`, and the ELF byte copy. Verification refuses to run without a sandbox unless
`--unsafe-no-sandbox` is passed; the mode is recorded in `verified.json`.

Use consumer verification only with packages you are willing to execute under that sandbox.

## Consumer proof packages

For proofs split across your own Lean modules, pass the Lake package root:

```sh
janus verify artifacts/Add --proof proofs/Add.lean --proof-root . --theorem MyProof.correctness
```

The package must:

* depend on **`janus`** and on nothing else, as a resolved git dependency pinned to a **full
  40-hex revision** (the standard `.lake/packages` layout) or a local path dependency;
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
consumer module's notation or unexpander cannot change what the statement means.

See [examples/consumer](../examples/consumer) for a tiny package: a shared lemma module
(`ConsumerExample.Spec`) plus two theorem modules (`ConsumerExample.Add`, `ConsumerExample.Max`).

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
janus verify-batch requests.json [--results FILE] [--json] [--fresh] [--unsafe-no-sandbox]
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

## Support cache

Successful runs keep a local cache under `$JANUS_CACHE_DIR` (default `~/.cache/janus`):

* the framework build (`v1/framework/<hash>`), built once per framework version and reused by
  every verification;
* consumer workspaces (`v1/consumer/<package+framework>/<extraction>`), keyed by the framework
  hash, the package root and the extraction. A second run with unchanged inputs rebuilds nothing;
  Lake decides reuse from its own traces, and a new extraction starts from a sibling workspace's
  build so the extraction-independent modules are not rebuilt.

Workspaces are locked while in use (concurrent runs are safe) and evicted after
`$JANUS_CACHE_RETENTION_DAYS` (default 7). `--fresh` bypasses the caches and builds in a throwaway
directory. The report's `consumer.rebuilt` lists which modules were (re)built; `consumer.workspace`
names the workspace, or `(temporary, --fresh)`.

## Limits

Consumer packages must be pure Lean source packages: a single `janus` dependency (git pinned to a
full revision, or a local path), the framework's toolchain, no other dependencies, no symlinked
sources, no `Extracted` module of their own. Lake configuration and Lean elaborators are
executable code and run under the sandbox; verify only packages you trust enough to execute
confined.
