# Example consumer package

Proofs about `example.com/basic` (`examples/basic`) kept in a Lake package of their own, the way
a user of Janus keeps theirs. The package depends on the `janus` Lean library and splits its
proofs across modules:

| Module | Imports | What it holds |
|---|---|---|
| `ConsumerExample.Spec` | `Janus` | `addSpec`, `maxSpec`, the shared statement shape `Computes`, lemmas about them |
| `ConsumerExample.Add` | `Extracted`, `ConsumerExample.Spec` | `correctness`: the compiled `Add` computes `addSpec` |
| `ConsumerExample.Max` | `Extracted`, `ConsumerExample.Spec` | `correctness` for `Max`, and `result_ge_left`, derived with a shared lemma |

`ConsumerExample.Spec` does not import `Extracted`, so `lake build` builds it here and `janus`
reuses its build for every extraction. The theorem modules import `Extracted`, the module that
`janus verify` generates from an artifact directory; check them with `janus verify`.

## Verify

From the repository root:

```sh
go build -o bin/janus ./cmd/janus
scripts/build-examples.sh                                   # artifacts/examples-arm64
bin/janus extract artifacts/examples-arm64 example.com/basic.Add artifacts/Add
bin/janus extract artifacts/examples-arm64 example.com/basic.Max artifacts/Max
bin/janus verify artifacts/Add --proof examples/consumer/ConsumerExample/Add.lean \
    --proof-root examples/consumer --theorem ConsumerExample.Add.correctness
bin/janus verify-batch examples/consumer/requests.json
```

`requests.json` verifies both theorem modules in one session: one snapshot of this package, one
workspace per distinct extraction (Add, Max), and one build of `ConsumerExample.Spec` shared
between them. Each request gets its own `verified.json`.

## The dependency

Inside this repository the package requires janus from the checkout (`path = "../.."` in
`lakefile.toml`, resolved in `lake-manifest.json`). A package of your own requires it from git,
pinned to the full commit whose framework your `janus` binary carries (`janus framework` prints
it; `janus init` writes this for you):

```toml
[[require]]
name = "janus"
git = "https://github.com/Giulio2002/Janus"
rev = "<40-hex commit>"
```

or, with `lakefile.lean`:

```lean
import Lake
open Lake DSL

package consumerExample

require janus from git "https://github.com/Giulio2002/Janus" @ "<40-hex commit>"

lean_lib ConsumerExample
```

Then run `lake update janus`. `janus verify` checks that the checked-out sources are byte for
byte the framework it carries; see [docs/CONSUMERS.md](../../docs/CONSUMERS.md).
