# DESIGN ONLY: a replay key that survives irrelevant upstream changes

Status: proposal for approval. No code. Author: engine proof-speed worker, 2026-11-06.

## Problem

`planReplayPinned` (cmd/janus/replay.go) keys the passing replay of a module `m` on the toolchain, the
name, the bytes of `m`'s module-data files and, recursively, the keys of all its imports. Any change of
an import's olean therefore invalidates every module below it, even when `m`'s olean is byte-identical and
nothing `m` uses has changed. Measured cost: after a framework bump (or any edit of a module near the
root of a package) the whole closure is replayed again (String amd64 bump-only: 512 s of 1766 s;
Log10 cold: 430-950 s; each `--fresh` verify repeats it).

## What is NOT sound: keying on source hashes

The proposal "key on the source hash instead of the olean hash" is unsound. The kernel replay exists to
catch an elaborator that produced a bad olean. The olean is a function of the source only if the compile
is deterministic, and Lean source can run arbitrary IO at elaboration time (`run_cmd`, `initialize`,
`macro`/`elab` with `IO`, `#eval`, environment extensions). A source that is honest on the first compile
and injects a declaration on the second (it reads a file, the clock, a marker it left) passes under a
source-hash key and is never replayed again. The key must keep the bytes of the olean being replayed.
Measured: for ordinary modules the olean IS deterministic (same source and import constants give the same
bytes; adding a theorem to an import leaves the importer's olean byte-identical, B.olean 6312 bytes in
both builds), so nothing is lost by keeping the bytes in the key.

## What can be relaxed: the import component

The replay of `m` checks `m`'s own constants against an environment built from its imports. Its verdict
depends on (a) `m`'s olean bytes and (b) the declarations of the imported constants that `m`'s constants
mention, directly or through delta unfolding, i.e. the dependency closure of `m`'s constants in the
imports. It does not depend on the rest of the imports (unrelated theorems, other modules' bytes).
Today (b) is over-approximated by "the bytes of every transitive import".

Proposed key: `K(m) = H(toolchain, name, bytes(m), D(m))` where `D(m)` is a cryptographic digest of the
dependency closure of `m` in its imports.

## Computing D(m)

A small Lean program (`janus-depdigest`, source embedded in the janus binary like the auditor) run by
janus with the same sandbox and toolchain as the auditor, importing `m`'s environment:

1. Collect the constants declared by `m` (the module's own constant table).
2. Walk each constant's type and value (`Expr`), collecting the names of referenced constants; for each
   referenced constant declared in an import, add it and walk its type and value too, until the set is
   closed (reaching Init/Std/Lean/Lake core constants: those are identified by name and by the toolchain
   in the key, as today).
3. Digest the closure: for every constant in the closure, in sorted name order, a SHA-256 over a
   canonical serialisation of its `ConstantInfo` (kind, level parameter names, type, value or the
   inductive/constructor/recursor data, `safety`, `unsafe`/`partial` flags). The serialisation is written
   in the program (not `Expr.hash`, which is 64-bit and not collision-resistant).
4. Also digest the extra kernel inputs that are not constants: the quotient flag, the inductive
   `isRec/isNested` data (inside ConstantInfo), and the module's import list (the names, so an added
   import changes the key).

The result is printed as one hex line; janus parses it and mixes it into `K(m)`.

## Why this is sound (the argument to be reviewed)

Claim: if `K(m)` equals the key of an earlier passing replay, then replaying `m` now passes.

* The kernel's check of a constant `c` of `m` reads only (i) `c`'s own declaration (inside `bytes(m)`,
  in the key) and (ii) the declarations of the constants reachable from `c` by reference, because
  type inference, whnf and defeq look up constants only by names occurring in the terms they traverse,
  and delta/iota/projection/quotient reduction unfold only constants found that way (plus the recursor
  rules of the inductives involved, which are part of their ConstantInfo and so of the closure; plus
  the built-in `Nat`/`String` literal and `Eq`/`Quot` support, which depend on the toolchain, in the key).
  `D(m)` digests exactly that closure, so the closure being unchanged means every lookup the replay can
  make returns the same declaration.
* The replay is of `m`'s own constants (docs/SOUNDNESS.md, parallel replay: "a module's check depends
  only on its own bytes and on the bytes of its imports"; we weaken "bytes of its imports" to "the
  declarations reachable from m"). Environment extensions of imports are not consulted by the kernel.
* The earlier pass was an authentic marker (HMAC) of a replay that happened on these bytes with this
  closure; the imports themselves are still replayed or covered by their own markers (per-module markers
  chain: every module in the audited closure has its own `K`, so an import whose own olean is bad is
  caught when it is replayed; nothing is skipped without its own marker).

Residual risks and how each is closed:

1. `janus-depdigest` is now in the trusted base for the cache: a bug that omits a reachable constant
   makes a stale marker usable. Mitigation: it runs a CONSERVATIVE walk (every constant name occurring
   anywhere in any term, including in universe-irrelevant positions and in `Expr.mdata`), and a
   self-check test: for a set of generated module pairs the digest changes whenever the kernel replay of
   the importer changes verdict (mutation test: edit each reachable declaration in turn, require the
   digest to change; edit unreachable ones, require it to stay).
2. A hostile import could try to make the digest program itself misbehave (it loads `m`'s olean).
   Mitigation: it runs sandboxed with the module data read-only and its output is only a hex line; a
   crash or malformed output is a miss (full replay), never a hit.
3. The digest is computed from the environment as Lean loads it; the pins check after the replay
   (already present) still ties those bytes to what was digested.
4. Axioms: the key contains the axioms-closure implicitly (axioms are constants in the closure); a
   changed axiom set changes `D(m)`. The existing auditor still runs on every verification regardless.

## Expected effect

Cold runs: none (nothing to reuse). After a framework bump or an upstream edit that does not touch what a
module reaches: replays of unaffected modules are hits. For String amd64 bump-only the 512 s replay should
fall to the modules that reach the changed framework declarations (the bump touched one tactic module,
so about none). `--fresh` verifies still replay everything (the cache is off by design).

## Implementation plan (after approval)

1. `janus-depdigest` Lean program + Go driver (cmd/janus/depdigest.go), run once per module not already
   keyed; digests cached by (bytes(m), digests of imports' olean bytes) so it is computed once per
   distinct olean closure.
2. `planReplayPinned`: replace the recursive import-key mixing with `D(m)`; marker kind/version bump
   (`janus-replay-v3`) so old markers are misses.
3. Tests: key unchanged when an unreachable import declaration changes; key changes when a reachable
   declaration, an axiom, the import list, the toolchain or `bytes(m)` changes; forged/planted marker
   rows as today; a module with a hostile `run_cmd` shows that bytes(m) stays in the key.
4. Measurements: String amd64 bump-only and Log10 bump-only before/after.

## Alternatives considered

* Keying on a per-module "interface hash" supplied by Lake: Lake traces hash sources, same unsoundness.
* Replaying only changed modules by timestamp: not tamper-evident.
* Keep the key and make the replay faster: done separately (batched replay).
