# Command-line reference

`janus` extracts the arm64 machine code of a Go function from a linux/arm64 ELF binary into
Lean, checks that extraction artifacts still match the binary, and verifies Lean proofs about
the extracted program.

All commands exit with `0` on success and `1` on failure. Diagnostics go to standard error.
Rejected artifacts and proofs print `Invalid:`; other failures (bad arguments, unreadable
binaries) print `Error:`. Both are followed by the failing stage and what to do next:

```text
Invalid: artifacts/Get/Extracted.lean was modified after extraction: SHA-256 6ab6…, identity.json records dc0c….
  Stage: extraction integrity
  Next: Rerun janus extract artifacts/examples-arm64 "example.com/basic.Get" artifacts/Get with the intended binary, then rerun this command.
```

Paths under the working directory are shown relative to it.

## Build

```sh
export PATH=/usr/local/go/bin:$PATH          # Go 1.26
go build -o bin/janus ./cmd/janus            # from the repository root
scripts/build-examples.sh                    # builds artifacts/examples-arm64
```

The CLI is a Go module (`github.com/Giulio2002/Janus`, `go.mod` at the repository root). Its
only dependency is `golang.org/x/arch` (pinned in `go.mod`/`go.sum`), used to find branch
targets during reachability. `verify` also needs Lean and Lake (via elan); the version comes from
`lean-toolchain`.

## Examples

`examples/basic` is a separate Go module (`example.com/basic`) with functions marked
`//go:noinline`: `Add`, `Max`, `Add128` (a `bits.Add64` chain), `Mul64` (`bits.Mul64`), `Sum`
over a slice, `Get(xs, i)` (bounds check), `Add256(z, x, y *[4]uint64)`, `Div(x, y)` (divide
check) and `AddThree` (calls `Add`, so its extraction has two functions). Five more load data
(see [Read-only data](#read-only-data)): `Table` (an `[8]uint64` literal), `HexDigit` (indexes a
string constant) and `SetOne256` (the 32-byte constant 1) read `.rodata`; `GlobalTable` reads an
initialised package-level `var` (`.noptrdata`) and `Bump` updates a zero-initialised one
(`.noptrbss`), both writable.
`examples/basic/cmd` is a `main` package that keeps every function alive: the Go linker removes
functions nothing references, so each one is stored in a package-level `[]any` and also called
on inputs derived from `os.Args`. `scripts/build-examples.sh` builds it with
`CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath` into `artifacts/examples-arm64`.

The CLI test fixtures `cmd/janus/testdata/Trivial.lean` (accepted; a placeholder statement that
says nothing about the code) and `cmd/janus/testdata/Sorry.lean` (rejected by the axiom audit)
exercise `verify` end to end. They are not proofs; real theorems live in `examples/proofs/`.

## List

```sh
janus list artifacts/examples-arm64 [--filter basic.]
```

```text
# artifacts/examples-arm64: example.com/basic, go1.26.0, linux/arm64, functions from symtab
ADDRESS                SIZE  NAME
0x00000000000930c0       16  example.com/basic.Add
0x00000000000930d0       32  example.com/basic.Max
...
```

Functions come from the ELF `.symtab` (`STT_FUNC` symbols in `.text`). If the binary was
stripped, they come from the Go `.gopclntab` (`debug/gosym`) instead; the header says which.
`SIZE` is the symbol size and includes the linker's zero padding.

## Extract

```sh
janus extract <binary> <symbol> <outdir> [--max-functions N]
janus extract artifacts/examples-arm64 example.com/basic.Get artifacts/Get
```

```text
Extracted example.com/basic.Get: 1 function(s), 22 word(s), 2 stub(s), 0 data object(s) (0 bytes) into artifacts/Get/Extracted.lean
  code  0x93140   22 words  example.com/basic.Get
  stub  0x87ef0 panic      runtime.panicBounds
  stub  0x85d20 morestack  runtime.morestack_noctxt.abi0
```

Extraction:

1. Validates the binary: 64-bit little-endian AArch64 ELF, **a non-PIE executable** (`ET_EXEC`,
   not `ET_DYN`), Go build information present (`debug/buildinfo`), `GOOS=linux`, `GOARCH=arm64`.
   A position-independent executable is rejected (`Stage: binary validation`): the model records
   link-time addresses, which a PIE does not run at. Build with `go build` (non-PIE; e.g.
   `CGO_ENABLED=0`), not `-buildmode=pie`.
2. Finds the symbol (exact, case-sensitive name as printed by `list`; ambiguous names fail).
3. Copies the function's raw 32-bit little-endian words from `.text`. Words are never
   translated. Trailing zero words (the linker's `udf #0` padding up to the next function) are
   trimmed; nothing inside the function is.
4. Computes the transitive set of **direct-branch callees**: every `BL`, `B`, `B.cond`,
   `CBZ`/`CBNZ` and `TBZ`/`TBNZ` whose target lies outside the current function. Targets are
   found with `golang.org/x/arch/arm64/arm64asm`. This decoding is untrusted: it only chooses
   which code to copy. A missed target is simply absent and the Lean model faults with `noCode`
   if execution reaches it, which is sound. Indirect branches (`BR`, `BLR`) are not followed for
   the same reason. Branches into no known function are reported as warnings and recorded in
   `identity.json` under `unresolvedBranches`.
5. Records known runtime stubs instead of copying them:
   * `.panic`: any `runtime.panic*` or `runtime.goPanic*` function and `runtime.gopanic`
     (e.g. `runtime.panicIndex`, `runtime.panicBounds`, `runtime.panicSlice*`,
     `runtime.panicdivide`, `runtime.panicshift`, `runtime.panicmem`, `runtime.panicwrap`);
   * `.morestack`: `runtime.morestack*` (the stack-growth path of every function prologue).

   A `.abi0` suffix is ignored when classifying.
6. Copies every other reachable function, runtime or not. `--max-functions N` (default 64)
   fails the extraction when more are reachable, listing them. For example `main.main` of the
   example binary reaches 421 functions through `println` and the allocator.
7. Copies the **read-only data** the copied code references (see [Read-only data](#read-only-data)).

Outputs, written into `<outdir>` (created if needed); any old `verified.json` there is removed:

### `Extracted.lean`

```lean
import Janus

/-! Generated by `janus extract` 0.2.0 from `example.com/basic.Get` (example.com/basic, go1.26.0).
Do not edit: … -/

namespace Extracted
open Janus

def segments : List Segment := [
  { name := "example.com/basic.Get", base := 0x93140, words := [
      0xf9400b90, 0xeb3063ff, 0x540001a9, 0xf81f0ffe, 0xf81f83fd, 0xd10023fd, 0xf9000fe0, 0xeb01007f,
      … ] } ]

def stubs : List Stub := [
  { name := "runtime.panicBounds", addr := 0x87ef0, kind := .panic },
  { name := "runtime.morestack_noctxt.abi0", addr := 0x85d20, kind := .morestack } ]

def exitAddr : Nat := 0

def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }

def entry : Nat := 0x93140

end Extracted
```

* The entry function is the first segment; callees follow in breadth-first discovery order.
* `entry` is the entry function's address. A caller sets `pc := entry` and `X30 := exitAddr`.
* **`exitAddr` is a non-code sentinel**, always `0`. Nothing is loaded at address 0 in a
  linux/arm64 Go binary (text starts far above it), and `Program.run` checks for `exitAddr`
  before fetching, so a `RET` to the planted return address ends the run with `.returned`
  instead of executing anything there.
* Word lists with more than 8 words wrap, 8 words per line.
* **Large programs.** Lean elaborates one big list literal with deep recursion; around 3000 words
  in one definition exceed the default `maxRecDepth`. When the program has more than 2048 words in
  total, each segment becomes its own definition and `segments` lists them:

  ```lean
  def seg0 : Segment :=
    { name := "main.main", base := 0x93390, words := [ … ] }
  …
  set_option maxRecDepth 100000 in     -- only for segments over 1024 words
  def seg12 : Segment := …

  def segments : List Segment := [
    seg0, seg1, …, seg420 ]
  ```

  Everything else (`stubs`, `exitAddr`, `program`, `entry`) is unchanged. Proofs that unfold
  `Extracted.segments` by name should also unfold `Extracted.seg<i>` in this form; kernel
  reduction (`decide`, `rfl`) is unaffected. The 421-function `main.main` extraction (37,276
  words, 81 data objects) elaborates in about 35 s.

### `identity.json`

```json
{
  "schema": 2,
  "extractorVersion": "0.2.0",
  "binary": "../examples-arm64",
  "binarySha256": "257b83ed…",
  "goVersion": "go1.26.0",
  "mainModule": "example.com/basic",
  "goos": "linux",
  "goarch": "arm64",
  "symbolSource": "symtab",
  "symbol": "example.com/basic.Get",
  "address": "0x93140",
  "size": 96,
  "maxFunctions": 64,
  "functions": [ { "name": "example.com/basic.Get", "address": "0x93140", "size": 96, "words": 22 } ],
  "stubs": [ { "name": "runtime.panicBounds", "address": "0x87ef0", "kind": "panic" }, … ],
  "unresolvedBranches": [],
  "data": [],
  "dataReferences": [],
  "skippedData": [],
  "extracted": "Extracted.lean",
  "extractedSha256": "dc0c105a…"
}
```

`binary` is relative to the artifact directory when both are under the same top-level
directory, otherwise absolute. `size` is the symbol size (with padding); `words` is the number of
copied words after trimming. `data`, `dataReferences` and `skippedData` are described under
[Read-only data](#read-only-data); for `example.com/basic.SetOne256`:

```json
  "data": [ { "name": ".rodata+0x2a3a0", "address": "0xca3a0", "size": 32, "section": ".rodata", "sha256": "01d0fabd…" } ],
  "dataReferences": [ { "from": "0x93324", "target": "0xca3a0", "kind": "adrp+add" },
                      { "from": "0x93328", "target": "0xca3a0", "kind": "adrp+ldst" }, … ],
  "skippedData": []
```

### Read-only data

Go code loads constants with `ADRP`+`ADD` (`MOVD $sym(SB), R`), `ADRP`+`LDR`/`LDP`
(`MOVD sym(SB), R`), and occasionally `ADR` or a PC-relative literal `LDR`. For example
`SetOne256` (`*z = [4]uint64{1, 0, 0, 0}`) loads the 32-byte constant from `.rodata`:

```text
93320: adrp x27, ca000 ; 93324: add x27, x27, #0x3a0 ; 93328: ldp x1, x2, [x27]
9332c: adrp x27, ca000 ; 93330: add x27, x27, #0x3b0 ; 93334: ldp x3, x4, [x27]
```

The extractor finds these address computations in every copied function with
`golang.org/x/arch/arm64/arm64asm` (`cmd/janus/data.go`). Like reachability, **this detection is
untrusted**: it tracks registers holding an `ADRP` page (then `ADD #imm`) through straight-line
code and forgets them at branches, branch targets, calls and any instruction that may overwrite
them. If it misses a reference, the bytes are not in `Program.data`, `Program.DataLoaded` does not
provide them, and the access faults as outside every allocation, which is sound. What is trusted is
the byte copy.

For each referenced address:

* In an allocated, **non-writable** section other than `.gopclntab` and `.text` (in practice
  `.rodata`, `.typelink`, `.itablink`): if a `.symtab` data symbol contains the address and is at
  most 4096 bytes, the whole symbol is copied under its name; a larger symbol gets a 256-byte
  window from the address (named `sym+0xoff`); with no symbol (Go's anonymous static data), a
  window from the address up to the next symbol, at most 256 bytes (named `.rodata+0xoff`, the
  offset in the section). Overlapping and adjacent objects in a section are merged.
* A literal `LDR` into `.text` copies the 8 bytes at the target (a literal pool).
* In a **writable** section (`.noptrdata`, `.data`, `.bss`, `.noptrbss`, anything with
  `SHF_WRITE`, including the `.go.buildinfo`/`.go.module` area): **not copied**, because the
  binary does not fix its run-time content. It is recorded in `skippedData` with
  `"reason": "writable"` and `extract` prints a warning. Go's `.noptrdata` holds initialised
  `var`s and is mapped read-write, so it is treated as writable; a theorem that needs such a
  global must add its region and contents to the precondition explicitly. For `GlobalTable`:

  ```text
  Warning: code at 0x93358 references 0x160840 (example.com/basic.tbl) in writable section .noptrdata; its content is not fixed by the binary, so it is not copied (accesses fault unless a precondition provides that memory).
  ```
* In `.gopclntab` (`"gopclntab"`), in code without a literal load (`"code"`, e.g. a function
  address for a closure), or in no section (`"unmapped"`): not copied, recorded in `skippedData`.

The objects appear sorted by address in `Extracted.lean`, 16 bytes per line. With no data the file
keeps exactly the shape shown above. With data:

```lean
def data : List DataSegment := [
  { name := ".rodata+0x2a3a0", base := 0xca3a0, bytes := [
      0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] } ]

def program : Program :=
  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }
```

Above 2048 bytes in total, each object becomes `def data<i> : DataSegment` (with
`set_option maxRecDepth 100000` above 1024 bytes) and `data` lists them, as for code segments.
A proof about such a program assumes `Program.DataLoaded Extracted.program s.mem` (the bytes are
in memory, inside a non-writable region). `check` regenerates the data along with the words, so
an edited byte or a dropped object is rejected.

## Check

```sh
janus check <outdir> [--binary PATH]
```

```text
Valid: extraction artifacts match the binary and recorded settings.
  Binary: artifacts/examples-arm64
  Module: example.com/basic (go1.26.0, linux/arm64)
  Entry: example.com/basic.Get at 0x93140
  Functions: 1, stubs: 2, data objects: 0
  Code: artifacts/Get/Extracted.lean
  Manifest: artifacts/Get/identity.json
  Matched: binary SHA-256, extractor version, Extracted.lean SHA-256, regenerated words and data.
```

`check` reads `identity.json`, re-runs the extraction in memory with the recorded symbol and
`--max-functions`, and byte-compares it with the saved files without writing anything. If the
binary moved, `--binary` names its new location; its SHA-256 must still match.

| Failure | Stage |
|---|---|
| `identity.json` missing or malformed | `artifact layout` |
| written by another extractor version or schema | `extractor version` |
| binary missing or not a linux/arm64 Go ELF | `binary identity` / `binary validation` |
| `Binary changed since extraction: … has SHA-256 X, identity.json records Y.` | `binary identity` |
| `Extracted.lean was modified after extraction` (hash differs from `identity.json`) | `extraction integrity` |
| `Extracted.lean differs from the regenerated extraction` (hash matches but content does not regenerate, e.g. both files edited) | `extraction integrity` |
| `identity.json differs from the regenerated identity` | `extraction integrity` |

## Verify

```sh
janus verify <outdir> [--proof FILE] [--theorem NAME] [--proof-root PKG [--allow-path-deps]] [--json]
             [--fresh] [--replay-fresh] [--janus-root DIR] [--binary PATH] [--unsafe-no-sandbox]
janus verify artifacts/Get --proof cmd/janus/testdata/Trivial.lean
```

```text
Verified: Proof.correctness
  Module: example.com/basic (go1.26.0)
  Entry: example.com/basic.Get at 0x93140
  Binary: artifacts/examples-arm64 (SHA-256 257b83ed…)
  Proof: cmd/janus/testdata/Trivial.lean
  Framework: embedded (SHA-256 1c26c3bb…, 30 files, leanprover/lean4:v4.34.1)
  Sandbox: bubblewrap (no network, read-only filesystem, private build dir)
  Axioms: (none)
  Kernel replay: leanchecker passed (Extracted, Janus, Janus.Arm64.Bits, …, Proof; 29 modules; 26 reused from the replay cache)
  Lean: Lean (version 4.34.1, …)
  Report: artifacts/Get/verified.json
  Statement:
    Proof.correctness : Extracted.entry = Extracted.entry
```

Defaults: `--proof <outdir>/Proof.lean`, `--theorem Proof.correctness`. The Janus Lean framework
is the copy **embedded in the `janus` binary** (see [the framework](#framework), [install
story](#install)), or a checkout named by `--janus-root` / `$JANUS_ROOT` (a directory whose
`lakefile.toml` has `name = "janus"`). `--proof-root` verifies a module of your own Lake package
(see [docs/CONSUMERS.md](CONSUMERS.md)); that package may have **extra dependencies** (a spec
library, Mathlib) when every one of them, transitively, is a git dependency pinned to a full
40-hex revision and checked out at exactly that revision with no local modifications
([details](CONSUMERS.md#extra-dependencies)). `--allow-path-deps` additionally accepts local
path dependencies other than janus, copied as they are and recorded as `"type": "path"` (not
pinned). `--json` prints the report as JSON; `--fresh` rebuilds the framework/caches from
scratch (and replays every module, ignoring the replay cache); `--replay-fresh` additionally
replays the theorem's module with `leanchecker --fresh`, re-checking its whole environment,
Lean core included, from an empty environment (slow: minutes).

### Threat model: the proof is untrusted code

A proof file is arbitrary Lean that `janus` elaborates and runs (`#eval`, `initialize`, macros,
tactics are all code). It is treated as **untrusted**, and the guarantee holds even if the proof
is hostile: a `Verified` line means the printed statement holds for the extracted bytes, and the
printed statement is the one the kernel checked. To make that true, verification:

* runs **every Lean process that loads the proof inside a sandbox** (bubblewrap, else an
  `unshare` namespace): no network; the filesystem — including the Janus sources, the
  `~/.cache/janus` build and the `janus` binary — is read-only except one fresh, private build
  directory; a private `/tmp`, `/dev/shm` and `/run` (so the host's live daemon sockets under
  `/run`, which a read-only bind would leave reachable, are not present), and a private PID and
  user namespace, killed with the parent. The `unshare`
  fallback remounts **every** mount read-only (not only `/`) and mounts private tmpfs `/tmp`,
  `/dev/shm` and `/run`; if some mount cannot be made read-only it refuses, and you should install
  bubblewrap. `JANUS_SANDBOX=unshare` forces the fallback (for testing it), `JANUS_SANDBOX=bwrap`
  forbids it. Without a sandbox verification refuses (`Stage: sandbox`) unless you pass
  `--unsafe-no-sandbox`. Install bubblewrap with `apt-get install -y bubblewrap`; the mode used
  is recorded in `verified.json`.
* audits the theorem with a **trusted compiled routine (`janus-audit`)** that imports the
  proof's compiled module *as data* and never runs its initializers, so the proof cannot forge
  the audit result or run code during it;
* checks the imported `Extracted` program is **definitionally the one extracted from the binary**
  (compared against an independently elaborated trusted copy), and puts that copy's directory
  first on an otherwise private `LEAN_PATH`, so a planted or shadowing `Extracted` is rejected;
* **prints the statement in a clean environment** that imports only `Janus` and `Extracted`,
  never the proof, so the proof's unexpanders, notations, delaborators and instances cannot make
  the printed statement differ from the checked one;
* requires the **printed statement to mean what was checked** (round 2, CRITICAL-1): every
  argument in an instance-implicit position must be a registered instance of the trusted
  environment (or an instance binder `[inst : C]` of the theorem), so an inline instance such as
  `@HMul.hMul _ _ _ ⟨fun a b => a + b⟩ x y` (printed `x * y`) is rejected, and the printed
  statement is **re-parsed and re-elaborated** in the clean environment and must be
  definitionally equal to the checked type (`Stage: statement identity`, "does not
  round-trip"). Coercions are printed with their target type (`(↑n : Int)`), and numerals with
  theirs (`(5 : BitVec 64)`) when the plain print would read back at another type. The report
  also carries `statementExplicit`, the statement printed with `pp.explicit` (every implicit and
  instance argument shown);
* requires the statement to mention `Extracted.program`/`Extracted.entry` and to be built only
  from Lean/Std core, `Janus.*`, `Extracted.*` and plain proof-local `def`s (whose bodies are
  disclosed in the report); a proof-local instance, class value, `opaque`, axiom or a name that
  shadows the `Extracted` namespace is rejected. With extra consumer dependencies, the
  statement may also use a dependency's plain `def`s, theorems and inductive types/structures
  (with their constructors and recursors), listed in the report's `dependencyConstants`; a
  dependency's instances, classes, class-valued defs, `opaque`s and axioms are rejected. Instance
  and class information is read from the modules' raw extension data, so no dependency code runs
  in the auditor, and dependency constants are printed from type-only copies in the clean
  environment (the dependency's own notation does not apply);
* **pins the trusted framework build**: the SHA-256 of every framework `.olean` (and of the
  trusted `Extracted`/`JanusTrusted`) is recorded after the trusted build and re-verified after
  every untrusted step, after the audit and after the replay; untrusted build outputs are pinned
  once final. In a consumer workspace the framework package is also mounted **read-only** for
  every sandboxed process. A replaced, corrupted, missing or extra framework module is rejected
  (`framework integrity`), so neither the proof nor a lakefile nor a dependency's build can
  change what `Janus.GoABI.Ensures` means or replace the auditor;
* **kernel-replays the whole non-core import closure** of the theorem (every `Janus.*` module it
  imports, `Extracted`, `JanusTrusted`, consumer and dependency modules), with passing results
  cached by content hash in the trusted cache.

See [docs/AUDIT.md](AUDIT.md) for the attacks these defend against.

Steps; any failure prints `Invalid:` with its stage and exits `1`:

1. **Withdraw** any previous `<outdir>/verified.json`. Only a successful run writes a new one.
2. **Check** the artifacts exactly as `janus check` does.
3. **Build the framework and `janus-audit`** (`lake build Janus Janus.Tools.Audit`) once in the
   cache (`Janus library build`).
4. **Compile the trusted copies**: the checked `Extracted.lean` as module `Extracted`, and a
   namespace-renamed copy as `JanusTrusted`, into a private read-only directory — no proof code
   involved.
5. **Compile the proof** as module `Proof` in a sandboxed, private work directory, with the
   trusted directory first on `LEAN_PATH`. Errors are summarised as `Lean errors (N):` with paths
   mapped back to the original files; the full output follows under `Details:` (`proof
   checking`). The proof may import `Extracted`, `Janus` and Lean/Std modules.
6. **Audit** with `janus-audit` (sandboxed): it imports `Extracted`, `JanusTrusted` and `Proof`
   without running their initializers, checks the theorem is a `theorem` in the proof module,
   checks `Extracted.program`/`entry` are defeq to `JanusTrusted`, enforces the statement rules
   above, collects transitive axioms (`collectAxioms`), pretty-prints the statement in the
   clean environment, checks its instance arguments and that the printed text re-elaborates to
   the checked type (`statement identity`), and prints it once more with `pp.explicit`. Only `propext`, `Quot.sound` and `Classical.choice` are allowed; anything
   else, including `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` and user axioms, is
   rejected (`axiom audit`). `--theorem` must be a plain **ASCII** dotted Lean name.
7. **Kernel replay**: `leanchecker` (shipped with the Lean toolchain) replays through the
   kernel every module of the theorem's import closure outside Lean core (`Init`, `Std`, `Lean`,
   `Lake`): every `Janus.*` framework module the environment imports, `Extracted`,
   `JanusTrusted` and `Proof` (for a consumer package also every consumer and dependency module).
   This catches environment hacking such as `set_option debug.skipKernelTC` with `addDecl`, in
   the proof or in any compiled module it imports (`kernel replay`). First every module must
   resolve from its home: core from the toolchain, `Janus.*` from the pinned framework build (and
   only modules the framework has a source for), `Extracted`/`JanusTrusted` from the trusted
   directory (`framework integrity`). Passing replays are cached in `v1/replay` of the cache,
   keyed by the SHA-256 of the module's `.olean` parts and, recursively, its imports' keys; the
   report's `kernelReplay.cached` lists the reused ones. The cache is not used with `--fresh` or
   `--unsafe-no-sandbox`. With `--replay-fresh` the theorem's module is also replayed with
   `leanchecker --fresh`. If the toolchain has no `leanchecker`, this step is skipped and
   `verified.json` records `"status": "unavailable"`.
8. **Re-check** the olean pins, the artifacts and the proof; they must be unchanged
   (`framework integrity`, `stale input`).
9. Write `verified.json`:

```json
{
  "schema": 1,
  "theorem": "Proof.correctness",
  "kind": "theorem",
  "module": "Proof",
  "statement": "Proof.correctness : Extracted.entry = Extracted.entry",
  "statementExplicit": "Proof.correctness : @Eq Nat Extracted.entry Extracted.entry",
  "axioms": [],
  "allowedAxioms": ["propext", "Quot.sound", "Classical.choice"],
  "kernelReplay": { "tool": "leanchecker", "status": "passed",
                    "modules": ["Extracted", "Janus", "Janus.Arm64.Bits", "…", "JanusTrusted", "Proof"],
                    "cached": ["Janus", "Janus.Arm64.Bits", "…"] },
  "sandbox": { "mode": "bwrap", "tool": "/usr/bin/bwrap" },
  "definitions": [],
  "proof": "../../cmd/janus/testdata/Trivial.lean",
  "proofSha256": "…",
  "extracted": "Extracted.lean",
  "extractedSha256": "…",
  "identitySha256": "…",
  "binary": "../examples-arm64",
  "binarySha256": "…",
  "symbol": "example.com/basic.Get",
  "address": "0x93140",
  "goVersion": "go1.26.0",
  "mainModule": "example.com/basic",
  "leanVersion": "Lean (version 4.34.1, …)",
  "framework": { "source": "embedded", "sha256": "1c26c3bb…", "files": 30, "toolchain": "leanprover/lean4:v4.34.1", "revision": "<commit>" },
  "janusRoot": "/root/.cache/janus/v1/framework/…",
  "janusCommit": "<git HEAD>[+dirty]",
  "extractorVersion": "0.2.0",
  "timestamp": "2026-10-23T09:56:16Z"
}
```

A verification establishes exactly the printed statement, with its hypotheses and quantifiers,
about the definitions in `Extracted`. `definitions` lists the body of each plain proof-local
`def` the statement uses. For a consumer package, `consumer.dependency` records janus and
`consumer.dependencies` every other dependency (name, type, URL, rev, inputRev, whether it is
inherited from another dependency, the number and tree SHA-256 of the files copied), and
`dependencyConstants` the dependency constants the statement uses, as `"<name> (<kind>,
<module>)"`; their meaning is that of the pinned dependency. `janus explain <verified.json>` prints a human-readable account of
what was proved.

### Framework

`janus framework [--json]` prints which Janus Lean framework the binary carries: its source
(`embedded` or a `--janus-root` directory), the SHA-256 over its sources, the toolchain and the
revision it was built from. This is the revision a consumer package pins its `janus` dependency
to; `janus init` writes it for you.

<a name="install"></a>
### Install

```sh
go install github.com/Giulio2002/Janus/cmd/janus@latest
```

The Janus Lean sources are embedded in the binary with `go:embed`, so the installed `janus`
needs no checkout: the framework it verifies against is exactly what it carries (the cleanest
identity story — the bundled sources and the version string move together). It is materialized
and built once under `~/.cache/janus` (override with `$JANUS_CACHE_DIR`). `--janus-root` /
`$JANUS_ROOT` override it with a checkout, for framework development. `janus` also needs Lean and
Lake (via elan), and bubblewrap for the sandbox.

### explain

```sh
janus explain <verified.json | outdir>
```

Prints the theorem and its statement, which function and address it is about, the binary and
Go module, the axioms and kernel replay, the framework, the consumer package and its
dependencies with their pinned revisions (if any), the dependency constants used and every
recorded hash together with whether the file on disk still matches it.

## Blockers

```sh
janus blockers <binary> <symbol>... [--max-functions N] [--janus-root DIR] [--json FILE]
janus blockers artifacts/examples-arm64 example.com/basic.Get example.com/basic.Bump main.main --max-functions 1000
```

```text
example.com/basic.Get: 1 function(s), 22 word(s) (22 distinct), 0 data object(s): all decoded
example.com/basic.Bump: 1 function(s), 6 word(s) (5 distinct), 0 data object(s): all decoded
  writable data referenced (not copied): example.com/basic.counter (.noptrbss)
main.main: 421 function(s), 37276 word(s) (14355 distinct), 81 data object(s): 674 rejected word(s)
  0x11de8  0x4cdf2c00  ld1 {v0.2d-v3.2d}, [x0],#64          runtime.memequal
  …
Summary: 3 symbol(s): 2 fully decoded, 1 with rejected words, 0 extraction failed (decoder: Janus.Arm64.decode via janus-decode, 14355 distinct words).
```

CI runs `blockers` on every `example.com/basic` function and requires all of them to be fully
decoded.

For each symbol, `blockers` computes the extraction exactly as `extract` does (nothing is
written) and runs every distinct copied word through **the trusted Lean decoder**: the
`janus-decode` executable (`Janus/Tools/Decode.lean`, `lake build janus-decode`, built
automatically in the Janus root) reads words on stdin and prints `ok <Instr>` or `none` per word
from `Janus.Arm64.decode`. A rejected word is exactly one whose execution faults with
`undecodable`, so a function is in the supported subset iff nothing is listed for it (a rejected
word only matters if execution can reach it). Each rejected word shows its first address, an
`arm64asm` disassembly (informational) and the function containing it. Writable data the code
references is listed too. Symbols whose extraction fails (unknown, or more than
`--max-functions`) are reported and skipped. `--json FILE` writes the full report, with every site.
The exit code is `0` whenever the report was produced, including when words are rejected.

## amd64 (x86-64) binaries

`list`, `extract` and `check` (and therefore `verify`) also accept linux/amd64 Go ELF binaries
(`EM_X86_64`, build setting `GOARCH=amd64`); `blockers` is arm64-only and refuses them.

```
scripts/build-examples-amd64.sh     # builds artifacts/examples-amd64, extracts artifacts/amd64/<Name>
janus extract artifacts/examples-amd64 example.com/basic.Add artifacts/amd64/Add
```

Differences from arm64:

* A segment is the raw bytes of the symbol's `[addr, addr+size)` in `.text`, copied as is (no
  alignment, nothing trimmed); Lean decodes the variable-length instructions from them.
  `Extracted.lean` defines `segments : List Amd64.Segment` (`{ name, base, bytes }`, 16 bytes
  per line) and `program : Amd64.Program`; `Stub`, `DataSegment`, `exitAddr` and `entry` are as
  for arm64. Above 8192 code bytes, segments get one definition each (`maxRecDepth` raised above
  4096 bytes).
* Reachability is a linear sweep with `golang.org/x/arch/x86/x86asm` following direct
  `JMP`/`Jcc`/`CALL`/`LOOP`/`JRCXZ` targets (undecodable bytes are skipped one at a time). Like
  the arm64 analysis it is untrusted and only selects what to copy.
* Read-only data references are the RIP-relative operands: `LEA r, [rip+d]` (kind `rip-lea`)
  and loads/stores through `[rip+d]` (`rip-mem`), with target = next instruction + `d`.
* `identity.json` records `goarch: "amd64"`, `goamd64` (the `GOAMD64` build setting) and, per
  function, `bytes` (the copied byte count; `words` is 0). These fields are omitted for arm64,
  whose artifacts are unchanged.

## Tests

```sh
go test ./cmd/...           # includes Lean verification (several minutes; needs bubblewrap)
go test -short ./cmd/...    # extraction, check and package validation only
audit/run-all.sh            # every attack in docs/AUDIT.md: each row blocked or honest
```

The Lean tests need a working sandbox (bubblewrap, or unprivileged user namespaces); on Ubuntu
24.04 runners that restrict them via AppArmor, CI runs
`sysctl kernel.apparmor_restrict_unprivileged_userns=0` first. `hardening_test.go` has one
regression test per audit attack: a disguised proof-local instance (A1), an unexpander that
would rewrite the printed statement (A2/A4), a forging `initialize` (A3), `#eval` IO trying to
write outside the sandbox (A6), `skipKernelTC` (A5), private and namespace shadows of
`Extracted` (A7, A9), `#exit` (A10), a stray `Extracted.olean` on the search path (C1), PIE
binaries (E1/F6), and the sandbox mode recorded in the report. `consumer_test.go` covers
consumer packages (`lakefile.toml` and `lakefile.lean`, path and git dependencies), batches,
`init`, `explain` and an install built outside the repository.

The tests build the example binary, extract every example function, cross-check every copied
word and every direct-branch target against `aarch64-linux-gnu-objdump -d` (skipped when it is
not installed), check that only zero words were trimmed, exercise `check` on edited, forged and
moved artifacts and on a changed binary, and run `verify` on accepted proofs and on proofs that
must be rejected: `sorry`, `native_decide`, a user axiom, a type error, a missing theorem, a
`def`, a theorem from another module, and a `skipKernelTC` forgery caught by `leanchecker`.
The data tests (`data_test.go`) use the data examples: the references found in `Table`,
`HexDigit`, `SetOne256`, `GlobalTable` and `Bump` are cross-checked against the `adrp` pairs in
`objdump -d` and the copied bytes byte for byte against `objdump -s`; the writable globals of
`GlobalTable` and `Bump` must be reported and not copied; and `check` must reject an edited data
byte or a dropped data record. `main.main` (about 80 objects, 40 KB) covers the rendering with
one definition per object: it is cross-checked against objdump the same way, passes `check`,
rejects an edited byte and, without `-short`, verifies a proof about `Extracted.program.data`. `TestBlockers` runs
`janus-decode`.
