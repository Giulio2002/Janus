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
janus extract <binary> <symbol> <outdir> [--max-functions N] [--targets SYM,...] [--contract SYM]... [--global SYM]...
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
   `CGO_ENABLED=0`), not `-buildmode=pie`. Then detects the **instrumented build modes**
   (`-race`, `-msan`, `-asan`, `-d=libfuzzer`, `-cover`, `-d=checkptr`, `-spectre=ret`) and
   rejects or records them before anything is extracted; see [Build modes](#build-modes).
2. Finds the symbol (exact, case-sensitive name as printed by `list`; ambiguous names fail).
3. Copies the function's raw 32-bit little-endian words from `.text`. Words are never
   translated. Trailing zero words (the linker's `udf #0` padding up to the next function) are
   trimmed; nothing inside the function is.
4. Computes the transitive set of **direct-branch callees**: every `BL`, `B`, `B.cond`,
   `CBZ`/`CBNZ` and `TBZ`/`TBNZ` whose target lies outside the current function. Targets are
   found with `golang.org/x/arch/arm64/arm64asm`. This decoding is untrusted: it only chooses
   which code to copy. A missed target is simply absent and the Lean model faults with `noCode`
   if execution reaches it, which is sound. Indirect branches (`BR`, `BLR`) cannot be followed;
   their possible targets are added as **dynamic targets** (step 8). Branches into no known
   function are reported as warnings and recorded in `identity.json` under
   `unresolvedBranches`. Calls of `runtime.deferreturn` are not followed (see step 8).
5. Records known runtime stubs instead of copying them:
   * `.panic`: the go1.26 runtime's panic functions, by exact linked name (`runtime.gopanic`,
     `runtime.goPanic*`, `runtime.panicBounds`, `runtime.panicdivide`, `runtime.panicshift`,
     `runtime.panicmem`, `runtime.panicwrap`, …; the list is `runtimePanicStubs` in
     `cmd/janus/extract.go`);
   * `.morestack`: `runtime.morestack.abi0` and `runtime.morestack_noctxt.abi0` (the
     stack-growth path of every function prologue).
   * `.syscall` (function level): the vDSO clock functions, `runtime.walltime.abi0` and
     `runtime.nanotime1.abi0` on arm64, `runtime.nanotime1.abi0` and `time.now` on amd64
     (`runtimeKernelStubs` in `cmd/janus/kernel.go`; authenticated and pinned like every stub).

   In every copied function it also puts **instruction-level stubs** (`cmd/janus/kernel.go`):
   `.syscall` on each `SVC #0`/`SYSCALL` and each environment read (`MRS` of `CNTVCT_EL0`,
   `CNTFRQ_EL0`, `MIDR_EL1`, `DIT`, `MSR DIT`; `CPUID`, `XGETBV`, `RDTSC`, `RDTSCP`), named
   `syscall` or `env:<register>`, and `.trap` on each trap instruction (`trap:BRK`, `trap:UDF`,
   `trap:INT3`, `trap:UD2`, `trap:HLT`; the zero / `INT3` padding after a function's last
   instruction and the targets of `LDR (literal)` excepted). Their effect is given by the kernel
   semantics of `Janus/Contracts/Syscall.lean` (`EnsuresK`, `ReturnsK`, `Traps`); the Lean side
   checks the instruction at each stub, so the placement is not trusted. `janus verify` prints
   `Kernel interface: …` and `Trap sites: …` and records `kernel` and `traps` in
   `verified.json`; `janus explain` prints them with what they mean.

   Names are matched exactly; no suffix is stripped. A listed name counts only in a go1.26
   binary with an ELF symbol table, when no other function has the same name (any package can
   name an assembly function or a `//go:linkname` push `runtime.panicX`;
   docs/AUDIT-ROUND7.md G1). Otherwise extraction stops with an error.
6. Records **runtime contracts** instead of copying them: `--contract SYM` (repeatable; a glob
   where `*` matches any run of characters including `.` and `/` and `?` one character; a name
   matches with or without its `.abi0`/`.abiinternal` suffix) names functions whose direct
   callers are not followed into them. Each matched callee is listed in `Extracted.lean` as
   `def contracts : List (String × Nat)` (and `contracts := contracts` in `program`; omitted when
   empty, so extractions without `--contract` are unchanged), and in `identity.json` with the
   patterns (`contractPatterns`, `contracts`). Stubs keep their stub meaning even if a pattern
   matches them; the entry function must not match. A pattern that matches no called function
   gets a `Note:`. There is no code at a contract address, so a run reaching it faults with
   `noCode` unless the theorem assumes the function's behaviour as a contract hypothesis
   ([RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md)). `janus verify` prints
   `Runtime contracts assumed: …` and records `contracts` in `verified.json`; `janus explain`
   prints `runtime contracts assumed: …`.
7. Copies every other reachable function, runtime or not. `--max-functions N` (default 64)
   fails the extraction when more are reachable, listing them. For example `main.main` of the
   example binary reaches 421 functions through `println` and the allocator.
8. Copies the **read-only data** the copied code references (see [Read-only data](#read-only-data)).
9. Adds **dynamic targets**, the code an indirect call may reach (interface methods, closures,
   method values, deferred closures; see [docs/RUNTIME-CONTRACTS.md](RUNTIME-CONTRACTS.md#dynamic-calls)),
   and everything they reach in turn:
   * `--targets SYM,...` names them: a function, a static itab `go:itab.*T,I` (its `Fun[k]`
     methods are copied, and the itab itself becomes a data object named after its symbol, which
     `Janus.Spec.ItabIs` refers to), or a static funcval `…·f` (its function). An itab name
     contains a comma of its own and is kept together:
     `--targets 'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher,example.com/basic.F.func1'`;
   * inferred, from functions outside the standard library (package `main`, or a path whose
     first element contains a dot): a function entry the code computes (`ADRP`+`ADD`, `LEA`:
     a closure or method-value wrapper it builds), and the itabs and funcvals it loads from
     `.rodata`.

   Like reachability this is untrusted: a missing target faults (`noCode`) when called.
   `runtime.deferreturn` is never followed: functions with open-coded defers call it only after a
   recovered panic (out of scope); it is recorded under `omittedCalls`.

   A dynamic target that matches a `--contract` pattern becomes a contract instead of being
   copied, and `--contract` takes precedence over the built-in omission of `runtime.deferreturn`.
10. Copies the **link-time images of writable globals** named by `--global SYM` (repeatable; an
    exact name or a glob as for `--contract`, e.g. `'math/big.*Threshold'`): for each writable data
    symbol (`.data`, `.noptrdata`, `.bss`, `.noptrbss`; it must lie in one writable section that a
    writable `PT_LOAD` maps from the file, or for `NOBITS` zero-fills past the file image), its
    address, size and file bytes (none for `.bss`/`.noptrbss`: the loader zeroes them), as
    `def globals : List GlobalSegment` (and `globals := globals` in `program`; omitted without
    `--global`, so other extractions are unchanged) and in `identity.json` (`globalPatterns`,
    `globals`: name, address, size, section, SHA-256 of the bytes). A read-only symbol, an unknown
    name, a stripped binary (no `.symtab`) or two partly overlapping symbols are errors. A
    **pointer chain** `SYM[+OFF]->SIZE…` follows the pointer the link-time image of `SYM` holds at
    offset `OFF` (default 0) to `SIZE` writable bytes, and records them as a global named by the
    chain itself: a package-level `&T{…}` or a slice literal is an anonymous static object with no
    symbol of its own (`'math/big.intOne->32'` is the `Int` that `intOne` points to,
    `'math/big.intOne->32+8->8'` the word its `abs` slice holds, the same bytes as
    `'math/big.natOne->8'`). A reference the code makes to a recorded global is reported with a
    `Note:` instead of the writable-data warning. Theorems use the list through
    `Janus.Spec.GlobalsInit` / `GlobalIs` / `GlobalBytesIs` ([PROOFS.md](PROOFS.md#writable-globals-mulalgo-double));
    the images are checked by `janus check` like the code, and `janus-audit` rejects a statement
    that names a global the extraction does not record.

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
copied words after trimming. Extractions with dynamic targets also record `targets` (the
`--targets` list, which `janus check` re-applies), `dynamicTargets` (each added function with
`via` = `targets`, `itab`, `funcval` or `code-address` and `from`, the itab/funcval symbol or the
instruction computing the address) and `omittedCalls` (direct calls not followed, with the
reason); these fields are absent when empty. A binary built in an accepted instrumented mode
records `buildModes` (`"cover"`, `"checkptr"`, `"spectre=ret"`; see [Build modes](#build-modes)),
absent for an ordinary build. For `HashWith` extracted with both itabs:

```json
  "targets": [ "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher",
               "go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher" ],
  "dynamicTargets": [
    { "name": "example.com/basic.(*MulHasher).Hash", "address": "0x8d070", "via": "itab",
      "from": "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher" }, … ],
```

`data`, `dataReferences` and `skippedData` are described under
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

### Build modes

Some `go build` flags rewrite the compiled code. `extract` (and so `check` and `verify`, which
regenerate the extraction) detects them from the binary: from the ELF symbol tables (`.symtab`,
`.dynsym`, or the pclntab's functions), the section headers and the build settings of
`debug/buildinfo`. It then rejects the binary or accepts it; nothing is silently extracted as if
the build were ordinary (`cmd/janus/buildmode.go`).

| mode | detected by | decision |
| --- | --- | --- |
| `-race` | `runtime.racefuncenter`, `runtime.raceread` or `__tsan_init`, or the setting `-race=true` | rejected |
| `-msan` | `runtime.msanread` or `__msan_init`, or `-msan=true` | rejected |
| `-asan` | `runtime.asanread` or `__asan_init`, or `-asan=true` | rejected |
| `-gcflags=-d=libfuzzer` | `runtime.libfuzzerTraceCmp*`, `runtime.libfuzzerTraceConstCmp*`, `runtime.libfuzzerHookStrCmp`, `runtime.libfuzzerHookEqualFold`, a `__sancov_cntrs` section or its `__start___sancov_cntrs` symbol | rejected |
| `-cover` | `runtime.covctrs` < `runtime.ecovctrs` (both are in every binary; the counters lie between them), `runtime.addCovMeta`, or `-cover=true` | accepted, `"cover"` |
| `-gcflags=-d=checkptr` | the extraction copies `runtime.checkptrAlignment` or `runtime.checkptrArithmetic`, or records one as a contract | accepted, `"checkptr"` |
| `-gcflags=-spectre=ret` (amd64; the arm64 compiler rejects it) | a retpoline thunk `runtime.retpolineAX` … `runtime.retpolineR15` | accepted, `"spectre=ret"` |

A symbol name matches with or without its `.abi0`/`.abiinternal` suffix. The rejected modes are
binary-wide: the whole program's semantics rely on the instrumented C runtime, so the binary is
rejected before anything is extracted, even for an entry function that does not itself call the
instrumentation. They print (`Stage: code extraction`, `Next: Rebuild the program without <flag>
(the same go build command without the flag) and extract from that binary.`):

```text
Error: built with -race: the race detector instruments every memory access with calls into the ThreadSanitizer runtime (runtime.raceread, ...); concurrency is out of scope for Janus (docs/SOUNDNESS.md). Rebuild without -race.
Error: built with -msan: every load and store calls the MemorySanitizer C runtime (runtime.msanread -> __msan_read_go) through the cgo boundary, whose shadow memory, reports and aborts Janus does not model. A Janus proof already establishes that every access stays inside the memory the precondition grants, which is what the sanitizer checks dynamically: verify the binary built without -msan.
Error: built with -asan: every load and store calls the AddressSanitizer C runtime (runtime.asanread -> __asan_read_go) through the cgo boundary, whose shadow memory, reports and aborts Janus does not model. A Janus proof already establishes that every access stays inside the memory the precondition grants, which is what the sanitizer checks dynamically: verify the binary built without -asan.
Error: built with -d=libfuzzer: comparisons call libFuzzer's C hooks (runtime.libfuzzerTraceCmp*, __sanitizer_cov_trace_cmp*) and the 8-bit coverage counters live in the libFuzzer section __sancov_cntrs; a libFuzzer build is a c-archive for libFuzzer's C driver, not a Go program Janus verifies. Verify the binary built without -d=libfuzzer.
```

(`-race`, `-msan` and `-asan` also turn on `-d=checkptr`; the rejection comes first.)

The accepted modes are recorded in `identity.json` as `buildModes`, in the order `cover`,
`checkptr`, `spectre=ret` (absent for an ordinary build, whose identity is unchanged), and
`check` regenerates them. `-cover` and `-spectre=ret` are binary-wide, so they are recorded for
every function extracted from such a binary; `checkptr` only when the extracted code reaches a
check. `extract` prints one line per mode on stderr:

```text
note: built with -cover: coverage counter updates are ordinary stores into the package's counter variable; a theorem states them (Janus/Contracts/Instrument.lean, CovBlock)
note: built with -d=checkptr: the code calls the runtime's pointer checks (runtime.checkptrAlignment, runtime.checkptrArithmetic), which are extracted as code unless --contract names them
note: built with -spectre=ret: indirect calls go through the runtime's retpoline thunks, which are executed like any other code; their targets are dynamic call targets (--targets)
```

* `-cover`: the counter updates are ordinary stores of the covered function into the package's
  counter variable (writable `.noptrbss`, which the extractor does not copy; it reports the
  references as `skippedData`). A theorem states them, with the counter bytes writable in its
  precondition (`CovBlock`).
* `-d=checkptr`: the checks are ordinary runtime code, copied like any other callee, or
  contracts when `--contract` names them.
* `-spectre=ret`: an indirect `CALL` goes to the thunk of its register, ordinary runtime assembly
  that the extraction copies and executes (an indirect jump to the register); the jump's targets
  are dynamic call targets, as for any indirect call.

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

`check` reads `identity.json`, re-runs the extraction in memory with the recorded symbol,
`--max-functions` and `--contract` patterns, and byte-compares it with the saved files without writing anything. If the
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

### Go assembly entries (ABI0)

Hand-written assembly needs no option ([ABI0.md](ABI0.md)). An assembly function is linked under
its ABI0 name: `janus extract bin example.com/asm.XorSlice.abi0 out` extracts the `.s` body;
`example.com/asm.XorSlice` is the ABIInternal wrapper the compiler generates when Go code uses
the function as a func value (it is extracted with the body it calls). Direct calls between Go
and assembly, in both directions, are followed like any call. When the entry is Go assembly or
an ABI wrapper, `extract` prints its convention after the summary line:

```text
Extracted example.com/asm.XorSlice: 2 function(s), 21 word(s), 0 stub(s), 0 data object(s) (0 bytes) into out/Extracted.lean
  entry: ABI wrapper: ABIInternal entry calling the ABI0 assembly function (arguments and results in registers); state theorems with Janus.GoABI.Ensures (docs/ABI0.md)
```

and `identity.json` records it after `size`:

```json
  "entryABI": "ABI0",
  "entrySource": "assembly",
```

`entryABI` is `ABI0` or `ABIInternal` (runtime assembly declared `<ABIInternal>`, and the
ABIInternal side of a wrapper); `entrySource` is `assembly` (the pclntab file of the entry is a
`.s` file) or `abi-wrapper` (`<autogenerated>`: a `g.abi0` wrapper of a Go function, or an `f`
wrapper next to an `f.abi0`). Both are absent for ordinary Go code, so its identities are
unchanged. `verify` copies them into `verified.json` and appends the convention to its `Entry:`
line (`Entry: example.com/asm.Twice.abi0 at 0x489300 (Go assembly, ABI0)`), `explain` prints a
`Calling convention:` line, and `verify` prints

```text
Warning: the entry function follows ABI0, but the statement uses GoABI.Ensures (ABIInternal) on Extracted.entry: …
```

when the contract applied to `Extracted.entry` is the other convention's (`GoABI.Ensures*` on an
ABI0 entry, `GoABI0.Ensures0*` on Go code). It is a warning, not a rejection: such a theorem is
still true, but about calls the program does not make. A missing name whose `.abi0` body
exists gets a hint (`internal/cpu.getMIDR.abi0 exists: Go assembly is linked under its ABI0
name; …`). The classification is informational and untrusted, like reachability.

## Verify

```sh
janus verify <outdir> [--proof FILE] [--theorem NAME] [--proof-root PKG [--allow-path-deps]] [--json]
             [--fresh] [--replay-fresh] [--janus-root DIR] [--binary PATH] [--unsafe-no-sandbox] [--asl]
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

`verify` first runs `check`, which regenerates the extraction, so the [build-mode](#build-modes)
detection applies again: a binary built with `-race`, `-msan`, `-asan` or `-d=libfuzzer` is
rejected (`Invalid: built with …`), and the recorded `buildModes` must match.

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

`--asl` additionally derives the theorem's **ASL corollary**: the same statement about Arm's ASL
(the Sail arm-v9.4-a model translated to Lean), from `JanusASL`'s `Ensures.toASL` applied to the
verified theorem about the identity-checked `Extracted.program`, after the kernel has checked that
every instruction word is in the subset proved equivalent to the ASL. It is audited by the same
trusted auditor, kernel-replayed (ArmASL included) and recorded under `asl` in `verified.json`,
with the model's version and hash and the assumptions in plain words; `janus explain` prints it.
A failure of this stage (`ASL coverage`, `ASL corollary`, `ASL audit`, …) prints `Invalid: ASL
corollary: …` and exits 1, but leaves the verified theorem and its `verified.json` in place. **The
first `--asl` run builds the JanusASL package in the cache: about an hour and 1 GB**, once per
framework and JanusASL version. Details: [docs/ASL.md](ASL.md#janus-verify---asl-the-corollary-of-a-verified-theorem).

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

### Memory limit

Every Lean-family process janus starts (lean, leanchecker, lake, `janus-audit`, `janus-decode`)
runs inside a **cgroup v2 memory limit** (`memory.max`, no swap), so a runaway job (a proof that
elaborates a huge term, a large kernel replay) is killed on its own by the kernel's cgroup OOM
killer instead of exhausting the host. The cgroup is entered before the sandbox starts, so it
covers the whole sandboxed process tree. A job killed for memory makes verification fail with

```
Invalid: lean Proof.lean Proof.olean exceeded the memory limit and was killed (limit 1.0 GiB, measured peak 1.0 GiB, mechanism systemd-user). This is not a verdict on the proof.
  Stage: resource limit
```

never with the proof or audit error the killed process would otherwise have caused, and no
`verified.json` is written. A successful report records the guard in `memoryGuard`: mechanism,
limit, the largest measured `memory.peak` of its jobs and how many jobs ran.

* `JANUS_MEM_MAX`: the per-job limit (`16G`, `1500M`, `off`); default min(24 GiB, 40% of RAM).
  `lake build` gets `LEAN_NUM_THREADS` (lake's job count) = limit / `JANUS_LAKE_JOB_MEM` (default
  3G), at most `JANUS_LEAN_THREADS_MAX`.
* `JANUS_LEAN_THREADS_MAX`: a CPU cap on one job's Lean parallelism (lake's job count, and the
  default of `memguard_jobs` in `scripts/lib/memguard.sh`); default max(2, CPUs/8), so that
  several concurrent jobs on one host do not each take every core.
* Mechanism, first that works: a child cgroup of a delegated `$JANUS_MEMGUARD_CGROUP` (set by
  `scripts/lib/memguard.sh`, so janus's limits nest inside a script's or a parallel slot's);
  `systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=0` (janus re-runs itself in the
  scope as a small supervisor that reads the scope's `memory.peak`); the same with the system
  manager as root; `prlimit --as` (limit + 16 GiB per process: weak, Lean reserves ~10 GiB of
  address space up front); none, with a warning. `JANUS_MEMGUARD=<mechanism>` forces one.
* `janus memguard` prints the active mechanism (and why stronger ones were skipped);
  `janus memguard -- CMD ARGS…` runs a command under it. Verification warns on stderr when no
  mechanism is available; `JANUS_MEMGUARD_VERBOSE=1` makes it always name the mechanism
  (`janus: memory guard: …`), `JANUS_MEMGUARD_LOG=1` also prints one line per job with its peak.

See docs/TESTING.md (Memory guard) for the measured peaks.

### Framework

`janus framework [--json]` prints which Janus Lean framework the binary carries: its source
(`embedded` or a `--janus-root` directory), the SHA-256 over its sources, the toolchain and the
revision it was built from, and the JanusASL package `--asl` uses (its hashes, the cache
directory of its build and whether it is built yet). This is the revision a consumer package pins its `janus` dependency
to; `janus init` writes it for you.

<a name="cache"></a>
### Cache

```sh
janus cache du [--json]
janus cache gc [--max SIZE] [--dry-run] [--grace DUR] [--all] [--janus-root DIR] [--json]
```

Everything janus keeps between runs lives under `$JANUS_CACHE_DIR` (default `~/.cache/janus`),
which must be private to the user (docs/AUDIT-ROUND8.md, C1):

| directory | entry | size | in use |
|---|---|---|---|
| `v1/framework/<key>` | the framework build, one per framework version (`.lock`, `.ready` next to it) | ~370 MB | shared lock |
| `v1/asl/<key>` | the JanusASL build for `--asl`, per framework, JanusASL version and framework directory | 1–2.5 GB, ~1 h to build | `.lock` while built, `.use` (shared) while used |
| `v1/consumer/<family>/<ws>` | one workspace per consumer package, framework and extraction | 100–300 MB | exclusive lock |
| `v1/trusted/<xx>/<key>` | compiled `Extracted`/`JanusTrusted` modules (HMAC-authenticated manifest) | ~1 MB | — |
| `v1/result/<xx>/<key>.json` | recorded verification results (HMAC-authenticated; the key is `v1/result/.key`) | ~7 KB | — |
| `v1/replay/…` | one empty marker per passing kernel replay | 4 KB | — |
| `v1/tmp`, `v1/run` | temporary trees of running (or killed) processes | | — |

`janus cache du` lists, per kind, the number of entries, their disk usage, how many are in use
(their lock is held by another process) and the oldest and newest last use, then the total and
the budget. `--json` prints the same as one object.

**Collection.** After every `janus verify`, `verify-batch` and `blockers` (at most once a minute
per cache, unless the filesystem is nearly full), and on `janus cache gc`, janus collects the
cache (`cmd/janus/cachegc.go`):

1. Temporary trees in which nothing changed for `$JANUS_CACHE_TMP_HOURS` (24) are removed.
2. Framework builds and consumer workspaces unused for `$JANUS_CACHE_RETENTION_DAYS` (7) and
   JanusASL builds unused for `$JANUS_ASL_RETENTION_DAYS` (30) are removed.
3. While the cache is larger than its **budget**, the least recently used entries are removed,
   in order of age divided by a weight (JanusASL builds 4, framework builds 2, everything else
   1: an older JanusASL build may outlive a newer workspace, since it costs an hour to rebuild).
   The budget is `--max` or `$JANUS_CACHE_MAX`: a size (`40G`, `500M`, `1.5GiB`, bytes), a
   percentage of the filesystem (`10%`) or `off`. The default is min(40 GiB, 10% of the
   filesystem), and min(8 GiB, 5%) when the cache is on a tmpfs (RAM). When the filesystem has
   less than min(20 GiB, 5%) free, the budget shrinks by the shortfall (also with `off`).

Never removed: an entry in use (janus takes its lock exclusively without waiting, so a running
verification's workspace, framework or JanusASL build is skipped; concurrent `janus verify`
processes are safe); an entry used within the grace period (`--grace`, default `10m`); the
framework and JanusASL builds the running janus uses, and for `janus cache gc` those of the
current framework (embedded, or `--janus-root`/`$JANUS_ROOT`), unless `--all`; the result key.
An entry's last use is the newest time of its directory and lock files, which janus sets on
every use (and of the file itself for result, trusted and replay entries, set on every hit).

`--dry-run` lists what would be removed without changing anything. `JANUS_CACHE_GC=off` turns
the automatic collection off (`janus cache gc` still works). `janus cache gc --max 0 --grace 0s
--all` removes everything not in use; the next verification rebuilds what it needs. Removing
entries never changes a verdict: every cache entry is checked when it is read and rebuilt from
the same inputs when missing (docs/SOUNDNESS.md, "Cache eviction").

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
recorded hash together with whether the file on disk still matches it. For an `--asl` report it
also prints the ASL corollary, how it was derived, the instruction coverage, its assumptions in
plain words (`Rel`, `LinuxEL0Config`, and `UserMapped` once load/store classes are proved), its
axioms and replay, and the ASL model's version and SHA-256 (or why the corollary was not
derived).

## Blockers

```sh
janus blockers <binary> <symbol>... [--max-functions N] [--contract SYM]... [--janus-root DIR] [--json FILE]
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
(`EM_X86_64`, build setting `GOARCH=amd64`); `blockers` handles them too: it sweeps each extracted function with x86asm (untrusted, it only finds instruction starts) and runs the bytes from each start, at most 15, through `Janus.Amd64.decode`. It reports an instruction when Lean rejects it, or when Lean decodes a different length than x86asm.

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
go test -timeout 60m ./cmd/...   # includes Lean verification (several minutes; needs bubblewrap)
go test -short ./cmd/...    # extraction, check and package validation only
audit/run-all.sh            # every attack in docs/AUDIT.md: each row blocked or honest
JANUS_TEST_ASL=1 go test -run TestASL ./cmd/janus   # --asl: builds JanusASL once (about an hour)
```

The tests use their own cache, never the user's: `$JANUS_TEST_CACHE_DIR` if set, else
`~/.cache/janus-test` (`$XDG_CACHE_HOME/janus-test`), or `/var/tmp/janus-test-cache-<uid>` if
that is on a RAM filesystem. It is not under `/tmp`, which is a tmpfs on many hosts: the
framework and JanusASL builds and one workspace per consumer test made it tens of GB of RAM. The
collector bounds it like any cache (`cachegc_test.go` tests the collector itself on private
fixture caches, and `TestCacheGCConcurrentVerify` runs verifications while it empties the cache).

The `--asl` tests (`asl_test.go`) run only with `JANUS_TEST_ASL=1`; `JANUS_TEST_ASL_SEED=<dir>`
seeds the test cache's JanusASL build from a built package (e.g. `JanusASL` after
`scripts/asl.sh build`). They derive the corollaries of Add, Max, Mul64 and Add128 from their
artifacts, check that Get's load is reported as uncovered, run the forgery attacks of
`audit/asl/attacks` and the consumer and batch paths.

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
